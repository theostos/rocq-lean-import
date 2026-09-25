open LeanExpr
module N = LeanName

module RRange = LeanParseShared.RRange

let do_bk = function
  | "#BD" -> NotImplicit
  | "#BI" -> Maximal
  | "#BS" -> NonMaximal
  | "#BC" -> Typeclass
  | bk ->
    CErrors.user_err
      Pp.(str "unknown binder kind " ++ str bk ++ str "." ++ fnl ())

let do_notation_kind = function
  | "#PREFIX" -> Prefix
  | "#INFIX" -> Infix
  | "#POSTFIX" -> Postfix
  | k -> assert false

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
  }

let get_name state n =
  let n = int_of_string n in
  RRange.get state.names n

let get_expr state e =
  let e = int_of_string e in
  RRange.get state.exprs e

let rec do_ctors state nctors acc l =
  if nctors = 0 then (List.rev acc, l)
  else
    match l with
    | name :: ty :: rest ->
      let name = get_name state name
      and ty = get_expr state ty in
      do_ctors state (nctors - 1) ((name, ty) :: acc) rest
    | _ -> CErrors.user_err Pp.(str "Not enough constructors")

let pop_params = LeanParseShared.pop_params
let fix_ctor = LeanParseShared.fix_ctor

let as_univ state s = RRange.get state.univs (int_of_string s)

let parse_hexa c =
  if '0' <= c && c <= '9' then int_of_char c - int_of_char '0'
  else if 'A' <= c && c <= 'F' then 10 + int_of_char c - int_of_char 'A'
  else if 'a' <= c && c <= 'f' then 10 + int_of_char c - int_of_char 'a'
  else
    CErrors.user_err
      Pp.(
        str "Invalid hexadecimal digit "
        ++ str (String.make 1 c)
        ++ str " in string literal")

let parse_char s =
  if String.length s <> 2 then
    CErrors.user_err
      Pp.(
        str "Expected two hexadecimal digits for a string byte, got "
        ++ int (String.length s));
  Char.chr ((parse_hexa s.[0] * 16) + parse_hexa s.[1])

let quot_name = LeanParseShared.quot_name

let do_line ~lcnt state l =
  let line_msg name =
    Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)
  in
  (* Lean printing strangeness: sometimes we get double spaces (typically with INFIX) *)
  match
    List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim l))
  with
  | [] -> (state, None) (* empty line *)
  | "#DEF" :: name :: ty :: body :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and body = get_expr state body
    and univs = List.map (get_name state) univs in
    let def = { name; ty; body; univs; hint = LegacyHint; kernel_opaque = false } in
    (state, Some (Entry (Def def)))
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { name; ty; univs } in
    (state, Some (Entry (Ax ax)))
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let name = get_name state name in
    line_msg name;
    let nparams = int_of_string nparams
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let params, ty = pop_params nparams ty in
    let ctors, univs = do_ctors state nctors [] rest in
    let ctors =
      List.map (fun (nctor, ty) -> (nctor, fix_ctor name nparams ty)) ctors
    in
    let univs = List.map (get_name state) univs in
    let ind = { name; params; ty; ctors; univs } in
    (state, Some (Entry (Ind ind)))
  | [ "#QUOT" ] ->
    line_msg quot_name;
    (state, Some (Entry (Quot quot_name)))
  | (("#PREFIX" | "#INFIX" | "#POSTFIX") as kind) :: rest ->
    (match rest with
    | [ n; level; token ] ->
      let kind = do_notation_kind kind
      and n = get_name state n
      and level = int_of_string level in
      (state, Some (Nota { kind; head = n; level; token }))
    | _ ->
      CErrors.user_err
        Pp.(
          str "bad notation: " ++ prlist_with_sep (fun () -> str "; ") str rest))
  | next :: rest ->
    let next =
      try int_of_string next
      with Failure _ ->
        CErrors.user_err Pp.(str "Unknown start of line " ++ str next)
    in
    let state =
      match rest with
      | [ "#NS"; base; cons ] ->
        assert (next = RRange.length state.names);
        let base = get_name state base in
        let cons = N.append base cons in
        { state with names = RRange.append state.names cons }
      | [ "#NI"; base; cons ] ->
        assert (next = RRange.length state.names);
        (* NI: private name. cons is an int, base is expected to be _private :: stuff
           (true in lean stdlib, dunno elsewhere) *)
        let base = get_name state base in
        let n = N.raw_append base cons in
        { state with names = RRange.append state.names n }
      | [ "#US"; base ] ->
        assert (next = RRange.length state.univs);
        let base = as_univ state base in
        { state with univs = RRange.append state.univs (Succ base) }
      | [ "#UM"; a; b ] ->
        assert (next = RRange.length state.univs);
        let a = as_univ state a
        and b = as_univ state b in
        { state with univs = RRange.append state.univs (Max (a, b)) }
      | [ "#UIM"; a; b ] ->
        assert (next = RRange.length state.univs);
        let a = as_univ state a
        and b = as_univ state b in
        { state with univs = RRange.append state.univs (IMax (a, b)) }
      | [ "#UP"; n ] ->
        assert (next = RRange.length state.univs);
        let n = get_name state n in
        { state with univs = RRange.append state.univs (UNamed n) }
      | [ "#EV"; n ] ->
        assert (next = RRange.length state.exprs);
        let n = int_of_string n in
        { state with exprs = RRange.append state.exprs (Bound n) }
      | [ "#ES"; u ] ->
        assert (next = RRange.length state.exprs);
        let u = as_univ state u in
        { state with exprs = RRange.append state.exprs (Sort u) }
      | "#EC" :: n :: univs ->
        let n = get_name state n in
        assert (next = RRange.length state.exprs);
        let univs = List.map (as_univ state) univs in
        { state with exprs = RRange.append state.exprs (Const (n, univs)) }
      | [ "#EA"; a; b ] ->
        assert (next = RRange.length state.exprs);
        let a = get_expr state a
        and b = get_expr state b in
        { state with exprs = RRange.append state.exprs (App (a, b)) }
      | [ "#EZ"; n; ty; v; rest ] ->
        assert (next = RRange.length state.exprs);
        let n = get_name state n
        and ty = get_expr state ty
        and v = get_expr state v
        and rest = get_expr state rest in
        {
          state with
          exprs = RRange.append state.exprs (Let { name = n; ty; v; rest });
        }
      | [ "#EL"; bk; n; ty; body ] ->
        assert (next = RRange.length state.exprs);
        let bk = do_bk bk
        and n = get_name state n
        and ty = get_expr state ty
        and body = get_expr state body in
        { state with exprs = RRange.append state.exprs (Lam (bk, n, ty, body)) }
      | [ "#EP"; bk; n; ty; body ] ->
        assert (next = RRange.length state.exprs);
        let bk = do_bk bk
        and n = get_name state n
        and ty = get_expr state ty
        and body = get_expr state body in
        { state with exprs = RRange.append state.exprs (Pi (bk, n, ty, body)) }
      | [ "#EJ"; ind; field; term ] ->
        let ind = get_name state ind
        and field = int_of_string field
        and term = get_expr state term in
        {
          state with
          exprs = RRange.append state.exprs (Proj (ind, field, term));
        }
      | [ "#ELN"; n ] ->
        let n = Z.of_string n in
        { state with exprs = RRange.append state.exprs (Nat n) }
      | "#ELS" :: bytes ->
        let s = Seq.map parse_char (List.to_seq bytes) in
        let s = String.of_seq s in
        { state with exprs = RRange.append state.exprs (String s) }
      | _ ->
        CErrors.user_err
          Pp.(str "cannot understand " ++ str l ++ str "." ++ fnl ())
    in
    (state, None)

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()

(* The expression index is a DAG in topological order: a checkpoint saves it
   as a byte string of nodes referring to earlier nodes by index, which
   Marshal would otherwise cover with a sharing table of every node. Names and
   universes stay marshalled values, shared with the entries. *)
module Checkpoint = struct
  type 'a node =
    | CBound of int | CSort of U.t | CConst of N.t * U.t list
    | CApp of 'a * 'a
    | CLet of N.t * 'a * 'a * 'a
    | CLam of binder_kind * N.t * 'a * 'a
    | CPi of binder_kind * N.t * 'a * 'a
    | CProj of N.t * int * 'a
    | CNat of Z.t | CString of string

  (* Expressions outside the index (adapted constructor types) are saved as
     trees whose indexed subterms are references. *)
  type saved_expr = Reference of int | Fresh of saved_expr node
  type saved_ind = N.t * (binder_kind * N.t * saved_expr) list * saved_expr
                   * (N.t * saved_expr) list * N.t list
  type saved_entry =
    | SavedDef of N.t * saved_expr * saved_expr * N.t list * reducibility_hint * bool
    | SavedAx of N.t * saved_expr * N.t list
    | SavedInd of saved_ind
    | SavedQuot of N.t

  type t = { names : N.t RRange.t; univs : U.t RRange.t; exprs : string }

  let map_node f = function
    | Bound n -> CBound n | Sort u -> CSort u | Const (n, us) -> CConst (n, us)
    | App (a, b) -> CApp (f a, f b)
    | Let {name; ty; v; rest} -> CLet (name, f ty, f v, f rest)
    | Lam (bk, n, a, b) -> CLam (bk, n, f a, f b)
    | Pi (bk, n, a, b) -> CPi (bk, n, f a, f b)
    | Proj (n, i, e) -> CProj (n, i, f e)
    | Nat n -> CNat n | String s -> CString s

  let unmap_node f = function
    | CBound n -> Bound n | CSort u -> Sort u | CConst (n, us) -> Const (n, us)
    | CApp (a, b) -> App (f a, f b)
    | CLet (name, ty, v, rest) -> Let {name; ty = f ty; v = f v; rest = f rest}
    | CLam (bk, n, a, b) -> Lam (bk, n, f a, f b)
    | CPi (bk, n, a, b) -> Pi (bk, n, f a, f b)
    | CProj (n, i, e) -> Proj (n, i, f e)
    | CNat n -> Nat n | CString s -> String s

  let save_ind f ({name; params; ty; ctors; univs} : ind) : saved_ind =
    (name, List.map (fun (bk, n, e) -> bk, n, f e) params, f ty,
     List.map (fun (n, e) -> n, f e) ctors, univs)

  let load_ind f (name, params, ty, ctors, univs) : ind =
    {name; params = List.map (fun (bk, n, e) -> bk, n, f e) params;
     ty = f ty; ctors = List.map (fun (n, e) -> n, f e) ctors; univs}

  let save_entry f = function
    | Def {name; ty; body; univs; hint; kernel_opaque} ->
      SavedDef (name, f ty, f body, univs, hint, kernel_opaque)
    | Ax {name; ty; univs} -> SavedAx (name, f ty, univs)
    | Ind ind -> SavedInd (save_ind f ind)
    | Quot n -> SavedQuot n

  let load_entry f = function
    | SavedDef (name, ty, body, univs, hint, kernel_opaque) ->
      Def {name; ty = f ty; body = f body; univs; hint; kernel_opaque}
    | SavedAx (name, ty, univs) -> Ax {name; ty = f ty; univs}
    | SavedInd ind -> Ind (load_ind f ind)
    | SavedQuot n -> Quot n

  let invalid () = invalid_arg "Invalid indexed Lean parser checkpoint"

  let hash value = Hashtbl.hash_param 64 256 value

  module Physical = Hashtbl.Make (struct
    type t = expr
    let equal = ( == )
    let hash = hash
  end)

  module SavedPhysical = Hashtbl.Make (struct
    type t = saved_expr
    let equal = ( == )
    let hash = hash
  end)

  (* Reverse index by physical identity: an open-addressed table of positions
     (half full at most), so no key or bucket is allocated per element. *)
  type 'a index = { values : 'a array; slots : int array }

  let find_slot index value =
    let capacity = Array.length index.slots in
    let rec probe slot =
      let stored = index.slots.(slot) in
      if stored = 0 || index.values.(stored - 1) == value then slot
      else probe (if slot + 1 = capacity then 0 else slot + 1)
    in
    probe (hash value mod capacity)

  let make_index range =
    let length = RRange.length range in
    if length > Sys.max_array_length / 2 then invalid ();
    let index = {
      values = Array.init length (RRange.get range);
      slots = Array.make (max 2 (length * 2)) 0;
    } in
    Array.iteri (fun i value ->
      let slot = find_slot index value in
      if index.slots.(slot) = 0 then index.slots.(slot) <- i + 1)
      index.values;
    index

  let find index value =
    match index.slots.(find_slot index value) with
    | 0 -> None | stored -> Some (stored - 1)

  let find_exn index value = match find index value with
    | Some i -> i | None -> invalid ()

  let put_uint oc value =
    if value < 0 then invalid ();
    let rec put value =
      if value < 128 then output_byte oc value
      else begin output_byte oc ((value land 127) lor 128); put (value lsr 7) end
    in
    put value

  let put_string oc s = put_uint oc (String.length s); output_string oc s
  let put_int oc n = put_string oc (string_of_int n)
  let binder_code = function
    | NotImplicit -> 0 | Maximal -> 1 | NonMaximal -> 2 | Typeclass -> 3
  let binder_of_code = function
    | 0 -> NotImplicit | 1 -> Maximal | 2 -> NonMaximal | 3 -> Typeclass | _ -> invalid ()

  let write_graph oc (state : parsing_state) save_metadata =
    let names = make_index state.names in
    let univs = make_index state.univs in
    let exprs = make_index state.exprs in
    let tag = output_byte oc in
    let name n = put_uint oc (find_exn names n) in
    let universe u = put_uint oc (find_exn univs u) in
    output_string oc "LCP1";
    put_uint oc (Array.length exprs.values);
    Array.iteri (fun i term ->
      let sub e =
        let j = find_exn exprs e in
        if j >= i then invalid ();
        put_uint oc j
      in
      let first = find_exn exprs term in
      if first < i then (tag 10; put_uint oc first) else
      match term with
      | Bound n -> tag 0; put_int oc n
      | Sort u -> tag 1; universe u
      | Const (n, us) -> tag 2; name n; put_uint oc (List.length us); List.iter universe us
      | App (a, b) -> tag 3; sub a; sub b
      | Let {name = n; ty; v; rest} -> tag 4; name n; sub ty; sub v; sub rest
      | Lam (bk, n, a, b) -> tag 5; tag (binder_code bk); name n; sub a; sub b
      | Pi (bk, n, a, b) -> tag 6; tag (binder_code bk); name n; sub a; sub b
      | Proj (n, field, e) -> tag 7; name n; put_int oc field; sub e
      | Nat n -> tag 8; put_string oc (Z.to_string n)
      | String s -> tag 9; put_string oc s)
      exprs.values;
    let fragments = Physical.create 127 in
    let rec save term = match find exprs term with
      | Some i -> Reference i
      | None -> match Physical.find_opt fragments term with
        | Some saved -> saved
        | None ->
          let saved = Fresh (map_node save term) in
          Physical.add fragments term saved;
          saved
    in
    save_metadata save

  (* Write through a temporary file, so that the writer's working memory is
     released before the result string is allocated. *)
  let output_to_string prefix write =
    let path, oc = Filename.open_temp_file ~mode:[Open_binary] prefix "" in
    Fun.protect
      ~finally:(fun () ->
        close_out_noerr oc;
        try Sys.remove path with Sys_error _ -> ())
      (fun () ->
        let result = write oc in
        close_out oc;
        let ic = open_in_bin path in
        let s = Fun.protect ~finally:(fun () -> close_in_noerr ic)
          (fun () -> really_input_string ic (in_channel_length ic)) in
        s, result)

  let pack (state : parsing_state) save_metadata =
    let exprs, metadata =
      output_to_string "lean-import-exprs" (fun oc -> write_graph oc state save_metadata)
    in
    {names = state.names; univs = state.univs; exprs}, metadata

  let unpack saved =
    let data = saved.exprs in
    let pos = ref 0 in
    let byte () =
      if !pos >= String.length data then invalid ();
      let b = Char.code data.[!pos] in incr pos; b
    in
    let uint () =
      let rec get shift acc =
        let b = byte () in
        let part = b land 127 in
        if shift >= Sys.int_size - 1 || part > max_int lsr shift then invalid ();
        let acc = acc lor (part lsl shift) in
        if b land 128 = 0 then acc else get (shift + 7) acc
      in get 0 0
    in
    let string () =
      let length = uint () in
      if length > String.length data - !pos then invalid ();
      let s = String.sub data !pos length in pos := !pos + length; s
    in
    let integer () = try int_of_string (string ()) with Failure _ -> invalid () in
    if String.length data < 4 || String.sub data 0 4 <> "LCP1" then invalid ();
    pos := 4;
    let exprs = ref RRange.empty in
    let get range i = try RRange.get range i with Not_found -> invalid () in
    let name () = get saved.names (uint ()) in
    let universe () = get saved.univs (uint ()) in
    let expr () = get !exprs (uint ()) in
    for _ = 1 to uint () do
      (* Fields are read one by one: argument evaluation order is unspecified. *)
      let term = match byte () with
        | 0 -> Bound (integer ())
        | 1 -> Sort (universe ())
        | 2 ->
          let n = name () in
          let us = List.init (uint ()) (fun _ -> universe ()) in
          Const (n, us)
        | 3 -> let a = expr () in let b = expr () in App (a, b)
        | 4 -> let name = name () in let ty = expr () in let v = expr () in
          let rest = expr () in Let {name; ty; v; rest}
        | (5 | 6) as tag ->
          let bk = binder_of_code (byte ()) in let n = name () in
          let a = expr () in let b = expr () in
          if tag = 5 then Lam (bk, n, a, b) else Pi (bk, n, a, b)
        | 7 -> let n = name () in let field = integer () in let e = expr () in Proj (n, field, e)
        | 8 -> let s = string () in
          (try Nat (Z.of_string s) with Invalid_argument _ -> invalid ())
        | 9 -> String (string ())
        | 10 -> expr ()
        | _ -> invalid ()
      in
      exprs := RRange.append !exprs term
    done;
    if !pos <> String.length data then invalid ();
    let fragments = SavedPhysical.create 127 in
    let rec load = function
      | Reference i -> get !exprs i
      | Fresh node as saved -> match SavedPhysical.find_opt fragments saved with
        | Some term -> term
        | None ->
          let term = unmap_node load node in
          SavedPhysical.add fragments saved term;
          term
    in
    ({names = saved.names; univs = saved.univs; exprs = !exprs} : parsing_state), load
end
