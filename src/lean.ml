(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open UVars
module RelDecl = Context.Rel.Declaration
open LeanExpr

let __ () = assert false
let invalid = Constr.(mkApp (mkSet, [| mkSet |]))

let add_universe l ~lbound g =
  let g = UGraph.add_universe l ~strict:false g in
  UGraph.enforce_constraint (lbound, Le, l) g

let quickdef ?(opaque = false) ~name ~types ~univs body =
  let entry = Declare.definition_entry ~opaque ?types ~univs body in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let uctx =
    UState.empty
    (* used for ubinders and hook *)
  in
  Declare.declare_entry ~name ~scope ~kind ~impargs:[] ~uctx entry

type extended_level = Level of Level.t | LSProp

type scheme_family = SchemeSProp | SchemeType

(** produce [args, recargs] inside mixed context [args/recargs] [info] is in
    reverse order, ie the head is about the last arg in application order

    examples: [] -> [],[] [false] -> [1],[] [true] -> [2],[1] [true;false] ->
    [3;2],[1] [false;true] -> [3;1],[2] [false;false] -> [2;1],[] [true;true] ->
    [4;2],[3;1] *)
let reorder_inside_core info =
  let rec aux i args recargs = function
    | [] -> (args, recargs)
    | false :: info -> aux (i + 1) (i :: args) recargs info
    | true :: info -> aux (i + 2) ((i + 1) :: args) (i :: recargs) info
  in
  aux 1 [] [] info

let reorder_inside info =
  let args, recargs = reorder_inside_core info in
  CArray.map_of_list Constr.mkRel (List.append args recargs)

let rec insert_after k ((n, t) as v) c =
  if k = 0 then Constr.mkProd (n, t, Vars.lift 1 c)
  else
    match Constr.kind c with
    | Prod (na, a, b) -> Constr.mkProd (na, a, insert_after (k - 1) v b)
    | _ -> assert false

let insert_after k (n, t) c =
  insert_after k (n, Vars.lift k t) (Vars.subst1 invalid c)

let rec reorder_outside info hyps c =
  match (info, hyps) with
  | [], [] -> (c, 0)
  | false :: info, (n, t) :: hyps ->
    let c, k = reorder_outside info hyps c in
    (Constr.mkProd (n, t, c), k + 1)
  | true :: info, (n, t) :: rhyp :: hyps ->
    let c, k = reorder_outside info hyps c in
    let c = insert_after k rhyp c in
    (Constr.mkProd (n, t, c), k + 1)
  | _ -> assert false

(** produce [forall args recargs, P (C args)] from mixed
    [forall args/recargs, P (C args)] *)
let reorder_outside info ft =
  let hyps, out = Term.decompose_prod ft in
  fst (reorder_outside (List.rev info) (List.rev hyps) out)

exception Occur

let occur_mind mind term =
  let rec occur_rec c =
    match Constr.kind c with
    | Constr.Ind ((mind', _), _) ->
      if MutInd.UserOrd.equal mind mind' then raise_notrace Occur
    | _ -> Constr.iter occur_rec c
  in
  try
    occur_rec term;
    true
  with Occur -> false

(** Build the body of a Lean-style scheme. [u] instantiates the inductive, [s]
    is [None] for the SProp scheme and [Some l] for a scheme with motive [l].

    Lean schemes differ from Coq schemes:
    - the motive universe is the first bound universe for Lean but the last for
      Coq (handled by caller)
    - Lean puts induction hypotheses after all the constructor arguments, Coq
      puts them immediately after the corresponding recursive argument. *)
let lean_scheme env ~dep (mind, ind_index) u s =
  let mib = Global.lookup_mind mind in
  let nparams = mib.mind_nparams in
  let ntypes = Array.length mib.mind_packets in
  (* if we start using non recursive params in the translation it will
     involve reordering arguments *)
  assert (nparams = mib.mind_nparams_rec);
  let body =
    let sigma = Evd.from_env env in
    let sigma, s', motive =
      match s with
      | LSProp -> (sigma, EConstr.ESorts.sprop, None)
      | Level _ ->
        let sigma, u = Evd.new_univ_level_variable UnivRigid sigma in
        (sigma, EConstr.ESorts.make (Sorts.sort_of_univ (Universe.make u)), Some u)
    in
    let sigma, body =
      if ntypes = 1 then
        Indrec.build_induction_scheme env sigma
          ((mind, ind_index), EConstr.EInstance.make u)
          dep s'
      else
        let specs = List.init ntypes (fun k -> ((mind, k), dep, s')) in
        let sigma, bodies =
          Indrec.build_mutual_induction_scheme env sigma ~force_mutual:true specs
            (EConstr.EInstance.make u)
        in
        (sigma, List.nth bodies ind_index)
    in
    let body = EConstr.Unsafe.to_constr body in
    (* A mutual scheme comes with sort variables and levels of its own: map
       the qualities to the motive's, and each level to an equal level of the
       instance if there is one, otherwise to the motive level (Set in SProp). *)
    let quality, default_level, usubst =
      match (s, motive) with
      | LSProp, _ -> (Sorts.Quality.qsprop, Level.set, Level.Map.empty)
      | Level s, Some v -> (Sorts.Quality.qtype, s, Level.Map.singleton v s)
      | Level _, None -> assert false
    in
    let (qvars, levels), csts = Evd.sort_context_set sigma in
    let body_qvars, _ = Vars.sort_and_universes_of_constr body in
    let qsubst =
      Sorts.QVar.Set.fold (fun q -> Sorts.QVar.Map.add q quality) qvars Sorts.QVar.Map.empty
    in
    let qsubst =
      Sorts.Quality.Set.fold
        (fun q qsubst ->
          match q with
          | Sorts.Quality.QVar q -> Sorts.QVar.Map.add q quality qsubst
          | Sorts.Quality.QConstant _ | Sorts.Quality.QGlobal _ -> qsubst)
        body_qvars qsubst
    in
    let allowed =
      Array.fold_right Level.Set.add (snd (Instance.to_array u)) (Level.Set.singleton Level.set)
    in
    let graph =
      Level.Set.fold
        (fun l graph ->
          try UGraph.add_universe l ~strict:false graph with UGraph.AlreadyDeclared -> graph)
        levels (Environ.universes env)
    in
    let graph = UGraph.merge_constraints (PConstraints.univs csts) graph in
    let usubst =
      Level.Set.fold
        (fun l usubst ->
          if Level.Map.mem l usubst || Level.Set.mem l allowed then usubst
          else
            let equal a = UGraph.check_eq graph (Universe.make l) (Universe.make a) in
            let target =
              match List.find_opt equal (Level.Set.elements allowed) with
              | Some a -> a
              | None -> default_level
            in
            Level.Map.add l target usubst)
        levels usubst
    in
    Vars.subst_univs_level_constr (qsubst, usubst) body
  in
  let recinfo (mip : Declarations.one_inductive_body) =
    assert (
      CArray.for_all2 Int.equal mip.mind_consnrealargs mip.mind_consnrealdecls);
    Array.mapi
      (fun i (args, _) ->
        let nargs = mip.mind_consnrealargs.(i) in
        (* skip params *)
        let args = CList.firstn nargs args in
        CList.map
          (fun arg ->
            let t = RelDecl.get_type arg in
            not (occur_mind mind t))
          args)
      mip.mind_nf_lc
  in
  let recinfo = Array.concat (Array.to_list (Array.map recinfo mib.mind_packets)) in
  let hasrec =
    (* NB: if the only recursive arg is the last arg, no need for reordering *)
    Array.exists
      (function [] -> false | _ :: info -> List.exists (fun x -> x) info)
      recinfo
  in

  if not hasrec then body
  else
    (* body := fun params P (fc : forall args/recargs, P (C args)) => ...

       becomes

       fun params P (fc : forall args, forall recargs, P (C args)) =>
       body params P (fun args/recargs, fc args recargs)
    *)
    let open Constr in
    let nlc = Array.length recinfo in
    let paramsP, inside = Term.decompose_lambda_n_assum (nparams + ntypes) body in
    let fcs, inside = Term.decompose_lambda_n nlc inside in
    let fcs = List.rev fcs in

    let body =
      mkApp (body, Array.init (nparams + ntypes) (fun i -> mkRel (nlc + nparams + ntypes - i)))
    in
    let body =
      mkApp
        ( body,
          Array.of_list
            (CList.map_i
               (fun i (_, ft) ->
                 let info = recinfo.(i) in
                 if not (List.exists (fun x -> x) info) then mkRel (nlc - i)
                 else
                   let hyps, _ = Term.decompose_prod ft in
                   let args = reorder_inside info in
                   Term.it_mkLambda_or_LetIn
                     (mkApp (mkRel (nlc - i + List.length hyps), args))
                     (List.map (fun (n, t) -> RelDecl.LocalAssum (n, t)) hyps))
               0 fcs) )
    in

    let fcs =
      CList.map_i
        (fun i (n, ft) ->
          let info = recinfo.(i) in
          let ft = reorder_outside info ft in
          RelDecl.LocalAssum (n, ft))
        0 fcs
    in
    let fcs = List.rev fcs in
    let body =
      let open CClosure in
      let open RedFlags in
      let env = Environ.push_rel_context paramsP env in
      let env = Environ.push_rel_context fcs env in
      norm_val (create_clos_infos betaiota env) (create_tab ()) (inject body)
    in
    Term.it_mkLambda_or_LetIn (Term.it_mkLambda_or_LetIn body fcs) paramsP

let with_unsafe_univs f () =
  let flags = Global.typing_flags () in
  Global.set_typing_flags { flags with check_eliminations = false };
  try
    let v = f () in
    Global.set_typing_flags flags;
    v
  with e ->
    let e = Exninfo.capture e in
    Global.set_typing_flags flags;
    Exninfo.iraise e

module N = LeanName

let sort_of_level = function
  | LSProp -> Sorts.sprop
  | Level u -> Sorts.sort_of_univ (Universe.make u)

let univ_of_sort = function
  | Sorts.SProp -> None
  | Prop -> assert false
  | Set -> Some Universe.type0
  | Type u | GSort (_, u) | VSort (_, u) -> Some u

let sort_max (s1 : Sorts.t) (s2 : Sorts.t) =
  match (s1, s2) with
  | SProp, SProp | Prop, Prop | Set, Set -> s1
  | SProp, ((Prop | Set | Type _) as s) | ((Prop | Set | Type _) as s), SProp ->
    s
  | Prop, ((Set | Type _) as s) | ((Set | Type _) as s), Prop -> s
  | Set, Type u | Type u, Set ->
    Sorts.sort_of_univ (Univ.Universe.sup Univ.Universe.type0 u)
  | Type u, Type v -> Sorts.sort_of_univ (Univ.Universe.sup u v)
  | GSort _, _ | _, GSort _ -> assert false
  | VSort _, _ | _, VSort _ -> assert false

(** [map] goes from lean names to universes (in practice either SProp or a named
    level) *)
let rec to_universe map = function
  | U.Prop -> Sorts.sprop
  | UNamed n -> sort_of_level (N.Map.get n map)
  | Succ u -> Sorts.super (to_universe map u)
  | Max (a, b) -> sort_max (to_universe map a) (to_universe map b)
  | IMax (a, b) ->
    let ub = to_universe map b in
    if Sorts.is_sprop ub then ub else sort_max (to_universe map a) ub

let rec do_n f x n = if n = 0 then x else do_n f (f x) (n - 1)

(** in lean, imax(Prop+1,l)+1 <= max(Prop+1,l+1) because:
    - either l=Prop, so Prop+1 <= Prop+1
    - or Prop+1 <= l so l+1 <= l+1

    to simulate this, each named level becomes > Set and we compute maxes
    accordingly *)

let simplify_universe u =
  match Universe.repr u with
  | (l, n) :: (l', n') :: rest when Level.is_set l ->
    if n <= n' + 1 || List.exists (fun (_, n') -> n <= n' + 1) rest then
      List.fold_left
        (fun u (l, n) ->
          Universe.sup u (do_n Universe.super (Universe.make l) n))
        (do_n Universe.super (Universe.make l') n')
        rest
    else u
  | _ -> u

let simplify_sort = function
  | Sorts.Type u -> Sorts.sort_of_univ (simplify_universe u)
  | s -> s

(* Return the biggest [n] such that [Set+n <= u]. Assumes a simplified
   [u] as above. *)
let max_increment u =
  match Universe.repr u with
  | (l, n) :: rest when Level.is_set l -> n
  | l -> List.fold_left (fun m (_, n) -> max m (n + 1)) 0 l

let to_universe map u =
  let u = to_universe map u in
  simplify_sort u

(** Map from [n] to the global level standing for [Set+n] (not including n=0).
*)
let sets : Level.t Int.Map.t ref =
  Summary.ref ~name:"lean-set-surrogates" Int.Map.empty

type uconv = {
  map : extended_level N.Map.t;  (** Map from lean names to Coq universes *)
  levels : Level.t Universe.Map.t;
      (** Map from algebraic universes to levels (only levels representing an
          algebraic) *)
  graph : UGraph.t;
}

let lean_id = Id.of_string "Lean"

let { Goptions.get = lean_fancy_univs } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Fancy"; "Universes" ]
    ~value:true ()

let level_of_universe_core u =
  let u =
    List.map
      (fun (l, n) ->
        let open Level in
        if is_set l then "Set+" ^ string_of_int n
        else
          match name l with
          | None -> assert false
          | Some name ->
            let d, s, i = UGlobal.repr name in
            let d = DirPath.repr d in
            (match (d, i) with
            | [ name; l ], 0 when Id.equal l lean_id ->
              Id.to_string name ^ if n = 0 then "" else "+" ^ string_of_int n
            | _ -> to_string l))
      u
  in
  let s = (match u with [ _ ] -> "" | _ -> "max__") ^ String.concat "_" u in
  Level.(
    make (UGlobal.make (DirPath.make [ Id.of_string_soft s; lean_id ]) "" 0))

let level_of_universe u =
  let u = Universe.repr u in
  level_of_universe_core u

let level_of_universe u =
  if lean_fancy_univs () then level_of_universe u else UnivGen.fresh_level ()

let update_graph (l, u) (l', u') graph =
  if UGraph.check_leq graph (Universe.super u) u' then
    UGraph.enforce_constraint (l, Lt, l') graph
  else if UGraph.check_leq graph (Universe.super u') u then
    UGraph.enforce_constraint (l', Lt, l) graph
  else if UGraph.check_leq graph u u' then
    UGraph.enforce_constraint (l, Le, l') graph
  else if UGraph.check_leq graph u' u then
    UGraph.enforce_constraint (l', Le, l) graph
  else graph

let is_sets u =
  match Universe.repr u with
  | [ (u, n) ] -> if Level.is_set u then Some n else None
  | _ -> None

(** Find or add a global level for Set+n *)
let rec level_of_sets uconv n =
  if n = 0 then (uconv, Level.set)
  else
    try (uconv, Int.Map.find n !sets)
    with Not_found ->
      let uconv, p = level_of_sets uconv (n - 1) in
      let l =
        if lean_fancy_univs () then level_of_universe_core [ (Level.set, n) ]
        else UnivGen.fresh_level ()
      in
      Global.push_context_set
        (Level.Set.singleton l, UnivConstraints.singleton (p, Lt, l));
      sets := Int.Map.add n l !sets;
      let graph = add_universe l ~lbound:p uconv.graph in
      ({ uconv with graph }, l)

let to_univ_level u uconv =
  match Universe.level u with
  | Some l -> (uconv, l)
  | None ->
    (match is_sets u with
    | Some n -> level_of_sets uconv n
    | None ->
      (match Universe.Map.find_opt u uconv.levels with
      | Some l -> (uconv, l)
      | None ->
        let uconv, mset = level_of_sets uconv (max_increment u) in
        let l = level_of_universe u in
        let graph = add_universe l ~lbound:mset uconv.graph in
        let graph =
          Universe.Map.fold
            (fun u' l' graph -> update_graph (l, u) (l', u') graph)
            uconv.levels graph
        in
        let graph =
          N.Map.fold
            (fun _ l' graph ->
              match l' with
              | LSProp -> graph
              | Level l' -> update_graph (l, u) (l', Universe.make l') graph)
            uconv.map graph
        in
        let uconv =
          { uconv with levels = Universe.Map.add u l uconv.levels; graph }
        in
        (uconv, l)))

(** Definitional height, used for unfolding heuristics.

    The definitional height is the longest sequence of constant unfoldings until
    we get a term without definitions (recursors don't count). *)

let height_cache = Summary.ref ~name:"lean-heights" N.Map.empty

let rec height = function
  | Const (c, _) ->
    (try N.Map.find c !height_cache + 1
     with Not_found ->
       (* non constant, recursor, or just skipped *)
       0)
  | Bound _ | Sort _ -> 0
  | Lam (_, _, a, b) | Pi (_, _, a, b) | App (a, b) -> max (height a) (height b)
  | Let { name = _; ty; v; rest } -> max (height ty) (max (height v) (height rest))
  | Proj (_, _, c) -> height c
  | Nat _ | String _ -> 0

let height n body =
  match N.Map.find_opt n !height_cache with
  | Some h -> h
  | None ->
    let h = height body in
    height_cache := N.Map.add n h !height_cache;
    h

type instantiation = {
  ref : GlobRef.t;
  algs : Universe.t list;
      (** For each extra universe, produce the algebraic it corresponds to (the
          initial universes are replaced by the appropriate Var) *)
}

(*
Lean classifies inductives in the following way:
- inductive landing in always >Prop (even when instantiated to all Prop) -> never squashed
- inductive which has Prop instantiation:
  + no constructor -> never squashed
  + multi constructor -> always squashed
  + 1 constructor
    * no non param arguments
      -> not squashed, special reduction
      typically [eq]
    * all arguments appear in the output type
      -> not squashed, basic reduction
      no real world examples? eg [Inductive foo : nat -> Prop := bar : forall x, foo x.]
      2019 "type theory of lean" implies that there should be special reduction
      but testing says otherwise
    * some arguments don't appear in the output type, but are Prop or recursive
      -> not squashed, basic reduction
      typically [Acc], [and]
    * some non-Prop non-recursive arguments (for some instantiation) don't appear in the output type
      -> squashed
      typically [exists]

Additionally, the recursor is always dependent (since Lean 4)
(this implem detail isn't in the TTofLean paper)
Special reduction also seems restricted to always-Prop types.

NB: in practice (all stdlib and mathlib) the target universe is available without reduction
(ie syntactic arity) even though the system doesn't require it.
so we can just look at it directly (we don't want to implement a reduction system)
Update: now we have correct Coq envs so we could reduce the Coq term?

Difference with Coq:
- a non-Prop instantiation of possibly Prop types will never be squashed
- non squashed possibly-Prop types at a Prop instantiation are squashed
  (unless empty or uip branch)
- we need uip for the special reduction.
  TTofLean sounds like we need an encoding with primitive records
  but testing indicates otherwise (all args in output type case).
- we will always need unsafe flags for [Acc], and possibly for [and].

Instantiating the type with all-Prop may side-effect instantiate
some other globals with Prop that won't actually be used
(assuming the inductive is not used with all-Prop)
This probably doesn't matter much, also if we start using upfront
instantiations it won't matter at all.

Primitive records:
Lean autodetects all record-capable types as having primitive
projections, and also autogenerates the eliminators.
Squashed Props with 1 ctor have primitive projections up to the first non-Prop field.
*)

type squashy = {
  maybe_prop : bool;  (** used for optim, not fundamental *)
  always_prop : bool;
      (** controls special reduction, but we just let Coq do its thing for that
      *)
  lean_squashes : bool;
      (** Self descriptive. We handle necessity of unsafe flags
          per-instantiation. *)
}

let noprop = { maybe_prop = false; always_prop = false; lean_squashes = false }

let pp_squashy { maybe_prop; always_prop; lean_squashes } =
  let open Pp in
  (if maybe_prop then
     if always_prop then str "is always Prop" else str "may be Prop"
   else str "is never Prop")
  ++ spc ()
  ++
  if lean_squashes then str "and is squashed by Lean"
  else str "and is not squashed by Lean"

let coq_squashes graph (entry : Entries.mutual_inductive_entry) =
  let env = Global.env () in
  let env = Environ.set_universes graph env in
  let ind =
    match entry.mind_entry_inds with [ ind ] -> ind | _ -> assert false
  in
  let params = entry.mind_entry_params in
  let ty = ind.mind_entry_arity in
  let env_params = Environ.push_rel_context params env in
  let _, s = Reduction.dest_arity env_params ty in
  (* TODO merge with uip branch *)
  if not (Sorts.is_sprop s) then false
  else
    match ind.mind_entry_lc with
    | [] -> false
    | _ :: _ :: _ -> true
    | [ c ] -> (match Constr.kind c with Rel _ | App _ -> false | _ -> true)

let with_env_evm rels uconv f x =
  (* In non upfront mode,
     because we interleave defining new constants as we encounter them,
     pushing rels and handling local universes,
     we pass just the rel_context_val and merge it with the global env and the uconv here *)
  let env = Global.env () in
  let env = Environ.set_rel_context_val rels env in
  let env = Environ.set_universes uconv.graph env in
  let evd = Evd.from_env env in
  f env evd x

let to_annot rels n t uconv =
  let r =
    with_env_evm rels uconv
      (fun env evd r ->
        let r = Retyping.relevance_of_type env evd r in
        EConstr.Unsafe.to_relevance r)
      (EConstr.of_constr t)
  in
  Context.make_annot (N.to_name n) r

(* bit n of [int_of_univs univs] is 1 iff [List.nth univs n] is SProp *)
let int_of_univs =
  let rec aux i acc = function
    | [] -> (i, acc)
    | u :: rest ->
      (match univ_of_sort u with
      | None -> aux ((i * 2) + 1) acc rest
      | Some u -> aux (i * 2) (u :: acc) rest)
  in
  fun l -> aux 0 [] (List.rev l)

let univ_of_name u =
  if lean_fancy_univs () then
    let u = DirPath.make [ N.to_id u; lean_id ] in
    Level.(make (UGlobal.make u "" 0))
  else UnivGen.fresh_level ()

let start_uconv univs i =
  let uconv =
    {
      graph = Global.universes ();
      map = N.Map.empty;
      levels = Universe.Map.empty;
    }
  in
  let uconv, set1 = level_of_sets uconv 1 in
  let rec aux uconv i = function
    | [] ->
      assert (i = 0);
      uconv
    | u :: univs ->
      let map, graph =
        if i mod 2 = 0 then
          let v = univ_of_name u in
          ( N.Map.add u (Level v) uconv.map,
            add_universe v ~lbound:set1 uconv.graph )
        else (N.Map.add u LSProp uconv.map, uconv.graph)
      in
      aux { uconv with map; graph } (i / 2) univs
  in
  aux uconv i univs

let rec make_unames univs ounivs =
  match (univs, ounivs) with
  | _, [] ->
    List.map (fun u -> Name (Id.of_string_soft (Level.to_string u))) univs
  | _u :: univs, o :: ounivs -> N.to_name o :: make_unames univs ounivs
  | [], _ :: _ -> assert false

let univ_entry_gen { map; levels; graph } ounivs =
  let ounivs =
    CList.map_filter
      (fun u ->
        let v = N.Map.get u map in
        match v with LSProp -> None | Level v -> Some (u, v))
      ounivs
  in
  let ounivs, univs = List.split ounivs in
  let univs, algs =
    if Universe.Map.is_empty levels then (univs, [])
    else
      let univs = List.rev univs in
      (* add the new levels to univs, add constraints between maxes
         (eg max(a,b) <= max(a,b,c)) *)
      let univs, algs =
        Universe.Map.fold
          (fun alg l (univs, algs) -> (l :: univs, alg :: algs))
          levels (univs, [])
      in
      let univs = List.rev univs in
      (univs, algs)
  in
  let uset =
    List.fold_left (fun kept l -> Level.Set.add l kept) Level.Set.empty univs
  in
  let kept = Level.Set.add Level.set uset in
  let kept = Int.Map.fold (fun _ -> Level.Set.add) !sets kept in
  let csts = UGraph.constraints_for ~kept graph in
  let csts =
    UnivConstraints.filter
      (fun (a, _, b) -> Level.Set.mem a uset || Level.Set.mem b uset)
      csts
  in
  let unames = { quals = [||]; univs = Array.of_list (make_unames univs ounivs)} in
  let univs = Instance.of_array ([||], Array.of_list univs) in
  let uctx = UContext.make unames (univs, PConstraints.of_univs csts) in
  let subst = snd (make_instance_subst univs) in
  let algs = List.rev_map (subst_univs_level_universe subst) algs in
  (uctx, algs)

let univ_entry a b =
  let uctx, algs = univ_entry_gen a b in
  ((UState.Polymorphic_entry uctx, UnivNames.empty_binders), algs)

(* TODO restrict univs (eg [has_add : Sort (u+1) -> Sort(u+1)] can
   drop the [u] and keep only the replacement for [u+1]??

   Preserve algebraics in codomain position? *)

let name_for_core n i =
  if i = 0 then N.to_id n
  else Id.of_string (N.to_coq_string n ^ "_inst" ^ string_of_int i)

(* NB collisions for constructors/recursors are still possible but
   should be rare *)
let name_for n i =
  let base = name_for_core n i in
  if not (Global.exists_objlabel base) then base
  else
    (* prevent resetting the number *)
    let base = if i = 0 then base else Id.of_string (Id.to_string base ^ "_") in
    Namegen.next_global_ident_away (Global.safe_env ()) base Id.Set.empty

let get_predeclared_ind indn n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name in
    match Rocqlib.lib_ref reg with
    | IndRef (ind, 0) -> Some (ind_name, ind)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected an inductive.")
    | exception _ -> None
  else None

(** Like [get_predeclared_ind] but looks for an inductive predeclared as a
    definition (using a ".cumul" suffix on the registration). Returns the
    ConstRef of the predeclared definition. *)
let get_predeclared_ind_as_def indn n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name ^ ".cumul" in
    match Rocqlib.lib_ref reg with
    | ConstRef c -> Some (ind_name, c)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected a constant.")
    | exception _ -> None
  else None

let get_predeclared_def defn n i =
  if N.equal n (N.append_list N.anon defn) then
    let def_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string def_name in
    match Rocqlib.lib_ref reg with
    | ConstRef c -> Some (def_name, c)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for " ++ str reg ++ str " expected a constant.")
    | exception _ -> None
  else None

type predeclared_ind_kind = Eq | Nat | Nat_le | Or | And | Fin | UInt32 | Char
type predeclared_def_kind = UInt32_size | Nat_isValidChar
type predeclared_ind_as_def_kind = ULift_cumul

let get_predeclared_cnames (k : predeclared_ind_kind) n =
  match k with
  | Eq -> [ N.append n "refl" ]
  | Nat -> [ N.append n "zero"; N.append n "succ" ]
  | Nat_le -> [ N.append n "refl"; N.append n "step" ]
  | Or -> [ N.append n "inl"; N.append n "inr" ]
  | And -> [ N.append n "intro" ]
  | Fin -> [ N.append n "mk" ]
  | UInt32 -> [ N.append n "mk" ]
  | Char -> [ N.append n "mk" ]

let get_predeclared_ind_any n i =
  List.filter_map
    (fun (indk, indh) ->
      get_predeclared_ind indh n i |> Option.map (fun x -> (indk, indh, x)))
    [
      (Eq, [ "Eq" ]);
      (Nat, [ "Nat" ]);
      (Nat_le, [ "Nat"; "le" ]);
      (Or, [ "Or" ]);
      (And, [ "And" ]);
      (Fin, [ "Fin" ]);
      (UInt32, [ "UInt32" ]);
      (Char, [ "Char" ]);
    ]

let get_predeclared_ind_some n i =
  match get_predeclared_ind_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared inductive types for " ++ N.pp n)

let get_predeclared_ind_as_def_any n i =
  List.filter_map
    (fun (k, h) ->
      get_predeclared_ind_as_def h n i |> Option.map (fun x -> (k, h, x)))
    [
      (ULift_cumul, [ "ULift" ]);
    ]

let get_predeclared_ind_as_def_some n i =
  match get_predeclared_ind_as_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared ind-as-def constants for " ++ N.pp n)

let get_predeclared_def_any n i =
  List.filter_map
    (fun (defk, defh) ->
      get_predeclared_def defh n i |> Option.map (fun x -> (defk, defh, x)))
    [
      (UInt32_size, [ "UInt32"; "size" ]);
      (Nat_isValidChar, [ "Nat"; "isValidChar" ]);
    ]

let get_predeclared_def_some n i =
  match get_predeclared_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err Pp.(str "Multiple predeclared constants for " ++ N.pp n)

(* let get_predeclared_eq n i = get_predeclared_ind "eq" n i *)
let mk_char_prim = "Char.mk.reflective_prim"

(*
Register Nat_isValidChar as lean.Nat_isValidChar.
Register reflective_Char_mk_prim as lean.Char.mk.reflective_prim. *)
let nat_double = "Nat_double"

(** For each name, the instantiation with all non-sprop univs should always be
    declared, but the instantiations with SProp may be lazily declared. We
    expect small instance lengths (experimentally at most 4 in the stdlib) so we
    represent instantiations as bit fields, bit n is 1 iff universe n is
    instantiated by SProp. *)
let declared : instantiation Int.Map.t N.Map.t ref =
  Summary.ref ~name:"lean-declared-instances" N.Map.empty

let entries : entry N.Map.t ref = Summary.ref ~name:"lean-entries" N.Map.empty

(* Constructor name -> inductive name, to instantiate the inductive when one of
   its constructors is the first reference to a universe instance. *)
let constructor_owners : N.t N.Map.t ref =
  Summary.ref ~name:"lean-constructor-owners" N.Map.empty

let add_constructor_owners (ind : ind) owners =
  List.fold_left (fun owners (c, _) -> N.Map.add c ind.name owners) owners ind.ctors

(* Member name -> whole mutual block: a universe instance of a member is
   declared as the block. *)
let mutual_entries : ind list N.Map.t ref =
  Summary.ref ~name:"lean-mutual-entries" N.Map.empty

let squash_info : squashy N.Map.t ref =
  Summary.ref ~name:"lean-squash-info" N.Map.empty

(* Constructor types of a block [names] refer to their own inductive as
   [Bound nparams] and to the others by name; rebind them to the context of
   the block, where the first inductive is the deepest. *)
let remap_mutual_ctor ~nparams ~names own =
  let ntypes = List.length names in
  let bound k depth = Bound (nparams + ntypes - 1 - k + depth) in
  let index name = try Some (CList.index0 N.equal name names) with Not_found -> None in
  let rec remap depth = function
    | Bound k when k = nparams + depth -> bound (CList.index0 N.equal own names) depth
    | Const (name, _) as e -> (match index name with Some k -> bound k depth | None -> e)
    | (Bound _ | Sort _ | Nat _ | String _) as e -> e
    | App (f, x) -> App (remap depth f, remap depth x)
    | Let { name; ty; v; rest } ->
      Let { name; ty = remap depth ty; v = remap depth v; rest = remap (depth + 1) rest }
    | Lam (bk, name, ty, body) -> Lam (bk, name, remap depth ty, remap (depth + 1) body)
    | Pi (bk, name, ty, body) -> Pi (bk, name, remap depth ty, remap (depth + 1) body)
    | Proj (name, field, c) -> Proj (name, field, remap depth c)
  in
  remap 0

let add_declared n i inst =
  declared :=
    N.Map.update n
      (function
        | None -> Some (Int.Map.singleton i inst)
        | Some m -> Some (Int.Map.add i inst m))
      !declared

let to_univ_level' u uconv =
  match to_universe uconv.map u with
  | SProp -> (uconv, LSProp)
  | Type u | GSort (_, u) | VSort (_, u) ->
    let uconv, u = to_univ_level u uconv in
    (uconv, Level u)
  | Set -> (uconv, Level Level.set)
  | Prop -> assert false

let empty_env = Environ.empty_rel_context_val
let default_proj_id = Id.of_string "default_proj_id"

type error_mode = Skip | Stop | Fail

let { Goptions.get = error_mode } =
  let print = function Skip -> "Skip" | Stop -> "Stop" | Fail -> "Fail" in
  let interp = function
    | "Skip" -> Skip
    | "Stop" -> Stop
    | "Fail" -> Fail
    | s ->
      CErrors.user_err Pp.(str "Unknown error mode " ++ qstring s ++ str ".")
  in
  Goptions.declare_interpreted_string_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Error"; "Mode" ]
    ~value:Fail interp print ()

exception MissingQuot

let { Goptions.get = skip_missing_quot } =
  Goptions.declare_bool_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Skip"; "Missing"; "Quotient" ]
    ~value:true ()

let error_mode = function
  | MissingQuot when skip_missing_quot () -> Skip
  | _ -> error_mode ()

module ZMap = CMap.Make (Z)

let nat_ints = ref ZMap.empty
let max_known_int = ref (Z.pred Z.zero)

let one_more_int nat =
  let i = Z.succ !max_known_int in
  let c =
    if Z.equal i Z.zero then Constr.mkConstructU ((nat, 1), UVars.Instance.empty)
    else
      let cpred = ZMap.get !max_known_int !nat_ints in
      Constr.(
        mkApp (mkConstructU ((nat, 2), UVars.Instance.empty), [| cpred |]))
  in
  nat_ints := ZMap.add i c !nat_ints;
  max_known_int := i

let max_nat_int = Z.of_string "5000"

let nat_int_binary nat double i =
  assert (Z.leq Z.zero i);
  let rec to_binary z acc =
    if Z.equal z Z.zero then acc
    else
      let bit = if Z.equal (Z.rem z (Z.of_int 2)) Z.zero then 0 else 1 in
      to_binary (Z.div z (Z.of_int 2)) (bit :: acc)
  in
  let binary_representation = to_binary i [] in
  let xO = Constr.mkConstructU ((nat, 1), UVars.Instance.empty) in
  let xS = Constr.mkConstructU ((nat, 2), UVars.Instance.empty) in
  let fS x = Constr.mkApp (xS, [| x |]) in
  let fDouble x = Constr.mkApp (double, [| x |]) in
  let rec construct_nat binary_list_rev =
    match binary_list_rev with
    | [] -> xO
    | 0 :: rest ->
      let rest_constr = construct_nat rest in
      fDouble rest_constr
    | 1 :: rest ->
      let rest_constr = construct_nat rest in
      fS (fDouble rest_constr)
    | _ -> assert false
  in
  construct_nat (List.rev binary_representation)

let nat_int nat double i =
  assert (Z.leq Z.zero i);
  if Z.leq max_nat_int i then nat_int_binary nat double i
  else begin
    while Z.lt !max_known_int i do
      one_more_int nat
    done;
    ZMap.get i !nat_ints
  end

(* Decode a UTF-8 string into a list of valid codepoints, with error reporting for bad characters *)
(* let string_to_codepoints s =
  (* Create a UTF-8 decoder for the input string *)
  let decoder = Uutf.decoder ~encoding:`UTF_8 (`String s) in

  (* Define the condition for filtering codepoints *)
  let is_valid_codepoint n = n < 0xd800 || (0xdfff < n && n < 0x110000) in

  (* Decode the string and collect valid codepoints *)
  let rec collect_codepoints acc =
    match Uutf.decode decoder with
    | `Uchar u when is_valid_codepoint (Uchar.to_int u) ->
      collect_codepoints (Uchar.to_int u :: acc)
    | `Uchar u when Uchar.to_int u >= 0x110000 ->
      (* Raise an exception with the problematic character *)
      let bad_char = Printf.sprintf "U+%04X" (Uchar.to_int u) in
      failwith (Printf.sprintf "Invalid codepoint (>= 0x110000): %s" bad_char)
    | `Uchar u when Uchar.to_int u >= 0xd800 && 0xdfff >= Uchar.to_int u ->
      (* Raise an exception with the problematic character *)
      let bad_char = Printf.sprintf "U+%04X" (Uchar.to_int u) in
      failwith
        (Printf.sprintf "Invalid codepoint (u >= 0xd800 && 0xdfff >= u): %s"
           bad_char)
    | `Uchar _ -> assert false
    | `End -> List.rev acc
    | `Malformed s ->
      (* Handle malformed UTF-8 sequences *)
      failwith (Printf.sprintf "Malformed UTF-8 sequence: %S" s)
    | `Await -> assert false (* This case should not occur for a string input *)
  in
  collect_codepoints [] *)

let string_to_codepoints str =
  let rec decode_utf8 s pos acc =
    if pos >= String.length s then List.rev acc
    else
      let c = Char.code (String.get s pos) in
      let n =
        if c < 0x80 then (1, c)
        else if c < 0xE0 then (2, c land 0x1F)
        else if c < 0xF0 then (3, c land 0x0F)
        else (4, c land 0x07)
      in
      let bytes, value = n in
      let code_point = ref value in
      for i = 1 to bytes - 1 do
        let next_byte = Char.code (String.get s (pos + i)) in
        code_point := (!code_point lsl 6) lor (next_byte land 0x3F)
      done;
      decode_utf8 s (pos + bytes) (!code_point :: acc)
  in
  decode_utf8 str 0 []

let check_valid_codepoints cs =
  List.map
    (fun c ->
      if c < 0xd800 || (0xdfff < c && c < 0x110000) then c
      else
        let bad_char = Printf.sprintf "U+%04X" c in
        CErrors.user_err
          Pp.(str (Printf.sprintf "Invalid codepoint: %s" bad_char)))
    cs

let mk_char mkChar (c : int) =
  Constr.(mkApp (mkChar, [| mkInt (Uint63.of_int c) |]))

let mk_list list uinst ty l =
  let cNil = Constr.(mkApp (mkConstructU ((list, 1), uinst), [| ty |])) in
  let cCons = Constr.mkConstructU ((list, 2), uinst) in
  let rec mk_list_rec l =
    match l with
    | [] -> cNil
    | hd :: tl -> Constr.mkApp (cCons, [| ty; hd; mk_list_rec tl |])
  in
  mk_list_rec l

let mk_string char string list char_uinst mkChar s =
  let codepoints =
    try check_valid_codepoints (string_to_codepoints s)
    with Failure msg as exn ->
      let _, info = Exninfo.capture exn in
      CErrors.user_err ~info Pp.(str msg)
  in
  let chars = List.map (mk_char mkChar) codepoints in
  let ls = mk_list list char_uinst char chars in
  Constr.(mkApp (mkConstructU ((string, 1), UVars.Instance.empty), [| ls |]))

(* [c] has type [indu] applied to [args] *)
let unfold_proj_case env evd ~field ~indu ~mib ~mip ~args c =
  let ind = fst indu in
  let npar = mib.Declarations.mind_nparams in
  let ntypes = Declareops.mind_ntypes mib in
  let u = snd indu in
  let ind_subst =
    List.init ntypes (fun i -> Constr.mkIndU ((fst ind, ntypes - i - 1), u))
  in
  let ctx, cty0 = mip.Declarations.mind_nf_lc.(0) in
  let cty_full = Term.it_mkProd_or_LetIn cty0 ctx in
  let rctx, _ = Term.decompose_prod_decls (Vars.substl ind_subst cty_full) in
  let ctor_ctx, _paramslet = CList.chop mip.mind_consnrealdecls.(0) rctx in
  let nargs = mip.mind_consnrealdecls.(0) in
  let ci =
    {
      Constr.ci_ind = ind;
      ci_npar = npar;
      ci_cstr_ndecls = mip.mind_consnrealdecls;
      ci_cstr_nargs = mip.mind_consnrealargs;
      ci_pp_info = { style = LetStyle };
    }
  in
  let params = Array.map EConstr.Unsafe.to_constr (Array.sub args 0 npar) in
  let self_annot = Context.make_annot Name.Anonymous mip.mind_relevance in
  let self_ty =
    Constr.mkApp
      (Constr.mkIndU indu, Array.map EConstr.Unsafe.to_constr args)
  in
  let env_self =
    Environ.push_rel
      (Context.Rel.Declaration.LocalAssum (self_annot, self_ty)) env
  in
  let make_case ~ret_env ~params ~field ~ret_ty c =
    let case_relev =
      EConstr.Unsafe.to_relevance
        (Retyping.relevance_of_type ret_env evd (EConstr.of_constr ret_ty))
    in
    let p = ([| self_annot |], ret_ty) in
    let branch_nas =
      Array.of_list (List.rev_map Context.Rel.Declaration.get_annot ctor_ctx)
    in
    let branch = (branch_nas, Constr.mkRel (nargs - field)) in
    Constr.mkCase
      (ci, u, params, (p, case_relev), Constr.NoInvert, c, [| branch |])
  in
  let params_self = Array.map (Vars.lift 1) params in
  let env_inner =
    Environ.push_rel
      (Context.Rel.Declaration.LocalAssum
         (self_annot, Vars.lift 1 self_ty))
      env_self
  in
  let ret_ty =
    let ctor = Constr.mkConstructU ((ind, 1), u) in
    let ctor_applied = Constr.mkApp (ctor, params) in
    let rec get_field_type i ty =
      match Constr.kind ty with
      | Constr.Prod (_, t, rest) ->
        if i = field then t
        else
          let previous =
            make_case ~ret_env:env_inner ~params:params_self ~field:i
              ~ret_ty:(Vars.lift 1 t) (Constr.mkRel 1)
          in
          get_field_type (i + 1) (Vars.subst1 previous rest)
      | _ -> assert false
    in
    let ctor_ty =
      Retyping.get_type_of env evd (EConstr.of_constr ctor_applied)
    in
    let ctor_ty =
      EConstr.Unsafe.to_constr (Reductionops.whd_all env evd ctor_ty)
    in
    get_field_type 0 (Vars.lift 1 ctor_ty)
  in
  make_case ~ret_env:env_self ~params ~field ~ret_ty c

let lcnt = ref 0

let line_msg name =
  Feedback.msg_info Pp.(str "line " ++ int !lcnt ++ str ": " ++ N.pp name)

let rec to_constr =
  let open Constr in
  let ( >>= ) x f uconv =
    let uconv, x = x uconv in
    f x uconv
  in
  let get_uconv uconv = (uconv, uconv) in
  let ret x uconv = (uconv, x) in
  let to_annot env n t u = (u, to_annot env n t u) in
  let push_rel = Environ.push_rel_context_val in
  fun env -> function
    | Bound i -> ret (mkRel (i + 1))
    | Sort univ ->
      to_univ_level' univ >>= fun u -> ret (mkSort (sort_of_level u))
    | Const (n, univs) -> instantiate n univs
    | App (a, b) ->
      to_constr env a >>= fun a ->
      to_constr env b >>= fun b -> ret (mkApp (a, [| b |]))
    | Let { name; ty; v; rest } ->
      to_constr env ty >>= fun ty ->
      to_annot env name ty >>= fun name ->
      to_constr env v >>= fun v ->
      to_constr (push_rel (LocalDef (name, v, ty)) env) rest >>= fun rest ->
      ret (mkLetIn (name, v, ty, rest))
    | Lam (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkLambda (n, a, b))
    | Pi (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkProd (n, a, b))
    | Proj (lean_ind, field, c) ->
      to_constr env c >>= fun c ->
      get_uconv >>= fun uconv ->
      (* we retype to get the ind, because otherwise we need the lean
       univs for instantiation
       This means we ignore the lean_ind in the Proj data. *)
      let c =
        with_env_evm env uconv
          (fun env evd () ->
            let tc = Retyping.get_type_of env evd (EConstr.of_constr c) in
            let tc =
              Reductionops.whd_all env evd tc
            in
            let tc_head, args = EConstr.decompose_app evd tc in
            match EConstr.kind evd tc_head with
            | Constr.Ind _ ->
              (* Standard inductive: use normal projection *)
              let ((ind, _) as indu) =
                Constr.destInd (EConstr.Unsafe.to_constr tc_head)
              in
              let mib, mip = Inductive.lookup_mind_specif (Global.env()) ind in
              begin
                match mip.mind_record with
                | PrimRecord infos ->
                  let p, r =
                    Declareops.inductive_make_projection ind mib ~proj_arg:field
                  in
                  (* unfolded?? *)
                  mkProj (Projection.make p false, r, c)
                | NotRecord | FakeRecord ->
                  unfold_proj_case env evd ~field ~indu ~mib ~mip ~args c
              end
            | _ ->
              (* Type is not an inductive (e.g., transparent cumulative ULift).
                 Projection is the identity. *)
              c)
          ()
      in
      ret c
    | Nat i ->
      (* [nat_ints] is not synchronized so ensure Nat is instantiated *)
      instantiate (N.append N.anon "Nat") [] >>= fun nat ->
      let nat, _ = Constr.destInd nat in
      get_uconv >>= fun uconv ->
      let double =
        with_env_evm env uconv
          (fun env evd () ->
            let _, p =
              Evd.fresh_global env evd (Rocqlib.lib_ref ("lean." ^ nat_double))
            in
            EConstr.to_constr evd p)
          ()
      in
      ret (nat_int nat double i)
    | String s ->
      (* instantiate (N.append N.anon "Char") [] >>= fun char -> *)
      (* let (_, charu) = Constr.destInd char in *)
      instantiate (N.append N.anon "String") [] >>= fun string ->
      let string, _ = Constr.destInd string in
      instantiate (N.append (N.append N.anon "String") "mk") []
      >>= fun string_mk ->
      get_uconv >>= fun uconv ->
      let list, char =
        with_env_evm env uconv
          (fun env evd () ->
            let ty =
              Retyping.get_type_of env evd (EConstr.of_constr string_mk)
            in
            let _, list_char, _ = EConstr.destProd evd ty in
            let list, char =
              match EConstr.destApp evd list_char with
              | list, [| char |] -> (list, char)
              | _ ->
                CErrors.user_err
                  Pp.(
                    str "Invalid type for string constructor: "
                    ++ Printer.pr_type_env env evd (EConstr.to_constr evd ty)
                    ++ str " ("
                    ++ Printer.pr_type_env env evd
                         (EConstr.to_constr evd list_char)
                    ++ str " should be an application of list to char)")
            in
            (EConstr.to_constr evd list, EConstr.to_constr evd char))
          ()
      in
      (* instantiate (N.append N.anon "List") [] >>= fun list -> *)
      let list, _ = Constr.destInd list in
      get_uconv >>= fun uconv ->
      let mkChar =
        with_env_evm env uconv
          (fun env evd () ->
            let _, mkChar =
              Evd.fresh_global env evd
                (Rocqlib.lib_ref ("lean." ^ mk_char_prim))
            in
            EConstr.to_constr evd mkChar)
          ()
      in
      ret (mk_string char string list UVars.Instance.empty mkChar s)

and instantiate n univs uconv =
  assert (List.length univs < Sys.int_size);
  (* TODO what happens when is_large_elim and the motive is instantiated with Prop? *)
  let univs = List.map (to_universe uconv.map) univs in
  let i, univs = int_of_univs univs in
  let inst = ensure_exists n i in
  let subst l =
    let u =
      match Level.var_index l with
      | None -> Universe.make l
      | Some n -> List.nth univs n
    in
    Some u
  in
  let extra =
    List.map
      (fun alg -> simplify_universe (UnivSubst.subst_univs_universe subst alg))
      inst.algs
  in
  let univs = List.concat [ univs; extra ] in
  let uconv, univs =
    CList.fold_left_map (fun uconv u -> to_univ_level u uconv) uconv univs
  in
  let u = Instance.of_array ([||], Array.of_list univs) in
  (uconv, Constr.mkRef (inst.ref, u))

and ensure_exists n i =
  try !declared |> N.Map.find n |> Int.Map.find i
  with Not_found ->
    (match N.Map.find_opt n !constructor_owners with
    | Some ind ->
      ignore (ensure_exists ind i);
      !declared |> N.Map.find n |> Int.Map.find i
    | None ->
      (match N.Map.find_opt n !mutual_entries with
      | Some inds ->
        ignore (declare_ind inds i);
        !declared |> N.Map.find n |> Int.Map.find i
      | None ->
        (match N.Map.find n !entries with
        | Def def -> declare_def def i
        | Ax ax -> declare_ax ax i
        | Ind ind -> declare_ind [ ind ] i
        | Quot _ -> CErrors.user_err Pp.(str "quot must be predeclared")
        | exception Not_found -> CErrors.user_err Pp.(str "missing " ++ N.pp n))))

and declare_def { name = n; ty; body; univs; hint; kernel_opaque } i =
  let ref, algs =
    match get_predeclared_def_some n i with
    | Some ((UInt32_size | Nat_isValidChar), _, (def_name, c)) ->
      (* Hack to let the user predeclare some constants
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared");
      (GlobRef.ConstRef c, [])
    | None ->
      let uconv = start_uconv univs i in
      let uconv, ty = to_constr empty_env ty uconv in
      let uconv, body = to_constr empty_env body uconv in
      let univs, algs = univ_entry uconv univs in
      let ref =
        try quickdef ~opaque:kernel_opaque ~name:(name_for n i) ~types:(Some ty) ~univs body
        with e ->
          let e = Exninfo.capture e in
          Feedback.msg_info
            Pp.(
              str "Failed with" ++ fnl ()
              ++ Printer.pr_constr_env (Global.env ())
                   (Evd.from_env (Global.env ()))
                   body
              ++ fnl () ++ str ": "
              ++ Printer.pr_constr_env (Global.env ())
                   (Evd.from_env (Global.env ()))
                   ty);
          Exninfo.iraise e
      in
      (ref, algs)
  in
  let () =
    let c = match ref with ConstRef c -> c | _ -> assert false in
    if not kernel_opaque then begin
      let strategy = match hint with
        | LegacyHint -> Conv_oracle.Level (-(height n body))
        | AbbrevHint -> Conv_oracle.Expand
        | OpaqueHint -> Conv_oracle.Level 1
        | RegularHint h ->
          height_cache := N.Map.add n h !height_cache;
          Conv_oracle.Level (-h)
      in
      Redexpr.set_strategy false [ (strategy, [ Evaluable.EvalConstRef c ]) ]
    end
  in
  let inst = { ref; algs } in
  let () = add_declared n i inst in
  inst

and declare_ax { name = n; ty; univs } i =
  let uconv = start_uconv univs i in
  let uconv, ty = to_constr empty_env ty uconv in
  let univs, algs = univ_entry uconv univs in
  let entry = Declare.(ParameterEntry (parameter_entry ~univs ty)) in
  let c =
    Declare.declare_constant ~name:(name_for n i)
      ~kind:Decls.(IsAssumption Definitional)
      entry
  in
  let inst = { ref = GlobRef.ConstRef c; algs } in
  let () = add_declared n i inst in
  inst

and to_params uconv params =
  let acc, params =
    CList.fold_left_map
      (fun (env, uconv) (_bk, p, ty) ->
        let uconv, ty = to_constr env ty uconv in
        let d = RelDecl.LocalAssum (to_annot env p ty uconv, ty) in
        let env = Environ.push_rel_context_val d env in
        ((env, uconv), d))
      (empty_env, uconv) params
  in
  (acc, List.rev params)

and declare_ind inds i =
  let { name = n; params; univs; _ } = List.hd inds in
  (* Handle inductives predeclared as definitions (e.g., ULift with cumulativity).
     We check if there's a cumul registration for this specific instance. *)
  match (inds, get_predeclared_ind_as_def_some n i) with
  | [ _ ], Some (ULift_cumul, _, _) ->
    let def_name = name_for_core n i in
    let cumul_reg nm = "lean." ^ Id.to_string (name_for_core nm i) ^ ".cumul" in
    Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared (cumulative)");
    (* The Rocq cumul definitions take four universes [r s s1 rs1] where
       [s1] stands for Lean's [s+1] and [rs1] for Lean's [max(r+1, s+1)].
       Lean provides two universes [r; s], so we supply two [algs] that
       synthesise the missing two on every use.  For [ULift.rec] at scheme
       j = 2*i (motive non-SProp), Lean also provides [motive] as the first
       universe, shifting [r] and [s] to positions 1 and 2 in [Level.var].
       For [ULift.rec] at j = 2*i+1 (motive SProp), [motive] is filtered
       out by [int_of_univs] so the indices match the non-rec case. *)
    let algs_of r_idx s_idx =
      let r = Universe.make (Level.var r_idx) in
      let s = Universe.make (Level.var s_idx) in
      [ Universe.super s; Universe.sup (Universe.super r) (Universe.super s) ]
    in
    let algs_2 = algs_of 0 1 in
    let algs_rec = algs_of 1 2 in
    let ulift_ref = Rocqlib.lib_ref (cumul_reg n) in
    let inst = { ref = ulift_ref; algs = algs_2 } in
    add_declared n i inst;
    (* Register ULift.up constructor *)
    let cname = N.append n "up" in
    add_declared cname i { ref = Rocqlib.lib_ref (cumul_reg cname); algs = algs_2 };
    (* Register ULift.down *)
    let dname = N.append n "down" in
    add_declared dname i { ref = Rocqlib.lib_ref (cumul_reg dname); algs = algs_2 };
    (* Register eliminator (Type scheme at j=2*i, SProp scheme at j=2*i+1) *)
    let nrec = N.append n "rec" in
    let rec_base = cumul_reg nrec in
    add_declared nrec (2 * i) { ref = Rocqlib.lib_ref rec_base; algs = algs_rec };
    add_declared nrec ((2 * i) + 1) { ref = Rocqlib.lib_ref (rec_base ^ ".ind"); algs = algs_2 };
    inst
  | _ ->
  (* the block, and for each of its inductives: name, Rocq name, constructors, squashiness *)
  let mind, algs, univs, packets =
    match (inds, get_predeclared_ind_some n i) with
    | [ _ ], Some (Eq, _, (ind_name, mind)) ->
      (* Hack to let the user predeclare eq and quot before running Lean Import
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      let cname = N.append n "refl" in
      let squashy =
        { maybe_prop = true; always_prop = true; lean_squashes = false }
      in
      let univs =
        match i with
        | 0 ->
          UContext.make
            { quals = [||]; univs =  [| Name (Id.of_string "u") |]}
            ( Instance.of_array ([||], [| univ_of_name (N.append N.anon "u") |]),
              PConstraints.empty )
        | 1 -> UContext.empty
        | _ -> assert false
      in
      (mind, [], univs, [ (n, ind_name, [ cname ], squashy) ])
    | [ _ ], Some
        ( ((Nat | Nat_le | Or | And | Fin | UInt32 | Char) as k),
          _,
          (ind_name, mind) ) ->
      (* Hack to let the user predeclare various types before running Lean Import
         TODO make a more general Register-like API? *)
      (* this case is for the ones without universes*)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      let cnames = get_predeclared_cnames k n in
      let squashy = N.Map.get n !squash_info in
      (mind, [], UContext.empty, [ (n, ind_name, cnames, squashy) ])
    | _ ->
      let ntypes = List.length inds in
      List.iter
        (fun ind ->
          if ind.params <> params || ind.univs <> univs then
            CErrors.user_err
              Pp.(str "Mutual inductives have different parameters or universes"))
        (List.tl inds);
      let names = List.map (fun ind -> ind.name) inds in
      let nparams = List.length params in
      let uconv = start_uconv univs i in
      let (env_params, uconv), params = to_params uconv params in
      let uconv, arities =
        CList.fold_left_map
          (fun uconv ind ->
            let uconv, ty = to_constr env_params ind.ty uconv in
            let indices, sort =
              let env_params =
                Environ.set_rel_context_val env_params
                  (Environ.set_universes uconv.graph (Global.env ()))
              in
              Reduction.dest_arity env_params ty
            in
            (uconv, (ty, indices, sort)))
          uconv inds
      in
      let env_inds =
        List.fold_left2
          (fun env ind (ty, _, sort) ->
            Environ.push_rel_context_val
              (LocalAssum
                 ( Context.make_annot (N.to_name ind.name) (Sorts.relevance_of_sort sort),
                   Term.it_mkProd_or_LetIn ty params ))
              env)
          empty_env inds arities
      in
      let env_ind_params =
        Context.Rel.fold_outside Environ.push_rel_context_val params
          ~init:env_inds
      in
      let uconv, packets =
        CList.fold_left2_map
          (fun uconv ind (ty, _, _) ->
            let uconv, ctys =
              CList.fold_left_map
                (fun uconv (_, cty) ->
                  let cty =
                    if ntypes = 1 then cty else remap_mutual_ctor ~nparams ~names ind.name cty
                  in
                  to_constr env_ind_params cty uconv)
                uconv ind.ctors
            in
            (uconv, (ind, name_for ind.name i, ty, ctys)))
          uconv inds arities
      in
      let graph = uconv.graph in
      let univs, algs = univ_entry_gen uconv univs in
      let record, fields, packets =
        match (packets, arities) with
        | [ (ind, ind_name, ty, ([ cty ] as ctys)) ], [ (_, [], sort) ] ->
          let record, fields, ctys =
          cty
          |> with_env_evm env_ind_params uconv (fun env evm cty ->
                 let fields, codom =
                   Reductionops.whd_decompose_prod env evm
                     (EConstr.of_constr cty)
                 in
                 let _, fields =
                   CList.fold_left_map
                     (fun ids (na, t) ->
                       match na.Context.binder_name with
                       | Names.Anonymous -> (ids, (na, t))
                       | Names.Name id ->
                         let id = Namegen.next_global_ident_away (Global.safe_env ()) id ids in
                         let ids = Id.Set.add id ids in
                         line_msg
                           (N.of_list
                              [
                                Names.Id.to_string id;
                                "(field)";
                                Names.Id.to_string ind_name;
                              ]);
                         (ids, ({ na with binder_name = Names.Name id }, t)))
                     (Id.Set.add ind_name Id.Set.empty)
                     fields
                 in
                 let cty' = EConstr.it_mkProd codom fields in
                 let cty' = EConstr.Unsafe.to_constr cty' in
                 (* A recursive single-constructor inductive cannot admit
                    eta, so the kernel rejects the primitive-record
                    encoding. Fall through to plain Inductive in that case. *)
                 let npars = List.length params in
                 let is_recursive =
                   let rec walk k c =
                     match Constr.kind c with
                     | Constr.Prod (_, t, body) ->
                       (not (Vars.noccurn k t)) || walk (k + 1) body
                     | _ -> false
                   in
                   walk (npars + 1) cty'
                 in
                 match (fields, Sorts.is_sprop sort, is_recursive) with
                 | [], true, _ -> (None, [], ctys)
                 | _ :: _, false, false ->
                   (* Proof-only Type records need ordinary induction: they have no primitive eta. *)
                   if
                     List.exists
                       (fun (na, _) ->
                         na.Context.binder_relevance
                         == EConstr.ERelevance.relevant)
                       fields
                   then (Some (Some [| default_proj_id |]), fields, [ cty' ])
                   else (None, [], ctys)
                 | [], false, _ -> (None, [], ctys)
                 | _ :: _, true, false ->
                   if
                     List.for_all
                       (fun (na, _) ->
                         na.Context.binder_relevance
                         == EConstr.ERelevance.irrelevant)
                       fields
                   then (Some (Some [| default_proj_id |]), fields, [ cty' ])
                   else (None, [], ctys)
                 | _ :: _, _, true -> (None, [], ctys))
          in
          (record, fields, [ (ind, ind_name, ty, ctys) ])
        | _ -> (None, [], packets)
      in
      let entry finite =
        {
          Entries.mind_entry_params = params;
          mind_entry_record = record;
          mind_entry_finite = finite;
          mind_entry_inds =
            List.map
              (fun (ind, ind_name, ty, ctys) ->
                {
                  Entries.mind_entry_typename = ind_name;
                  mind_entry_arity = ty;
                  mind_entry_consnames = List.map (fun (c, _) -> name_for c i) ind.ctors;
                  mind_entry_lc = ctys;
                })
              packets;
          mind_entry_private = None;
          mind_entry_universes = Polymorphic_ind_entry univs;
          mind_entry_variance = None;
        }
      in
      let squashy = N.Map.get n !squash_info in
      (* Rocq's own squashing is only overridden for a single inductive. *)
      let coq_squashes =
        match inds with
        | [ _ ] when squashy.maybe_prop -> coq_squashes graph (entry Finite)
        | _ -> false
      in
      let mind =
        let act finite =
          (* no Rocq schemes for a block, only the Lean eliminators below *)
          DeclareInd.declare_mutual_inductive_with_eliminations
            ~schemes:(match inds with [ _ ] -> DeclareInd.Default | _ -> DeclareInd.None)
            (entry finite)
            (* the ubinders API is kind of shit here *)
            (UState.Polymorphic_entry UContext.empty, UnivNames.empty_binders)
            []
        in
        let act () = try act BiFinite with e -> act Finite in
        if squashy.lean_squashes || not coq_squashes then act ()
        else with_unsafe_univs act ()
      in
      assert (
        ntypes > 1 || squashy.lean_squashes
        || (Global.lookup_mind mind).mind_packets.(0).mind_squashed == None);
      (* Declare projections if the inductive is a record *)
      let () =
        match record with
        | Some (Some _) ->
          let _, inhabitant_id, _, _ = List.hd packets in
          let kind = Decls.StructureComponent in
          let proj_flags =
            List.map
              (fun _ ->
                {
                  Record.Data.pf_coercion = None;
                  pf_instance = None;
                  pf_canonical = false;
                })
              fields
          in
          let implfs = List.map (fun _ -> []) fields in
          ignore
            (Record.Internal.declare_projections (mind, 0) ~kind ~inhabitant_id
               proj_flags implfs)
        | _ -> ()
      in
      ( mind,
        algs,
        univs,
        List.map
          (fun (ind, ind_name, _, _) ->
            (ind.name, ind_name, List.map fst ind.ctors, N.Map.get ind.name !squash_info))
          packets )
  in

  (* add inds and ctors to [declared] *)
  List.iteri
    (fun k (n, _, cnames, _) ->
      add_declared n i { ref = GlobRef.IndRef (mind, k); algs };
      CList.iteri
        (fun cnum cname ->
          add_declared cname i { ref = GlobRef.ConstructRef ((mind, k), cnum + 1); algs })
        cnames)
    packets;

  List.iteri (declare_schemes ~i ~univs ~algs mind) packets;
  { ref = GlobRef.IndRef (mind, 0); algs }

(* the Lean eliminators of the [k]th inductive of the block *)
and declare_schemes ~i ~univs ~algs mind k (n, ind_name, _, squashy) =
  let make_scheme fam =
    let u =
      if fam = SchemeSProp then LSProp
      else
        let u =
          if lean_fancy_univs () then
            let u = DirPath.make [ Id.of_string "motive"; lean_id ] in
            Level.(make (UGlobal.make u "" 0))
          else UnivGen.fresh_level ()
        in
        Level u
    in
    let env = Environ.push_context ~strict:true univs (Global.env ()) in
    let env =
      match u with
      | LSProp -> env
      | Level u ->
        Environ.push_context_set ~strict:false (Univ.ContextSet.singleton u) env
    in
    let inst, uentry =
      let inst = UContext.instance univs in
      let csts = UContext.constraints univs in
      let { quals = qnames; univs = unames} = UContext.names univs in
      let uentry =
        match u with
        | LSProp -> UState.Polymorphic_entry univs
        | Level u ->
          UState.Polymorphic_entry
            (UContext.make
               {quals = qnames; univs = Array.append [| Name (Id.of_string "motive") |] unames}
               ( Instance.of_array
                   ([||], Array.append [| u |] (snd (Instance.to_array inst))),
                 csts ))
      in
      (inst, uentry)
    in
    (* lean 4 change: always dep? was not squashy.always_prop*)
    (lean_scheme env ~dep:true (mind, k) inst u, uentry)
  in
  let nrec = N.append n "rec" in
  let elims =
    if squashy.lean_squashes then [ ("_indl", SchemeSProp) ]
    else [ ("_recl", SchemeType); ("_indl", SchemeSProp) ]
  in

  let declare_one_scheme (suffix, sort) =
    let id = Id.of_string (Id.to_string ind_name ^ suffix) in
    let body, uentry = make_scheme sort in
    let elim =
      quickdef ~name:id ~types:None
        ~univs:(uentry, UnivNames.empty_binders)
        body
      (* TODO implicits? *)
    in
    (* TODO AFAICT Lean reduces recursors eagerly, but ofc only when applied to a ctor
       Can we simulate that with strategy better than by leaving them at the default strat? *)
    let liftu l =
      let u =
        match Level.var_index l with
        | None -> Universe.make l (* Set *)
        | Some i -> Universe.make (Level.var (i + 1))
      in
      Some u
    in
    let algs =
      if sort = SchemeSProp then algs
      else List.map (UnivSubst.subst_univs_universe liftu) algs
    in
    let elim = { ref = elim; algs } in
    let j =
      if squashy.lean_squashes then i
      else if sort == SchemeType then 2 * i
      else (2 * i) + 1
    in
    add_declared nrec j elim
  in
  List.iter
    (fun x ->
      try declare_one_scheme x
      with e when CErrors.noncritical e && error_mode e = Skip ->
        Feedback.msg_info Pp.(str "Skipping scheme"))
    elims

(** Squashy info of the [k]th inductive of a block whose arities have sorts
    [aritiesP] at the all-SProp instance and [aritiesT] at instance 0. *)
let squashy inds aritiesP aritiesT k { name = n; params; ctors; _ } =
  let _, sortP = List.nth aritiesP k in
  if not (Sorts.is_sprop sortP) then noprop
  else
    let uconvT, _, paramsT, aritiesT = Lazy.force aritiesT in
    let always_prop = Sorts.is_sprop (snd (List.nth aritiesT k)) in
    match (inds, ctors) with
    | _ :: _ :: _, _ when always_prop ->
      (* a mutual block in Prop only eliminates into Prop *)
      { maybe_prop = true; always_prop; lean_squashes = true }
    | _, [] -> { maybe_prop = true; always_prop; lean_squashes = false }
    | _, _ :: _ :: _ -> { maybe_prop = true; always_prop; lean_squashes = true }
    | _, [ (_, ctor) ] ->
      let ntypes = List.length inds in
      let envT =
        Context.Rel.fold_outside Environ.push_rel_context_val paramsT
          ~init:
            (List.fold_left2
               (fun env ind (tyT, sortT) ->
                 Environ.push_rel_context_val
                   (LocalAssum
                      ( Context.make_annot (N.to_name ind.name)
                          (Sorts.relevance_of_sort sortT),
                        Term.it_mkProd_or_LetIn tyT paramsT ))
                   env)
               empty_env inds aritiesT)
      in
      let ctor =
        if ntypes = 1 then ctor
        else
          remap_mutual_ctor ~nparams:(List.length params)
            ~names:(List.map (fun ind -> ind.name) inds) n ctor
      in
      let uconvT, ctorT = to_constr envT ctor uconvT in
      let envT =
        Environ.set_rel_context_val envT
          (Environ.set_universes uconvT.graph (Global.env ()))
      in
      let args, out = Reduction.whd_decompose_prod envT ctorT in
      let forced =
        (* NB dest_prod returns [out] in whnf *)
        let _, outargs = Constr.decompose_app out in
        Array.fold_left
          (fun forced arg ->
            match Constr.kind arg with
            | Rel i -> Int.Set.add i forced
            | _ -> forced)
          Int.Set.empty outargs
      in
      let sigma = Evd.from_env envT in
      let npars = List.length params in
      let nargs = List.length args in
      let lean_squashes, _, _ =
        Context.Rel.fold_outside
          (fun d (squashed, i, envT) ->
            let squashed =
              if squashed then true
              else if Int.Set.mem (nargs - i) forced then false
              else
                let t = RelDecl.get_type d in
                if
                  List.exists
                    (fun k -> not (Vars.noccurn (npars + i + 1 + k) t))
                    (List.init ntypes Fun.id)
                then (* recursive argument *)
                  false
                else
                  not
                    (EConstr.ESorts.is_sprop sigma
                       (Retyping.get_sort_of envT sigma (EConstr.of_constr t)))
            in

            (squashed, i + 1, Environ.push_rel d envT))
          args ~init:(false, 0, envT)
      in
      (* TODO translate to use non recursively uniform params (fix extraction)*)
      { maybe_prop = true; always_prop; lean_squashes }

(** Generate and add the squashy info *)
let squashify inds =
  let first = List.hd inds in
  (* the arities and their sorts, translated at instance [i] *)
  let arities i =
    let uconv = start_uconv first.univs i in
    let (env_params, uconv), params = to_params uconv first.params in
    let uconv, arities =
      CList.fold_left_map
        (fun uconv ind ->
          let uconv, ty = to_constr env_params ind.ty uconv in
          let env =
            Environ.set_rel_context_val env_params
              (Environ.set_universes uconv.graph (Global.env ()))
          in
          (uconv, (ty, snd (Reduction.dest_arity env ty))))
        uconv inds
    in
    (uconv, env_params, params, arities)
  in
  (* NB: if univs = [] this is just instantiation 0 *)
  let _, _, _, aritiesP = arities ((1 lsl List.length first.univs) - 1) in
  let aritiesT = lazy (arities 0) in
  List.iteri
    (fun k ind ->
      squash_info := N.Map.add ind.name (squashy inds aritiesP aritiesT k ind) !squash_info)
    inds

(* pairs of (name * number of univs) *)
let quots = [ ("", 1); ("mk", 1); ("lift", 2); ("ind", 1) ]

let declare_quot quot_name =
  let () =
    List.iter
      (fun (n, nunivs) ->
        let rec loop i =
          if i = 1 lsl nunivs then ()
          else
            let lean =
              if CString.is_empty n then quot_name else N.append quot_name n
            in
            let reg =
              "lean." ^ N.to_lean_string lean
              ^ if i = 0 then "" else "_inst" ^ string_of_int i
            in
            let ref = Rocqlib.lib_ref reg in
            let () = add_declared lean i { ref; algs = [] } in
            loop (i + 1)
        in
        loop 0)
      quots
  in
  Feedback.msg_info Pp.(str "quot registered")

let declare_quot quot_name =
  if Rocqlib.has_ref "lean.Quot" then declare_quot quot_name else raise MissingQuot

let { Goptions.get = just_parse } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Just"; "Parsing" ]
    ~value:false ()

(* with this off: best line 23000 in stdlib
   stack overflow

   update: got fixed by e9e637de26 (distinguish names foo.bar and foo_bar)
*)
let { Goptions.get = upfront_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Upfront"; "Instantiation" ]
    ~value:false ()

let { Goptions.get = lazy_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Lazy"; "Instantiation" ]
    ~value:false ()

let declare_instances act univs =
  let stop = if upfront_instances () then 1 lsl List.length univs else 1 in
  let rec loop i =
    if i = stop then ()
    else
      let () = act i in
      loop (i + 1)
  in
  if not (lazy_instances ()) then loop 0

let declare_def def =
  declare_instances (fun i -> ignore (declare_def def i)) def.univs

let declare_ax ax =
  declare_instances (fun i -> ignore (declare_ax ax i)) ax.univs

let declare_ind inds =
  let () = squashify inds in
  declare_instances (fun i -> ignore (declare_ind inds i)) (List.hd inds).univs

let entry_name = function
| Quot name | Def { name } | Ax { name } | Ind { name } -> name

let add_entry entry =
  let () =
    match entry with
    | Quot quot_name -> declare_quot quot_name
    | Def def -> declare_def def
    | Ax ax -> declare_ax ax
    | Ind ind -> declare_ind [ ind ]
  in
  entries := N.Map.add (entry_name entry) entry !entries;
  match entry with
  | Ind ind -> constructor_owners := add_constructor_owners ind !constructor_owners
  | Def _ | Ax _ | Quot _ -> ()

(* The inductives of a block are entries of their own, instantiated together. *)
let add_inductives = function
  | [ ind ] -> add_entry (Ind ind)
  | inds ->
    List.iter
      (fun ind ->
        entries := N.Map.add ind.name (Ind ind) !entries;
        constructor_owners := add_constructor_owners ind !constructor_owners;
        mutual_entries := N.Map.add ind.name inds !mutual_entries)
      inds;
    declare_ind inds

let rec is_arity = function
  | Sort _ -> true
  | Pi (_, _, _, b) -> is_arity b
  | _ -> false

let { Goptions.get = print_squashes } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Print"; "Squash"; "Info" ]
    ~value:false ()

type input_state = {
  pstate : LeanParse.parsing_state;
  skips : int;
}

let finish ?(completed = true) state =
  let max_univs, cnt =
    N.Map.fold
      (fun _ entry (m, cnt) ->
        match entry with
        | Ax { univs } | Def { univs } | Ind { univs } ->
          let l = List.length univs in
          (max m l, cnt + (1 lsl l))
        | Quot _ -> (max m 1, cnt + 2))
      !entries (0, 0)
  in
  let nonarities =
    N.Map.fold
      (fun _ entry cnt ->
        match entry with
        | Ax _ | Def _ | Quot _ -> cnt
        | Ind ind -> if is_arity ind.ty then cnt else cnt + 1)
      !entries 0
  in
  let squashes =
    if not (print_squashes ()) then Pp.mt ()
    else
      N.Map.fold
        (fun n s pp -> Pp.(pp ++ fnl () ++ N.pp n ++ spc () ++ pp_squashy s))
        !squash_info
        Pp.(mt ())
  in
  Feedback.msg_info
    Pp.(
      fnl () ++ fnl ()
      ++ str (if completed then "Done!" else "Stopped!")
      ++ fnl () ++ str "- "
      ++ int (N.Map.cardinal !entries)
      ++ str " entries (" ++ int cnt ++ str " possible instances)"
      ++ (if N.Map.exists (fun _ -> function Quot _ -> true | _ -> false) !entries then
            str " (including quot)."
          else str ".")
      ++ fnl () ++
      LeanParse.pp_state state.pstate ++
      (if state.skips > 0 then str "Skipped " ++ int state.skips ++ fnl ()
       else mt ())
      ++ str "Max universe instance length "
      ++ int max_univs ++ str "." ++ fnl () ++ int nonarities
      ++ str " inductives have non syntactically arity types."
      ++ squashes)

let prtime t0 t1 =
  let diff = System.time_difference t0 t1 in
  if diff > 1.0 then
    Feedback.msg_info
      Pp.(
        str "line " ++ int !lcnt ++ str " took "
        ++ System.fmt_time_difference t0 t1)

let timeout = ref None

let () =
  Goptions.declare_int_option
    {
      optdepr = None;
      optstage = Interp;
      optkey = [ "Lean"; "Line"; "Timeout" ];
      optread = (fun () -> !timeout);
      optwrite = (fun x -> timeout := x);
    }

exception TimedOut

let () =
  CErrors.register_handler (function
    | TimedOut -> Some Pp.(str "Lean import line timed out.")
    | _ -> None)

let with_line_timeout act =
  match !timeout with
  | None -> act ()
  | Some t ->
    (match Control.timeout (float_of_int t) act () with
    | Ok v -> v
    | Error info -> Exninfo.iraise (TimedOut, info))

let do_line parse state l =
  let t0 = System.get_time () in
  match with_line_timeout (fun () -> parse ~lcnt:!lcnt state l) with
  | state ->
    prtime t0 (System.get_time ());
    state
  | exception e ->
    let e = Exninfo.capture e in
    if fst e <> TimedOut then prtime t0 (System.get_time ());
    Exninfo.iraise e

let before_from = function None -> false | Some from -> !lcnt < from
let freeze () = (Lib.Interp.freeze (), Summary.Interp.freeze_summaries ())

let unfreeze (lib, sum) =
  Lib.Interp.unfreeze lib;
  Summary.Interp.unfreeze_summaries sum

(* Run a declaration at [line]; [None] when the import stops there. *)
let declare state ch ~line ~raw ~name act =
  (* freeze is actually pretty costly, so make sure we don't run it for non sideffect lines. *)
  let st = freeze () in
  match with_line_timeout act with
  | () -> Some state
  | exception e ->
    let e = Exninfo.capture e in
    let epp =
      Pp.(
        str "Error at line " ++ int line ++ str " (for " ++ N.pp name ++ str ")"
        ++ str (": " ^ raw) ++ fnl () ++ CErrors.iprint e)
    in
    (* without this unfreeze, the global state.declared and the
       global env are out of sync *)
    unfreeze st;
    match error_mode (fst e) with
    | Skip ->
      Feedback.msg_info Pp.(str "Skipping: " ++ epp);
      Some { state with skips = state.skips + 1 }
    | Stop ->
      close_in ch;
      finish ~completed:false state;
      Feedback.msg_info epp;
      None
    | Fail ->
      close_in ch;
      CErrors.user_err epp

(* Consecutive inductive lines form one mutual block, declared (under the line
   of its first member) when a line of another kind follows. *)
type pending = { line : int; raw : string; inds : ind list (* reversed *) }

let declare_pending state ch = function
  | None -> Some state
  | Some { line; raw; inds } ->
    let inds = List.rev inds in
    declare state ch ~line ~raw ~name:(List.hd inds).name (fun () -> add_inductives inds)

let rec do_input parse state ~from ~until ~pending ch =
  let finished state =
    close_in ch;
    finish state;
    state
  in
  if until = Some !lcnt then
    match declare_pending state ch pending with
    | None -> state
    | Some state -> finished state
  else
    match input_line ch with
    | exception End_of_file ->
      (match declare_pending state ch pending with
      | None -> state
      | Some state ->
        let state = finished state in
        if not (until = None) then CErrors.user_err Pp.(str "unexpected EOF!");
        state)
    | _ when before_from from ->
      incr lcnt;
      do_input parse state ~from ~until ~pending ch
    | raw ->
      let pstate, action = do_line parse state.pstate raw in
      let state = { state with pstate } in
      (match (just_parse (), action) with
      | false, Some (Entry (Ind ind)) ->
        let pending =
          match pending with
          | None -> Some { line = !lcnt; raw; inds = [ ind ] }
          | Some pending -> Some { pending with inds = ind :: pending.inds }
        in
        incr lcnt;
        do_input parse state ~from ~until ~pending ch
      | _ ->
        (match declare_pending state ch pending with
        | None -> state
        | Some state ->
          let declared =
            match (just_parse (), action) with
            | true, _ | false, None -> Some state
            | false, Some (Nota _) -> Some state (* notations not yet implemented *)
            | false, Some (Entry entry) ->
              declare state ch ~line:!lcnt ~raw ~name:(entry_name entry) (fun () ->
                  add_entry entry)
            | false, Some (MutualInd inds) ->
              declare state ch ~line:!lcnt ~raw ~name:(List.hd inds).name (fun () ->
                  add_inductives inds)
          in
          (match declared with
          | None -> state
          | Some state ->
            incr lcnt;
            do_input parse state ~from ~until ~pending:None ch)))

let do_input state ~from ~until ch =
  let start = pos_in ch in
  let rec detect () =
    match input_line ch with
    | line when String.trim line = "" -> detect ()
    | line -> LeanParseNdjson.is_ndjson_line line
    | exception End_of_file -> false
  in
  let ndjson = detect () in
  seek_in ch start;
  let parse =
    if not ndjson then LeanParse.do_line
    else
      let parser = ref
        (LeanParseNdjson.of_state ~seen_meta:(before_from from) state.pstate) in
      fun ~lcnt _ line ->
        let next, action = LeanParseNdjson.do_line ~lcnt !parser line in
        parser := next;
        LeanParseNdjson.to_state next, action
  in
  do_input parse state ~from ~until ~pending:None ch

let pstate = Summary.ref ~name:"lean-parse-state" LeanParse.empty_state

(* The importer state is kept in a library object as one marshalled string, with
   the expression index encoded by [LeanParse.Checkpoint], and is unpacked at
   the next [Lean Import] rather than when the library is loaded. *)
module Checkpoint = struct
  module C = LeanParse.Checkpoint

  type saved = {
    parser : C.t;
    sets : Level.t Int.Map.t;
    declared : instantiation Int.Map.t N.Map.t;
    entries : C.saved_entry N.Map.t;
    mutual_entries : C.saved_ind list N.Map.t;
    squash_info : squashy N.Map.t;
    heights : int N.Map.t;
  }

  type packed = { format : int; digest : string; blob : string }

  (* Version of the [saved] layout. *)
  let format = 3

  let save () =
    let parser, (entries, mutual_entries) =
      C.pack !pstate (fun save ->
        N.Map.map (C.save_entry save) !entries,
        N.Map.map (List.map (C.save_ind save)) !mutual_entries)
    in
    { parser; sets = !sets; declared = !declared; entries; mutual_entries;
      squash_info = !squash_info; heights = !height_cache }

  let restore saved =
    let parser, load = C.unpack saved.parser in
    pstate := parser;
    sets := saved.sets;
    declared := saved.declared;
    entries := N.Map.map (C.load_entry load) saved.entries;
    mutual_entries := N.Map.map (List.map (C.load_ind load)) saved.mutual_entries;
    constructor_owners :=
      N.Map.fold
        (fun _ entry owners ->
          match entry with
          | Ind ind -> add_constructor_owners ind owners
          | Def _ | Ax _ | Quot _ -> owners)
        !entries N.Map.empty;
    squash_info := saved.squash_info;
    height_cache := saved.heights

  let pack () =
    (* Reclaim the garbage left by conversion before the encoding allocates. *)
    Gc.compact ();
    let saved = save () in
    Gc.compact ();
    let blob, () =
      C.output_to_string "lean-import-state" (fun oc -> Marshal.to_channel oc saved [])
    in
    { format; digest = Digest.to_hex (Digest.string blob); blob }

  let unpack packed =
    if packed.format <> format then
      CErrors.user_err
        Pp.(str "Unsupported Lean importer checkpoint format " ++ int packed.format ++ str ".");
    if packed.digest <> Digest.to_hex (Digest.string packed.blob) then
      CErrors.user_err Pp.(str "Corrupted Lean importer checkpoint.");
    try (Marshal.from_string packed.blob 0 : saved)
    with Failure _ | Invalid_argument _ ->
      CErrors.user_err Pp.(str "Invalid Lean importer checkpoint.")

  let pending = Summary.ref ~name:"lean-pending-checkpoint" None

  let obj =
    let open Libobject in
    declare_object
      {
        (default_object "LEAN-IMPORT-STATE-V2") with
        (* [import] has installed the state itself before [Lib.add_leaf]. *)
        cache_function = (fun _ -> ());
        load_function = (fun _ packed -> pending := Some packed);
        classify_function = (fun _ -> Keep);
      }

  let force () =
    match !pending with
    | None -> ()
    | Some packed ->
      let saved = unpack packed in
      pending := None;
      restore saved

  let add_leaf () = Lib.add_leaf (obj (pack ()))
end

let import ~from ~until f =
  Checkpoint.force ();
  lcnt := 1;
  (* silence the definition messages from Coq *)
  let { pstate = pstatev } =
    Flags.silently (fun () ->
        do_input { pstate = !pstate; skips = 0 } ~from ~until (open_in f)) ()
  in
  pstate := pstatev;
  Checkpoint.add_leaf ()
