(* Public-parser regressions for the persistent index and its legacy migration.
   Parsing only: no Lean declaration is submitted to the Rocq kernel. *)
open LeanExpr
module N = LeanName

let check condition message = if not condition then failwith message

let parse state line = LeanParse.do_line ~lcnt:1 state line

let add state line =
  match parse state line with
  | state, None -> state
  | _, Some _ -> failwith "expected an index entry"

let definition state name ty body univs =
  let fields = ["#DEF"; string_of_int name; string_of_int ty; string_of_int body]
    @ List.map string_of_int univs in
  match parse state (String.concat " " fields) with
  | _, Some (Entry (Def def)) -> def
  | _ -> failwith "expected a definition"

let body_at state index = (definition state 0 0 index []).body

let expect_missing state index =
  try
    ignore (body_at state index);
    failwith "an old snapshot acquired a later expression"
  with Not_found -> ()

let append_named_sort state index label =
  let state = add state (Printf.sprintf "%d #NS 0 %s" index label) in
  let state = add state (Printf.sprintf "%d #UP %d" index index) in
  add state (Printf.sprintf "%d #ES %d" index index)

let check_index state index =
  let def = definition state index index index [index] in
  let expected =
    if index = 0 then N.anon else N.append N.anon (Printf.sprintf "n%d" index)
  in
  check (N.equal def.name expected) "name index changed";
  check (def.ty == def.body) "type/body no longer share their expression";
  (match def.univs with
  | [name] -> check (name == def.name) "universe parameter name was copied"
  | _ -> failwith "wrong universe parameters");
  match def.body with
  | Sort U.Prop when index = 0 -> ()
  | Sort (U.UNamed name) when index > 0 ->
    check (name == def.name) "named universe lost name sharing"
  | _ -> failwith "expression/universe index changed"

let check_indices state =
  for index = 0 to 600 do check_index state index done

let make_states () =
  let states = Array.make 601 LeanParse.empty_state in
  states.(0) <- add LeanParse.empty_state "0 #ES 0";
  for index = 1 to 600 do
    states.(index) <- append_named_sort states.(index - 1) index
      (Printf.sprintf "n%d" index)
  done;
  states

let check_branches states =
  (* Append immediately before, at, and after both chunk boundaries. *)
  List.iter (fun index ->
    let saved = states.(index - 1) in
    let old_body = body_at saved (index - 1) in
    let left = append_named_sort saved index "left" in
    let right = append_named_sort saved index "right" in
    let restored = saved in
    let third = append_named_sort restored index "restored" in
    List.iter (fun (state, label) ->
      let def = definition state index index index [index] in
      check (N.equal def.name (N.append N.anon label)) "append branches interfered";
      check (body_at state (index - 1) == old_body) "prefix expression was copied";
      match def.body with
      | Sort (U.UNamed name) ->
        check (name == def.name) "branch name/universe/expression indexes diverged"
      | _ -> failwith "wrong branch expression")
      [left, "left"; right, "right"; third, "restored"];
    expect_missing saved index;
    check_index saved (index - 1))
    [255; 256; 257; 511; 512; 513]

let check_graph state expected_body =
  let base = body_at state 600 in
  let def = definition state 600 600 602 [] in
  check (def.body == expected_body) "declaration body lost its graph alias";
  check (def.ty == base) "declaration type lost its graph alias";
  match def.body with
  | App (left, right) ->
    check (left == right) "shared application child was duplicated";
    (match left with
    | App (first, second) ->
      check (first == base && second == base) "shared leaf was duplicated"
    | _ -> failwith "missing inner application")
  | _ -> failwith "missing outer application"

let check_new_roundtrip state =
  let state = add state "601 #EA 600 600" in
  let state = add state "602 #EA 601 601" in
  let body = body_at state 602 in
  check_graph state body;
  let (state, body) : LeanParse.parsing_state * expr =
    Marshal.from_string (Marshal.to_string (state, body) []) 0
  in
  check_graph state body

(* These record shapes are the original wire representation, independently
   defined here; do not replace them with the new index implementation. *)
module Legacy = struct
  type 'a range = { data : 'a Range.t; len : int }
  type state = {
    names : N.t range;
    exprs : expr range;
    univs : U.t range;
  }

  let range values =
    Array.fold_left (fun range value ->
      { data = Range.cons value range.data; len = range.len + 1 })
      { data = Range.empty; len = 0 } values

  let empty = {
    names = range [|N.anon|]; exprs = range [||]; univs = range [|U.Prop|];
  }
end

let migrate (state : Legacy.state) =
  let legacy : LeanParse.legacy_parsing_state =
    Marshal.from_string (Marshal.to_string state []) 0
  in
  LeanParse.migrate_legacy_state legacy

let check_migration () =
  let empty = migrate Legacy.empty in
  let singleton = add empty "0 #ES 0" in
  check_index singleton 0;
  let old_singleton : Legacy.state =
    { Legacy.empty with exprs = Legacy.range [|Sort U.Prop|] }
  in
  check_index (migrate old_singleton) 0;
  let names = Array.init 601 (fun index ->
    if index = 0 then N.anon else N.append N.anon (Printf.sprintf "n%d" index)) in
  let univs = Array.init 601 (fun index ->
    if index = 0 then U.Prop else U.UNamed names.(index)) in
  let exprs = Array.make 603 (Bound 0) in
  for index = 0 to 600 do exprs.(index) <- Sort univs.(index) done;
  exprs.(601) <- App (exprs.(600), exprs.(600));
  exprs.(602) <- App (exprs.(601), exprs.(601));
  let old : Legacy.state = {
    names = Legacy.range names;
    exprs = Legacy.range exprs;
    univs = Legacy.range univs;
  } in
  (* Decode the parser and an external body together, preserving wire aliases. *)
  let (legacy, body) : LeanParse.legacy_parsing_state * expr =
    Marshal.from_string (Marshal.to_string (old, exprs.(602)) []) 0
  in
  let state = LeanParse.migrate_legacy_state legacy in
  check_indices state;
  check_graph state body;
  let extended = add state "603 #EA 602 600" in
  (match body_at extended 603 with
  | App (left, right) ->
    check (left == body && right == body_at state 600) "post-migration append copied AST"
  | _ -> failwith "wrong post-migration application");
  expect_missing state 603;
  check_graph state body;
  let (state, body) : LeanParse.parsing_state * expr =
    Marshal.from_string (Marshal.to_string (extended, body) []) 0
  in
  check_graph state body

let () =
  let states = make_states () in
  check_indices states.(600);
  check_branches states;
  check_new_roundtrip states.(600);
  check_migration ();
  print_endline "chunked parser: indexes, snapshots, sharing and legacy migration passed"
