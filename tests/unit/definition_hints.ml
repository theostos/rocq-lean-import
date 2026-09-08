(* All definition tags retain a body. An opaque reducibility hint must not
   silently turn a transparent definition into a genuinely opaque one. *)
open LeanExpr
module N = LeanName

let parse state line = LeanParse.do_line ~lcnt:1 state line
let add state line = fst (parse state line)
let check condition message = if not condition then failwith message

let definition state tag =
  match snd (parse state (tag ^ " 1 0 1 3 2")) with
  | Some (Entry (Def def)) -> def
  | _ -> failwith (tag ^ " did not produce a definition with a body")

let () =
  let state = List.fold_left add LeanParse.empty_state [
    "1 #NS 0 example"; "2 #NS 0 u"; "3 #NS 0 v";
    "0 #ES 0"; "1 #ELN 42"
  ] in
  let legacy = definition state "#DEF" in
  List.iter (fun (tag, hint, opaque) ->
    let def = definition state tag in
    check (def.hint = hint) (tag ^ ": wrong reducibility hint");
    check (def.kernel_opaque = opaque) (tag ^ ": wrong declaration opacity");
    check (N.equal def.name (N.append N.anon "example")) (tag ^ ": name changed");
    check (def.univs = [N.append N.anon "v"; N.append N.anon "u"])
      (tag ^ ": universe parameter order changed");
    check (def.ty == legacy.ty && def.body == legacy.body)
      (tag ^ ": declaration type/body sharing changed");
    (match def.ty, def.body with
    | Sort U.Prop, Nat n -> check (Z.equal n (Z.of_int 42)) (tag ^ ": body changed")
    | _ -> failwith (tag ^ ": declaration type or body was lost")))
    [
      "#DEF", LegacyHint, false;
      "#ABBREV", AbbrevHint, false;
      "#REGULAR 0", RegularHint 0, false;
      "#REGULAR 123", RegularHint 123, false;
      "#HINT_OPAQUE", OpaqueHint, false;
      "#OPAQUE", OpaqueHint, true;
    ];
  print_endline "definition hints: legacy, abbreviation, height and genuine opacity passed"
