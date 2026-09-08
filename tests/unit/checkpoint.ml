open LeanExpr
module C = LeanParse.Checkpoint

let check b message = if not b then failwith message
let add state line = fst (LeanParse.do_line ~lcnt:1 state line)
let body state id =
  match snd (LeanParse.do_line ~lcnt:1 state (Printf.sprintf "#DEF 0 0 %d" id)) with
  | Some (Entry (Def d)) -> d.body | _ -> assert false

let roundtrip value = Marshal.from_string (Marshal.to_string value []) 0

let () =
  let empty, () = C.pack LeanParse.empty_state (fun _ -> ()) in
  ignore (C.unpack (roundtrip empty));
  let state = List.fold_left add LeanParse.empty_state [
    "1 #NS 0 T"; "2 #NS 1 mk"; "1 #US 0"; "2 #UP 1";
    "3 #UM 1 2"; "4 #UIM 2 3";
    "0 #EV 0"; "1 #ES 4"; "2 #EC 1 0 1 2 3 4";
    "3 #EA 2 0"; "4 #EZ 1 1 3 0";
    "5 #EL #BI 1 1 4"; "6 #EP #BC 2 1 5";
    "7 #EJ 1 3 6"; "8 #ELN 123456789012345678901234567890";
    "9 #ELS 00 FF 41"; "10 #EV -3";
    "11 #EL #BD 0 1 0"; "12 #EP #BS 0 1 0"
  ] in
  let state = ref state in
  for i = 13 to 620 do
    state := add !state (Printf.sprintf "%d #EA %d %d" i (i - 1) (i - 1))
  done;
  let original = !state in
  let root = body original 620 in
  let fragment = Let {name = LeanName.anon; ty = body original 1; v = root; rest = root} in
  let fragment_dag = App (fragment, fragment) in
  let ind : ind = {name = LeanName.anon; params = [NotImplicit, LeanName.anon, fragment];
    ty = root; ctors = [LeanName.anon, fragment]; univs = []} in
  let entries = [
    Def {name = LeanName.anon; ty = body original 1; body = root;
      univs = []; hint = RegularHint 123; kernel_opaque = true};
    Ax {name = LeanName.anon; ty = fragment; univs = []};
    Ind ind; Quot LeanName.anon
  ] in
  let saved, (saved_entries, saved_ind, saved_fragment) =
    C.pack original (fun save ->
      List.map (C.save_entry save) entries, C.save_ind save ind, save fragment_dag)
  in
  let saved, saved_entries, saved_ind, saved_fragment =
    roundtrip (saved, saved_entries, saved_ind, saved_fragment) in
  let restored, load = C.unpack saved in
  (* Compare only shallow nodes of the deep DAG, not its exponential unfolding. *)
  for i = 0 to 12 do check (body restored i = body original i) "node roundtrip changed" done;
  for i = 13 to 620 do
    match body restored i with
    | App (a, b) -> check (a == b && a == body restored (i - 1)) "parser sharing lost"
    | _ -> failwith "application changed"
  done;
  let loaded_entries = List.map (C.load_entry load) saved_entries in
  (match List.hd loaded_entries with
  | Def d -> check (d.body == body restored 620) "entry/parser alias lost";
    check (d.ty == body restored 1 && d.hint = RegularHint 123 && d.kernel_opaque)
      "definition metadata changed"
  | _ -> assert false);
  let loaded_ind = C.load_ind load saved_ind in
  (match List.nth loaded_entries 2 with
  | Ind i -> check (i.ty == loaded_ind.ty && snd (List.hd i.ctors) == snd (List.hd loaded_ind.ctors))
      "mutual/entry fragment alias lost"
  | _ -> assert false);
  (match load saved_fragment with
  | App (a, b) -> check (a == b) "fresh fragment DAG was expanded";
    (match a with Let {v; rest; _} -> check (v == rest && v == body restored 620)
      "fragment/parser alias lost" | _ -> assert false)
  | _ -> assert false);
  let extended = add restored "621 #EA 620 0" in
  (match body extended 621 with
  | App (a, b) -> check (a == body restored 620 && b == body restored 0) "append copied prefix"
  | _ -> assert false);
  (try ignore (body restored 621); failwith "old snapshot changed" with Not_found -> ());
  (* Malformed-wire fixtures only: the opaque record has two unchanged indices
     and a byte string. Rebuild its wire value without mutating the valid one. *)
  let raw = Obj.repr saved in
  let data : string = Obj.obj (Obj.field raw 2) in
  let corrupt data : C.t = roundtrip (Obj.obj (Obj.field raw 0), Obj.obj (Obj.field raw 1), data) in
  (* Two parser IDs may refer to one node: exercise the alias wire tag and
     its re-encoding, even though ordinary parsing allocates fresh nodes. *)
  let aliases, _ = C.unpack (corrupt "LCP1\002\000\0010\010\000") in
  check (body aliases 0 == body aliases 1) "alias tag copied its target";
  let aliases, () = C.pack aliases (fun _ -> ()) in
  let aliases, _ = C.unpack (roundtrip aliases) in
  check (body aliases 0 == body aliases 1) "alias re-encoding lost sharing";
  let reject data =
    try ignore (C.unpack (corrupt data)); failwith "malformed graph accepted"
    with Invalid_argument _ -> ()
  in
  reject ""; reject ("BAD!" ^ String.sub data 4 (String.length data - 4));
  reject (data ^ "x"); reject (String.sub data 0 (String.length data - 1));
  reject "LCP1\001\003\000\000"; (* forward reference in the first node *)
  reject "LCP1\001\255";
  reject "LCP1\001\001\127"; (* universe index outside its saved range *)
  reject "LCP1\001\002\127\000"; (* name index outside its saved range *)
  reject ("LCP1" ^ String.make 12 '\255'); (* overflowing varint count *)
  reject "LCP1\001\009\127"; (* string length exceeds the remaining bytes *)
  let original_blob = Marshal.to_string original [] in
  let indexed_blob = Marshal.to_string saved [] in
  Printf.printf "parser Marshal bytes: original=%d indexed=%d\n%!"
    (String.length original_blob) (String.length indexed_blob);
  print_endline "indexed checkpoint: nodes, DAG aliases, fragments, metadata, branches and invalid data passed"
