open Names

type t = string list
(** "foo.bar.baz" is [baz;bar;foo] (like with dirpaths) *)

let anon : t = []
let of_list x = x

let toclean =
  [
    ('@', "__at__");
    ('?', "__q");
    ('!', "__B");
    ('#', "__hash");
    ('$', "__dollar");
    ('%', "__pct");
    ('&', "__amp");
    ('\\', "__bs");
    ('/', "__fs");
    ('^', "__v");
    ('(', "__o");
    (')', "__c");
    ('*', "__star");
    ('+', "__plus");
    (',', "__comma");
    ('-', "__dash");
    ('.', "__dot");
    (':', "__co");
    (';', "__semi");
    ('<', "__lt");
    ('=', "__eq");
    ('>', "__gt");
    ('[', "__lbrack");
    (']', "__rbrack");
    ('{', "__lbrace");
    ('|', "__bar");
    ('}', "__rbrace");
    ('~', "__tilde");
  ]

let clean_string s =
  List.fold_left
    (fun s (c, replace) -> String.concat replace (String.split_on_char c s))
    (Unicode.ascii_of_ident s) toclean

let append a b = clean_string b :: a
let append_list a bs = List.append (List.rev_map clean_string bs) a
let unappend = function [] -> None | component :: parent -> Some (parent, component)
let raw_append a b = match a with [] -> [ b ] | hd :: tl -> (hd ^ b) :: tl
(* A spelling that is not a Rocq identifier is escaped here only, so that
   internal (and checkpointed) names are unchanged. *)
let to_coq_string x =
  let s = String.concat "_" (List.rev x) in
  if Id.is_valid s then s
  else
    let out = Buffer.create (String.length s + 16) in
    Buffer.add_string out "lean_name_";
    String.iter
      (function
        | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'') as c ->
          Buffer.add_char out c
        | c -> Printf.bprintf out "_x%02x_" (Char.code c))
      s;
    Buffer.contents out

let to_id (x : t) = Id.of_string (to_coq_string x)
let to_name x = if x = [] then Anonymous else Name (to_id x)
let to_lean_string x = String.concat "." (List.rev x)
let pp x = Pp.(prlist_with_sep (fun () -> str ".") str) (List.rev x)
let equal = CList.equal String.equal

module Self = struct
  type nonrec t = t

  let compare = CList.compare String.compare
end

module Set = Set.Make (Self)
module Map = CMap.Make (Self)
