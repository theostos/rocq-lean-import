From LeanImport Require Import Lean.

(* Newer Lean versions construct strings from character lists with
   [String.ofList]; [String]'s actual constructor stores a byte array. *)
Lean Import "../dumps/string_of_list".

Check stringFromLiteral : String.
