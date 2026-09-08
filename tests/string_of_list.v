From LeanImport Require Import Lean.

(* Isolate literal construction when [String.ofList], rather than [String.mk],
   is exported. This synthetic fixture abstracts over the byte-array layout. *)
Lean Import "../dumps/string_of_list".

Check stringFromLiteral : String.
