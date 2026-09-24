open LeanExpr

type parsing_state

val empty_state : parsing_state

(** The NDJSON parser shares the indices of the line parser, with the
    checkpointed state, and only adds [seen_meta]. *)
val of_state : seen_meta:bool -> LeanParse.parsing_state -> parsing_state
val to_state : parsing_state -> LeanParse.parsing_state
val is_ndjson_line : string -> bool
val do_line : lcnt:int -> parsing_state -> string -> parsing_state * action option
