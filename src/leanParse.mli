type parsing_state

type legacy_parsing_state

val migrate_legacy_state : legacy_parsing_state -> parsing_state

val empty_state : parsing_state

val do_line : lcnt:int -> parsing_state -> string ->
  parsing_state * LeanExpr.action option

val pp_state : parsing_state -> Pp.t

module Checkpoint : sig
  type t
  type saved_expr
  type saved_ind
  type saved_entry

  (** Use [save] for metadata roots to preserve sharing with parser expressions. *)
  val pack : parsing_state -> ((LeanExpr.expr -> saved_expr) -> 'a) -> t * 'a
  val unpack : t -> parsing_state * (saved_expr -> LeanExpr.expr)
  val save_ind : (LeanExpr.expr -> saved_expr) -> LeanExpr.ind -> saved_ind
  val load_ind : (saved_expr -> LeanExpr.expr) -> saved_ind -> LeanExpr.ind
  val save_entry : (LeanExpr.expr -> saved_expr) -> LeanExpr.entry -> saved_entry
  val load_entry : (saved_expr -> LeanExpr.expr) -> saved_entry -> LeanExpr.entry
end
