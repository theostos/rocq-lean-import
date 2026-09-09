type parsing_state

type legacy_parsing_state
(** Parser representation stored before the chunked index (packed format 1). *)

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

  (** Encode parser edges by index. Metadata must use [save] for expression
      roots so they reload as references into the very same parser graph.
      Non-indexed fragments, such as adapted constructor types, remain typed
      expression trees with indexed references to their existing subterms. *)
  val pack : parsing_state -> ((LeanExpr.expr -> saved_expr) -> 'a) -> t * 'a
  val unpack : t -> parsing_state * (saved_expr -> LeanExpr.expr)
  val save_ind : (LeanExpr.expr -> saved_expr) -> LeanExpr.ind -> saved_ind
  val load_ind : (saved_expr -> LeanExpr.expr) -> saved_ind -> LeanExpr.ind
  val save_entry : (LeanExpr.expr -> saved_expr) -> LeanExpr.entry -> saved_entry
  val load_entry : (saved_expr -> LeanExpr.expr) -> saved_entry -> LeanExpr.entry
end
