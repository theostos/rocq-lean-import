type parsing_state = {
  names : LeanName.t LeanParseShared.RRange.t;
  exprs : LeanExpr.expr LeanParseShared.RRange.t;
  univs : LeanExpr.U.t LeanParseShared.RRange.t;
}

val empty_state : parsing_state

val do_line : lcnt:int -> parsing_state -> string ->
  parsing_state * LeanExpr.action option

val pp_state : parsing_state -> Pp.t

(** Compact representation of the parser state for library objects. *)
module Checkpoint : sig
  type t
  type saved_expr
  type saved_ind
  type saved_entry

  (** [pack state save_metadata] encodes the expression index; the metadata
      saved with it must go through [save] so that its expressions reload as
      references into the same index. *)
  val pack : parsing_state -> ((LeanExpr.expr -> saved_expr) -> 'a) -> t * 'a
  val unpack : t -> parsing_state * (saved_expr -> LeanExpr.expr)
  val output_to_string : string -> (out_channel -> 'a) -> string * 'a
  val save_ind : (LeanExpr.expr -> saved_expr) -> LeanExpr.ind -> saved_ind
  val load_ind : (saved_expr -> LeanExpr.expr) -> saved_ind -> LeanExpr.ind
  val save_entry : (LeanExpr.expr -> saved_expr) -> LeanExpr.entry -> saved_entry
  val load_entry : (saved_expr -> LeanExpr.expr) -> saved_entry -> LeanExpr.entry
end
