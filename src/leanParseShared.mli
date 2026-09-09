open LeanExpr

module RRange : sig
  type 'a t
  (** Persistent, append-only index. Published chunks are never mutated. *)

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end

type indices = {
  names : LeanName.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
}

val pop_params : int -> expr -> (binder_kind * LeanName.t * expr) list * expr
val fix_ctor : LeanName.t -> int -> expr -> expr
val quot_name : LeanName.t
