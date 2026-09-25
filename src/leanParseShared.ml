open LeanExpr
module N = LeanName

module RRange : sig
  type 'a t
  (** Like Range.t, but instead of cons we append *)

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end = struct
  type 'a t = {
    chunks : 'a array Range.t;
    tail : 'a Range.t;
    len : int;
  }

  (* Elements are packed into arrays of [chunk_size] once appended, so the
     tree only holds one node per chunk plus the unfinished tail. *)
  let chunk_size = 256
  let empty = { chunks = Range.empty; tail = Range.empty; len = 0 }
  let length x = x.len

  let append { chunks; tail; len } x =
    let tail = Range.cons x tail in
    let len = len + 1 in
    if len mod chunk_size <> 0 then { chunks; tail; len }
    else
      let chunk =
        Array.init chunk_size (fun i -> Range.get tail (chunk_size - i - 1))
      in
      { chunks = Range.cons chunk chunks; tail = Range.empty; len }

  let get { chunks; tail; len } i =
    if i < 0 || i >= len then raise Not_found;
    let full_chunks = len / chunk_size in
    if i / chunk_size = full_chunks then Range.get tail (len - i - 1)
    else
      let chunk = Range.get chunks (full_chunks - i / chunk_size - 1) in
      chunk.(i mod chunk_size)

  let singleton x = append empty x
end

(** Replace [n] (meant to be an the inductive type appearing in the constructor
    type) by (Bound k). *)
let rec replace_ind ind k = function
  | Const (n', _) when N.equal ind n' -> Bound k
  | (Const _ | Bound _ | Sort _) as e -> e
  | App (a, b) -> App (replace_ind ind k a, replace_ind ind k b)
  | Let { name; ty; v; rest } ->
    Let
      {
        name;
        ty = replace_ind ind k ty;
        v = replace_ind ind k v;
        rest = replace_ind ind (k + 1) rest;
      }
  | Lam (bk, name, a, b) ->
    Lam (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)
  | Pi (bk, name, a, b) ->
    Pi (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)
  | Proj (n, field, c) -> Proj (n, field, replace_ind ind k c)
  | (Nat _ | String _) as x -> x

let rec pop_params npar ty =
  if npar = 0 then ([], ty)
  else
    match ty with
    | Pi (bk, name, a, b) ->
      let pars, ty = pop_params (npar - 1) b in
      ((bk, name, a) :: pars, ty)
    | _ -> assert false

let fix_ctor ind nparams ty =
  let _, ty = pop_params nparams ty in
  replace_ind ind nparams ty

let quot_name = N.append N.anon "Quot"
