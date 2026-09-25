From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Redirect "ndjson_nested_containers.log" Lean Import "../dumps/nested_containers.ndjson".
(* nested through a self-nested container (Tagged, through Array) and a
   two-constructor wrapper: the list fixpoint is not reused inside Tagged's *)
Check (fun t => eq_refl _ : eq (Embed_count (Embed_trace Nat_zero t (SOrL_lazy _ Nat Nat_zero)))
  (Nat_succ (plus (Embed_countT t) Nat_zero))).
Definition leaf := Embed_trace Nat_zero (Tagged_text Embed Nat_zero) (SOrL_lazy _ Nat Nat_zero).
Definition deep := Tagged_append Embed (Array_mk_inst1 _ (List_cons_inst1 _
  (Tagged_tag Embed leaf (Tagged_text Embed Nat_zero)) (List_nil_inst1 _))).
Check (eq_refl _ : eq (Embed_count (Embed_trace Nat_zero deep
  (SOrL_strict _ Nat (Array_mk_inst1 _ (List_cons_inst1 _ deep (List_nil_inst1 _))))))
  (Nat_succ (Nat_succ (Nat_succ Nat_zero)))).
