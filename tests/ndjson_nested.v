From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Redirect "ndjson_nested.log" Lean Import "../dumps/nested.ndjson".
(* nested occurrences get their hypotheses through the All scheme of the container *)
Check (LTree_recl : forall P : LTree -> Type,
  (forall l, List_inst1_all LTree P l -> P (LTree_node l)) -> forall t, P t).
Check (WTree_recl : forall P : WTree -> Type,
  (forall w, Wrap_all WTree P w -> P (WTree_node w)) -> forall t, P t).
Check (MB_recl : forall (P : MA -> Type) (P0 : MB -> Type),
  (forall l, List_inst1_all MB P0 l -> P (MA_node l)) -> P0 MB_leaf ->
  (forall a, P a -> P0 (MB_node a)) -> forall b, P0 b).
Check (Array_inst1_all : forall A, (A -> Type) -> Array_inst1 A -> Type).
Check (Prod_inst3_all_01 : forall A B, (B -> Type) -> Prod_inst3 A B -> Type).
(* Lean's main and auxiliary recursors reduce on constructors *)
Check (eq_refl _ : eq (LTree_size LTree_two) (Nat_succ (Nat_succ Nat_zero))).
Check (fun ts => eq_refl _ : eq (ATree_size (ATree_node (Array_mk_inst1 ATree ts))) (Nat_succ (ATree_sizes ts))).
Check (fun t => eq_refl _ : eq (OTree_size (OTree_node (Option_some_inst1 OTree t))) (Nat_succ (OTree_size t))).
Check (fun n t => eq_refl _ : eq (PTree_size (PTree_node (Prod_mk_inst3 Nat PTree n t))) (Nat_succ (plus n (PTree_size t)))).
Check (fun n t => eq_refl _ : eq (WTree_size (WTree_node (Wrap_mk WTree n t))) (Nat_succ (plus n (WTree_size t)))).
Check (fun ts => eq_refl _ : eq (MA_size (MA_node ts)) (Nat_succ (MB_sizes ts))).
Check (fun n t => eq_refl _ : eq (TA_count (Nat_succ n) (TA_node n (TB_wrap n t))) (Nat_succ (TA_count n t))).
