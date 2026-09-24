From LeanImport Require Import Lean.
Redirect "ndjson_mutual.log" Lean Import "../dumps/mutual.ndjson".
Check (Tree_recl : forall (P : Tree -> Type) (P0 : Forest -> Type),
  (forall f, P0 f -> P (Tree_node f)) -> P0 Forest_nil ->
  (forall t f, P t -> P0 f -> P0 (Forest_cons t f)) -> forall t, P t).
Check Even_indl.
Fail Check Even_recl.
Check (pt2 : PT_inst1 True).
Check PF_inst1_recl.
