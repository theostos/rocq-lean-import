From LeanImport Require Import Lean.

(* Checking record eta must expose the imported definition's constructor
   without evaluating its ten-million-step original body. *)
Lean Import "../dumps/record_valued_definition_eta".

Timeout 5 Definition record_eta_check :
  @eq (Prod_inst3 Nat Nat) RecordValuedDefinitionEta_expensive
    (Prod_mk_inst3 Nat Nat
       (fst1 Nat Nat RecordValuedDefinitionEta_expensive)
       (snd1 Nat Nat RecordValuedDefinitionEta_expensive)) :=
  @eq_refl (Prod_inst3 Nat Nat) RecordValuedDefinitionEta_expensive.
