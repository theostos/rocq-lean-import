set_option autoImplicit false
structure Proofy : Type where
  h : True
theorem Proofy.eta (a : Proofy) : Eq a (Proofy.mk a.h) := rfl
inductive U : Type
  | u : U
noncomputable def U.elim (x : U) : Nat := @U.rec (fun _ => Nat) Nat.zero x
theorem U.elim_any (x : U) : Eq (U.elim x) Nat.zero := rfl
