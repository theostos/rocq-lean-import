set_option autoImplicit false
structure Pair (α β : Type) where
  fst : α
  snd : β
def Pair.swap {α β : Type} (p : Pair α β) : Pair β α := Pair.mk p.snd p.fst
noncomputable def Pair.first {α β : Type} (p : Pair α β) : α := @Pair.fst α β p
theorem Pair.first_mk (a b : Nat) : Eq (Pair.first (Pair.mk a b)) a := rfl
noncomputable def Pair.elim {α β : Type} (p : Pair α β) : α := @Pair.rec α β (fun _ => α) (fun a _ => a) p
theorem Pair.elim_fst (p : Pair Nat Nat) : Eq (Pair.elim p) (Pair.first p) := rfl
@[reducible] def Pair.diag (n : Nat) : Pair Nat Nat := Pair.mk n n
theorem Pair.diag_fst (n : Nat) : Eq (Pair.diag n).fst n := rfl
