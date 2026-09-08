namespace PrimitiveRecordEliminator

abbrev Poly := List Nat

opaque P : Poly → Poly → Prop

def f : Nat → Poly → Poly → Poly × Poly
  | 0, xs, ys => (xs, ys)
  | _ + 1, [], ys => ([], ys)
  | fuel + 1, _ :: xs, ys => f fuel xs ys

def big := 10000000

def g (xs ys : Poly) : Poly × Poly :=
  f big xs ys

structure Box where
  xs : Poly
  ys : Poly

abbrev Box.ok (b : Box) : Prop :=
  P b.xs b.ys

def wrap (b : Box) : Box :=
  let (xs, ys) := g b.xs b.ys
  { xs, ys }

axiom g_ok (xs ys : Poly) :
  P (g xs ys).fst (g xs ys).snd = P xs ys

theorem explicit (xs ys : Poly) :
    P (g xs ys).fst (g xs ys).snd = P xs ys := by
  exact g_ok xs ys

theorem repro (xs ys : Poly) :
    (wrap { xs, ys }).ok = Box.ok { xs, ys } := by
  simp [Box.ok, wrap]
  exact Iff.of_eq (g_ok xs ys)

end PrimitiveRecordEliminator
