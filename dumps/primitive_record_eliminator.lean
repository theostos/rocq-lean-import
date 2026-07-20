namespace NoImportListPairSimpleTimeoutShort

abbrev Data := List Nat

opaque Good : Data → Data → Prop

def expensiveSplit : Nat → Data → Data → Data × Data
  | 0, left, right => (left, right)
  | _ + 1, [], right => ([], right)
  | fuel + 1, _ :: left, right => expensiveSplit fuel left right

def largeFuel := 10000000

def transform (left right : Data) : Data × Data :=
  expensiveSplit largeFuel left right

structure Box where
  left : Data
  right : Data

abbrev Box.good (box : Box) : Prop :=
  Good box.left box.right

def wrap (box : Box) : Box :=
  let (left, right) := transform box.left box.right
  { left, right }

axiom transform_preserves_good (left right : Data) :
  Good (transform left right).fst (transform left right).snd = Good left right

theorem explicit (left right : Data) :
    Good (transform left right).fst (transform left right).snd = Good left right := by
  exact transform_preserves_good left right

theorem repro (left right : Data) :
    (wrap { left, right }).good = Box.good { left, right } := by
  simp [Box.good, wrap]
  exact Iff.of_eq (transform_preserves_good left right)

end NoImportListPairSimpleTimeoutShort
