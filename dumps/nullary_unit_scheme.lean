universe u v

inductive Token (α : Type u) : Type u where
  | mk : Token α

def choose {α : Type u} (x : Token α) : Nat :=
  match x with | .mk => 37

theorem choose_eq {α : Type u} (x : Token α) : choose x = 37 := rfl

def chooseDep {α : Type u} (P : Token α → Sort v)
    (h : P .mk) (x : Token α) : P x :=
  match x with | .mk => h

theorem chooseDep_eq {α : Type u} (P : Token α → Sort v)
    (h : P .mk) (x : Token α) : chooseDep P h x = h := rfl

def unitMatch (x : Unit) : Nat := match x with | () => 37
theorem unitMatch_eq (x : Unit) : unitMatch x = 37 := rfl

-- The selection must not erase relevant fields or multiple constructors.
inductive Box where | mk : Nat → Box
def unbox (b : Box) : Nat := match b with | .mk n => n
theorem unbox_eq (n : Nat) : unbox (.mk n) = n := rfl

inductive Bit where | off | on
def bitValue (b : Bit) : Nat := match b with | .off => 0 | .on => 1
theorem bitValue_off : bitValue .off = 0 := rfl
theorem bitValue_on : bitValue .on = 1 := rfl

inductive Indexed : Nat → Type where | mk : Indexed 0
def indexedValue (n : Nat) (x : Indexed n) : Nat := match x with | .mk => 0
theorem indexedValue_eq : indexedValue 0 .mk = 0 := rfl
