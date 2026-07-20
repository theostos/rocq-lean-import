import Init.Prelude

def huge : Nat := 18446744073709551616

def castBound (n : Nat) (h : n < huge) : n < 2 ^ 64 := h
