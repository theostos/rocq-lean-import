namespace RecordValuedDefinitionEta

def spin : Nat -> Nat × Nat
  | 0 => (1, 2)
  | fuel + 1 => spin fuel

def hugeFuel := 10000000

def expensive : Nat × Nat := spin hugeFuel

end RecordValuedDefinitionEta
