def subtypeSPropProperty (A : Prop) (p : A → Prop) (s : Subtype p) :
    p s.val := s.property
