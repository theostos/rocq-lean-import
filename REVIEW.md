# Align the foundation with modern UInt32 and character computations

Base: `review/compact-kernel-integration`. Compare against this base, not upstream.

Extend the already integrated UInt32/Char layout with their toNat/validity predeclarations and update the foundation character computations and stdlib imports. This is the later foundation delta, not a replacement for pr/uint32-modern-dump or pr/string-of-list. The imported core fixture exercises Char.ofNatAux and its dependent proof. Requires the compact arithmetic branch below it.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
