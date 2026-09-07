# Register unit-like inductives and simplify their nullary schemes

Base: `review/reducibility-hints`. Compare against this base, not upstream.

Register eligible unit-like types, including types restored from a checkpoint. For a nullary constructor, check the branch-only eliminator against the generated dependent scheme type. This fixes Cslib.Automata.NA.FinAcc.instTotalSumUnitFinLoopOfNonemptyElemStart. Constructors with fields and indexed types retain ordinary schemes. Requires the experimental kernel unit-eta rule.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
