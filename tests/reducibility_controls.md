# Reducibility and strict-import controls

`reducibility_controls.v` checks transparent legacy/abbreviation/regular/opaque-hint
definitions, genuine opacity, and rejection of ill-typed bodies under the default
error mode. The two-constructor type avoids unit-eta obscuring the opacity check.

Compile `reducibility_controls_reload.v` in a second Rocq process, using the test
project's `-R . Test` mapping. It checks opacity again and continues importing from
the parser state restored by `Require Import`.

Both files print the oracle entries for manual inspection:

```text
ControlsPlain : transparent
ControlsAbbrev : expand
ControlsRegular : level -7
ControlsHintOpaque : level 1
```

The reduction tests do not assert the exact strategy levels; compare these lines
in both logs when reviewing serialization. The five-second per-line limit bounds
the fixtures, but is not a regression test for timeout delivery or stopped-import
summary messages. The fixture is hand-written, has 26 lines and contains three
deliberately ill-typed declarations; it is not a valid Lean library export.
