From Test Require Import reducibility_controls.
From LeanImport Require Import Lean.

(* Loading the .vo must preserve both transparent and opaque definitions. *)
Definition controls_reloaded_hint_reduces : Lean.eq ControlsHintOpaque ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.
Fail Definition controls_reloaded_opaque_reduces : Lean.eq ControlsOpaque ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.

(* This line uses names and expressions held by the saved importer state. *)
Lean Import "../dumps/reducibility_controls" 26 27.
Definition controls_replayed_state : Lean.eq ControlsReplay ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.

Print Strategy ControlsPlain.
Print Strategy ControlsAbbrev.
Print Strategy ControlsRegular.
Print Strategy ControlsHintOpaque.
