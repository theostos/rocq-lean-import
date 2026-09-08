From LeanImport Require Import Lean.

Set Lean Line Timeout 5.

(* Import a two-constructor type and four reducibility hints plus an opaque body. *)
Lean Import "../dumps/reducibility_controls" 1 23.

Definition controls_plain_reduces : Lean.eq ControlsPlain ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.
Definition controls_abbrev_reduces : Lean.eq ControlsAbbrev ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.
Definition controls_regular_reduces : Lean.eq ControlsRegular ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.
Definition controls_hint_reduces : Lean.eq ControlsHintOpaque ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.

(* An opaque hint is reducible; a genuinely opaque declaration is not. *)
Check ControlsOpaque : ControlsBit.
Fail Definition controls_opaque_reduces : Lean.eq ControlsOpaque ControlsBit_zero :=
  Lean.eq_refl ControlsBit_zero.

(* Each invalid body is a sort where ControlsBit is expected. Leave the error
   mode at its default: silently stopping would make these Fail commands fail. *)
Fail Lean Import "../dumps/reducibility_controls" 23 24.
Fail Lean Import "../dumps/reducibility_controls" 24 25.
Fail Lean Import "../dumps/reducibility_controls" 25 26.
Fail Check ControlsBadPlain.
Fail Check ControlsBadHint.
Fail Check ControlsBadOpaque.

(* Inspect these four oracle entries again after loading the compiled file. *)
Print Strategy ControlsPlain.
Print Strategy ControlsAbbrev.
Print Strategy ControlsRegular.
Print Strategy ControlsHintOpaque.
