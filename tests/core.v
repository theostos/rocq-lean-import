From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".

(* This prefix includes the nested Syntax.below/brecOn declarations and the
   modern UInt32 constructor. They are no longer expected failures. *)
Redirect "core1.log" Lean Import "../dumps/core" 1 19152.

(* UInt32.ofNatLT requires converting the BitVec bound to UInt32.size.
   Stock unary conversion still exceeds the budget; compact arithmetic is
   tested separately on the experimental branch. *)
Redirect "core2.log" Fail Timeout 1
  Lean Import "../dumps/core" 19152 19153.
Fail Check UInt32_ofNatLT.
