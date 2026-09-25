import Lean
set_option autoImplicit false
open Lean Meta Elab Command in
elab "#eta " ids:ident* : command => liftTermElabM do
  for id in ids do
    let n := id.getId
    let ci ← getConstInfo n
    let v ← forallTelescope ci.type fun xs _ =>
      mkLambdaFVars xs (mkAppN (.const n (ci.levelParams.map Level.param)) xs)
    let e : Name := Name.mkStr n "eta"
    let d : DefinitionVal :=
      { name := e, levelParams := ci.levelParams, type := ci.type, value := v,
        hints := .abbrev, safety := .safe, all := [e] }
    addDecl (.defnDecl d)
noncomputable def plus (a b : Nat) : Nat := @Nat.rec (fun _ => Nat) a (fun _ ih => Nat.succ ih) b
-- a container nested through itself (Array), and a two-constructor wrapper
inductive Tagged (α : Type) : Type
  | text : Nat → Tagged α
  | append : Array (Tagged α) → Tagged α
  | tag : α → Tagged α → Tagged α
inductive SOrL (α β : Type) : Type
  | strict : α → SOrL α β
  | lazy : β → SOrL α β
inductive Embed : Type
  | expr : Tagged Nat → Embed
  | trace : Nat → Tagged Embed → SOrL (Array (Tagged Embed)) Nat → Embed
#eta Embed.rec Embed.rec_1 Embed.rec_2 Embed.rec_3 Embed.rec_4
noncomputable def Embed.count : Embed → Nat :=
  @Embed.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat.zero) (fun _ _ _ ih1 ih2 => Nat.succ (plus ih1 ih2))
    (fun _ => Nat.zero) (fun _ ih => ih) (fun _ _ ih1 ih2 => plus ih1 ih2)
    (fun _ ih => ih) (fun _ => Nat.zero)
    (fun _ ih => ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
noncomputable def Embed.countT : Tagged Embed → Nat :=
  @Embed.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat.zero) (fun _ _ _ ih1 ih2 => Nat.succ (plus ih1 ih2))
    (fun _ => Nat.zero) (fun _ ih => ih) (fun _ _ ih1 ih2 => plus ih1 ih2)
    (fun _ ih => ih) (fun _ => Nat.zero)
    (fun _ ih => ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
theorem Embed.count_trace (t : Tagged Embed) :
    Eq (Embed.count (Embed.trace Nat.zero t (SOrL.lazy Nat.zero)))
      (Nat.succ (plus (Embed.countT t) Nat.zero)) := rfl
-- containers nested in containers
inductive LPTree : Type
  | node : List (Prod Nat LPTree) → LPTree
#eta LPTree.rec LPTree.rec_1 LPTree.rec_2
-- a directly recursive user container, under the self-nested one
inductive MyList (α : Type) : Type
  | nil : MyList α
  | cons : α → MyList α → MyList α
inductive MTree : Type
  | node : MyList (Tagged MTree) → MTree
  | leaf : Tagged (MyList MTree) → MTree
#eta MTree.rec MTree.rec_1 MTree.rec_2 MTree.rec_3 MTree.rec_4 MTree.rec_5 MTree.rec_6 MTree.rec_7
-- a record with several parameters, nested in its last and first fields
structure Two (α β : Type) where
  a : α
  b : β
inductive TwoTree : Type
  | node : Two Nat TwoTree → TwoTree
  | list : List (Two Nat TwoTree) → TwoTree
#eta TwoTree.rec TwoTree.rec_1 TwoTree.rec_2
-- mutual and nested through the self-nested container
mutual
inductive NA : Type
  | node : Tagged NB → NA
inductive NB : Type
  | leaf : NB
  | node : List NA → NB
end
#eta NA.rec NA.rec_1 NA.rec_2 NA.rec_3 NA.rec_4 NB.rec
