set_option autoImplicit false
noncomputable def plus (a b : Nat) : Nat := @Nat.rec (fun _ => Nat) a (fun _ ih => Nat.succ ih) b
inductive LTree : Type
  | node : List LTree → LTree
noncomputable def LTree.size : LTree → Nat :=
  @LTree.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
noncomputable def LTree.sizes : List LTree → Nat :=
  @LTree.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
theorem LTree.size_node (ts : List LTree) : Eq (LTree.size (LTree.node ts)) (Nat.succ (LTree.sizes ts)) := rfl
def LTree.two : LTree := LTree.node (List.cons (LTree.node List.nil) List.nil)
theorem LTree.size_two : Eq LTree.two.size (Nat.succ (Nat.succ Nat.zero)) := rfl
inductive ATree : Type
  | node : Array ATree → ATree
noncomputable def ATree.size : ATree → Nat :=
  @ATree.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) (fun _ ih => ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
noncomputable def ATree.sizes : List ATree → Nat :=
  @ATree.rec_2 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) (fun _ ih => ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
theorem ATree.size_node (ts : List ATree) : Eq (ATree.size (ATree.node (Array.mk ts))) (Nat.succ (ATree.sizes ts)) := rfl
inductive OTree : Type
  | node : Option OTree → OTree
noncomputable def OTree.size : OTree → Nat :=
  @OTree.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) Nat.zero (fun _ ih => ih)
theorem OTree.size_some (t : OTree) : Eq (OTree.size (OTree.node (Option.some t))) (Nat.succ (OTree.size t)) := rfl
inductive PTree : Type
  | leaf : PTree
  | node : Prod Nat PTree → PTree
noncomputable def PTree.size : PTree → Nat :=
  @PTree.rec (fun _ => Nat) (fun _ => Nat) Nat.zero (fun _ ih => Nat.succ ih) (fun n _ ih => plus n ih)
theorem PTree.size_node (n : Nat) (t : PTree) : Eq (PTree.size (PTree.node (Prod.mk n t))) (Nat.succ (plus n (PTree.size t))) := rfl
structure Wrap (α : Type) where
  n : Nat
  val : α
inductive WTree : Type
  | node : Wrap WTree → WTree
noncomputable def WTree.size : WTree → Nat :=
  @WTree.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) (fun n _ ih => plus n ih)
theorem WTree.size_node (n : Nat) (t : WTree) : Eq (WTree.size (WTree.node (Wrap.mk n t))) (Nat.succ (plus n (WTree.size t))) := rfl
mutual
inductive MA : Type
  | node : List MB → MA
inductive MB : Type
  | leaf : MB
  | node : MA → MB
end
noncomputable def MA.size : MA → Nat :=
  @MA.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) Nat.zero (fun _ ih => Nat.succ ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
noncomputable def MB.sizes : List MB → Nat :=
  @MA.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => Nat.succ ih) Nat.zero (fun _ ih => Nat.succ ih) Nat.zero (fun _ _ ih1 ih2 => plus ih1 ih2)
theorem MA.size_node (ts : List MB) : Eq (MA.size (MA.node ts)) (Nat.succ (MB.sizes ts)) := rfl
mutual
inductive TA : Nat → Type
  | leaf : TA Nat.zero
  | node : ∀ n, TB n → TA (Nat.succ n)
inductive TB : Nat → Type
  | wrap : ∀ n, TA n → TB n
end
noncomputable def TA.count (n : Nat) : TA n → Nat :=
  @TA.rec (fun _ _ => Nat) (fun _ _ => Nat) Nat.zero (fun _ _ ih => Nat.succ ih) (fun _ _ ih => ih) n
theorem TA.count_node (n : Nat) (t : TA n) : Eq (TA.count (Nat.succ n) (TA.node n (TB.wrap n t))) (Nat.succ (TA.count n t)) := rfl
