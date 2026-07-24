From Stdlib Require ZArith NArith Lia ZifyBool Uint63.
Declare ML Module "coq-lean-import.plugin".

Set Universe Polymorphism.
Set Printing Universes.
Set Primitive Projections.

Declare Scope lean_scope.
Global Open Scope lean_scope.

Global Set Definitional UIP.

Cumulative
Inductive eq@{u|} {α:Type@{u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
Notation "x = y" := (eq x y) : lean_scope.

Register eq as lean.Eq.

Inductive eq_inst1@{|} {α:SProp} (a:α) : α -> SProp
  := eq_refl_inst1 : eq_inst1 a a.

Register eq_inst1 as lean.Eq_inst1.

Inductive Bool := Bool_false | Bool_true.

Register Bool as lean.Bool.

(* Inductive List@{u Lean.u+1.0} (α : Type@{Lean.u+1.0}) : Type@{Lean.u+1.0} :=
    List_nil : List@{u Lean.u+1.0} α
  | List_cons : α -> List@{u Lean.u+1.0} α -> List@{u Lean.u+1.0} α. *)

Monomorphic Universe set.
Inductive List_inst1@{} (α : Type@{set}) : Type@{set} :=
| List_nil_inst1 : List_inst1 α
| List_cons_inst1 : α -> List_inst1 α -> List_inst1 α.

Register List_inst1 as lean.List_inst1.

Module Quot.

  Private Inductive quot@{u|} {α : Type@{u}} (r : α -> α -> SProp) : Type@{u}
    := mk (a:α).

  Register quot as lean.Quot.
  Register mk as lean.Quot.mk.

  Definition lift@{u v|} {α : Type@{u}} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift as lean.Quot.lift.

  Definition lift_inst2@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift_inst2 as lean.Quot.lift_inst2.

  Definition ind@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : quot r -> SProp}
    : (forall a : α, β (mk r a)) -> forall q : quot r, β q
    := fun f q => match q with mk _ x => f x end.

  Register ind as lean.Quot.ind.

  (* Because quot_inst1 is SProp we don't need to make it Private: the
     axiom declared by lean about it is a tautology. *)
  Inductive quot_inst1@{|} {α : SProp} (r : α -> α -> SProp) : SProp
    := mk_inst1 (a:α).

  Register quot_inst1 as lean.Quot_inst1.
  Register mk_inst1 as lean.Quot.mk_inst1.

  (* This non-uniform translation avoids breaking SR ;) *)
  Definition lift_inst1@{v|} {α : SProp} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst1 as lean.Quot.lift_inst1.

  Definition lift_inst3@{|} {α : SProp} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst3 as lean.Quot.lift_inst3.

  Definition ind_inst1@{|} {α : SProp} {r:α -> α -> SProp} {β : quot_inst1 r -> SProp}
    : (forall a : α, β (mk_inst1 r a)) -> forall q : quot_inst1 r, β q
    := fun f q => match q with mk_inst1 _ x => f x end.

  Register ind_inst1 as lean.Quot.ind_inst1.

End Quot.

Inductive Nat := Nat_zero : Nat | Nat_succ : Nat -> Nat.

Register Nat as lean.Nat.

Fixpoint double (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => Nat_succ (Nat_succ (double n))
  end.

Register double as lean.Nat_double.

Declare Scope Nat_scope.
Delimit Scope Nat_scope with Nat.
Open Scope Nat_scope.
Bind Scope Nat_scope with Nat.

Inductive Nat_le@{} (n : Nat) : Nat -> SProp :=
| Nat_le_refl : Nat_le n n
| Nat_le_step : forall m : Nat, Nat_le n m -> Nat_le n (Nat_succ m).

Register Nat_le as lean.Nat_le.

Notation "n <= m" := (Nat_le n m) : Nat_scope.
Notation "n < m" := (Nat_le (Nat_succ n) m) (only parsing) : Nat_scope.
(*
Definition Nat_pred (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => n
  end. *)

Variant Or@{} (a a0 : SProp) : SProp :=
| Or_inl : a -> Or a a0
| Or_inr : a0 -> Or a a0.
Register Or as lean.Or.
Record And@{} (a a0 : SProp) : SProp := And_intro
  { left : a;  right : a0 }.
Register And as lean.And.

Inductive sEmpty : SProp := .
Register sEmpty as lean.False.

Inductive Decidable (p : SProp) : Type :=
| Decidable_isFalse : (p -> sEmpty) -> Decidable p
| Decidable_isTrue : p -> Decidable p.
Register Decidable as lean.Decidable.

Section nat_notation.
  Import ZifyClasses ZArith NArith.
  Fixpoint nat_of_Nat (n : Nat) : nat :=
    match n with
    | Nat_zero => 0
    | Nat_succ n => S (nat_of_Nat n)
    end%nat.
  Fixpoint Nat_of_nat (n : nat) : Nat :=
    match n with
    | O => Nat_zero
    | S n => Nat_succ (Nat_of_nat n)
    end.

  Definition Nat_of_N (n : N) : Nat := Nat_of_nat (N.to_nat n).
  Definition N_of_Nat (n : Nat) : N := N.of_nat (nat_of_Nat n).
  Definition Nat_of_num_uint n : Nat := Nat_of_N (N.of_num_uint n).
  Definition Nat_to_num_uint (n : Nat) := N.to_num_uint (N_of_Nat n).

  Lemma nat2Natid (n : nat) : nat_of_Nat (Nat_of_nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.
  Lemma Nat2natid (n : Nat) : Nat_of_nat (nat_of_Nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.

  #[global]
  Monomorphic Instance Inj_Nat_Z : InjTyp Nat Z :=
    mkinj _ _ (fun n => Z.of_nat (nat_of_Nat n)) (fun x =>  0 <= x )%Z (fun n => Nat2Z.is_nonneg _).

  Lemma nat_le_Nat_le' (n m : nat) : (n <= m)%nat -> (Nat_of_nat n <= Nat_of_nat m)%Nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma nat_le_Nat_le (n m : Nat) : (nat_of_Nat n <= nat_of_Nat m)%nat -> (n <= m)%Nat.
  Proof.
    intro H; apply nat_le_Nat_le' in H.
    rewrite !Nat2natid in H; assumption.
  Qed.

  Definition Nat_le_ind (n : Nat) (P : forall m, n <= m -> Prop)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Qed.

  Register Scheme Nat_le_ind as ind_dep for Nat_le.

  Definition Nat_le_rect (n : Nat) (P : forall m, n <= m -> Type)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Defined.

  Register Scheme Nat_le_rect as rect_dep for Nat_le.

  Lemma Nat_le_nat_le' (n m : Nat) : (n <= m)%Nat -> (nat_of_Nat n <= nat_of_Nat m)%nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma Nat_le_nat_le (n m : nat) : (Nat_of_nat n <= Nat_of_nat m)%Nat -> (n <= m)%nat.
  Proof.
    intro H; apply Nat_le_nat_le' in H.
    rewrite !nat2Natid in H; assumption.
  Qed.
End nat_notation.
Add Zify InjTyp Inj_Nat_Z.

Number Notation Nat Nat_of_num_uint Nat_to_num_uint (abstract after 5000) : Nat_scope.
(* Tell the kernel to unfold these wrappers early, to speed things up *)
#[global] Strategy -10000 [Nat_of_num_uint Nat_to_num_uint].

Fixpoint Nat_add n m :=
  match m with
  | 0 => n
  | Nat_succ p => Nat_succ (Nat_add n p)
  end.

Fixpoint Nat_mul n m :=
  match m with
  | 0 => 0
  | Nat_succ p => Nat_add (Nat_mul n p) n
  end.

Fixpoint Nat_pow n m :=
  match m with
    | 0 => 1
    | Nat_succ m => Nat_mul (Nat_pow n m) n
  end.

Definition Nat_pred n :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => n
  end.

Fixpoint Nat_sub n m :=
  match m with
  | Nat_zero => n
  | Nat_succ m => Nat_pred (Nat_sub n m)
  end.

Fixpoint Nat_beq n m :=
  match n, m with
  | Nat_zero, Nat_zero => Bool_true
  | Nat_succ n, Nat_succ m => Nat_beq n m
  | _, _ => Bool_false
  end.

Fixpoint Nat_ble n m :=
  match n, m with
  | Nat_zero, _ => Bool_true
  | Nat_succ _, Nat_zero => Bool_false
  | Nat_succ n, Nat_succ m => Nat_ble n m
  end.

Definition Nat_blt n m := Nat_ble (Nat_succ n) m.

Lemma Nat_beq_refl (n : Nat) : Logic.eq (Nat_beq n n) Bool_true.
Proof.
  induction n as [|n IH]; cbn [Nat_beq]; assumption || reflexivity.
Qed.

Lemma Nat_beq_true_eq (n m : Nat) :
  Logic.eq (Nat_beq n m) Bool_true -> eq n m.
Proof.
  revert m.
  induction n as [|n IH]; intros [|m] H; cbn [Nat_beq] in H.
  - exact (eq_refl Nat_zero).
  - discriminate H.
  - discriminate H.
  - destruct (IH m H). constructor.
Qed.

Lemma Nat_beq_false_ne (n m : Nat) :
  Logic.eq (Nat_beq n m) Bool_false -> eq n m -> sEmpty.
Proof.
  intros H E.
  destruct E.
  rewrite Nat_beq_refl in H.
  discriminate H.
Qed.

Definition Nat_decEq (n m : Nat) : Decidable (eq n m).
Proof.
  destruct (Nat_beq n m) eqn:H.
  - exact (Decidable_isFalse _ (Nat_beq_false_ne n m H)).
  - exact (Decidable_isTrue _ (Nat_beq_true_eq n m H)).
Defined.

Register Nat_add as lean.Nat_add.
Register Nat_mul as lean.Nat_mul.
Register Nat_pow as lean.Nat_pow.
Register Nat_pred as lean.Nat_pred.
Register Nat_sub as lean.Nat_sub.
Register Nat_beq as lean.Nat_beq.
Register Nat_ble as lean.Nat_ble.
Register Nat_blt as lean.Nat_blt.
Register Nat_decEq as lean.Nat_decEq.

Import NArith.

(** A proof-producing bridge for closed arithmetic.

    The importer evaluates closed [Nat] expressions with Zarith, but the
    result is never trusted by the Rocq kernel.  Instead it builds a value of
    [NatCertificate x n], using the lemmas below for each operation it
    evaluates.  Two expressions reflected to the same binary [N] can then be
    related by [NatCertificate_equal], and [Nat_transport_sprop] moves a proof
    across that checked equality. *)
Definition NatCertificate (x : Nat) (n : N) : Prop :=
  Logic.eq (N_of_Nat x) n.

Lemma nat_of_Nat_add_logic (a b : Nat) :
  Logic.eq (nat_of_Nat (Nat_add a b))
    (nat_of_Nat a + nat_of_Nat b)%nat.
Proof.
  induction b as [|b IH].
  - cbn [Nat_add nat_of_Nat]. now rewrite PeanoNat.Nat.add_0_r.
  - cbn [Nat_add nat_of_Nat].
    now rewrite IH, PeanoNat.Nat.add_succ_r.
Qed.

Lemma nat_of_Nat_mul_logic (a b : Nat) :
  Logic.eq (nat_of_Nat (Nat_mul a b))
    (nat_of_Nat a * nat_of_Nat b)%nat.
Proof.
  induction b as [|b IH].
  - cbn [Nat_mul nat_of_Nat]. now rewrite PeanoNat.Nat.mul_0_r.
  - cbn [Nat_mul nat_of_Nat].
    rewrite nat_of_Nat_add_logic, IH, PeanoNat.Nat.mul_succ_r.
    reflexivity.
Qed.

Lemma nat_of_Nat_pow_logic (a b : Nat) :
  Logic.eq (nat_of_Nat (Nat_pow a b))
    (PeanoNat.Nat.pow (nat_of_Nat a) (nat_of_Nat b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - cbn [Nat_pow nat_of_Nat].
    rewrite nat_of_Nat_mul_logic, IH, PeanoNat.Nat.pow_succ_r.
    apply PeanoNat.Nat.mul_comm.
    apply PeanoNat.Nat.le_0_l.
Qed.

Lemma nat_of_Nat_pred_logic (a : Nat) :
  Logic.eq (nat_of_Nat (Nat_pred a)) (PeanoNat.Nat.pred (nat_of_Nat a)).
Proof. destruct a; reflexivity. Qed.

Lemma nat_of_Nat_sub_logic (a b : Nat) :
  Logic.eq (nat_of_Nat (Nat_sub a b))
    (nat_of_Nat a - nat_of_Nat b)%nat.
Proof.
  induction b as [|b IH].
  - now rewrite PeanoNat.Nat.sub_0_r.
  - cbn [Nat_sub nat_of_Nat].
    rewrite nat_of_Nat_pred_logic, IH.
    symmetry; apply PeanoNat.Nat.sub_succ_r.
Qed.

Lemma N_of_Nat_add_logic (a b : Nat) :
  Logic.eq (N_of_Nat (Nat_add a b))
    (N_of_Nat a + N_of_Nat b)%N.
Proof.
  unfold N_of_Nat.
  rewrite nat_of_Nat_add_logic, Nat2N.inj_add.
  reflexivity.
Qed.

Lemma N_of_Nat_mul_logic (a b : Nat) :
  Logic.eq (N_of_Nat (Nat_mul a b))
    (N_of_Nat a * N_of_Nat b)%N.
Proof.
  unfold N_of_Nat.
  rewrite nat_of_Nat_mul_logic, Nat2N.inj_mul.
  reflexivity.
Qed.

Lemma N_of_Nat_pow_logic (a b : Nat) :
  Logic.eq (N_of_Nat (Nat_pow a b))
    (N_of_Nat a ^ N_of_Nat b)%N.
Proof.
  unfold N_of_Nat.
  rewrite nat_of_Nat_pow_logic, Nat2N.inj_pow.
  reflexivity.
Qed.

Lemma N_of_Nat_sub_logic (a b : Nat) :
  Logic.eq (N_of_Nat (Nat_sub a b))
    (N_of_Nat a - N_of_Nat b)%N.
Proof.
  unfold N_of_Nat.
  rewrite nat_of_Nat_sub_logic, Nat2N.inj_sub.
  reflexivity.
Qed.

Lemma NatCertificate_zero : NatCertificate Nat_zero 0%N.
Proof. reflexivity. Qed.

Lemma nat2Natid_logic (n : nat) :
  Logic.eq (nat_of_Nat (Nat_of_nat n)) n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma NatCertificate_of_N (n : N) :
  NatCertificate (Nat_of_N n) n.
Proof.
  unfold NatCertificate, N_of_Nat, Nat_of_N.
  rewrite nat2Natid_logic, N2Nat.id.
  reflexivity.
Qed.

(** Fused binary decoding exposes only the constructors demanded by the
    consumer.  In contrast, [Nat_of_nat (N.to_nat n)] first allocates the
    complete unary intermediate before Lean's [Nat] can be inspected. *)
Fixpoint CompactPos (p : positive) : Nat :=
  match p with
  | xH => Nat_succ Nat_zero
  | xO p => double (CompactPos p)
  | xI p => Nat_succ (double (CompactPos p))
  end.

Definition CompactNat (n : N) : Nat :=
  match n with
  | N0 => Nat_zero
  | Npos p => CompactPos p
  end.

Lemma NatCertificate_succ (x : Nat) (n : N) :
  NatCertificate x n -> NatCertificate (Nat_succ x) (N.succ n).
Proof.
  unfold NatCertificate, N_of_Nat.
  cbn [nat_of_Nat].
  intro H.
  now rewrite Nat2N.inj_succ, H.
Qed.

Import Lia.

Lemma nat_of_Nat_double_logic (x : Nat) :
  Logic.eq (nat_of_Nat (double x)) (2 * nat_of_Nat x)%nat.
Proof.
  induction x as [|x IH]; cbn [double nat_of_Nat].
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma NatCertificate_double (x : Nat) (n : N) :
  NatCertificate x n -> NatCertificate (double x) (2 * n)%N.
Proof.
  unfold NatCertificate, N_of_Nat.
  intro H.
  rewrite nat_of_Nat_double_logic, Nat2N.inj_mul, H.
  reflexivity.
Qed.

Lemma NatCertificate_CompactPos (p : positive) :
  NatCertificate (CompactPos p) (Npos p).
Proof.
  induction p as [p IH|p IH|]; cbn [CompactPos].
  - change
      (NatCertificate (Nat_succ (double (CompactPos p)))
         (N.succ (2 * Npos p)%N)).
    apply NatCertificate_succ.
    exact (NatCertificate_double _ _ IH).
  - change
      (NatCertificate (double (CompactPos p)) (2 * Npos p)%N).
    exact (NatCertificate_double _ _ IH).
  - unfold NatCertificate, N_of_Nat. reflexivity.
Qed.

Lemma NatCertificate_CompactNat (n : N) :
  NatCertificate (CompactNat n) n.
Proof.
  destruct n as [|p]; cbn [CompactNat].
  - exact NatCertificate_zero.
  - exact (NatCertificate_CompactPos p).
Qed.

(** [CompactNat] is kept transparent so weak-head reduction can reveal one
    constructor at a time without first materializing the complete unary
    normal form. *)

Lemma NatCertificate_add (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  NatCertificate (Nat_add a b) (na + nb)%N.
Proof.
  unfold NatCertificate.
  intros Ha Hb.
  rewrite N_of_Nat_add_logic, Ha, Hb.
  reflexivity.
Qed.

Lemma NatCertificate_mul (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  NatCertificate (Nat_mul a b) (na * nb)%N.
Proof.
  unfold NatCertificate.
  intros Ha Hb.
  rewrite N_of_Nat_mul_logic, Ha, Hb.
  reflexivity.
Qed.

Lemma NatCertificate_pow (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  NatCertificate (Nat_pow a b) (na ^ nb)%N.
Proof.
  unfold NatCertificate.
  intros Ha Hb.
  rewrite N_of_Nat_pow_logic, Ha, Hb.
  reflexivity.
Qed.

Lemma NatCertificate_sub (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  NatCertificate (Nat_sub a b) (na - nb)%N.
Proof.
  unfold NatCertificate.
  intros Ha Hb.
  rewrite N_of_Nat_sub_logic, Ha, Hb.
  reflexivity.
Qed.

Lemma Nat2natid_logic (n : Nat) :
  Logic.eq (Nat_of_nat (nat_of_Nat n)) n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma Nat_of_N_N_of_Nat_logic (n : Nat) :
  Logic.eq (Nat_of_N (N_of_Nat n)) n.
Proof.
  cbv [Nat_of_N N_of_Nat].
  rewrite Nat2N.id.
  apply Nat2natid_logic.
Qed.

Lemma NatCertificate_equal (a b : Nat) (n : N) :
  NatCertificate a n -> NatCertificate b n -> eq a b.
Proof.
  unfold NatCertificate.
  intros Ha Hb.
  assert (Logic.eq a b) as Hab.
  { apply (f_equal Nat_of_N) in Ha.
    apply (f_equal Nat_of_N) in Hb.
    rewrite !Nat_of_N_N_of_Nat_logic in Ha, Hb.
    exact (Logic.eq_trans Ha (Logic.eq_sym Hb)). }
  destruct Hab.
  constructor.
Qed.

(** A checked bridge from Lean's [Bool] to Rocq's [bool].  Like
    [NatCertificate], it lets the importer evaluate compact host values while
    requiring a Rocq proof for every result. *)
Definition bool_of_Bool (b : Bool) : bool :=
  match b with
  | Bool_false => false
  | Bool_true => true
  end.

Definition Bool_of_bool (b : bool) : Bool :=
  if b then Bool_true else Bool_false.

Definition BoolCertificate (x : Bool) (b : bool) : Prop :=
  Logic.eq (bool_of_Bool x) b.

Lemma Bool_of_bool_bool_of_Bool_logic (b : Bool) :
  Logic.eq (Bool_of_bool (bool_of_Bool b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma BoolCertificate_of_bool (b : bool) :
  BoolCertificate (Bool_of_bool b) b.
Proof. destruct b; reflexivity. Qed.

Lemma BoolCertificate_equal (a b : Bool) (value : bool) :
  BoolCertificate a value -> BoolCertificate b value -> eq a b.
Proof.
  unfold BoolCertificate.
  intros Ha Hb.
  assert (Logic.eq a b) as Hab.
  { apply (f_equal Bool_of_bool) in Ha.
    apply (f_equal Bool_of_bool) in Hb.
    rewrite !Bool_of_bool_bool_of_Bool_logic in Ha, Hb.
    exact (Logic.eq_trans Ha (Logic.eq_sym Hb)). }
  destruct Hab.
  constructor.
Qed.

Lemma bool_of_Nat_beq_logic (a b : Nat) :
  Logic.eq (bool_of_Bool (Nat_beq a b))
    (PeanoNat.Nat.eqb (nat_of_Nat a) (nat_of_Nat b)).
Proof.
  revert b; induction a as [|a IH]; destruct b; cbn; auto.
Qed.

Lemma bool_of_Nat_ble_logic (a b : Nat) :
  Logic.eq (bool_of_Bool (Nat_ble a b))
    (PeanoNat.Nat.leb (nat_of_Nat a) (nat_of_Nat b)).
Proof.
  revert b; induction a as [|a IH]; destruct b; cbn; auto.
Qed.

Lemma bool_of_Nat_blt_logic (a b : Nat) :
  Logic.eq (bool_of_Bool (Nat_blt a b))
    (PeanoNat.Nat.ltb (nat_of_Nat a) (nat_of_Nat b)).
Proof.
  unfold Nat_blt.
  rewrite bool_of_Nat_ble_logic.
  reflexivity.
Qed.

Lemma NatCertificate_beq (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  BoolCertificate (Nat_beq a b) (N.eqb na nb).
Proof.
  unfold NatCertificate, BoolCertificate, N_of_Nat.
  intros Ha Hb.
  rewrite bool_of_Nat_beq_logic.
  rewrite PeanoNat.Nat.eqb_compare, N.eqb_compare, Nat2N.inj_compare, Ha, Hb.
  reflexivity.
Qed.

Lemma NatCertificate_ble (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  BoolCertificate (Nat_ble a b) (N.leb na nb).
Proof.
  unfold NatCertificate, BoolCertificate, N_of_Nat.
  intros Ha Hb.
  rewrite bool_of_Nat_ble_logic.
  rewrite PeanoNat.Nat.leb_compare, N.leb_compare, Nat2N.inj_compare, Ha, Hb.
  reflexivity.
Qed.

Lemma NatCertificate_blt (a b : Nat) (na nb : N) :
  NatCertificate a na -> NatCertificate b nb ->
  BoolCertificate (Nat_blt a b) (N.ltb na nb).
Proof.
  unfold NatCertificate, BoolCertificate, N_of_Nat.
  intros Ha Hb.
  rewrite bool_of_Nat_blt_logic.
  rewrite PeanoNat.Nat.ltb_compare, N.ltb_compare, Nat2N.inj_compare, Ha, Hb.
  reflexivity.
Qed.

Definition Bool_transport_sprop (P : Bool -> SProp)
    (a b : Bool) (e : eq a b) (x : P a) : P b :=
  match e in eq _ b return P b with
  | eq_refl _ => x
  end.

Definition Nat_transport_sprop (P : Nat -> SProp)
    (a b : Nat) (e : eq a b) (x : P a) : P b :=
  match e in eq _ b return P b with
  | eq_refl _ => x
  end.

Register NatCertificate as lean.NatCertificate.
Register NatCertificate_zero as lean.NatCertificate_zero.
Register NatCertificate_of_N as lean.NatCertificate_of_N.eager.
Register NatCertificate_CompactNat as lean.NatCertificate_of_N.
Register NatCertificate_succ as lean.NatCertificate_succ.
Register NatCertificate_add as lean.NatCertificate_add.
Register NatCertificate_mul as lean.NatCertificate_mul.
Register NatCertificate_pow as lean.NatCertificate_pow.
Register NatCertificate_sub as lean.NatCertificate_sub.
Register NatCertificate_equal as lean.NatCertificate_equal.
Register Nat_transport_sprop as lean.Nat_transport_sprop.
Register Bool_of_bool as lean.Bool_of_bool.
Register BoolCertificate as lean.BoolCertificate.
Register BoolCertificate_of_bool as lean.BoolCertificate_of_bool.
Register BoolCertificate_equal as lean.BoolCertificate_equal.
Register NatCertificate_beq as lean.NatCertificate_beq.
Register NatCertificate_ble as lean.NatCertificate_ble.
Register NatCertificate_blt as lean.NatCertificate_blt.
Register Bool_transport_sprop as lean.Bool_transport_sprop.
Register Nat_of_N as lean.Nat_of_N.eager.
Register CompactNat as lean.Nat_of_N.

#[local] Set Warnings "-abstract-large-number".
Definition UInt32_size : Nat := 0x100000000%Nat.
Register UInt32_size as lean.UInt32_size.

Record Fin@{} (n : Nat) := Fin_mk { val : Nat; isLt : (val < n)%Nat }.
Register Fin as lean.Fin.

(* UInt32 used a Fin field before Lean 4.17 and a BitVec field afterwards.
   Keep both kernel-level representations available; the importer selects the
   one matching the constructor type in the dump. *)
Record UInt32_legacy@{} := UInt32_legacy_mk { val0 : Fin UInt32_size }.
Register UInt32_legacy as lean.UInt32.legacy.

Record BitVec@{} (w : Nat) := BitVec_ofFin { toFin : Fin (Nat_pow 2 w) }.
Register BitVec as lean.BitVec.

Record UInt32@{} := UInt32_ofBitVec { toBitVec : BitVec 32 }.
Register UInt32 as lean.UInt32.
Register toBitVec as lean.toBitVec.


Section strings.
  Import ZArith NArith Lia Zify ZifyBool.
  Variant InvalidUInt32 (n : N) : Set := invalid_uint32.
  Variant InvalidChar (n : N) : Set := invalid_char.
  #[local] Set Warnings "-abstract-large-number".

  Lemma Nat_lt_to_N (n : N) (m : N) : (n <? m)%N = true -> Nat_of_N n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite ?nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_l (n : Nat) (m : N) : (N_of_Nat n <? m)%N = true -> n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_r (n : N) (m : Nat) : (n <? N_of_Nat m)%N = true -> Nat_of_N n < m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  (* Section with_or. *)
    (* Context (Or : SProp -> SProp -> SProp)
            (Or_inl : forall P Q, P -> Or P Q)
            (Or_inr : forall P Q, Q -> Or P Q)
            (And : SProp -> SProp -> SProp)
            (And_intro : forall P Q, P -> Q -> And P Q). *)
  #[local] Set Warnings "-notation-overridden".
  #[local] Infix "\/" := Or : type_scope.
  #[local] Infix "/\" := And : type_scope.
  #[local] Open Scope Nat_scope.

  Definition Nat_isValidChar (n : Nat) : SProp
    := n < 0xd800 \/ (0xdfff < n /\ n < 0x110000).

  Record Char_legacy@{} := Char_legacy_mk
  { val1_legacy : UInt32_legacy;
    valid_legacy : Nat_isValidChar val1_legacy.(val0).(val _) }.

  Record Char@{} := Char_mk
  { val1 : UInt32; valid : Nat_isValidChar val1.(toBitVec).(toFin _).(val _) }.

  Definition check_N_isValidChar (n : N) : bool
    := ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Lemma Nat_nat_add n m : Nat_of_nat (n + m) = Nat_add (Nat_of_nat n) (Nat_of_nat m).
  Proof.
    rewrite Nat.add_comm.
    induction m. 
    - reflexivity.
    - simpl. now f_equal.
  Qed.

  Lemma Nat_nat_mul n m : Nat_of_nat (n * m) = Nat_mul (Nat_of_nat n) (Nat_of_nat m).
  Proof.
    rewrite Nat.mul_comm.
    induction m; simpl.
    - reflexivity. 
    - rewrite Nat.add_comm, Nat_nat_add. now f_equal.
  Qed. 
  
  Lemma Nat_nat_pow n m : Nat_of_nat (n ^ m) = Nat_pow (Nat_of_nat n) (Nat_of_nat m).
  Proof.
    induction m; simpl.
    - reflexivity. 
    - rewrite Nat.mul_comm, Nat_nat_mul. now f_equal. 
  Qed.
  
  Lemma Nat_pow_comm (n : N) : Nat_of_N (2 ^ n) = Nat_pow 2 (Nat_of_N n).
  Proof.
    unfold Nat_of_N. rewrite N2Nat.inj_pow.
    eapply Nat_nat_pow. 
  Qed.
  
  Lemma Nat_lt_to_N_pow (n : N) (m : N) : (n <? 2 ^ m)%N = true -> Nat_of_N n < Nat_pow 2 (Nat_of_N m).
  Proof.
    rewrite <- Nat_pow_comm. eapply Nat_lt_to_N.
  Qed.

  Definition Fin_mk_N_pow (n : N) (val : N) (isLt : (val <? 2 ^ n)%N = true) : Fin (Nat_pow 2 (Nat_of_N n))
    := Fin_mk (Nat_pow 2 (Nat_of_N n)) (Nat_of_N val) (Nat_lt_to_N_pow val n isLt).

  Definition Fin_mk_N (n : N) (val : N) (isLt : (val <? n)%N = true)
    : Fin (Nat_of_N n) :=
    Fin_mk (Nat_of_N n) (Nat_of_N val) (Nat_lt_to_N val n isLt).

  Definition UInt32_legacy_mk_N
    (val : N) (isLt : (val <? 0x100000000)%N = true) : UInt32_legacy :=
    UInt32_legacy_mk (Fin_mk_N 0x100000000 val isLt).

  Definition UInt32_mk_N (val : N) (isLt : (val <? 0x100000000)%N = true) : UInt32
    := UInt32_ofBitVec (BitVec_ofFin 32 (Fin_mk_N_pow 32 val isLt)).

  Lemma Nat_isValidChar_mk_N (n : N) (isLt : check_N_isValidChar n = true)
    : Nat_isValidChar (Nat_of_N n).
  Proof.
    cbv [Nat_isValidChar Nat_of_num_uint check_N_isValidChar] in *.
    pose proof (Nat_lt_to_N n 0xd800) as H1.
    pose proof (Nat_lt_to_N 0xdfff n) as H2.
    pose proof (Nat_lt_to_N n 0x110000) as H3.
    destruct N.ltb; cbn [orb] in *;
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.

  Definition Char_mk_N (val : N) (isLt : ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = true) : Char
    := Char_mk (UInt32_mk_N val (proj1 (andb_prop _ _ isLt))) (Nat_isValidChar_mk_N val (proj2 (andb_prop _ _ isLt))).

  Definition Char_legacy_mk_N
    (val : N)
    (isLt : ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = true)
    : Char_legacy :=
    Char_legacy_mk
      (UInt32_legacy_mk_N val (proj1 (andb_prop _ _ isLt)))
      (Nat_isValidChar_mk_N val (proj2 (andb_prop _ _ isLt))).

  Definition reflective_Char_mk (val : N)
    : if ((val <? 0x100000000)%N && check_N_isValidChar val)%bool
      then Char
      else InvalidChar val
    := let isLt := ((val <? 0x100000000)%N && check_N_isValidChar val)%bool in
       match isLt return ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = isLt -> if isLt then Char else InvalidChar val with
       | true => fun H => Char_mk_N val H
       | false => fun _ => invalid_char val
       end Logic.eq_refl.

  Definition reflective_Char_mk_prim (val : Uint63.int)
    := reflective_Char_mk (Z.to_N (Uint63.to_Z val)).

  Definition reflective_Char_legacy_mk (val : N)
    : if ((val <? 0x100000000)%N && check_N_isValidChar val)%bool
      then Char_legacy
      else InvalidChar val
    := let isLt := ((val <? 0x100000000)%N && check_N_isValidChar val)%bool in
       match isLt return ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = isLt -> if isLt then Char_legacy else InvalidChar val with
       | true => fun H => Char_legacy_mk_N val H
       | false => fun _ => invalid_char val
       end Logic.eq_refl.

  Definition reflective_Char_legacy_mk_prim (val : Uint63.int)
    := reflective_Char_legacy_mk (Z.to_N (Uint63.to_Z val)).


  (* Definition reflective_UInt32_mk (val : N) : if (val <? 0x100000000)%N
                                              then UInt32
                                              else InvalidUInt32 val
    := let isLt := (val <? 0x100000000)%N in
       match isLt return (val <? 0x100000000)%N = isLt -> if isLt then UInt32 else InvalidUInt32 val with
       | true => fun H => UInt32_mk_N val H
       | false => fun _ => invalid_uint32 val
       end Logic.eq_refl.

  Definition reflective_UInt32_mk_prim (val : Uint63.int)
    := reflective_UInt32_mk (Z.to_N (Uint63.to_Z val)).


  Definition check_isValidChar (n : Nat) : bool
    := let n := N_of_Nat n in
        ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Definition reflective_isValidChar_mk (n : Nat)
    : if check_isValidChar n
      then n < 0xd800 \/ (0xdfff < n /\ n < 0x110000)
      else InvalidChar n.
  Proof.
    cbv [check_isValidChar].
    pose proof (Nat_lt_to_N_l n 0xd800) as H1.
    pose proof (Nat_lt_to_N_r 0xdfff n) as H2.
    pose proof (Nat_lt_to_N_l n 0x110000) as H3.
    destruct N.ltb; cbn [orb];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.
  End with_or. *)


End strings.

Register Nat_isValidChar as lean.Nat_isValidChar.
Register Char as lean.Char.
Register Char_legacy as lean.Char.legacy.
Register reflective_Char_mk_prim as lean.Char.mk.reflective_prim.
Register reflective_Char_legacy_mk_prim as lean.Char.legacy.mk.reflective_prim.

Goal forall a n, Nat_pow a (Nat_succ n) = Nat_mul (Nat_pow a n) a.
Proof.
  intros. simpl. reflexivity.
Abort.
