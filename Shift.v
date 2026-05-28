From HOL Require Import ExprAxiomsRules.
From HOL Require Import MinVarNoVar.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.
Set Default Goal Selector "!".
Notation app := ExprAxiomsRules.app.

(** ----------- Shift function and shift-statements -----------*)

Fixpoint shift_basic_f (m k : nat) (p : bool) (e : expr) : expr :=
  match e with
    | idx i => if m <=? i
                then if p then idx (i + k) else idx (i - k)
                else idx i
    | cst c => cst c
    | app e1 e2 => app (shift_basic_f m k p e1) (shift_basic_f m k p e2)
    | lmb a e => lmb (shift_basic_f m k p a) (shift_basic_f (1+m) k p e)
    | pi  a e => pi  (shift_basic_f m k p a) (shift_basic_f (1+m) k p e)
  end
.

Definition shift_f (k : nat) (p : bool) (e : expr) : expr :=
  shift_basic_f 0 k p e.

Inductive shift_basic : nat -> nat -> bool -> expr -> expr -> Prop :=
  | shift_by_idx_same : forall m k p i,
      ~ (m <= i) ->
      shift_basic m k p (idx i) (idx i)
  | shift_by_idx_plus : forall m k i,
      m <= i ->
      shift_basic m k true (idx i) (idx (i + k))
  | shift_by_idx_sub : forall m k i,
      m <= i ->
      shift_basic m k false (idx i) (idx (i - k))
  | shift_by_const : forall m k p c,
      shift_basic m k p (cst c) (cst c)
  | shift_by_app : forall m k p e1 e2 e1' e2',
      shift_basic m k p e1 e1' ->
      shift_basic m k p e2 e2' ->
      shift_basic m k p (app e1 e2) (app e1' e2')
  | shift_by_lmb : forall m k p a e a' e',
      shift_basic m k p a a' ->
      shift_basic (1+m) k p e e' ->
      shift_basic m k p (lmb a e) (lmb a' e')
  | shift_by_pi : forall m k p a e a' e',
      shift_basic m k p a a' ->
      shift_basic (1+m) k p e e' ->
      shift_basic m k p (pi a e) (pi a' e')
.

Definition shift k p e1 e2 : Prop := shift_basic 0 k p e1 e2.


(** ------------- Shift as function and as prop are equivalent ------------------ *)

Theorem shift_equiv_shift_f : forall m k p e e',
  shift_basic m k p e e' <-> e' = shift_basic_f m k p e.
Proof.
  intros m k p e e'; split.
  - generalize dependent e'; generalize dependent m; induction e; intros; subst; simpl.
    + inversion H; subst.
      * rewrite <- Nat.leb_nle in H4.
        rewrite H4. reflexivity.
      * rewrite <- Nat.leb_le in H4.
        rewrite H4. reflexivity.
      * rewrite <- Nat.leb_le in H4.
        rewrite H4. reflexivity.
    + inversion H. reflexivity.
    + inversion H; subst.
      rewrite <- (IHe1 m e1' H5), <- (IHe2 m e2' H7).
      reflexivity.
    + inversion H; subst.
      rewrite <- (IHe1 m a' H5), <- (IHe2 (S m) e'0 H7).
      reflexivity.
    + inversion H; subst.
      rewrite <- (IHe1 m a' H5), <- (IHe2 (S m) e'0 H7).
      reflexivity.
  - generalize dependent e'; generalize dependent m; induction e; intros; subst; simpl;
      try (simpl; constructor; auto).
    destruct (m <=? n) eqn:Eq.
    + simpl; destruct p; constructor;
      rewrite <- Nat.leb_le; auto.
    + constructor. rewrite <- Nat.leb_nle; auto.
Qed.

(** ------------------- Safe version of shift ----------------------------- *)

Inductive shift_basic_safe : nat -> nat -> bool -> expr -> expr -> Prop :=
  | shift_basic_plus : forall m k e e',
      shift_basic m k true e e' ->
      shift_basic_safe m k true  e e'
  | shift_basic_minus : forall m k e e',
      k <= m ->
      shift_basic m k false e e' ->
      shift_basic_safe m k false e e'
.

Definition shift_safe (k : nat) (p : bool) (e e' : expr) : Prop :=
  shift_basic_safe 0 k p e e'.

(** ------------------- Conditions for shift being safe ------------------- *)

Lemma shift_plus_is_safe : forall m k e e',
  shift_basic_safe m k true e e' <->
  shift_basic m k true e e'.
Proof.
  intros. split.
  - intros. inversion H; auto.
  - intros. constructor; auto.
Qed.

Lemma shift_minus_can_be_safe : forall m k e e',
  shift_basic_safe m k false e e' <->
  (k <= m /\ shift_basic m k false e e').
Proof.
  intros. split.
  - intros. inversion H; subst. split; assumption.
  - intros [H H']. constructor; assumption.
Qed.

Lemma shift_safe_is_shift : forall m k p e e',
  shift_basic_safe m k p e e' ->
  shift_basic m k p e e'.
Proof.
  intros. inversion H; auto.
Qed.

(** ----------------- Shift preserves the abscence of a variable -----------------*)

Lemma shift_preserves_no_var1 : forall i e m k e',
  no_var i e ->
  i < m ->
  shift_basic_safe m k true e e' ->
  no_var i e'.
Proof.
  intros i e; generalize dependent i;
  induction e; intros.
  - inversion H1; inversion H2; subst.
    + assumption.
    + inversion H; subst.
      constructor. destruct k; try lia.
  - inversion H1; inversion H2; subst.
    constructor.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor;
     [ eapply IHe1 | eapply IHe2 ];
    eauto; econstructor; eauto.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor.
    + eapply IHe1.
      * auto.
      * apply H0.
      * constructor; eauto.
    + eapply IHe2.
      * auto.
      * assert (i + 1 < 1 + m) by lia.
        eauto.
      * constructor; eauto.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor.
    + eapply IHe1.
      * auto.
      * apply H0.
      * constructor; eauto.
    + eapply IHe2.
      * auto.
      * assert (i + 1 < 1 + m) by lia.
        eauto.
      * constructor; eauto.
Qed.

Lemma shift_preserves_no_var2 : forall i e m k e',
  no_var i e ->
  m <= i ->
  shift_basic_safe m k true e e' ->
  no_var (i + k) e'.
Proof.
  intros i e; generalize dependent i;
  induction e; intros.
  - inversion H1; inversion H2; subst.
    + constructor. lia.
    + inversion H; subst.
      constructor. destruct k; try lia.
  - inversion H1; inversion H2; subst.
    constructor.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor;
     [ eapply IHe1 | eapply IHe2 ];
    eauto; econstructor; eauto.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor.
    + eapply IHe1.
      * auto.
      * apply H0.
      * constructor; eauto.
    + replace (i + k + 1) with (i + 1 + k) by lia; eapply IHe2.
      * auto.
      * assert (1 + m <= i + 1) by lia.
        eauto.
      * constructor; eauto.
  - inversion H1; inversion H2; subst.
    inversion H; subst; constructor.
    + eapply IHe1.
      * auto.
      * apply H0.
      * constructor; eauto.
    + replace (i + k + 1) with (i + 1 + k) by lia; eapply IHe2.
      * auto.
      * assert (1 + m <= i + 1) by lia.
        eauto.
      * constructor; eauto.
Qed.

Lemma no_var_after_shift_f : forall j m k e,
  j < m + k + 1 -> m <= j ->
  no_var j (shift_basic_f m (k + 1) true e).
Proof.
  intros. generalize dependent k; generalize dependent m;
  generalize dependent j; induction e; intros; subst.
  - simpl. destruct (Nat.leb_spec m n);
      constructor; lia.
  - simpl. constructor.
  - simpl. constructor; auto.
  - simpl. constructor.
    + eapply IHe1; lia.
    + eapply IHe2; lia.
  - simpl. constructor.
    + eapply IHe1; lia.
    + eapply IHe2; lia.
Qed.

Lemma no_var_after_shift_f' : forall m j e k,
  m <= j -> no_var j e ->
  no_var (j + (k + 1)) (shift_basic_f m (k + 1) true e).
Proof.
  intros m j e; generalize dependent j;
  generalize dependent m; induction e;
  intros; subst; unfold shift_f; simpl.
  - inversion H0; subst.
    destruct (Nat.leb_spec m n).
    + inversion H; subst; constructor; lia.
    + constructor; lia.
  - constructor.
  - inversion H0; subst; constructor; auto; lia.
  - inversion H0; subst; constructor.
    + eapply IHe1; auto.
    + replace (j + (k + 1) + 1) with ((j + 1) + (k + 1)) by lia.
      apply IHe2; try lia. auto.
  - inversion H0; subst; constructor.
    + eapply IHe1; auto.
    + replace (j + (k + 1) + 1) with ((j + 1) + (k + 1)) by lia.
      apply IHe2; try lia. auto.
Qed.

(** --------------- Shift by 0 doesn't change the expression ----------------*)

Lemma shift_by_0 : forall m p e,
  shift_basic m 0 p e e.
Proof.
  intros. generalize dependent p; generalize dependent m;
  induction e; intros.
  - destruct (Nat.leb_spec m n).
    + destruct p.
      * rewrite <- (Nat.add_0_r n).
        replace (shift_basic m 0 true (idx (n + 0)) (idx (n + 0)))
           with (shift_basic m 0 true (idx n) (idx (n + 0))).
        ** constructor; auto.
        ** rewrite (Nat.add_0_r n). reflexivity.
      * assert (n = n - 0) by lia.
        rewrite H0.
        replace (shift_basic m 0 false (idx (n - 0)) (idx (n - 0)))
           with (shift_basic m 0 false (idx n) (idx (n - 0))).
        ** constructor; auto.
        ** rewrite <- H0. reflexivity.
    + constructor; auto. lia.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma shift_f_by_0 : forall m p e,
  e = shift_basic_f m 0 p e.
Proof.
  intros. rewrite <- shift_equiv_shift_f.
  apply shift_by_0.
Qed.

(** ---------------------- Shift is total ----------------------------------*)

Lemma shift_f_sats_shift : forall m k p e,
  shift_basic m k p e (shift_basic_f m k p e).
Proof.
  intros.
  rewrite shift_equiv_shift_f.
  reflexivity.
Qed.

(** ------------------------- Shift is determined function ----------------------- *)

Lemma shift_determination : forall m k p e e1 e2,
  shift_basic m k p e e1 ->
  shift_basic m k p e e2 ->
  e1 = e2.
Proof.
  intros. rewrite shift_equiv_shift_f in *.
  rewrite H, H0. reflexivity.
Qed.

(** ---------------------- Shift is injection ------------------------------*)

Lemma shift_injection : forall m k e1 e0 e2,
  shift_basic_safe m k true e1 e0 ->
  shift_basic_safe m k true e2 e0 ->
  e1 = e2.
Proof.
  intros m k e1; generalize dependent k;
  generalize dependent m. induction e1; intros.
  - inversion H; inversion H1; subst; try lia.
    + inversion H0; inversion H2; subst; try lia.
      reflexivity.
    + inversion H0; inversion H2; subst; try lia.
      replace i with n by lia. reflexivity.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    reflexivity.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    replace e1_1 with e1.
    + replace e1_2 with e0; try reflexivity.
      symmetry. eapply IHe1_2; constructor; eauto.
    + symmetry. eapply IHe1_1; constructor; eauto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    replace e1_1 with a.
    + replace e1_2 with e0; try reflexivity.
      symmetry. eapply IHe1_2; constructor; eauto.
    + symmetry. eapply IHe1_1; constructor; eauto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    replace e1_1 with a.
    + replace e1_2 with e0; try reflexivity.
      symmetry. eapply IHe1_2; constructor; eauto.
    + symmetry. eapply IHe1_1; constructor; eauto.
Qed.

(** ---------------------- Shift's additivity ------------------------------*)

Lemma shift_safe_additivity_plus_plus : forall m k1 k2 e e' e'',
  shift_basic_safe  m       k1        true   e  e'  ->
  shift_basic_safe (m + k1) k2        true   e' e'' ->
  shift_basic_safe  m       (k1 + k2) true   e  e''.
Proof.
  intros m k1 k2 e. generalize dependent k2;
  generalize dependent k1; generalize dependent m.
  induction e; intros.
  - inversion H; inversion H1; subst.
    + inversion H0; inversion H2; subst.
      * repeat constructor; auto.
      * lia.
    + inversion H0; inversion H2; subst.
      * lia.
      * rewrite <- Nat.add_assoc.
        repeat constructor; auto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    repeat constructor.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    repeat constructor.
    + assert (shift_basic_safe m k1 true e1 e1') by (constructor; auto).
      assert (shift_basic_safe (m + k1) k2 true e1' e1'0) by (constructor; auto).
      assert (shift_basic_safe m (k1 + k2) true e1 e1'0) by eauto.
      inversion H5; auto.
    + assert (shift_basic_safe m k1 true e2 e2') by (constructor; auto).
      assert (shift_basic_safe (m + k1) k2 true e2' e2'0) by (constructor; auto).
      assert (shift_basic_safe m (k1 + k2) true e2 e2'0) by eauto.
      inversion H5; auto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    repeat constructor.
    + assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
      assert (shift_basic_safe (m + k1) k2 true a' a'0) by (constructor; auto).
      assert (shift_basic_safe m (k1 + k2) true e1 a'0) by eauto.
      inversion H5; auto.
    + assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
      assert (shift_basic_safe (1 + (m + k1)) k2 true e'1 e'0) by (constructor; auto).
      assert (shift_basic_safe (1 + m) (k1 + k2) true e2 e'0) by eauto.
      inversion H5; auto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    repeat constructor.
    + assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
      assert (shift_basic_safe (m + k1) k2 true a' a'0) by (constructor; auto).
      assert (shift_basic_safe m (k1 + k2) true e1 a'0) by eauto.
      inversion H5; auto.
    + assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
      assert (shift_basic_safe (1 + (m + k1)) k2 true e'1 e'0) by (constructor; auto).
      assert (shift_basic_safe (1 + m) (k1 + k2) true e2 e'0) by eauto.
      inversion H5; auto.
Qed.

Lemma shift_safe_additivity_plus_minus : forall m k1 k2 e e' e'',
  shift_basic_safe  m k1 true e e' ->
  shift_basic_safe (m + k1) k2 false e' e'' ->
  (k2 <= k1 /\ shift_basic_safe m (k1 - k2) true  e e'') \/
  (k1 <  k2 /\ shift_basic_safe m (k2 - k1) false e e'').
Proof.
  intros m k1 k2 e. generalize dependent k2;
  generalize dependent k1; generalize dependent m.
  induction e; intros;
    (destruct (Nat.leb_spec k2 k1); [left | right]; split; auto);
    inversion H; inversion H2; subst; inversion H0; inversion H4; subst; try lia.
    + repeat constructor; auto.
    + replace (n + k1 - k2) with (n + (k1 - k2)) by lia.
      repeat constructor; auto.
    + repeat constructor; auto. lia.
    + replace (n + k1 - k2) with (n - (k2 - k1)) by lia.
      repeat constructor; auto. lia.
    + repeat constructor.
    + repeat constructor. lia.
    + repeat constructor.
      * assert (shift_basic_safe m k1 true e1 e1') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false e1' e1'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 e1' e1'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
      * assert (shift_basic_safe m k1 true e2 e2') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false e2' e2'0) by (constructor; try lia; auto).
        destruct (IHe2 m k1 k2 e2' e2'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
    + repeat constructor; try lia.
      * assert (shift_basic_safe m k1 true e1 e1') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false e1' e1'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 e1' e1'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
      * assert (shift_basic_safe m k1 true e2 e2') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false e2' e2'0) by (constructor; try lia; auto).
        destruct (IHe2 m k1 k2 e2' e2'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
    + repeat constructor.
      * assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false a' a'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 a' a'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
      * assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
        assert (shift_basic_safe (1 + (m + k1)) k2 false e'1 e'0) by (constructor; try lia; auto).
        destruct (IHe2 (1 + m) k1 k2 e'1 e'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
    + repeat constructor; try lia.
      * assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false a' a'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 a' a'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
      * assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
        assert (shift_basic_safe (1 + (m + k1)) k2 false e'1 e'0) by (constructor; try lia; auto).
        destruct (IHe2 (1 + m) k1 k2 e'1 e'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
    + repeat constructor.
      * assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false a' a'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 a' a'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
      * assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
        assert (shift_basic_safe (1 + (m + k1)) k2 false e'1 e'0) by (constructor; try lia; auto).
        destruct (IHe2 (1 + m) k1 k2 e'1 e'0 H5 H6) as [[_ L] | [contra _]].
        ** inversion L; subst. assumption.
        ** lia.
    + repeat constructor; try lia.
      * assert (shift_basic_safe m k1 true e1 a') by (constructor; auto).
        assert (shift_basic_safe (m + k1) k2 false a' a'0) by (constructor; try lia; auto).
        destruct (IHe1 m k1 k2 a' a'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
      * assert (shift_basic_safe (1 + m) k1 true e2 e'1) by (constructor; auto).
        assert (shift_basic_safe (1 + (m + k1)) k2 false e'1 e'0) by (constructor; try lia; auto).
        destruct (IHe2 (1 + m) k1 k2 e'1 e'0 H5 H6) as [[contra _] | [_ L]].
        ** lia.
        ** inversion L; subst. assumption.
Qed.

Lemma shift_additivity_plus_minus_1 : forall m k1 k2 e e' e'',
  shift_basic_safe  m k1 true e e' ->
  shift_basic_safe (m + k1) k2 false e' e'' ->
  k2 <= k1 ->
  shift_basic_safe m (k1 - k2) true  e e''.
Proof.
  intros.
  destruct (shift_safe_additivity_plus_minus m k1 k2 e e' e'' H H0) as [[_ L] | [contra _]]; try lia.
  assumption.
Qed.

Lemma shift_additivity_plus_minus_2 : forall m k1 k2 e e' e'',
  shift_basic_safe  m k1 true e e' ->
  shift_basic_safe (m + k1) k2 false e' e'' ->
  k1 <  k2 ->
  shift_basic_safe m (k2 - k1) false  e e''.
Proof.
  intros.
  destruct (shift_safe_additivity_plus_minus m k1 k2 e e' e'' H H0) as [[contra _] | [_ L]]; try lia.
  assumption.
Qed.

Lemma shift_f_additivity_plus_plus : forall m k1 k2 e,
  shift_basic_f m (k1 + k2) true e = shift_basic_f (m + k1) k2 true (shift_basic_f m k1 true e).
Proof.
  intros.
  remember (shift_basic_f m k1 true e) as e' eqn:H'.
  remember (shift_basic_f (m + k1) k2 true e') as e'' eqn:H''.
  symmetry. rewrite <- shift_equiv_shift_f in *.
  rewrite <- shift_plus_is_safe.
  eapply shift_safe_additivity_plus_plus;
    econstructor; eauto.
Qed.

Lemma shift_f_additivity_plus_minus_1 : forall m k1 k2 e,
  k2 <= k1 ->
  shift_basic_f m (k1 - k2) true e =
    shift_basic_f (m + k1) k2 false (shift_basic_f m k1 true e).
Proof.
  intros.
  remember (shift_basic_f m k1 true e) as e' eqn:H'.
  remember (shift_basic_f (m + k1) k2 false e') as e'' eqn:H''.
  symmetry. rewrite <- shift_equiv_shift_f in *.
  apply shift_safe_is_shift.
  eapply shift_additivity_plus_minus_1; auto; econstructor; eauto; lia.
Qed.

Lemma shift_f_additivity_plus_minus_2 : forall m k1 k2 e,
  k1 <  k2 -> k2 <= m + k1 ->
  shift_basic_f m (k2 - k1) false e =
    shift_basic_f (m + k1) k2 false (shift_basic_f m k1 true e).
Proof.
  intros.
  remember (shift_basic_f m k1 true e) as e' eqn:H'.
  remember (shift_basic_f (m + k1) k2 false e') as e'' eqn:H''.
  symmetry. rewrite <- shift_equiv_shift_f in *.
  apply shift_safe_is_shift.
  eapply shift_additivity_plus_minus_2; auto; econstructor; eauto.
Qed.

Lemma shift_additivity_diff_m_plus_plus_1 : forall m1 k1 e e' m2 k2 e'',
  shift_basic_safe m1 k1 true e  e'  ->
  shift_basic_safe m2 k2 true e' e'' ->
  m1 <= m2 ->
  m2 <= m1 + k1 ->
  shift_basic_safe m1 (k1 + k2) true e e''.
Proof.
  intros m1 k1 e; generalize dependent k1;
  generalize dependent m1; induction e; intros;
  apply shift_safe_is_shift in H, H0; subst; constructor.
  - inversion H; subst; inversion H0; subst.
    + constructor; lia.
    + lia.
    + lia.
    + replace (n + k1 + k2) with (n + (k1 + k2)) by lia; constructor; lia.
  - inversion H; subst.
    inversion H0; subst.
    constructor.
  - inversion H; subst.
    inversion H0; subst.
    constructor; apply shift_safe_is_shift.
    + eapply IHe1.
      * constructor. apply H8.
      * constructor. apply H9.
      * auto.
      * auto.
    + eapply IHe2.
      * constructor. apply H10.
      * constructor. apply H12.
      * auto.
      * auto.
  - inversion H; subst.
    inversion H0; subst.
    constructor; apply shift_safe_is_shift.
    + eapply IHe1.
      * constructor. apply H8.
      * constructor. apply H9.
      * auto.
      * auto.
    + eapply IHe2.
      * constructor. apply H10.
      * constructor. apply H12.
      * lia.
      * lia.
  - inversion H; subst.
    inversion H0; subst.
    constructor; apply shift_safe_is_shift.
    + eapply IHe1.
      * constructor. apply H8.
      * constructor. apply H9.
      * auto.
      * auto.
    + eapply IHe2.
      * constructor. apply H10.
      * constructor. apply H12.
      * lia.
      * lia.
Qed.

(** ----------------------------- Shift can be inverted -----------------------------*)

Lemma shift_reverse : forall m k e e',
  shift_basic_safe  m      k true  e  e' ->
  shift_basic_safe (m + k) k false e' e.
Proof.
  intros m k e; generalize dependent k; generalize dependent m.
  induction e; intros; subst.
  - inversion H; inversion H0; subst.
    + constructor; try lia. constructor; lia.
    + constructor; try lia. replace (idx n) with (idx (n + k - k)).
      * constructor; lia.
      * replace (n + k - k) with n by lia. reflexivity.
  - inversion H; inversion H0; subst.
    repeat constructor. lia.
  - inversion H; inversion H0; subst. apply shift_basic_plus in H10, H12.
    constructor; try lia; constructor; auto; apply shift_safe_is_shift; auto.
  - inversion H; inversion H0; subst. apply shift_basic_plus in H10, H12.
    constructor; try lia. constructor; apply shift_safe_is_shift; auto.
    replace (1 + (m + k)) with ((1 + m) + k) by lia; auto.
  - inversion H; inversion H0; subst. apply shift_basic_plus in H10, H12.
    constructor; try lia. constructor; apply shift_safe_is_shift; auto.
    replace (1 + (m + k)) with ((1 + m) + k) by lia; auto.
Qed.

(** --------------------------- Shift associativity --------------------------------*)

Lemma shift_assoc_minus_plus : forall m1 e1 e2 m2 k e3,
  no_var m1 e1 ->
  shift_basic_safe (1  + m1) 1 false e1 e2 ->
  shift_basic_safe (m2 + m1) k true  e2 e3 ->
  exists e2',
  shift_basic_safe (1 + m2 + m1) k true e1 e2' /\
  shift_basic_safe (1 + m1) 1 false e2' e3.
Proof.
  intros m1 e1; generalize dependent m1;
  induction e1; intros m1 e2 m2 k e3 Hm H H0.
  - inversion Hm; subst.
    inversion H; inversion H2; subst.
    + assert (F : n < m1) by lia.
      inversion H0; inversion H4; subst; try lia.
      exists (idx n).
      split; repeat constructor; lia.
    + inversion H0; inversion H4; subst.
      * exists (idx n); split.
        -- constructor. constructor. lia.
        -- constructor; try lia. constructor. lia.
      * exists (idx (n + k)); split.
        -- repeat constructor; lia.
        -- constructor; try lia.
           replace (n - 1 + k) with (n + k - 1) by lia.
           constructor. lia.
  - inversion H; inversion H2; subst.
    inversion H0; inversion H3; subst.
    exists (cst c); split.
    + repeat constructor.
    + constructor; try lia. constructor.
  - inversion H; inversion H2; subst.
    inversion H0; inversion H3; subst.
    inversion Hm; subst.
    assert (L1 : exists e2' : expr,
      shift_basic_safe (1 + m2 + m1) k true e1_1 e2' /\
      shift_basic_safe (1 + m1) 1 false e2' e1'0).
    { apply (IHe1_1 m1 e1'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
      shift_basic_safe (1 + m2 + m1) k true e1_2 e2' /\
      shift_basic_safe (1 + m1) 1 false e2' e2'0).
    { apply (IHe1_2 m1 e2'); try constructor; auto. }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (app e1_1' e1_2'); split.
    + repeat constructor; auto.
    + constructor; try lia. constructor; try lia; auto.
  - inversion H; inversion H2; subst.
    inversion H0; inversion H3; subst.
    inversion Hm; subst.
    assert (L1 : exists e2' : expr,
      shift_basic_safe (1 + m2 + m1) k true e1_1 e2' /\
      shift_basic_safe (1 + m1) 1 false e2' a'0).
    { apply (IHe1_1 m1 a'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
      shift_basic_safe (1 + m2 + (1 + m1)) k true e1_2 e2' /\
      shift_basic_safe (1 + (1 + m1)) 1 false e2' e'1).
    { apply (IHe1_2 (1 + m1) e'0).
      + rewrite Nat.add_comm; auto.
      + constructor; auto.
      + constructor; try lia.
        replace (m2 + (1 + m1)) with (1 + (m2 + m1)); try lia; auto.
    }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (lmb e1_1' e1_2'); split.
    + repeat constructor; auto.
      replace (1 + (1 + m2 + m1)) with (1 + m2 + (1 + m1)) by lia; auto.
    + constructor; try lia. constructor; try lia; auto.
  - inversion H; inversion H2; subst.
    inversion H0; inversion H3; subst.
    inversion Hm; subst.
    assert (L1 : exists e2' : expr,
      shift_basic_safe (1 + m2 + m1) k true e1_1 e2' /\
      shift_basic_safe (1 + m1) 1 false e2' a'0).
    { apply (IHe1_1 m1 a'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
      shift_basic_safe (1 + m2 + (1 + m1)) k true e1_2 e2' /\
      shift_basic_safe (1 + (1 + m1)) 1 false e2' e'1).
    { apply (IHe1_2 (1 + m1) e'0).
      + rewrite Nat.add_comm; auto.
      + constructor; auto.
      + constructor; try lia.
        replace (m2 + (1 + m1)) with (1 + (m2 + m1)); try lia; auto.
    }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (pi  e1_1' e1_2'); split.
    + repeat constructor; auto.
      replace (1 + (1 + m2 + m1)) with (1 + m2 + (1 + m1)) by lia; auto.
    + constructor; try lia. constructor; try lia; auto.
Qed.

Lemma shift_assoc_minus_plus' : forall m1 e1 m2 k ,
  no_var m1 e1 ->
  shift_basic_f (m2 + m1) k true (shift_basic_f (1 + m1) 1 false e1) =
  shift_basic_f (1 + m1) 1 false (shift_basic_f (1 + m2 + m1) k true e1).
Proof.
  intros.
  remember (shift_basic_f (1 + m1) 1 false e1) as e2.
  remember (shift_basic_f (m2 + m1) k true e2) as e3.
  rewrite <- shift_equiv_shift_f in *.
  eapply shift_assoc_minus_plus in H;
  [idtac | constructor; try lia; eauto | constructor; eauto].
  destruct H as [e2' [H1 H2]].
  remember (shift_basic_f (1 + m2 + m1) k true e1) as e2''.
  rewrite <- shift_equiv_shift_f in *.
  inversion H1; subst.
  replace e2'' with e2'.
  - inversion H2; auto.
  - eapply shift_determination; eauto.
Qed.

Lemma shift_assoc_plus_plus : forall m1 e1 e2 m2 k e3,
  shift_basic_safe           m1  1 true e1 e2 ->
  shift_basic_safe (1 + m2 + m1) k true e2 e3 ->
  exists e2', 
  shift_basic_safe (m2 + m1) k true e1 e2' /\
  shift_basic_safe       m1  1 true e2' e3.
Proof.
  intros m1 e1; generalize dependent m1;
  induction e1; intros m1 e2 m2 k e3 H H0.
  - inversion H; inversion H1; subst.
    + inversion H0; inversion H2; subst; try lia.
      exists (idx n). split.
      * constructor. constructor. lia.
      * repeat constructor; lia.
    + inversion H0; inversion H2; subst; try lia.
      * exists (idx n). split.
        -- constructor. constructor. lia.
        -- constructor. constructor. lia.
      * exists (idx (n + k)). split.
        -- constructor. constructor. lia.
        -- constructor. replace (n + 1 + k) with (n + k + 1) by lia.
           constructor. lia.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    exists (cst c); split; repeat constructor.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    assert (L1 : exists e2' : expr,
          shift_basic_safe (m2 + m1) k true e1_1 e2' /\
          shift_basic_safe       m1  1 true e2' e1'0).
        { apply (IHe1_1 m1 e1'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
          shift_basic_safe (m2 + m1) k true e1_2 e2' /\
          shift_basic_safe       m1  1 true e2' e2'0).
        { apply (IHe1_2 m1 e2'); try constructor; auto. }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (app e1_1' e1_2'); split.
    + repeat constructor; auto.
    + repeat constructor; try lia; auto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    assert (L1 : exists e2' : expr,
          shift_basic_safe (m2 + m1) k true e1_1 e2' /\
          shift_basic_safe       m1  1 true e2' a'0).
        { apply (IHe1_1 m1 a'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
          shift_basic_safe (m2 + (1 + m1)) k true e1_2 e2' /\
          shift_basic_safe       (1 + m1)  1 true e2'  e'1).
        { apply (IHe1_2 (1 + m1) e'0); try constructor; auto.
          replace (1 + m2 + (1 + m1)) with (1 + (1 + m2 + m1)) by lia; auto. }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (lmb e1_1' e1_2'); split.
    + repeat constructor; auto.
      replace (1 + (m2 + m1)) with (m2 + (1 + m1)) by lia; auto.
    + repeat constructor; try lia; auto.
  - inversion H; inversion H1; subst.
    inversion H0; inversion H2; subst.
    assert (L1 : exists e2' : expr,
          shift_basic_safe (m2 + m1) k true e1_1 e2' /\
          shift_basic_safe       m1  1 true e2' a'0).
        { apply (IHe1_1 m1 a'); try constructor; auto. }
    assert (L2 : exists e2' : expr,
          shift_basic_safe (m2 + (1 + m1)) k true e1_2 e2' /\
          shift_basic_safe       (1 + m1)  1 true e2'  e'1).
        { apply (IHe1_2 (1 + m1) e'0); try constructor; auto.
          replace (1 + m2 + (1 + m1)) with (1 + (1 + m2 + m1)) by lia; auto. }
    destruct L1 as [e1_1' [L11 L12]], L2 as [e1_2' [L21 L22]].
    inversion L11; inversion L12; inversion L21; inversion L22; try lia; subst.
    exists (pi  e1_1' e1_2'); split.
    + repeat constructor; auto.
      replace (1 + (m2 + m1)) with (m2 + (1 + m1)) by lia; auto.
    + repeat constructor; try lia; auto.
Qed.

Lemma shift_assoc_plus_plus' : forall m1 m2 k e1,
  shift_basic_f  (1 + m2 + m1) k true (shift_basic_f m1 1 true e1) =
  shift_basic_f m1 1 true (shift_basic_f (m2 + m1) k true e1).
Proof.
  intros.
  remember (shift_basic_f m1 1 true e1) as e2.
  remember (shift_basic_f (1 + m2 + m1) k true e2) as e3.
  rewrite <- shift_equiv_shift_f in *.
  apply shift_basic_plus in Heqe2.
  eapply shift_assoc_plus_plus in Heqe2;
  [idtac | constructor; eauto].
  destruct Heqe2 as [e2' [H1 H2]].
  remember (shift_basic_f (m2 + m1) k true e1) as e2''.
  rewrite <- shift_equiv_shift_f in *.
  inversion H1; subst.
  replace e2'' with e2'.
  - inversion H2; auto.
  - eapply shift_determination; eauto.
Qed.

Lemma shift_after_shift : forall k' k2 m k1 e,
  k' <= k2 ->
  shift_basic_f m k1 true (shift_basic_f m k2 true e) =
  shift_basic_f (m + k') k1 true (shift_basic_f m k2 true e).
Proof.
  intros k' k2 m k1 e; generalize dependent k1; generalize dependent m;
  generalize dependent k2; generalize dependent k'; induction e; intros.
  - simpl. destruct (m <=? n) eqn:Eq1.
    + simpl. assert (L1 : m <=? n + k2 = true).
      { rewrite Nat.leb_le in *. lia. }
      assert (L2 : m + k' <=? n + k2 = true).
      { rewrite Nat.leb_le in *; lia. }
      rewrite L1, L2. reflexivity.
    + simpl. assert (L : m + k' <=? n = false).
      { rewrite Nat.leb_nle in *. lia. }
      rewrite Eq1, L. reflexivity.
  - reflexivity.
  - simpl. replace (shift_basic_f m k1 true (shift_basic_f m k2 true e1))
             with (shift_basic_f (m + k') k1 true (shift_basic_f m k2 true e1)).
    + replace (shift_basic_f m k1 true (shift_basic_f m k2 true e2))
        with (shift_basic_f (m + k') k1 true (shift_basic_f m k2 true e2)).
      * reflexivity.
      * symmetry; auto.
    + symmetry; auto.
  - simpl. replace (shift_basic_f (m + k') k1 true (shift_basic_f m k2 true e1))
             with (shift_basic_f m k1 true (shift_basic_f m k2 true e1)).
    + replace (shift_basic_f (S (m + k')) k1 true (shift_basic_f (S m) k2 true e2))
        with (shift_basic_f (S m) k1 true (shift_basic_f (S m) k2 true e2)).
      * reflexivity.
      * replace (S (m + k')) with (S m + k') by lia; auto.
    + auto.
  - simpl. replace (shift_basic_f (m + k') k1 true (shift_basic_f m k2 true e1))
             with (shift_basic_f m k1 true (shift_basic_f m k2 true e1)).
    + replace (shift_basic_f (S (m + k')) k1 true (shift_basic_f (S m) k2 true e2))
        with (shift_basic_f (S m) k1 true (shift_basic_f (S m) k2 true e2)).
      * reflexivity.
      * replace (S (m + k')) with (S m + k') by lia; auto.
    + auto.
Qed.