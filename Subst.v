From HOL Require Import ExprAxiomsRules.
From HOL Require Import Shift.
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

(** ------------------------ Subst function and proposition definition ----------------*)

Fixpoint subst_f (j : nat) (s e : expr) : expr :=
  match e with
    | idx i => if j =? i
               then s
               else idx i
    | cst c => cst c
    | app e1 e2 => app (subst_f j s e1) (subst_f j s e2)
    | lmb a e => lmb (subst_f j s a) (subst_f (1+j) (shift_f 1 true s) e)
    | pi  a e => pi  (subst_f j s a) (subst_f (1+j) (shift_f 1 true s) e)
  end
.

Inductive subst : nat -> expr -> expr -> expr -> Prop :=
  | subst_by_idx_same : forall j s,
      subst j s (idx j) s
  | subst_by_idx_skip : forall j s i,
      j <> i ->
      subst j s (idx i) (idx i)
  | subst_by_const : forall j s c,
      subst j s (cst c) (cst c)
  | subst_by_app : forall j s e1 e2 e1' e2',
      subst j s e1 e1' ->
      subst j s e2 e2' ->
      subst j s (app e1 e2) (app e1' e2')
  | subst_by_lmb : forall j s s' a e a' e',
      subst j s a a' ->
      shift_safe 1 true s s' ->
      subst (1+j) s' e e' ->
      subst j s (lmb a e) (lmb a' e')
  | subst_by_pi : forall j s s' a e a' e',
      subst j s a a' ->
      shift_safe 1 true s s' ->
      subst (1+j) s' e e' ->
      subst j s (pi a e) (pi a' e')
.

(** ----------------- Subst function and prop are equivalent ------------------------*)

Theorem subst_equiv_subst_f : forall j s e e',
  subst j s e e' <-> e' = subst_f j s e.
Proof.
  intros; split.
  - generalize dependent e'; generalize dependent s; generalize dependent j.
    induction e; intros; simpl.
    + inversion H; subst.
      * rewrite Nat.eqb_refl; reflexivity.
      * rewrite <- Nat.eqb_neq in H3.
        rewrite H3; reflexivity.
    + inversion H; subst. reflexivity.
    + inversion H; subst.
      rewrite <- (IHe1 j s e1' H4), <- (IHe2 j s e2' H6).
      reflexivity.
    + inversion H; subst. unfold shift in H5.
      inversion H5; subst. rewrite shift_equiv_shift_f in H0; subst.
      apply IHe1 in H2; apply IHe2 in H7; subst.
      reflexivity.
    + inversion H; subst. unfold shift in H5. inversion H5.
      rewrite shift_equiv_shift_f in H0; subst.
      apply IHe1 in H2; apply IHe2 in H7; subst.
      reflexivity.
  - generalize dependent e'; generalize dependent s; generalize dependent j; induction e; intros;
      simpl; subst; try (constructor; auto).
    + simpl. destruct (j =? n) eqn:Eq.
      * rewrite Nat.eqb_eq in Eq. subst. simpl. constructor.
      * constructor. 
        rewrite Nat.eqb_neq in Eq; auto.
    + fold subst_f. eapply subst_by_lmb; eauto.
      constructor.
      apply shift_f_sats_shift.
    + eapply subst_by_pi; eauto. constructor.
      apply shift_f_sats_shift.
Qed.

(** ---------------------------- Subst is total ---------------------------*)

Lemma subst_f_sats_subst : forall j s e,
  subst j s e (subst_f j s e).
Proof.
  intros.
  rewrite subst_equiv_subst_f.
  reflexivity.
Qed.

(** ----------------- Subst preserves the abscence of a variable -----------------*)

Lemma no_var_after_subst_f : forall j s e,
  no_var j s ->
  no_var j (subst_f j s e).
Proof.
  intros j s e; generalize dependent s; generalize dependent j;
  induction e; intros; subst.
  - destruct (Nat.eqb_spec j n); subst.
    + simpl. rewrite (Nat.eqb_refl n). auto.
    + simpl. rewrite <- (Nat.eqb_neq j n) in n0. rewrite n0; auto.
      constructor. rewrite (Nat.eqb_neq j n) in n0; subst; auto.
  - simpl. constructor.
  - simpl. constructor; eauto.
  - simpl. constructor.
    + eapply IHe1; auto.
    + simpl. remember (shift_f 1 true s) as s'.
      replace (S j) with (j + 1) by lia. eapply IHe2; subst.
      replace 1 with (0 + 1) by lia.
      apply no_var_after_shift_f'; try lia. auto.
  - simpl. constructor.
    + eapply IHe1; auto.
    + simpl. remember (shift_f 1 true s) as s'.
      replace (S j) with (j + 1) by lia. eapply IHe2; subst.
      replace 1 with (0 + 1) by lia.
      apply no_var_after_shift_f'; try lia. auto.
Qed.

(** ------------------------- Subst is determined function -----------------------*)

Lemma subst_determination : forall j s e e1 e2,
  subst j s e e1 -> subst j s e e2 -> e1 = e2.
Proof.
  intros j s e; generalize dependent s; generalize dependent j;
  induction e; intros.
  - inversion H; subst.
    + inversion H0; subst; auto. lia.
    + inversion H0; subst; auto.
      inversion H; subst; auto. lia.
  - inversion H. inversion H0. reflexivity.
  - inversion H; subst. inversion H0; subst.
    replace e1' with e1'0; replace e2' with e2'0; eauto.
  - inversion H; inversion H0; subst.
    + inversion H6; inversion H14; subst.
      replace a' with a'0; replace e' with e'0; eauto;
        replace s' with s'0 in *; eauto;
          eapply shift_determination; eauto.
  - inversion H; inversion H0; subst.
    + inversion H6; inversion H14; subst.
      replace a' with a'0; replace e' with e'0; eauto;
        replace s' with s'0 in *; eauto;
          eapply shift_determination; eauto.
Qed.

(** -------------------------- Shift and subst associativity ---------------------------*)

Lemma shift_through_subst : forall j s e r m k r' s' e',
  subst j s e r ->
  shift_basic_safe (1 + j + m) k true s s' ->
  shift_basic_safe (1 + j + m) k true e e' ->
  shift_basic_safe (1 + j + m) k true r r' ->
  subst j s' e' r'.
Proof.
  intros j s e; generalize dependent s; generalize dependent j;
  induction e; intros; subst.
  - inversion H; subst.
    + inversion H1; inversion H3; subst.
      * inversion H0. replace s' with r'.
        -- constructor.
        -- subst. eapply shift_determination; eauto.
           inversion H2; subst. auto.
      * lia.
    + inversion H1; inversion H3; subst.
      * inversion H2; inversion H4; subst; try lia.
        constructor; auto.
      * inversion H2; inversion H4; subst; try lia.
        constructor; lia.
  - inversion H1; inversion H3; subst.
    inversion H; subst.
    inversion H2; inversion H4; subst.
    constructor.
  - inversion H1; inversion H3; subst.
    inversion H; subst.
    inversion H2; inversion H4; subst.
    constructor.
    + eapply IHe1; eauto;
      constructor; auto.
    + eapply IHe2; eauto;
      constructor; auto.
  - inversion H1; inversion H3; subst.
    inversion H; subst.
    inversion H2; inversion H4; subst.
    econstructor.
    + eapply IHe1; eauto;
      constructor; auto.
    + constructor. apply shift_f_sats_shift.
    + remember (shift_basic_f 0 1 true s') as s''.
      rewrite <- shift_equiv_shift_f in Heqs''.
      eapply IHe2.
      * apply H11.
      * constructor. inversion H0; subst. inversion H9; subst. 
        rewrite shift_equiv_shift_f in *.
        subst. Check shift_assoc_plus_plus'.
        replace (1 + j + m) with (1 + j + m + 0) by lia.
        rewrite <- shift_assoc_plus_plus'.
        replace (1 + (1 + j + m) + 0) with (1 + (1 + j) + m) by lia.
        reflexivity.
      * replace (1 + (1 + j) + m) with (1 + (1 + j + m)) by lia.
        constructor; auto.
      * replace (1 + (1 + j) + m) with (1 + (1 + j + m)) by lia.
        constructor; auto.
  - inversion H1; inversion H3; subst.
    inversion H; subst.
    inversion H2; inversion H4; subst.
    econstructor.
    + eapply IHe1; eauto;
      constructor; auto.
    + constructor. apply shift_f_sats_shift.
    + remember (shift_basic_f 0 1 true s') as s''.
      rewrite <- shift_equiv_shift_f in Heqs''.
      eapply IHe2.
      * apply H11.
      * constructor. inversion H0; subst. inversion H9; subst. 
        rewrite shift_equiv_shift_f in *.
        subst. Check shift_assoc_plus_plus'.
        replace (1 + j + m) with (1 + j + m + 0) by lia.
        rewrite <- shift_assoc_plus_plus'.
        replace (1 + (1 + j + m) + 0) with (1 + (1 + j) + m) by lia.
        reflexivity.
      * replace (1 + (1 + j) + m) with (1 + (1 + j + m)) by lia.
        constructor; auto.
      * replace (1 + (1 + j) + m) with (1 + (1 + j + m)) by lia.
        constructor; auto.
Qed.

Lemma shift_through_subst' : forall j m k s e,
  shift_basic_f (1 + j + m) k true (subst_f j s e) =
  subst_f j (shift_basic_f (1 + j + m) k true s) (shift_basic_f (1 + j + m) k true e).
Proof.
  intros. remember (subst_f j s e) as r.
  remember (shift_basic_f (1 + j + m) k true r) as r'.
  remember (shift_basic_f (1 + j + m) k true s) as s'.
  remember (shift_basic_f (1 + j + m) k true e) as e'.
  rewrite <- shift_equiv_shift_f in *.
  rewrite <- subst_equiv_subst_f in *.
  apply shift_basic_plus in Heqr', Heqs', Heqe'.
  eapply shift_through_subst; eauto.
Qed.