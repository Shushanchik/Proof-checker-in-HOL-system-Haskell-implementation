From HOL Require Import ExprAxiomsRules.
From HOL Require Import Shift.
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

(** ------------------- Not-Abstraction definition --------------------------*)

Definition na_f (e : expr) : bool :=
  match e with
    | lmb _ _ => false
    | _       => true
  end
.

Inductive na : expr -> Prop :=
  | na_from_f : forall e,
      na_f e = true -> na e
.

(** ---------------- Not-Abstraction is the same as not lambda -------------*)

Lemma na_lmb_is_false : forall a e,
  ~ na (lmb a e).
Proof.
  intros. intros contra.
  inversion contra. simpl in H. discriminate.
Qed.

Lemma na_or_abs : forall e,
  na e \/ exists a e', e = lmb a e'.
Proof.
  destruct e; try (left; constructor; reflexivity).
  right. eauto.
Qed.

(** --------------- Not-abstraction expression stays na after shift --------------*)

Lemma shift_preserves_na : forall e m k p e',
  na e -> shift_basic_safe m k p e e' -> na e'.
Proof.
  induction e; intros.
  - inversion H0; inversion H1; subst; constructor; simpl; try lia;
    inversion H2; constructor.
  - inversion H0; [(inversion H1) | (inversion H2)]; constructor; reflexivity.
  - inversion H; subst.
    inversion H0; inversion H2; subst; constructor; try reflexivity; inversion H3; constructor.
  - inversion H. apply na_lmb_is_false in H; contradiction.
  - inversion H0.
    + inversion H1. constructor. reflexivity.
    + inversion H2. constructor. reflexivity.
Qed.

(** --- Normal Form (nf) and Not-Abastraction Normal Form (nanf) definitions ---*)

Inductive nanf : expr -> Prop :=
  | varibale_value : forall i,
      nanf (idx i)
  | app_values : forall e1 e2,
      nanf e1 ->
      nf e2 ->
      nanf (app e1 e2)
  | pi_value : forall a e,
      nf a ->
      nf e ->
      nanf (pi a e)
  | const_value : forall c,
      nanf (cst c)
  with nf : expr -> Prop :=
  | abs_value : forall a e,
      nf a ->
      nf e ->
      nf (lmb a e)
  | nonabs_value : forall e,
      nanf e ->
      nf e
.

(** --------------------------- nanf = nf + na -------------------------------*)

Lemma nanf_is_nf : forall e,
  nanf e ->
  nf e.
Proof.
  intros e H; induction H; try (constructor; constructor; auto).
Qed.

Lemma nanf_is_na : forall e,
  nanf e -> na e.
Proof.
  intros. constructor. destruct (na_f e) eqn:Eq.
  - reflexivity.
  - destruct e; try discriminate.
    inversion H.
Qed.

(** ---------- Shift operation preserves normality and not-abstraction -----------*)

Lemma shift_preserves_nf : forall m k p e,
  nf e ->
  nf (shift_basic_f m k p e).
Proof.
  intros m k p e.
  generalize dependent p; generalize dependent k; generalize dependent m.
  induction e; intros; subst.
  - inversion H; inversion H0; subst.
    simpl. destruct (m <=? n), p; constructor; constructor.
  - inversion H; inversion H0; subst.
    simpl. repeat constructor.
  - inversion H; inversion H0; subst.
    simpl. constructor. constructor.
    + pose proof (nanf_is_nf e1 H4) as H2.
      apply (IHe1 m k p) in H2. inversion H2; subst; auto.
      rewrite <- shift_equiv_shift_f in H1.
      inversion H1; subst.
      inversion H0; subst.
      inversion H9.
    + auto.
  - simpl. inversion H; subst.
    + simpl. constructor; auto.
    + inversion H0.
  - simpl. inversion H; inversion H0; subst.
    simpl. constructor. constructor; auto. 
Qed.

Lemma shift_preserves_nanf : forall m k p e,
  nanf e ->
  nanf (shift_basic_f m k p e).
Proof.
  intros. generalize dependent p; generalize dependent k; generalize dependent m.
  induction H; intros; subst; simpl.
  - destruct (m <=? i), p; constructor.
  - constructor; auto. apply shift_preserves_nf. assumption.
  - constructor;
    apply shift_preserves_nf; assumption.
  - constructor.
Qed.

Lemma shift_preserves_na' : forall e' m k p e,
  na e' -> shift_basic_safe m k p e e' -> na e.
Proof.
  induction e'; intros; inversion H; 
    inversion H0; subst;
    try (inversion H3; constructor; reflexivity);
    try (inversion H4; constructor; reflexivity).
  - apply na_lmb_is_false in H; contradiction.
  - apply na_lmb_is_false in H; contradiction.
Qed.

Lemma shift_preserves_nf' : forall e' m k p e,
  nf e' -> shift_basic_safe m k p e e' -> nf e.
Proof.
  induction e'; intros; subst.
  - inversion H0; [inversion H1 | inversion H2]; subst; repeat constructor.
  - inversion H0; [inversion H1 | inversion H2]; subst; repeat constructor.
  - inversion H; inversion H1; subst.
    inversion H0; [inversion H2 | inversion H3]; subst; constructor; constructor.
    + assert (F : nf e'1). { apply nanf_is_nf; auto. }
      eapply IHe'1 in F; try (econstructor; apply H16).
      inversion F; subst.
      * inversion H16; subst. inversion H5.
      * auto.
    + apply shift_basic_plus in H17; eauto.
    + assert (F : nf e'1). { apply nanf_is_nf; auto. }
      apply shift_basic_minus in H17; try lia.
      eapply IHe'1 in F; try (apply H17).
      inversion F; subst.
      * inversion H17; inversion H9; subst. inversion H5.
      * auto.
    + apply shift_basic_minus in H18; try lia; eauto.
  - inversion H; subst.
    + inversion H0; [inversion H1 | inversion H2]; subst; constructor.
      * apply shift_basic_plus in H15. eapply IHe'1; eauto.
      * apply shift_basic_plus in H16. eapply IHe'2; eauto.
      * apply shift_basic_minus in H16; try lia. eapply IHe'1; eauto.
      * apply shift_basic_minus in H17; try lia. eapply IHe'2; eauto.
    + inversion H1.
  - inversion H; inversion H1; subst.
    inversion H0; [inversion H2 | inversion H3]; subst; constructor; constructor.
    + eapply IHe'1; auto. constructor; eauto.
    + eapply IHe'2; auto. constructor; eauto.
    + eapply IHe'1; auto. apply shift_basic_minus in H17; try lia. eauto.
    + eapply IHe'2; auto. apply shift_basic_minus in H18; try lia. eauto.
Qed.

Lemma shift_preserves_nanf' : forall e' m k p e,
  nanf e' -> shift_basic_safe m k p e e' -> nanf e.
Proof.
  induction e'; intros.
  - inversion H0; [inversion H1 | inversion H2]; subst; constructor.
  - inversion H0; [inversion H1 | inversion H2]; subst; constructor.
  - inversion H0; [inversion H1 | inversion H2]; subst; constructor;
    inversion H; subst.
    + eapply IHe'1; auto. constructor; apply H13.
    + eapply shift_preserves_nf'; eauto. constructor; apply H14.
    + eapply IHe'1; auto. apply shift_basic_minus in H14; try lia; apply H14.
    + eapply shift_preserves_nf'; eauto. apply shift_basic_minus in H15; try lia; apply H15.
  - inversion H.
  - inversion H0; [inversion H1 | inversion H2]; subst; constructor;
    inversion H; subst.
    + eapply shift_preserves_nf'; try (apply H4). apply shift_basic_plus in H13; apply H13.
    + eapply shift_preserves_nf'; try (apply H5). apply shift_basic_plus in H14; apply H14.
    + eapply shift_preserves_nf'; try (apply H5). apply shift_basic_minus in H14; try lia; apply H14.
    + eapply shift_preserves_nf'; try (apply H6). apply shift_basic_minus in H15; try lia; apply H15.
Qed.