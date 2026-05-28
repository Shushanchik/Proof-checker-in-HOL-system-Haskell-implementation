From HOL Require Import ExprAxiomsRules.
From HOL Require Import Shift.
From HOL Require Import Subst.
From HOL Require Import NormalForms.
From HOL Require Import BetaStep.
From HOL Require Import Infer.
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

Fixpoint beta_potential_f (e : expr) : nat :=
  match e with
    | app e1 e2 => match e1 with
                     | lmb _ _ => if beta_potential_f e2 <=? beta_potential_f e1
                                   then 1 + beta_potential_f e1
                                   else 1 + beta_potential_f e2
                     | e1      => if beta_potential_f e2 <=? beta_potential_f e1
                                  then beta_potential_f e1
                                  else beta_potential_f e2
                   end
    | lmb a e   => if beta_potential_f e <=? beta_potential_f a
                   then beta_potential_f a
                   else beta_potential_f e
    | pi e1 e2  => if beta_potential_f e2 <=? beta_potential_f e1
                   then beta_potential_f e1
                   else beta_potential_f e2
    | _ => 0
  end
.

Inductive beta_potential : expr -> nat -> Prop :=
  | beta_potential_of_redex_1 : forall a e n1 s n2,
    beta_potential (lmb a e) n1 ->
    beta_potential s n2 ->
    n2 <= n1 ->
    beta_potential (app (lmb a e) s) (1 + n1)
  | beta_potential_of_redex_2 : forall a e n1 s n2,
    beta_potential (lmb a e) n1 ->
    beta_potential s n2 ->
    n1 <  n2 ->
    beta_potential (app (lmb a e) s) (1 + n2)
  | beta_potential_of_app_1 : forall e1 n1 e2 n2,
    na e1 ->
    beta_potential e1 n1 ->
    beta_potential e2 n2 ->
    n2 <= n1 ->
    beta_potential (app e1 e2) n1
  | beta_potential_of_app_2 : forall e1 n1 e2 n2,
    na e1 ->
    beta_potential e1 n1 ->
    beta_potential e2 n2 ->
    n1 <  n2 ->
    beta_potential (app e1 e2) n2
  | beta_potential_of_lmb_1 : forall a n1 e n2,
    beta_potential a n1 ->
    beta_potential e n2 ->
    n2 <= n1 ->
    beta_potential (lmb a e) n1
  | beta_potential_of_lmb_2 : forall a n1 e n2,
    beta_potential a n1 ->
    beta_potential e n2 ->
    n1 <  n2 ->
    beta_potential (lmb a e) n2
  | beta_potential_of_pi_1 : forall e1 n1 e2 n2,
    beta_potential e1 n1 ->
    beta_potential e2 n2 ->
    n2 <= n1 ->
    beta_potential (pi e1 e2) n1
  | beta_potential_of_pi_2 : forall e1 n1 e2 n2,
    beta_potential e1 n1 ->
    beta_potential e2 n2 ->
    n1 <  n2 ->
    beta_potential (pi e1 e2) n2
  | beta_potential_of_cst : forall c,
    beta_potential (cst c) 0
  | beta_potential_of_idx : forall i,
    beta_potential (idx i) 0
.

Lemma beta_potential_f_sats_beta_potential : forall e,
  beta_potential e (beta_potential_f e).
Proof.
  induction e; try (simpl; constructor).
  - simpl. destruct e1.
    + simpl in *. destruct (beta_potential_f e2 <=? 0) eqn:Eq.
      * rewrite Nat.leb_le in Eq.
        inversion Eq. rewrite H0.
        econstructor.
        -- constructor. reflexivity.
        -- constructor.
        -- apply IHe2.
        -- auto.
      * eapply beta_potential_of_app_2.
        -- constructor. reflexivity.
        -- apply IHe1.
        -- apply IHe2.
        -- rewrite Nat.leb_nle in Eq. lia.
    + simpl in *. destruct (beta_potential_f e2 <=? 0) eqn:Eq.
      * rewrite Nat.leb_le in Eq.
        inversion Eq. rewrite H0.
        econstructor.
        -- constructor. reflexivity.
        -- constructor.
        -- apply IHe2.
        -- auto.
      * eapply beta_potential_of_app_2.
        -- constructor. reflexivity.
        -- apply IHe1.
        -- apply IHe2.
        -- rewrite Nat.leb_nle in Eq. lia.
    + remember (app e1_1 e1_2) as e1.
      destruct (beta_potential_f e2 <=? beta_potential_f e1) eqn:Eq.
      * econstructor.
        -- rewrite Heqe1. constructor. reflexivity.
        -- auto.
        -- apply IHe2.
        -- rewrite Nat.leb_le in Eq. auto.
      * eapply beta_potential_of_app_2.
        -- rewrite Heqe1. constructor. reflexivity.
        -- apply IHe1.
        -- auto.
        -- rewrite Nat.leb_gt in Eq. auto.
    + remember (lmb e1_1 e1_2) as e1.
      destruct (beta_potential_f e2 <=? beta_potential_f e1) eqn:Eq.
      * replace (S (beta_potential_f e1)) with (1 + beta_potential_f e1) by lia.
        subst. eapply beta_potential_of_redex_1.
        -- auto.
        -- apply IHe2.
        -- rewrite Nat.leb_le in Eq. auto.
      * replace (S (beta_potential_f e2)) with (1 + beta_potential_f e2) by lia.
        subst. eapply beta_potential_of_redex_2.
        -- eauto.
        -- auto.
        -- rewrite Nat.leb_gt in Eq. lia.
    + remember (pi e1_1 e1_2) as e1.
      destruct (beta_potential_f e2 <=? beta_potential_f e1) eqn:Eq.
      * econstructor.
        -- rewrite Heqe1. constructor. reflexivity.
        -- auto.
        -- apply IHe2.
        -- rewrite Nat.leb_le in Eq. auto.
      * eapply beta_potential_of_app_2.
        -- rewrite Heqe1. constructor. reflexivity.
        -- apply IHe1.
        -- auto.
        -- rewrite Nat.leb_gt in Eq. auto.
  - simpl.
    destruct (beta_potential_f e2 <=? beta_potential_f e1) eqn:Eq.
    + econstructor; eauto.
      rewrite Nat.leb_le in Eq. auto.
    + eapply beta_potential_of_lmb_2; eauto.
      rewrite Nat.leb_gt in Eq. auto.
  - simpl.
    destruct (beta_potential_f e2 <=? beta_potential_f e1) eqn:Eq.
    + econstructor; eauto.
      rewrite Nat.leb_le in Eq. auto.
    + eapply beta_potential_of_pi_2; eauto.
      rewrite Nat.leb_gt in Eq. auto.
Qed.

Lemma beta_potential_equiv_beta_potential_f : forall e n,
  beta_potential e n <-> n = beta_potential_f e.
Proof.
  intros; split; intros; [induction H | idtac]; intros; subst.
  - simpl in *. destruct (beta_potential_f e <=? beta_potential_f a) eqn:Eq.
    + rewrite <- Nat.leb_le in H1. rewrite H1. auto.
    + rewrite <- Nat.leb_le in H1. rewrite H1. auto.
  - simpl in *. destruct (beta_potential_f e <=? beta_potential_f a) eqn:Eq.
    + rewrite <- Nat.leb_gt in H1. rewrite H1. auto.
    + rewrite <- Nat.leb_gt in H1. rewrite H1. auto.
  - simpl. destruct e1.
    + simpl in *. rewrite <- Nat.leb_le in H2. rewrite H2. auto.
    + simpl in *. rewrite <- Nat.leb_le in H2. rewrite H2. auto.
    + rewrite <- Nat.leb_le in H2. rewrite H2. auto.
    + apply na_lmb_is_false in H;contradiction.
    + rewrite <- Nat.leb_le in H2. rewrite H2. auto.
  - simpl. assert (F : beta_potential_f e2 <=? beta_potential_f e1 = false).
    { rewrite Nat.leb_nle. lia. } destruct e1; rewrite F; auto.
    apply na_lmb_is_false in H; contradiction.
  - simpl. rewrite <- Nat.leb_le in H1. rewrite H1. auto.
  - assert (F : beta_potential_f e <=? beta_potential_f a = false).
    { rewrite Nat.leb_nle. lia. }
    simpl. rewrite F. auto.
  - simpl. rewrite <- Nat.leb_le in H1. rewrite H1. auto.
  - assert (F : beta_potential_f e2 <=? beta_potential_f e1 = false).
    { rewrite Nat.leb_nle. lia. }
    simpl. rewrite F. auto.
  - reflexivity.
  - reflexivity.
  - apply beta_potential_f_sats_beta_potential.
Qed.

Lemma shift_preserves_beta_potential : forall e n m k p e',
  beta_potential e n ->
  shift_basic_safe m k p e e' ->
  beta_potential e' n.
Proof.
  induction e; intros.
  - inversion H; subst. inversion H0; [inversion H1 | inversion H2]; constructor.
  - inversion H; subst. inversion H0; [inversion H1 | inversion H2]; constructor.
  - inversion H; subst.
    + inversion H0; subst.
      * inversion H1; subst. inversion H10; subst. econstructor.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst. inversion H11; subst. econstructor.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus; eauto.
        -- assumption.
    + inversion H0; subst.
      * inversion H1; subst. inversion H10; subst.
        eapply beta_potential_of_redex_2.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst. inversion H11; subst.
        eapply beta_potential_of_redex_2.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus; eauto.
        -- assumption.
    + inversion H0; subst.
      * inversion H1; subst. econstructor.
        -- eapply shift_preserves_na; eauto. constructor; eauto.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst. econstructor.
        -- eapply shift_preserves_na; eauto.
           eapply shift_basic_minus; eauto.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus; eauto.
        -- assumption.
    + inversion H0; subst.
      * inversion H1; subst.
        eapply beta_potential_of_app_2.
        -- eapply shift_preserves_na; eauto. constructor; eauto.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst.
        eapply beta_potential_of_app_2.
        -- eapply shift_preserves_na; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus; eauto.
        -- assumption.
  - inversion H; subst.
    + inversion H0; subst.
      * inversion H1; subst. econstructor.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst. econstructor.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus.
           ++ assert (F : k <= 1 + m) by lia. apply F.
           ++ eauto.
        -- assumption.
    + inversion H0; subst.
      * inversion H1; subst.
        eapply beta_potential_of_lmb_2.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst.
        eapply beta_potential_of_lmb_2.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus.
           ++ assert (F : k <= 1 + m) by lia. apply F.
           ++ eauto.
        -- assumption.
  - inversion H; subst.
    + inversion H0; subst.
      * inversion H1; subst. econstructor.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst. econstructor.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus.
           ++ assert (F : k <= 1 + m) by lia. apply F.
           ++ eauto.
        -- assumption.
    + inversion H0; subst.
      * inversion H1; subst.
        eapply beta_potential_of_pi_2.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
        -- assumption.
      * inversion H2; subst.
        eapply beta_potential_of_pi_2.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus.
           ++ assert (F : k <= 1 + m) by lia. apply F.
           ++ eauto.
        -- assumption.
Qed.

Fixpoint redex_amount_f (e : expr) : nat :=
  match e with
    | app e1 e2 => match e1 with
                     | lmb a t =>
                        1 + redex_amount_f a + redex_amount_f t + redex_amount_f e2
                     | _ => redex_amount_f e1 + redex_amount_f e2
                   end
    | lmb a e => redex_amount_f a + redex_amount_f e
    | pi e1 e2 => redex_amount_f e1 + redex_amount_f e2
    | _ => 0
  end
.

Inductive redex_amount : expr -> nat -> Prop :=
  | redex_amount_in_idx : forall i,
      redex_amount (idx i) 0
  | redex_amount_in_cst : forall c,
      redex_amount (cst c) 0
  | redex_amount_in_app_r : forall a e n1 e2 n2,
      redex_amount (lmb a e) n1 ->
      redex_amount e2 n2 ->
      redex_amount (app (lmb a e) e2) (1 + n1 + n2)
  | redex_amount_in_app : forall e1 n1 e2 n2,
      na e1 ->
      redex_amount e1 n1 ->
      redex_amount e2 n2 ->
      redex_amount (app e1 e2) (n1 + n2)
  | redex_amount_in_lmb : forall a n1 e n2,
      redex_amount a n1 ->
      redex_amount e n2 ->
      redex_amount (lmb a e) (n1 + n2)
  | redex_amount_in_pi : forall e1 n1 e2 n2,
      redex_amount e1 n1 ->
      redex_amount e2 n2 ->
      redex_amount (pi e1 e2) (n1 + n2)
.

Lemma redex_amount_f_sats_redex_amount : forall e,
  redex_amount e (redex_amount_f e).
Proof.
  induction e; try (simpl; constructor); auto.
  destruct e1.
  - simpl in *. replace (redex_amount_f e2) with (0 + redex_amount_f e2) by lia.
      repeat constructor. auto.
  - simpl in *. replace (redex_amount_f e2) with (0 + redex_amount_f e2) by lia.
      repeat constructor. auto.
  - repeat constructor; auto.
  - simpl. constructor; auto.
  - simpl. constructor; auto. constructor; auto.
Qed.

Lemma redex_amount_equiv_redex_amount_f : forall e n,
  redex_amount e n <-> n = redex_amount_f e.
Proof.
  intros; split; intros;
  [induction H | subst; apply redex_amount_f_sats_redex_amount]; auto.
  - simpl. subst. simpl. lia.
  - destruct e1; try (simpl; subst; simpl; lia).
    apply na_lmb_is_false in H; contradiction.
  - simpl. subst. simpl. lia.
  - simpl. subst. simpl. lia.
Qed.

Lemma shift_preserves_redex_amount : forall e n m k p e',
  redex_amount e n ->
  shift_basic_safe m k p e e' ->
  redex_amount e' n.
Proof.
  induction e; intros.
  - inversion H; subst.
    inversion H0; [inversion H1 | inversion H2]; subst; constructor.
  - inversion H; subst.
    inversion H0; [inversion H1 | inversion H2]; subst; constructor.
  - inversion H; subst.
    + inversion H0; subst.
      * inversion H1; subst. inversion H9; subst. constructor; auto.
        -- eapply IHe1; eauto. constructor; eauto.
        -- eapply IHe2; eauto. constructor; eauto.
      * inversion H2; subst. inversion H10; subst. constructor; auto.
        -- eapply IHe1; eauto. eapply shift_basic_minus; eauto.
        -- eapply IHe2; eauto. eapply shift_basic_minus; eauto.
    + inversion H0; subst.
      * inversion H1; subst; constructor.
        -- eapply shift_preserves_na; eauto. constructor; eauto.
        -- eapply IHe1; auto. constructor; eauto.
        -- eapply IHe2; auto. constructor; eauto.
      * inversion H2; subst. constructor.
        -- eapply shift_preserves_na; eauto.
           eapply shift_basic_minus; eauto.
        -- eapply IHe1; auto.
           eapply shift_basic_minus; eauto.
        -- eapply IHe2; auto.
           eapply shift_basic_minus; eauto.
  - inversion H; subst. inversion H0; subst.
    + inversion H1; subst. constructor.
      * eapply IHe1; eauto. constructor; eauto.
      * eapply IHe2; eauto. constructor; eauto.
    + inversion H2; subst. constructor.
      * eapply IHe1; eauto. eapply shift_basic_minus; eauto.
      * eapply IHe2; auto. eapply shift_basic_minus.
        -- assert (F : k <= 1 + m) by lia. apply F.
        -- auto.
  - inversion H; subst. inversion H0; subst.
    + inversion H1; subst. constructor.
      * eapply IHe1; eauto. constructor; eauto.
      * eapply IHe2; eauto. constructor; eauto.
    + inversion H2; subst. constructor.
      * eapply IHe1; eauto. eapply shift_basic_minus; eauto.
      * eapply IHe2; auto. eapply shift_basic_minus.
        -- assert (F : k <= 1 + m) by lia. apply F.
        -- auto.
Qed.

Lemma somefact : forall e e',
  beta_step e e' ->
  beta_potential_f e' < beta_potential_f e \/
  redex_amount_f e' < redex_amount_f e.
Proof.
  intros; induction H.
  - simpl.
    remember (beta_potential_f e1) as bpn_e1.
    remember (beta_potential_f a) as bpn_a.
    remember (beta_potential_f e2) as bpn_e2.
    remember (beta_potential_f e1'') as bpn_e1''.
    remember (redex_amount_f a) as ran_a.
    remember (redex_amount_f e1) as ran_e1.
    remember (redex_amount_f e2) as ran_e2.
    remember (redex_amount_f e1'') as ran_e1''.
    rewrite <- beta_potential_equiv_beta_potential_f in *.
    rewrite <- redex_amount_equiv_redex_amount_f in *.
    destruct (bpn_e1 <=? bpn_a) eqn:Eq1.
    + destruct (bpn_e2 <=? bpn_a) eqn:Eq2.
      * left.
Admitted.

Fixpoint degree_f (e : expr) :=
  match e with
    | pi e1 e2 => if degree_f e2 <=? degree_f e1
                  then 1 + degree_f e1
                  else 1 + degree_f e2
    | _ => 0
  end
.

Inductive is_pi : expr -> Prop :=
  | pi_is_pi : forall e1 e2,
      is_pi (pi e1 e2)
.

Inductive degree : expr -> nat -> Prop := 
  | degree_of_pi_1 : forall e1 n1 e2 n2,
      degree e1 n1 ->
      degree e2 n2 ->
      n2 <= n1 ->
      degree (pi e1 e2) (1 + n1)
  | degree_of_pi_2 : forall e1 n1 e2 n2,
      degree e1 n1 ->
      degree e2 n2 ->
      n1 < n2 ->
      degree (pi e1 e2) (1 + n2)
  | degree_of_type : forall e,
      ~ is_pi e ->
      degree e 0
.

Lemma degree_f_sats_degree : forall e,
  degree e (degree_f e).
Proof.
  induction e; try (simpl; constructor; intros contra; inversion contra).
  simpl. destruct (degree_f e2 <=? degree_f e1) eqn:Eq.
  - eapply degree_of_pi_1; eauto. rewrite <- Nat.leb_le; auto.
  - eapply degree_of_pi_2; eauto. rewrite <- Nat.leb_gt; auto.
Qed.

Lemma degree_equiv_degree_f : forall e n,
  degree e n <-> n = degree_f e.
Proof.
  intros; split; intros; [induction H | idtac].
  - subst. simpl. rewrite <- Nat.leb_le in H1.
    rewrite H1. reflexivity.
  - subst. simpl. rewrite <- Nat.leb_gt in H1.
    rewrite H1. reflexivity.
  - destruct e; try reflexivity.
    assert (F : is_pi (pi e1 e2)) by constructor.
    contradiction.
  - subst. apply degree_f_sats_degree.
Qed.

Theorem shift_preserves_degree : forall e n m k p e',
  degree e n ->
  shift_basic_safe m k p e e' ->
  degree e' n.
Proof.
  intros; generalize dependent e'; generalize dependent p;
  generalize dependent k; generalize dependent m; induction H; intros.
  - inversion H2; [inversion H3 | inversion H4]; subst.
    + econstructor.
      * eapply IHdegree1; constructor; eauto.
      * eapply IHdegree2; constructor; eauto.
      * lia.
    + econstructor.
      * eapply IHdegree1; eapply shift_basic_minus; eauto.
      * eapply IHdegree2; eapply shift_basic_minus.
        -- assert (F : k <= (1 + m)) by lia; eauto.
        -- eauto.
      * lia.
  - inversion H2; [inversion H3 | inversion H4]; subst.
    + eapply degree_of_pi_2.
      * eapply IHdegree1; constructor; eauto.
      * eapply IHdegree2; constructor; eauto.
      * lia.
    + eapply degree_of_pi_2.
      * eapply IHdegree1; eapply shift_basic_minus; eauto.
      * eapply IHdegree2; eapply shift_basic_minus.
        -- assert (F : k <= (1 + m)) by lia; eauto.
        -- eauto.
      * lia.
  - destruct e;
      try (inversion H0; [inversion H1 | inversion H2]; subst; constructor;
      intros contra; inversion contra).
    + subst. assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
    + subst. assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
Qed.

Lemma degree_determined : forall e n1 n2,
  degree e n1 ->
  degree e n2 ->
  n1 = n2.
Proof.
  induction e; intros.
  - inversion H; inversion H0; reflexivity.
  - inversion H; inversion H0; reflexivity.
  - inversion H; inversion H0; subst. reflexivity.
  - inversion H; inversion H0; subst. reflexivity.
  - inversion H; inversion H0; subst.
    + replace n4 with n0; try reflexivity.
      eapply IHe1; eauto.
    + replace n4 with n0 in *.
      * replace n5 with n3 in *; try lia.
        eapply IHe2; auto.
      * eapply IHe1; auto.
    + assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
    + replace n4 with n0 in *.
      * replace n5 with n3 in *; try lia.
        eapply IHe2; auto.
      * eapply IHe1; auto.
    + replace n5 with n3 in *; auto.
    + assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
    + assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
    + assert (F : is_pi (pi e1 e2)) by constructor; contradiction.
    + auto.
Qed.

Inductive redex_height : expr -> nat -> Prop :=
  | height_of_redex : forall a gamma e b n s,
      infer (a :: gamma) e b ->
      degree (pi a b) n ->
      redex_height (app (lmb a e) s) n
.

Lemma redex_height_determined : forall e n1 n2,
  redex_height e n1 -> redex_height e n2 -> n1 = n2.
Proof.
  intros. inversion H; inversion H0; subst.
  inversion H7; subst.
Qed.

(*Lemma shift_preserves_height : forall ,
  shift_basic_safe
Proof.
  
Admitted.*)

(** m e = (h_max e, amount_of h e) 
    m  ->
    redex_heigt (app (lmb a e) s) n
    m (app (lmb a e) s) (1 + prev_res) 1

    h_max t n = forall a e s, multi_sub_term (app (lmb a e) s) t ->
                              redex_height (app (lmb a e) s) n' ->
                              n' <= n

    
    
*)

Inductive measure : expr -> nat -> nat -> Prop :=
  | measure_beta_rule : forall a e s n,
      redex_height (app (lmb a e) s) n ->
      measure (app (lmb a e) s) n 1
  | measure_app_na_0 : forall e1 h n1 e2 n2,
      na e1 ->
      measure e1 h n1 ->
      measure e2 h n2 ->
      measure (app e1 e2) h (n1 + n2)
  | measure_app_na_1 : forall e1 h1 n1 e2 h2 n2,
      na e1 ->
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h2 < h1 ->
      measure (app e1 e2) h1 n1
  | measure_app_na_2 : forall e1 h1 n1 e2 h2 n2,
      na e1 ->
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h1 < h2 ->
      measure (app e1 e2) h2 n2
  | measure_lmb_0 : forall a h n1 e n2,
      measure a h n1 ->
      measure e h n2 ->
      measure (lmb a e) h (n1 + n2)
  | measure_lmb_1 : forall e1 h1 n1 e2 h2 n2,
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h2 < h1 ->
      measure (lmb e1 e2) h1 n1
  | measure_lmb_2 : forall e1 h1 n1 e2 h2 n2,
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h1 < h2 ->
      measure (lmb e1 e2) h2 n2
  | measure_pi_0 : forall a h n1 e n2,
      measure a h n1 ->
      measure e h n2 ->
      measure (pi a e) h (n1 + n2)
  | measure_pi_1 : forall e1 h1 n1 e2 h2 n2,
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h2 < h1 ->
      measure (pi e1 e2) h1 n1
  | measure_pi_2 : forall e1 h1 n1 e2 h2 n2,
      measure e1 h1 n1 ->
      measure e2 h2 n2 ->
      h1 < h2 ->
      measure (pi e1 e2) h2 n2
  | measure_cst : forall c,
      measure (cst c) 0 1
  | measure_idx : forall i,
      measure (idx i) 0 1
.

Lemma measure_determined : forall e h1 n1 h2 n2,
  measure e h1 n1 -> measure e h2 n2 -> h1 = h2 /\ n1 = n2.
Proof.
  intros; generalize dependent n2; generalize dependent h2; induction H; intros.
  - inversion H0; subst.
    * split; auto. eapply redex_height_determined; eauto.
Qed.

Theorem shift_preserves_measure : forall e h n m k p e',
  measure e h n ->
  shift_basic_safe m k p e e' ->
  measure e' h n.
Proof.
  intros; generalize dependent e'; generalize dependent p;
  generalize dependent k; generalize dependent m;
  induction H; intros.
  - inversion H0.
    + inversion H1; subst.
      inversion H12; subst.
      constructor. inversion H; subst. econstructor.
Admitted.

Theorem beta_step_flattens_measure : forall e e' h n h' n',
  beta_step e e' ->
  measure e h n ->
  measure e' h' n' ->
  h' < h \/ h' = h /\ n' < n.
Proof.
  induction e; intros.
  - inversion H.
  - inversion H.
  - generalize dependent n'; generalize dependent h';
    generalize dependent n; generalize dependent h;
    inversion H; subst.
    + induction e'; intros.
      * inversion H1; subst.
        inversion H0; subst.
        -- inversion H10; subst.
           inversion H11; left; try lia.
           assert (F : is_pi (pi a b)) by constructor; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
      * inversion H1; subst.
        inversion H0; subst.
        -- inversion H10; subst.
           inversion H11; left; try lia.
           assert (F : is_pi (pi a b)) by constructor; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
        -- apply na_lmb_is_false in H7; contradiction.
      * inversion H5; inversion H6; subst.
        inversion H3; subst.
        -- inversion H2; inversion H7; subst.
           inversion H0; subst.
           ++ inversion H13; subst.
              inversion H14; subst.
              ** replace n2 with n1 in *.
                 --- admit.
                 --- admit.
              ** admit.
              ** admit.
           ++ admit.
           ++ admit.
           ++ admit.
        -- admit.
      * admit.
      * admit.
    + admit.
    + admit.
  - inversion H; subst.
    + inversion H0; inversion H1; subst.
      * eapply IHe1 in H5.
        -- destruct H5 as [H5 | [Eq H5]].
           ++ left. apply H5.
           ++ 
Qed.

Theorem normalization : forall gamma e T,
  infer gamma e T ->
  exists e', nf e' /\ multistep e e'.
Proof.
  intros; induction H.
  - exists (cst c). split; repeat constructor.
  - exists (idx 0). split; repeat constructor.
  - destruct IHinfer1 as [e [Hnf Hms]].
    assert (L : shift_safe 1 true e (shift_f 1 true e)).
    { constructor. apply shift_f_sats_shift. }
    remember (shift_f 1 true e) as e'.
    unfold shift_f in Heqe'.
    rewrite <- shift_equiv_shift_f in Heqe'.
    apply shift_basic_plus in Heqe'.
    eapply shift_preserves_multistep in Hms.
    + eapply shift_preserves_nf in Hnf.
      exists e'. split.
      -- apply shift_safe_is_shift in Heqe'.
           rewrite shift_equiv_shift_f in Heqe'.
           subst. apply Hnf.
      -- apply Hms.
    + apply H1.
    + apply L.
  - 
Qed.
