From HOL Require Import ExprAxiomsRules.
From HOL Require Import Shift.
From HOL Require Import Subst.
From HOL Require Import NormalForms.
From HOL Require Import BetaStep.
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

Inductive infer : list expr -> expr -> expr -> Prop :=
  | by_axiom : forall c s,
      axiom c s ->
      infer [] (cst c) (cst (fromSort s))
  | init_rule : forall gamma a s,
      infer gamma a (cst (fromSort s)) ->
      infer  (a :: gamma) (idx 0) a
  | thinning_rule : forall gamma m m' a a' b s,
      infer gamma m a ->
      infer gamma b (cst (fromSort s)) ->
      shift_safe 1 true m m' ->
      shift_safe 1 true a a' ->
      infer  (b :: gamma) m' a'
  | prod_rule : forall gamma a b s1 s2 s3,
      infer gamma a (cst (fromSort s1)) ->
      infer  (a :: gamma) b (cst (fromSort s2)) ->
      rule s1 s2 s3 ->
      infer gamma (pi a b) (cst (fromSort s3))
  | app_rule : forall gamma m a b n b',
      infer gamma m (pi a b) ->
      infer gamma n a ->
      subst 0 n b b' ->
      infer gamma (app m n) b'
  | abs_rule : forall gamma a m b s,
      infer (a :: gamma) m b ->
      infer gamma (pi a b) (cst (fromSort s)) ->
      infer gamma (lmb a m) (pi a b)
  | type_change_rule : forall gamma m a b s, 
      infer gamma m a ->
      infer gamma b s ->
      beta_equiv a b ->
      infer gamma m b
.

Theorem progress : forall t T,
  infer [] t T ->
  nf t \/ exists t', beta_step t t'.
Proof.
  intros t T H. induction H.
  (* by_axiom *)
  - left; repeat constructor.
  (* init_rule *)
  - left; repeat constructor.
  (* thinning_rule *)
  - destruct IHinfer1 as [IH1 | [m1 IH1]].
    + inversion H1; subst.
      left. rewrite shift_equiv_shift_f in H3.
      rewrite H3. apply shift_preserves_nf. auto.
    + right. eapply shift_preserves_beta_step in IH1.
      * eexists. apply IH1.
      * apply H1.
      * constructor. apply shift_f_sats_shift.
  (* prod_rule *)
  - destruct IHinfer1 as [IH1 | [a' IH1]].
    + destruct IHinfer2 as [IH2 | [b' IH2]].
      * left. constructor. constructor; auto.
      * right. exists (pi a b'). constructor; auto.
    + right. exists (pi a' b). constructor; auto.
  (* app_rule *)
  - destruct IHinfer1 as [IH1 | [m' IH1]].
    + inversion IH1; subst.
      * right. eexists. eapply beta_rule.
        -- constructor. apply shift_f_sats_shift.
        -- apply subst_f_sats_subst.
        -- constructor; try lia. apply shift_f_sats_shift.
      * destruct IHinfer2 as [IH2 | [n' IH2]].
        -- left. constructor. constructor; auto.
        -- right. exists (app m n'). constructor; auto.
    + right. destruct (na_or_abs m) as [L | [a' [e' L]]].
      * exists (app m' n). constructor; auto.
      * subst. eexists. eapply beta_rule.
        -- constructor. apply shift_f_sats_shift.
        -- apply subst_f_sats_subst.
        -- constructor; try lia. apply shift_f_sats_shift.
  (* abs_rule *)
  - destruct IHinfer1 as [IH1 | [m' IH1]].
    + destruct IHinfer2 as [IH2 | [p' IH2]].
      * inversion IH2; inversion H1; subst.
        left. constructor; auto.
      * inversion IH2; subst.
        -- right. exists (lmb a' m); constructor; auto.
        -- left. constructor; auto.
    + right. destruct IHinfer2 as [IH2 | [p' IH2]].
      * inversion IH2; inversion H1; subst.
        exists (lmb a m'). constructor; auto.
      * inversion IH2; subst.
        -- exists (lmb a' m); constructor; auto.
        -- exists (lmb a m'); constructor; auto.
  (* type_change_rule *)
  - destruct IHinfer1 as [IH1 | [m' IH1]].
    + left; auto.
    + right; eexists; eauto.
Qed.

Inductive valid_env : list expr -> Prop :=
  | valid_env_empty :
      valid_env []
  | valid_env_thinning : forall gamma a s,
      valid_env gamma ->
      infer gamma a (cst (fromSort s)) ->
      valid_env (a::gamma)
.

Theorem weakening : forall gamma e T gamma' e' T',
  infer gamma e T ->
  shift_safe (length gamma') true e e' ->
  shift_safe (length gamma') true T T' ->
  valid_env (gamma' ++ gamma) ->
  infer (gamma' ++ gamma) e' T'.
Proof.
  intros gamma e T gamma'; induction gamma'; intros.
  - simpl in *. inversion H0; inversion H1; subst.
    rewrite shift_equiv_shift_f in H3, H6.
    rewrite <- shift_f_by_0 in H3, H6. subst. assumption.
  - simpl in H2. inversion H2; subst.
    simpl. econstructor.
    + eapply IHgamma'; eauto.
      * constructor. apply shift_f_sats_shift.
      * constructor. apply shift_f_sats_shift.
    + apply H6.
    + constructor. rewrite shift_equiv_shift_f.
      rewrite shift_after_shift with (k' := length gamma'); try lia.
      rewrite <- shift_f_additivity_plus_plus.
      rewrite <- shift_equiv_shift_f.
      replace (Datatypes.length gamma' + 1) with (S (Datatypes.length gamma')) by lia.
      simpl in H0. inversion H0; auto.
    + constructor. rewrite shift_equiv_shift_f.
      rewrite shift_after_shift with (k' := length gamma'); try lia.
      rewrite <- shift_f_additivity_plus_plus.
      rewrite <- shift_equiv_shift_f.
      replace (Datatypes.length gamma' + 1) with (S (Datatypes.length gamma')) by lia.
      simpl in H1. inversion H1; auto.
Qed.

Lemma used_env_is_valid : forall gamma e T,
  infer gamma e T -> valid_env gamma.
Proof.
  intros; induction H; try auto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Theorem infer_determined : forall gamma1 e T1 gamma2 T2,
  infer gamma1 e T1 -> infer gamma2 e T2 -> T1 = T2.
Proof.
  intros; generalize dependent T2; generalize dependent gamma2;
  induction H; intros.
  - assert (F : infer [] (cst c) T2).
    { econstructor.  }
        
Qed.
