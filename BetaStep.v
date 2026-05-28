From HOL Require Import ExprAxiomsRules.
From HOL Require Import Shift.
From HOL Require Import Subst.
From HOL Require Import NormalForms.
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

(** -------------------- Beta-step definition ------------------------- *)

Inductive beta_step : expr -> expr -> Prop :=
  | beta_rule : forall a e1 e1' e1'' e2 e2',
      shift_safe 1 true e2 e2' ->
      subst 0 e2' e1 e1' ->
      shift_basic_safe 1 1 false e1' e1'' ->
      beta_step (app (lmb a e1) e2) e1''
  | beta_step_app_rule1 : forall e1 e2 e1',
      na e1 ->
      beta_step e1 e1' ->
      beta_step (app e1 e2) (app e1' e2)
  | beta_step_app_rule2 : forall e1 e2 e2',
      nanf e1 ->
      beta_step e2 e2' ->
      beta_step (app e1 e2) (app e1 e2')
  | beta_step_lmb_rule1 : forall a e a',
      beta_step a a' ->
      beta_step (lmb a e) (lmb a' e)
  | beta_step_lmb_rule2 : forall a e e',
      nf a ->
      beta_step e e' ->
      beta_step (lmb a e) (lmb a e')
  | beta_step_pi_rule1 : forall a e a',
      beta_step a a' ->
      beta_step (pi a e) (pi a' e)
  | beta_step_pi_rule2 : forall a e e',
      nf a ->
      beta_step e e' ->
      beta_step (pi a e) (pi a e')
.

(** --------------------- Progress theorem, weak version --------------------*)

Theorem not_beta_step_and_nf : forall e,
  ~ ((exists e', beta_step e e') /\ nf e).
Proof.
  intros e; induction e; intros [[e' Hbs] Hnf].
  - inversion Hbs.
  - inversion Hbs.
  - inversion Hbs; subst.
    + inversion Hnf; subst.
      inversion H; subst.
      inversion H5.
    + inversion Hnf; inversion H; subst.
      apply nanf_is_nf in H5. apply IHe1; split; eauto.
    + inversion Hnf; inversion H; subst.
      apply IHe2; split; eauto.
  - inversion Hbs; subst.
    + inversion Hnf; subst.
      * apply IHe1; split; eauto.
      * inversion H; subst.
    + inversion Hnf; subst.
      * apply IHe2; split; eauto.
      * inversion H; subst.
  - inversion Hbs; subst.
    + inversion Hnf; subst.
      apply IHe1; split; eauto.
      inversion H; subst. auto.
    + inversion Hnf; subst.
      apply IHe2; split; eauto.
      inversion H; subst. auto.
Qed.

(** ------------------------- Beta-step is determined ------------------------*)

Lemma beta_step_determination : forall e e1 e2,
  beta_step e e1 ->
  beta_step e e2 ->
  e1 = e2.
Proof.
  induction e; intros.
  - inversion H.
  - inversion H.
  - inversion H; inversion H0; subst.
    + replace e2'0 with e2' in *.
      * inversion H7; subst.
        replace e1'0 with e1' in *.
        -- apply shift_safe_is_shift in H6, H12.
           eapply shift_determination; eauto.
        -- eapply subst_determination; eauto.
      * unfold shift_safe in *;
        apply shift_safe_is_shift in H3, H9.
        eapply shift_determination; eauto.
    + apply na_lmb_is_false in H9. contradiction.
    + apply nanf_is_na in H9. apply na_lmb_is_false in H9. contradiction.
    + apply na_lmb_is_false in H3. contradiction.
    + replace e1'0 with e1'; auto.
    + apply nanf_is_nf in H8.
      assert (contra : False).
      { apply (not_beta_step_and_nf e1); split; eauto. }
      contradiction.
    + inversion H3.
    + inversion H3; subst.
      * inversion H10.
      * inversion H10; subst.
        -- inversion H1.
        -- apply nanf_is_nf in H1.
           assert (contra : False).
           { apply (not_beta_step_and_nf e0); split; eauto. }
           contradiction.
        -- assert (contra : False).
           { apply (not_beta_step_and_nf e3); split; eauto. }
           contradiction.
      * inversion H10; subst.
        -- assert (contra : False).
           { apply (not_beta_step_and_nf a); split; eauto. }
           contradiction.
        -- assert (contra : False).
           { apply (not_beta_step_and_nf e); split; eauto. }
           contradiction.
      * inversion H10.
    + replace e2'0 with e2'.
      * reflexivity.
      * apply IHe2; auto.
  - inversion H; inversion H0; subst.
    + replace a'0 with a'.
      * reflexivity.
      * auto.
    + assert (contra : False).
      { apply (not_beta_step_and_nf e1); split; eauto. }
      contradiction.
    + assert (contra : False).
      { apply (not_beta_step_and_nf e1); split; eauto. }
      contradiction.
    + replace e'0 with e'.
      * reflexivity.
      * auto.
  - inversion H; inversion H0; subst.
    + replace a'0 with a'.
      * reflexivity.
      * auto.
    + assert (contra : False).
      { apply (not_beta_step_and_nf e1); split; eauto. }
      contradiction.
    + assert (contra : False).
      { apply (not_beta_step_and_nf e1); split; eauto. }
      contradiction.
    + replace e'0 with e'.
      * reflexivity.
      * auto.
Qed.

(** ----------------- Shift preserves possibility of beta-step -------------------*)

Theorem shift_preserves_beta_step : forall e e' m k e1 e1',
  beta_step e e' ->
  shift_basic_safe m k true e  e1  ->
  shift_basic_safe m k true e' e1' ->
  beta_step e1 e1'.
Proof.
  induction e; intros.
  (* e = idx n *)
  - inversion H.
  (* e =  cst *)
  - inversion H.
  (* e = app e1 e2 *)
  - inversion H; subst.
    + inversion H0; subst; inversion H2; subst.
      inversion H11; subst.
      econstructor.
      * constructor. apply shift_f_sats_shift.
      * apply subst_f_sats_subst.
      * rewrite shift_equiv_shift_f in H15, H13; subst.
        replace (shift_basic_f 0 1 true (shift_basic_f m k true e2))
          with (shift_basic_f (1 + m) k true (shift_basic_f 0 1 true e2)).
        -- constructor; try lia.
           
           remember (subst_f 0 
                            (shift_basic_f (1 + m) k true 
                                  (shift_basic_f 0 1 true e2)
                            )
                            (shift_basic_f (1 + m) k true 
                                  e3)
                    ) as sub.
           rewrite <- shift_through_subst' in Heqsub. subst.
           rewrite shift_equiv_shift_f. replace (1 + 0 + m) with (1 + m + 0) by lia.
           rewrite <- shift_assoc_minus_plus'.
           ++ replace (shift_basic_f (1 + 0) 1 false (subst_f 0 (shift_basic_f 0 1 true e2) e3)) with e'.
              ** replace (m + 0) with m by lia.
                 rewrite <- shift_equiv_shift_f. apply shift_safe_is_shift; auto.
              ** simpl. replace (subst_f 0 (shift_basic_f 0 1 true e2) e3) with e1'0.
                 --- rewrite <- shift_equiv_shift_f. apply shift_safe_is_shift; auto.
                 --- replace (shift_basic_f 0 1 true e2) with e2'.
                     +++ rewrite <- subst_equiv_subst_f; auto.
                     +++ rewrite <- shift_equiv_shift_f. apply shift_safe_is_shift; auto.
           ++ apply no_var_after_subst_f. replace 1 with (0 + 1) by lia; apply no_var_after_shift_f; lia.
        -- replace m with (m + 0) by lia. rewrite <- shift_assoc_plus_plus'.
           replace (1 + m + 0) with (1 + (m + 0)) by lia; reflexivity.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e2'0 with e2'.
      * constructor.
        -- eapply shift_preserves_na; eauto. constructor. eauto.
        -- eapply IHe1; eauto; constructor; eauto.
      * eapply shift_determination; eauto.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e1'0 with e1'1.
      * constructor.
        -- rewrite shift_equiv_shift_f in H17. 
           subst. eapply shift_preserves_nanf; eauto.
        -- eapply IHe2; eauto; constructor; eauto.
      * eapply shift_determination; eauto.
  - inversion H; subst.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e'1 with e'0.
      * constructor.
        eapply IHe1; eauto; constructor; eauto.
      * eapply shift_determination; auto; [apply H15 | apply H18].
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace a'0 with a'.
      * constructor.
        -- rewrite shift_equiv_shift_f in H14. subst.
           apply shift_preserves_nf; auto.
        -- eapply IHe2; eauto; constructor; eauto.
      * eapply shift_determination; auto; [apply H14 | apply H17].
  - inversion H; subst.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e'1 with e'0.
      * constructor.
        eapply IHe1; eauto; constructor; eauto.
      * eapply shift_determination; auto; [apply H15 | apply H18].
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace a'0 with a'.
      * constructor.
        -- rewrite shift_equiv_shift_f in H14. subst.
           apply shift_preserves_nf; auto.
        -- eapply IHe2; eauto; constructor; eauto.
      * eapply shift_determination; auto; [apply H14 | apply H17].
Qed.

Theorem shift_preserves_beta_step' : forall e e' m k e1 e1',
  beta_step e1 e1' ->
  shift_basic_safe m k true e  e1  ->
  shift_basic_safe m k true e' e1' ->
  beta_step e e'.
Proof.
  intros e e' m k e1; generalize dependent k; generalize dependent m;
  generalize dependent e'; generalize dependent e; induction e1; intros.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + inversion H0; inversion H2; subst.
      inversion H16; subst.
      econstructor.
      * constructor. apply shift_f_sats_shift.
      * apply subst_f_sats_subst.
      * constructor; try lia.
        inversion H1; inversion H7; inversion H4; subst.
        rewrite shift_equiv_shift_f in *.
        rewrite subst_equiv_subst_f in *.
        subst e1'0. subst e2' e1. subst e1_2.
        eapply shift_injection.
        -- constructor. rewrite shift_equiv_shift_f; apply H3.
        -- constructor. rewrite shift_equiv_shift_f.
           replace (shift_basic_f m k true
  (shift_basic_f 1 1 false (subst_f 0 (shift_basic_f 0 1 true e3) e)))
             with  (shift_basic_f (m + 0) k true
  (shift_basic_f (1 + 0) 1 false (subst_f 0 (shift_basic_f 0 1 true e3) e))).
           ++ rewrite shift_assoc_minus_plus'.
              ** replace (shift_basic_f (1 + m + 0) k true (subst_f 0 (shift_basic_f 0 1 true e3) e)) 
                   with  (subst_f 0 (shift_basic_f 0 1 true (shift_basic_f m k true e3))
                     (shift_basic_f (1 + m) k true e)); auto.
                 replace (1 + m + 0) with (1 + 0 + m) by lia.
                 rewrite shift_through_subst'.
                 replace (shift_basic_f 0 1 true (shift_basic_f m k true e3))
                   with (shift_basic_f (1 + 0 + m) k true (shift_basic_f 0 1 true e3)); auto.
                 replace (1 + 0 + m) with (1 + m + 0) by lia.
                 rewrite shift_assoc_plus_plus'.
                 replace (m + 0) with m by lia; auto.
              ** apply no_var_after_subst_f.
                 replace 1 with (0 + 1) by lia.
                 apply no_var_after_shift_f; lia.
           ++ replace (m + 0) with m by lia.
              replace (1 + 0) with 1 by lia.
              reflexivity.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      eapply shift_preserves_na' in H4.
      * replace e3 with e2.
        -- constructor; eauto.
           eapply IHe1_1; eauto; constructor; eauto.
        -- eapply shift_injection; constructor; eauto.
      * constructor. eauto.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e0 with e1 in *.
      * constructor.
        -- eapply shift_preserves_nanf'; try (apply H4).
           apply shift_basic_plus in H15. apply H15.
        -- eapply IHe1_2; try (apply H6).
           ++ constructor. apply H16.
           ++ constructor. apply H19.
      * eapply shift_injection; constructor; eauto.
  - inversion H; subst.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e0 with e1.
      * constructor. eapply IHe1_1; try (apply H5).
        -- constructor. apply H14.
        -- constructor. apply H17.
      * eapply shift_injection.
        -- constructor; eauto.
        -- constructor; eauto.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace a0 with a in *.
      * constructor.
        ++ eapply shift_preserves_nf'; try (apply H4).
           apply shift_basic_plus in H18; eauto.
        ++ eapply IHe1_2; try (apply H6).
           ** constructor; eauto.
           ** constructor; eauto.
      * eapply shift_injection; constructor; eauto.
  - inversion H; subst.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace e0 with e1.
      * constructor. eapply IHe1_1; try (apply H5).
        -- constructor. apply H14.
        -- constructor. apply H17.
      * eapply shift_injection.
        -- constructor; eauto.
        -- constructor; eauto.
    + inversion H0; inversion H2; subst.
      inversion H1; inversion H3; subst.
      replace a0 with a in *.
      * constructor.
        ++ eapply shift_preserves_nf'; try (apply H4).
           apply shift_basic_plus in H18; eauto.
        ++ eapply IHe1_2; try (apply H6).
           ** constructor; eauto.
           ** constructor; eauto.
      * eapply shift_injection; constructor; eauto.
Qed.


(** -------------------- Beta-step-and-shift diamond -----------------------------*)

Lemma shift_surjection_if_beta_step : forall d k m m' e',
  shift_basic_safe d (1 + k) true m m' ->
  beta_step m' e' ->
  exists e, shift_basic_safe d (1 + k) true e e'.
Proof.
  intros d k m m' e'; generalize dependent m'; generalize dependent m;
  generalize dependent d; generalize dependent k; induction e'; intros.
  - inversion H0; subst.
    Check (Nat.leb_spec d n).
    destruct (Nat.leb_spec d n).
    + inversion H3; inversion H6; subst; try lia.
      * inversion H; subst; try lia.
        replace n with 0 in * by lia.
        inversion H2; subst; try lia.
        inversion H1; inversion H8; lia.
      * inversion H2; subst.
        -- inversion H1; inversion H7; subst; try lia.
           destruct i0.
           ++ inversion H; inversion H8; subst.
              inversion H22; subst; try lia.
           ++ destruct (Nat.leb_spec d i0).
              ** inversion H; inversion H9; subst.
                 inversion H23; subst; try lia.
                 replace (i + S k + 1 - 1) with (i + (1 + k)) by lia.
                 exists (idx i). constructor. constructor; lia.
              ** replace d with (i0 + 1) in * by lia.
                 inversion H; inversion H9; subst.
                 inversion H23; subst; try lia.
        -- inversion H; inversion H7; subst.
           inversion H20; inversion H17; subst; try lia.
           destruct i0; try lia.
           replace (S i0 + S k - 1) with (i0 + (1 + k)) by lia.
           exists (idx i0). constructor. constructor. lia.
    + exists (idx n). constructor. constructor; lia.
  - exists (cst c). constructor. constructor.
  - inversion H0; subst.
    + inversion H3; inversion H5; subst.
      inversion H2; subst; try lia.
      * inversion H1; inversion H6; subst.
        inversion H; inversion H7; subst.
        inversion H23; subst.
        exists (app e6 e7). constructor. constructor.
        -- replace e'1 with e1 in *; auto.
           rewrite shift_equiv_shift_f in H19, H16; subst.
           replace (shift_basic_f 1 1 false (shift_basic_f 0 1 true e1))
              with (shift_basic_f (0 + 1) 1 false (shift_basic_f 0 1 true e1)).
           ++ rewrite <- shift_f_additivity_plus_minus_1; try lia. simpl.
              apply shift_f_by_0.
           ++ simpl. reflexivity.
        -- replace e'2 with e4 in *; auto.
           rewrite shift_equiv_shift_f in H20, H17; subst.
           replace (shift_basic_f 1 1 false (shift_basic_f 0 1 true e4))
              with (shift_basic_f (0 + 1) 1 false (shift_basic_f 0 1 true e4)).
           ++ rewrite <- shift_f_additivity_plus_minus_1; try lia. simpl.
              apply shift_f_by_0.
           ++ simpl. reflexivity.
      * inversion H; inversion H6; subst.
        inversion H21. inversion H18; subst.
        rewrite shift_equiv_shift_f in H16; subst.
        rewrite subst_equiv_subst_f in H11; subst.
        rename e7 into y.
        rewrite shift_equiv_shift_f in H27; subst.
        rename e8 into z.
        rewrite shift_equiv_shift_f in H28; subst.
        rename e6 into s.
        rename e2' into s'.
        rewrite shift_equiv_shift_f in H22; subst.
        inversion H1; subst. rewrite shift_equiv_shift_f in H7; subst.
        rewrite shift_equiv_shift_f in H17; subst.
        rewrite subst_equiv_subst_f in H12; subst.
        eexists. constructor. constructor.
        -- rewrite shift_equiv_shift_f.
           replace (shift_basic_f 0 1 true (shift_basic_f d (1 + k) true s))
             with (shift_basic_f (d + 1) (1 + k) true (shift_basic_f 0 1 true s)).
           ++ replace (d + 1) with (1 + d) by lia;
              replace (1 + d) with (1 + 0 + d) by lia.
              rewrite <- shift_through_subst'.
              remember (subst_f 0 (shift_basic_f 0 1 true s) y) as yr.
              replace (shift_basic_f 1 1 false (shift_basic_f (1 + 0 + d) 1 true yr))
                with (shift_basic_f (1 + 0) 1 false (shift_basic_f (1 + 0 + d) 1 true yr)).
              ** replace (1 + 0 + d) with (1 + d + 0) by lia.
                 rewrite <- shift_assoc_minus_plus'.
                 --- replace (d + 0) with d by lia.
                     remember (shift_basic_f (1 + 0) 1 false yr).
                     subst. reflexivity.
                 --- subst. apply no_var_after_subst_f.
                     replace 1 with (0 + 1) by lia.
                     apply no_var_after_shift_f; lia.
              ** reflexivity.
           ++ replace d with (d + 0) by lia.
              replace (d + 0 + 1) with (1 + d + 0) by lia.
              apply shift_assoc_plus_plus'.
        -- rewrite shift_equiv_shift_f.
           replace (shift_basic_f 0 1 true (shift_basic_f d (1 + k) true s))
             with (shift_basic_f (d + 1) (1 + k) true (shift_basic_f 0 1 true s)).
           ++ replace (d + 1) with (1 + d) by lia;
              replace (1 + d) with (1 + 0 + d) by lia.
              rewrite <- shift_through_subst'.
              remember (subst_f 0 (shift_basic_f 0 1 true s) z) as zr.
              replace (shift_basic_f 1 1 false (shift_basic_f (1 + 0 + d) 1 true zr))
                with (shift_basic_f (1 + 0) 1 false (shift_basic_f (1 + 0 + d) 1 true zr)).
              ** replace (1 + 0 + d) with (1 + d + 0) by lia.
                 rewrite <- shift_assoc_minus_plus'.
                 --- replace (d + 0) with d by lia.
                     remember (shift_basic_f (1 + 0) 1 false zr).
                     subst. reflexivity.
                 --- subst. apply no_var_after_subst_f.
                     replace 1 with (0 + 1) by lia.
                     apply no_var_after_shift_f; lia.
              ** reflexivity.
           ++ replace d with (d + 0) by lia.
              replace (d + 0 + 1) with (1 + d + 0) by lia.
              apply shift_assoc_plus_plus'.
    + inversion H; inversion H1; subst.
      eapply IHe'1 in H5.
      * destruct H5 as [e1' H5].
        inversion H5; subst.
        exists (app e1' e2); constructor; constructor; eauto.
      * constructor. apply H14.
    + inversion H; inversion H1; subst.
      eapply IHe'2 in H5.
      * destruct H5 as [e2' H5]. inversion H5; subst.
        exists (app e1 e2'). constructor. constructor; eauto.
      * constructor. eauto.
  - inversion H0; subst.
    + inversion H3; inversion H5; subst.
      inversion H2; subst.
      * inversion H1; inversion H6; subst.
        simpl in *. inversion H; inversion H7; subst.
        inversion H22; inversion H23; subst.
        simpl in *. inversion H15; subst; try lia.
        rewrite shift_equiv_shift_f in *.
        rewrite subst_equiv_subst_f in *.
        clear H13 H15. subst e'1 e'2.
        subst a0 e0. subst a1 e1. exists (lmb a3 e4).
        constructor. constructor.
        -- rewrite shift_equiv_shift_f.
           replace (shift_basic_f 0 1 true (shift_basic_f d (1 + k) true a3))
             with (shift_basic_f (1 + d + 0) (1 + k) true (shift_basic_f 0 1 true a3)) in *.
           ++ Check shift_f_additivity_plus_minus_1.
              replace (shift_basic_f 1 1 false
                        (shift_basic_f 0 1 true (shift_basic_f d (S k) true a3)))
                with (shift_basic_f (0 + 1) 1 false
                       (shift_basic_f 0 1 true (shift_basic_f d (S k) true a3)))
                  by auto.
              rewrite <- shift_f_additivity_plus_minus_1; try lia.
              simpl. symmetry. apply shift_f_by_0.
           ++ Check shift_assoc_plus_plus'.
              replace d with (d + 0) by lia.
              replace (1 + (d + 0) + 0) with (1 + d + 0) by lia.
              apply shift_assoc_plus_plus'.
        -- rewrite shift_equiv_shift_f. replace (S d) with (d + 1) by lia.
           rewrite <- shift_assoc_plus_plus'.
           rewrite <- shift_assoc_minus_plus'.
           ++ Check shift_f_additivity_plus_minus_1.
              rewrite <- shift_f_additivity_plus_minus_1; try lia.
              simpl. rewrite <- shift_f_by_0.
              replace (S d) with (d + 1) by lia; reflexivity.
           ++ replace (shift_basic_f 1 1 true e4)
                with (shift_basic_f 1 (0 + 1) true e4) by auto.
              apply no_var_after_shift_f; lia.
      * simpl in *. inversion H12; subst.
        inversion H1; inversion H; subst.
        inversion H11; inversion H20; inversion H29; subst.
        simpl in *. rewrite shift_equiv_shift_f in *.
        rewrite subst_equiv_subst_f in *.
        subst e'1 e'2. rewrite H8, H13. subst e2' a1 s' e e2.
        replace (shift_basic_f 0 1 true (shift_basic_f d (S k) true e3))
          with (shift_basic_f (1 + d) (1 + k) true (shift_basic_f 0 1 true e3)).
        -- replace (S d) with (1 + d) by lia. replace (1 + d) with (1 + 0 + d) by lia.
           Check shift_through_subst'.
           rewrite <- shift_through_subst'.
           Check shift_assoc_minus_plus'.
           replace (1 + 0 + d) with (1 + d + 0) by lia.
           rewrite <- shift_assoc_minus_plus' with (m1 := 0).
           ++ remember (shift_basic_f (1 + 0) 1 false
                          (subst_f 0 (shift_basic_f 0 1 true e3) a3)).
              Check shift_assoc_plus_plus'.
              rewrite <- shift_assoc_plus_plus'.
              Check shift_through_subst'.
              replace (1 + (1 + d) + 0) with (1 + 1 + d) by lia.
              replace (S (1 + d + 0)) with (1 + 1 + d) by lia.
              rewrite <- shift_through_subst'.
              Check shift_assoc_minus_plus'.
              replace 2 with (1 + 1) by lia. replace (1 + 1 + d) with (1 + d + 1) by lia.
              rewrite <- shift_assoc_minus_plus'.
              ** remember (shift_basic_f (1 + 1) 1 false
                              (subst_f 1 (shift_basic_f 0 1 true (shift_basic_f 0 1 true e3))
                                 e5)).
                 exists (lmb e e1). constructor. constructor.
                 --- replace (d + 0) with d by lia.
                     apply shift_f_sats_shift.
                 --- replace (d + 1) with (1 + d) by lia.
                     apply shift_f_sats_shift.
              ** apply no_var_after_subst_f.
                 Check shift_after_shift.
                 rewrite shift_after_shift with (k' := 1); try lia. simpl.
                 replace (shift_basic_f 1 1 true (shift_basic_f 0 1 true e3))
                   with (shift_basic_f 1 (0 + 1) true (shift_basic_f 0 1 true e3))
                     by auto.
                 apply no_var_after_shift_f; try lia.
           ++ apply no_var_after_subst_f.
              replace 1 with (0 + 1) by lia.
              apply no_var_after_shift_f; try lia.
        -- Check shift_assoc_plus_plus'.
           replace d with (d + 0) by lia.
           replace (1 + (d + 0)) with (1 + d + 0) by lia.
           apply shift_assoc_plus_plus'.
    + inversion H; inversion H1; subst. eapply IHe'1 in H3; try (constructor; eauto).
      destruct H3 as [e1 H3]. inversion H3; subst.
      rewrite shift_equiv_shift_f in *. subst e'2 e'1.
      exists (lmb e1 e0). constructor. constructor; apply shift_f_sats_shift.
    + inversion H; inversion H1; subst. eapply IHe'2 in H5.
      * destruct H5 as [e0 H5]. inversion H5.
        exists (lmb a e0). constructor; constructor; eauto.
      * constructor; eauto.
  - inversion H0; subst.
    + inversion H3; inversion H5; subst.
      inversion H2; subst.
      * inversion H1; inversion H6; subst.
        simpl in *. inversion H; inversion H7; subst.
        inversion H22; inversion H23; subst.
        simpl in *. inversion H15; subst; try lia.
        rewrite shift_equiv_shift_f in *.
        rewrite subst_equiv_subst_f in *.
        clear H13 H15. subst e'1 e'2.
        subst a0 e0. subst a1 e1. exists (pi a3 e4).
        constructor. constructor.
        -- rewrite shift_equiv_shift_f.
           replace (shift_basic_f 0 1 true (shift_basic_f d (S k) true a3))
             with (shift_basic_f (1 + d + 0) (1 + k) true (shift_basic_f 0 1 true a3)) in *.
           ++ Check shift_assoc_minus_plus'. rewrite <- shift_assoc_minus_plus'.
              ** replace (1 + 0) with (0 + 1) by lia.
                 rewrite <- shift_f_additivity_plus_minus_1; try lia.
                 simpl. rewrite <- shift_f_by_0.
                 replace (d + 0) with d by lia. reflexivity.
              ** replace 1 with (0 + 1) by lia. apply no_var_after_shift_f; lia.
           ++ Check shift_assoc_plus_plus'.
              replace d with (d + 0) by lia.
              replace (1 + (d + 0) + 0) with (1 + d + 0) by lia.
              apply shift_assoc_plus_plus'.
        -- rewrite shift_equiv_shift_f. replace (S d) with (d + 1) by lia.
           rewrite <- shift_assoc_plus_plus'.
           rewrite <- shift_assoc_minus_plus'.
           ++ Check shift_f_additivity_plus_minus_1.
              rewrite <- shift_f_additivity_plus_minus_1; try lia.
              simpl. rewrite <- shift_f_by_0.
              replace (S d) with (d + 1) by lia; reflexivity.
           ++ replace (shift_basic_f 1 1 true e4)
                with (shift_basic_f 1 (0 + 1) true e4) by auto.
              apply no_var_after_shift_f; lia.
      * simpl in *. inversion H12; subst.
        inversion H1; inversion H; subst.
        inversion H11; inversion H20; inversion H29; subst.
        simpl in *. rewrite shift_equiv_shift_f in *.
        rewrite subst_equiv_subst_f in *.
        subst e'1 e'2. rewrite H8, H13. subst e2' a1 s' e e2.
        replace (shift_basic_f 0 1 true (shift_basic_f d (S k) true e3))
          with (shift_basic_f (1 + d) (1 + k) true (shift_basic_f 0 1 true e3)).
        -- replace (S d) with (1 + d) by lia. replace (1 + d) with (1 + 0 + d) by lia.
           Check shift_through_subst'.
           rewrite <- shift_through_subst'.
           Check shift_assoc_minus_plus'.
           replace (1 + 0 + d) with (1 + d + 0) by lia.
           rewrite <- shift_assoc_minus_plus' with (m1 := 0).
           ++ remember (shift_basic_f (1 + 0) 1 false
                          (subst_f 0 (shift_basic_f 0 1 true e3) a3)).
              Check shift_assoc_plus_plus'.
              rewrite <- shift_assoc_plus_plus'.
              Check shift_through_subst'.
              replace (1 + (1 + d) + 0) with (1 + 1 + d) by lia.
              replace (S (1 + d + 0)) with (1 + 1 + d) by lia.
              rewrite <- shift_through_subst'.
              Check shift_assoc_minus_plus'.
              replace 2 with (1 + 1) by lia. replace (1 + 1 + d) with (1 + d + 1) by lia.
              rewrite <- shift_assoc_minus_plus'.
              ** remember (shift_basic_f (1 + 1) 1 false
                              (subst_f 1 (shift_basic_f 0 1 true (shift_basic_f 0 1 true e3))
                                 e5)).
                 exists (pi e e1). constructor. constructor.
                 --- replace (d + 0) with d by lia.
                     apply shift_f_sats_shift.
                 --- replace (d + 1) with (1 + d) by lia.
                     apply shift_f_sats_shift.
              ** apply no_var_after_subst_f.
                 Check shift_after_shift.
                 rewrite shift_after_shift with (k' := 1); try lia. simpl.
                 replace (shift_basic_f 1 1 true (shift_basic_f 0 1 true e3))
                   with (shift_basic_f 1 (0 + 1) true (shift_basic_f 0 1 true e3))
                     by auto.
                 apply no_var_after_shift_f; try lia.
           ++ apply no_var_after_subst_f.
              replace 1 with (0 + 1) by lia.
              apply no_var_after_shift_f; try lia.
        -- Check shift_assoc_plus_plus'.
           replace d with (d + 0) by lia.
           replace (1 + (d + 0)) with (1 + d + 0) by lia.
           apply shift_assoc_plus_plus'.
    + inversion H; inversion H1; subst. eapply IHe'1 in H3; try (constructor; eauto).
      destruct H3 as [e1 H3]. inversion H3; subst.
      rewrite shift_equiv_shift_f in *. subst e'2 e'1.
      exists (pi e1 e0). constructor. constructor; apply shift_f_sats_shift.
    + inversion H; inversion H1; subst. eapply IHe'2 in H5.
      * destruct H5 as [e0 H5]. inversion H5.
        exists (pi a e0). constructor; constructor; eauto.
      * constructor; eauto.
Qed.


(** -------------------- Introducing multi-beta-step ------------------------*)

Definition multistep : expr -> expr -> Prop := multi beta_step.

Lemma multistep_is_transitive : forall a b c,
  multistep a b -> multistep b c -> multistep a c.
Proof.
  intros; generalize dependent c; induction H; intros.
  - auto.
  - econstructor.
    + apply H.
    + apply IHmulti; auto.
Qed.

(** ------------------- Shift preserves multistep -------------------------*)

Lemma shift_preserves_multistep : forall a b m k a' b',
  multistep a b ->
  shift_basic_safe m k true a a' ->
  shift_basic_safe m k true b b' ->
  multistep a' b'.
Proof.
  intros a b m k a' b' Hms; generalize dependent b';
  generalize dependent a'; generalize dependent k;
  generalize dependent m; induction Hms; intros.
  - replace a' with b' in *.
    + constructor.
      
    + inversion H; inversion H0; subst.
      eapply shift_determination; eauto.
  - assert (shift_basic m k true y (shift_basic_f m k true y)) by (apply shift_f_sats_shift).
    assert (beta_step a' (shift_basic_f m k true y)).
    { eapply shift_preserves_beta_step; eauto.
      constructor; auto. }
    econstructor.
    + apply H3.
    + eapply IHHms; eauto. constructor. auto.
Qed.

Theorem shift_preserves_multistep' : forall e1 e1' m k e e',
  multistep e1 e1' ->
  shift_basic_safe m k true e  e1  ->
  shift_basic_safe m k true e' e1' ->
  multistep e e'.
Proof.
  intros; generalize dependent e'; generalize dependent e;
  generalize dependent k; generalize dependent m; induction H; intros.
  - replace e' with e in *.
    + constructor.
    + apply shift_reverse in H0, H1.
      inversion H0; inversion H1; subst.
      eapply shift_determination; eauto.
  - destruct k.
    + replace x with e in *.
      * econstructor.
        -- apply H.
        -- eapply IHmulti.
           ++ constructor. apply shift_by_0.
           ++ apply H2.
      * inversion H1; subst.
        rewrite shift_equiv_shift_f in H3.
        rewrite H3; apply shift_f_by_0.
    + replace (S k) with (1 + k) in * by lia.
      assert (Copy : beta_step x y) by auto.
      eapply shift_surjection_if_beta_step in H.
      * destruct H as [y' H].
        econstructor.
        -- eapply shift_preserves_beta_step'; eauto.
        -- eapply IHmulti; eauto.
      * eauto.
Qed.

(** --------------- Association of multistep and expression-constructors -------- *)

Lemma multistep_pi_1 : forall a a' b,
  multistep a a' ->
  multistep (pi a b) (pi a' b).
Proof.
  intros; generalize dependent b; induction H; intros.
  - constructor.
  - econstructor.
    + econstructor.
      apply H.
    + apply IHmulti.
Qed.

Lemma multistep_pi_2 : forall a b b',
  nf a -> multistep b b' ->
  multistep (pi a b) (pi a b').
Proof.
  intros; generalize dependent a;
  induction H0; intros.
  - constructor.
  - econstructor.
    + apply beta_step_pi_rule2; eauto.
    + apply IHmulti; auto.
Qed.

Lemma multistep_pi : forall a a' b b',
  multistep a a' ->
  nf a' ->
  multistep b b' ->
  multistep (pi a b) (pi a' b').
Proof.
  intros.
  apply multistep_is_transitive with (b := pi a' b).
  - apply multistep_pi_1; auto.
  - apply multistep_pi_2; auto.
Qed.

Lemma multistep_lmb_1 : forall a a' b,
  multistep a a' ->
  multistep (lmb a b) (lmb a' b).
Proof.
  intros; generalize dependent b.
  induction H; intros.
  - constructor.
  - econstructor.
    + constructor.
      apply H.
    + apply IHmulti.
Qed.

Lemma multistep_lmb_2 : forall a b b',
  nf a -> multistep b b' ->
  multistep (lmb a b) (lmb a b').
Proof.
  intros; generalize dependent a.
  induction H0; subst; intros.
  - constructor.
  - econstructor.
    + apply beta_step_lmb_rule2; eauto.
    + apply IHmulti; auto.
Qed.

Lemma multistep_lmb : forall a a' b b',
  multistep a a' ->
  nf a' ->
  multistep b b' ->
  multistep (lmb a b) (lmb a' b').
Proof.
  intros.
  apply multistep_is_transitive with (b := lmb a' b).
  - apply multistep_lmb_1; auto.
  - apply multistep_lmb_2; auto.
Qed.

(** ------------------- Beta-equivalence of expressions --------------------*)

Definition beta_equiv (a b : expr) : Prop :=
  exists c,
  (multistep a c \/ multistep c a) /\
  (multistep b c \/ multistep c b)
.