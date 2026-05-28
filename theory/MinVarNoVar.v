From HOL Require Import ExprAxiomsRules.
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


(** --------------- Variables that are minimal or even not in expr    ------------------*)

Fixpoint min_var (e : expr) : option nat :=
  match e with
    | idx i => Some i
    | cst c => None
    | app e1 e2 => match min_var e1, min_var e2 with
                     | None,    None    => None
                     | Some i1, None    => Some i1
                     | None,    Some i2 => Some i2
                     | Some i1, Some i2 => if i1 <=? i2
                                           then Some i1
                                           else Some i2
                   end
    | lmb a e  => match min_var a, min_var e with
                    | None,    None    => None
                    | Some i1, None    => Some i1
                    | None,    Some i2 => Some i2
                    | Some i1, Some i2 => if i1 <=? i2
                                          then Some i1
                                          else Some i2
                 end
    | pi a e  => match min_var a, min_var e with
                   | None,    None    => None
                   | Some i1, None    => Some i1
                   | None,    Some i2 => Some i2
                   | Some i1, Some i2 => if i1 <=? i2
                                         then Some i1
                                         else Some i2
                 end
  end
.

Inductive no_var : nat -> expr -> Prop := 
  | no_var_idx : forall i j,
      i <> j ->
      no_var i (idx j)
  | no_var_cst : forall i c,
      no_var i (cst c)
  | no_var_app : forall i e1 e2,
      no_var i e1 ->
      no_var i e2 ->
      no_var i (app e1 e2)
  | no_var_lmb : forall i a e,
      no_var i a ->
      no_var (i+1) e ->
      no_var i (lmb a e)
  | no_var_pi : forall i e1 e2,
      no_var i e1 ->
      no_var (i+1) e2 ->
      no_var i (pi e1 e2)
.

Fixpoint no_var_f (i : nat) (e : expr) : bool :=
  match e with
    | idx j => negb (i =? j)
    | cst _ => true
    | app e1 e2 => no_var_f i e1 && no_var_f  i    e2
    | lmb a  e  => no_var_f i a  && no_var_f (i+1) e
    | pi  e1 e2 => no_var_f i e1 && no_var_f (i+1) e2
  end
.

Lemma no_var_spec : forall i e,
  reflect (no_var i e) (no_var_f i e).
Proof.
  intros i e; generalize dependent i;
  induction e; intros; apply iff_reflect; split; intros.
  - inversion H; subst. simpl. destruct (i =? n) eqn:Eq.
    + rewrite (Nat.eqb_eq) in Eq. lia.
    + reflexivity.
  - inversion H. destruct (i =? n) eqn:Eq.
    + discriminate.
    + constructor. intros contra; subst. inversion H.
      rewrite Nat.eqb_refl in H2. discriminate.
  - constructor.
  - constructor.
  - simpl. inversion H; subst.
    destruct (IHe1 i); try contradiction.
    destruct (IHe2 i); try contradiction.
    reflexivity.
  - simpl in H. 
    destruct (IHe1 i); try discriminate.
    destruct (IHe2 i); try discriminate.
    constructor; auto.
  - simpl. inversion H; subst.
    destruct (IHe1 i); try contradiction.
    destruct (IHe2 (i + 1)); try contradiction.
    reflexivity.
  - simpl in H. 
    destruct (IHe1 i); try discriminate.
    destruct (IHe2 (i + 1)); try discriminate.
    constructor; auto.
  - simpl. inversion H; subst.
    destruct (IHe1 i); try contradiction.
    destruct (IHe2 (i + 1)); try contradiction.
    reflexivity.
  - simpl in H. 
    destruct (IHe1 i); try discriminate.
    destruct (IHe2 (i + 1)); try discriminate.
    constructor; auto.
Qed.
