From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.
Set Default Goal Selector "!".

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
    end
  end
.

Inductive sort : Type := 
  | prop
  | ast
  | box
.

Inductive const : Type :=
  | fromSort (s : sort)
.

Inductive expr : Type :=
  | idx (n : nat)
  | cst (c : const)
  | app (e1 e2 : expr)
  | lmb (d : expr) (e : expr)
  | pi  (d : expr) (e : expr)
.

Inductive axiom : const -> sort -> Type :=
  | axiom1 :
      axiom (fromSort prop) ast
  | axiom2 :
      axiom (fromSort ast) box
.

Inductive rule : sort -> sort -> sort -> Prop :=
  | rule1 :
      rule ast prop prop
  | rule2 :
      rule prop prop prop
  | rule3 :
      rule ast ast ast
.

Inductive sub_term : expr -> expr -> Prop :=
  | sub_term_app_1 : forall e1 e2,
      sub_term e1 (app e1 e2)
  | sub_term_app_2 : forall e1 e2,
      sub_term e2 (app e1 e2)
  | sub_term_lmb_1 : forall a e,
      sub_term a (lmb a e)
  | sub_term_lmb_2 : forall a e,
      sub_term e (lmb a e)
  | sub_term_pi_1 : forall e1 e2,
      sub_term e1 (pi e1 e2)
  | sub_term_pi_2 : forall e1 e2,
      sub_term e2 (pi e1 e2)
.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition multi_st : expr -> expr -> Prop := multi sub_term.