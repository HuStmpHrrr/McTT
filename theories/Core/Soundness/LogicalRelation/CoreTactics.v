From Equations Require Import Equations.

From Stdlib Require Import Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions.

(** State the universes below a level, [glu_univ_below i j], by
    [glu_univ_below_spec], wherever [uidx_lt j i] is known. *)
Ltac rewrite_glu_univ_below :=
  repeat match goal with
    | H : context [glu_univ_below ?i ?j] |- _ =>
        rewrite (glu_univ_below_spec i j) in H by solve_uidx
    | |- context [glu_univ_below ?i ?j] =>
        rewrite (glu_univ_below_spec i j) by solve_uidx
    end.

Ltac basic_invert_glu_univ_elem H :=
  progress simp glu_univ_elem in H;
  unmark_vars;
  dependent destruction H;
  rewrite_glu_univ_below;
  try rewrite <- glu_univ_elem_equation_1 in *.

Ltac basic_glu_univ_elem_econstructor :=
  progress simp glu_univ_elem;
  econstructor;
  rewrite_glu_univ_below;
  try rewrite <- glu_univ_elem_equation_1 in *.

Ltac invert_glu_rel1 :=
  match goal with
  | H : pi_glu_typ_pred _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : pi_glu_exp_pred _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_typ_pred _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_exp_pred _ _ _ _ _ _ |- _ =>
      progressive_invert H
  end.
