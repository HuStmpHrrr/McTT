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

(** Two witnesses and the two facts about them: an existential, or a record
    of that shape ([suniv_glu_typ], [glu_typ_at]). *)
Ltac glu_witness2 := first [ do 2 eexists; split | econstructor ].

(** Take apart one hypothesis that is a record-shaped gluing predicate, as
    [destruct_all] does a conjunction. *)
Ltac destruct_glu_record1 :=
  match goal with
  | H : level_glu_exp_pred _ _ _ _ _ _ |- _ => destruct H
  | H : level_glu_exp _ _ _ _ _ _ |- _ => destruct H
  | H : suniv_glu_typ_pred _ _ _ _ |- _ => destruct H
  | H : suniv_glu_typ _ _ _ _ |- _ => destruct H
  | H : univ_glu_exp_pred' _ _ _ _ _ _ _ |- _ => destruct H
  | H : univ_glu_exp _ _ _ _ _ _ _ |- _ => destruct H
  | H : suniv_glu_exp_pred' _ _ _ _ _ _ _ |- _ => destruct H
  | H : suniv_glu_exp _ _ _ _ _ _ _ |- _ => destruct H
  | H : univ_glu_exp_pred _ _ _ _ _ _ |- _ => destruct H
  | H : suniv_glu_exp_pred _ _ _ _ _ _ |- _ => destruct H
  | H : glu_typ_at _ _ _ _ |- _ => destruct H
  | H : glu_univ_typ _ _ _ _ |- _ => destruct H
  end.

Ltac destruct_glu_records := repeat destruct_glu_record1.

(** The gluing of an element of an inductive type, taken apart only where
    the scripts ask for it: its components are read by name elsewhere. *)
Ltac destruct_ind_glu_exp :=
  repeat match goal with
    | H : ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
    | H : ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
    end.

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
  | _ => destruct_glu_record1
  end.
