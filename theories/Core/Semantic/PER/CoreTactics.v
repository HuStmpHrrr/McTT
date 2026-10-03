From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Definitions.
Import Domain_Notations Fixed_Notations.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : Dom ?c ≈ ?c' ∈ ?in_rel0 |- _ =>
        unify in_rel0 in_rel;
        destruct (H _ _ H') as [];
        destruct_all;
        mark_with H' 1
    end;
  unmark_all_with 1.
Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_eval _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_app _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_rel_typ :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_typ _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_typ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    (** The bodies of a definition entry come with the types. *)
    | H : (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ ?in_rel), rel_elem _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_elem _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

(** Helper tactics for the universe/element PER. *)

(** State the universes below a level, [per_univ_below i j], by
    [per_univ_below_spec], wherever [j < i] is known. *)
Ltac rewrite_per_univ_below :=
  repeat match goal with
    | H : context [per_univ_below ?i ?j] |- _ =>
        rewrite (per_univ_below_spec i j) in H by lia
    | |- context [per_univ_below ?i ?j] =>
        rewrite (per_univ_below_spec i j) by lia
    end.

Ltac basic_invert_per_univ_elem H :=
  progress simp per_univ_elem in H;
  unmark_vars;
  dependent destruction H;
  rewrite_per_univ_below;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac basic_per_univ_elem_econstructor :=
  progress simp per_univ_elem;
  econstructor;
  rewrite_per_univ_below;
  try rewrite <- per_univ_elem_equation_1 in *.
