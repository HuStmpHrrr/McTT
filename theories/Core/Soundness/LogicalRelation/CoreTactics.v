From Equations Require Import Equations.

From Stdlib Require Import Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
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
    | H : ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
    | H : ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
    (** and of an element of a record type *)
    | H : record_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
    | H : record_glu_exp _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H
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

(** ** The Gluing Judgments *)

(** Open the case of a rule: fix a sound embedding, read every premise at
    its target, take the universes apart, and state a universe at the
    target by its two parts. *)
Ltac glu_intro :=
  unfold glu_ctx, glu_exp, glu_is_univ in *; intros;
  repeat match goal with IH : forall _ _, glu_emb _ _ _ _ -> _, Hμ : glu_emb _ _ _ _ |- _ =>
    specialize (IH _ _ Hμ) end;
  repeat match goal with H : glu_is_univ_at _ _ _ _ |- _ => destruct H end;
  try match goal with |- glu_is_univ_at _ _ _ _ => constructor end.

(** The syntactic judgments of the source, moved along the sound embedding
    to its target ([emb_preserves_wf]). *)
Ltac glu_emb_wf :=
  match goal with Hμ : glu_emb _ _ _ _ |- _ =>
    let Hem := fresh "Hem" in
    pose proof (gem_emb _ _ _ _ Hμ) as Hem;
    let Hwc := fresh "Hwc" in let Hwe := fresh "Hwe" in let Hweq := fresh "Hweq" in
    let Hwst := fresh "Hwst" in let Hwx := fresh "Hwx" in let Hwu := fresh "Hwu" in
    let Hwm := fresh "Hwm" in
    destruct (emb_preserves_wf _ _ _ _ Hem) as (Hwc & Hwe & Hweq & Hwst & Hwx & Hwu & Hwm) end.
