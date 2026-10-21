(** * Regressions for the Gluing of Groups

    [T (f : TF) := node (p : Phantom (T f) (f Z))], with
    [Phantom (A B) := mk (a : A)]: the view [Phantom (T f) (f Z)] has a
    phantom argument.  An element glued at [T] at [f := g] is glued at [T]
    at a [g'] whose readback agrees with [g]'s: the gluing of the type at
    [g] is one at [g'] ([t_over_phantom_glu_moves]), as for every pair of
    related types ([glu_univ_elem_resp_per_univ]), at the relation of
    [Semantic.Inductives.Regressions.t_over_phantom_related]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
From Mctt.Core.Semantic.Inductives Require Import Regressions.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions CoreLemmas.
Import Domain_Notations.

Section PhantomGluing.
  Context {GC : GCtx}.
  Variables (pP pT pmP pmT : qname) (TA TB TF SP ST Z : exp).

  Hypothesis HlP : ind_lookup gc_deps gc_stack pP = Some (phantom_group pmP TA TB SP).
  Hypothesis HlT : ind_lookup gc_deps gc_stack pT = Some (t_over_phantom_group pP pT pmT TF ST Z).

  Theorem t_over_phantom_glu_moves : forall i g g' P El,
      per_top_ps (ce_ass TF :: nil) (g :: nil) (g' :: nil) ->
      DG d_ind pT 0 (g :: nil) ∈ glu_univ_elem i ↘ P ↘ El ->
      DG d_ind pT 0 (g' :: nil) ∈ glu_univ_elem i ↘ P ↘ El.
  Proof.
    intros * Hg HG.
    eapply glu_univ_elem_resp_per_univ; [| exact HG ].
    eexists; exact (t_over_phantom_related pP pT pmP pmT TA TB TF SP ST Z HlP HlT i g g' Hg).
  Qed.

End PhantomGluing.
