(** * Corollaries of the Syntactic Theory

    Reasoning about context lookup, needed by the variable case of the
    soundness proof.  The laws of the substitution calculus are propositional
    equalities of [exp], proved in [Substitution]. *)

From Stdlib Require Import List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations Wk_Notations.

Open Scope list_scope.

Lemma ctx_lookup_functional : forall n T Γ,
    Γ ∋ #n : T ->
    forall T',
      Γ ∋ #n : T' ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  erewrite IHctx_lookup; eauto.
Qed.
