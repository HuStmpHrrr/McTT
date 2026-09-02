(** * Soundness of Normalization by Evaluation

    Where the explicit-substitution development had to travel through [A[Id][Id]] to line the statement up with the gluing
    predicate, [exp_sub_id] and [exp_wk_id] now discharge the same bookkeeping by
    rewriting. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Export FundamentalTheorem.
Import Domain_Notations.

Theorem soundness : forall {Γ M A},
    Γ ⊢ M : A ->
    exists W, nbe Γ M A W /\ Γ ⊢ M ≈ W : A.
Proof.
  intros * H.
  assert (⊢ Γ) by mauto 3.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ]
      by mauto 3 using completeness_fundamental_ctx, sem_ctx_per_ctx_env.
  destruct (soundness_fundamental_exp _ _ _ H) as [Sb [? [i]]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [ρ [? ?]].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢s Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  assert (Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top i a) as [? ? ? ? ? ? Hrb]
      by (eapply realize_glu_elem_top; mauto 3).
  match_by_head per_top ltac:(fun H => destruct (H (length Γ)) as [W []]).
  assert (Γ ⊢k wk_id : Γ) by mauto 3.
  assert (Γ ⊢ M[Id]⟨wk_id⟩ ≈ W : A[Id]⟨wk_id⟩) as Heq by (eapply Hrb; eassumption).
  rewrite !exp_wk_id, !exp_sub_id in Heq.
  exists W; split; [econstructor |]; eassumption.
Qed.

Theorem soundness' : forall {Γ M A W},
    Γ ⊢ M : A ->
    nbe Γ M A W ->
    Γ ⊢ M ≈ W : A.
Proof.
  intros * [? []]%soundness ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Lemma soundness_ty : forall {Γ i A},
    Γ ⊢ A : Type@i ->
    exists W, nbe_ty Γ A W /\ Γ ⊢ A ≈ W : Type@i.
Proof.
  intros.
  assert (exists W', nbe Γ A Type@i W' /\ Γ ⊢ A ≈ W' : Type@i) as [? [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
  firstorder.
Qed.

Lemma soundness_ty' : forall {Γ i A B},
    Γ ⊢ A : Type@i ->
    nbe_ty Γ A B ->
    Γ ⊢ A ≈ B : Type@i.
Proof.
  intros.
  assert (exists B', nbe_ty Γ A B' /\ Γ ⊢ A ≈ B' : Type@i) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
