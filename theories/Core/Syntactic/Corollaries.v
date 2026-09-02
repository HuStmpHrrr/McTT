(** * Corollaries of the Syntactic Theory

    This file used to collect some thirty rearrangements of the substitution
    calculus — [q σ ∘ (τ ,, t) ≈ σ ∘ τ ,, t], [A[Wk][σ ,, M] ≈ A[σ]],
    [Type@i[σ] : Type@(S i)] and so on — each proved as a judgmental equality
    from the congruence and computation rules.  With substitution as an
    operation every one of them is a propositional equality of [exp], proved
    once and for all in [Substitution]; the typing corollaries that remained
    were instances of [sub_preserves_exp] and its siblings.

    What is left is the reasoning about *context lookup* that the soundness
    proof's variable case needs, which is genuinely about lists and not about
    substitution. *)

From Stdlib Require Import List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations Wk_Notations.

Open Scope list_scope.

(** The type of the [n]-th binding of [Δ ++ T :: Γ], when [Δ] has length [n], is
    [T] shifted past [Δ] and past [T] itself — that is, [T⟨⇑^(S n)⟩]. *)
Lemma app_ctx_lookup : forall Δ T Γ n,
    length Δ = n ->
    (Δ ++ T :: Γ) ∋ #n : T⟨wk_shiftn (S n)⟩.
Proof.
  induction Δ; intros * <-; simpl.
  - rewrite <- wk_shiftn_succ, wk_shiftn_zero, wk_compose_id_left.
    constructor.
  - rewrite <- wk_shiftn_succ, <- exp_wk_wk.
    constructor; apply IHΔ; reflexivity.
Qed.

Lemma app_ctx_vlookup : forall Δ T Γ n,
    ⊢ (Δ ++ T :: Γ) ->
    length Δ = n ->
    (Δ ++ T :: Γ) ⊢ #n : T⟨wk_shiftn (S n)⟩.
Proof.
  intros; econstructor; auto using app_ctx_lookup.
Qed.

Lemma ctx_lookup_functional : forall n T Γ,
    Γ ∋ #n : T ->
    forall T',
      Γ ∋ #n : T' ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  erewrite IHctx_lookup; eauto.
Qed.
