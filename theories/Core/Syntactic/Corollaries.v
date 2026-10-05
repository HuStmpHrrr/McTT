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

(** The type of the [n]-th binding of [Δ ++ ce_ass T :: Γ], when [Δ] has length [n], is
    [T] shifted past [Δ] and past [T] itself — that is, [T[⇑^(S n)]ʷ]. *)
Lemma app_ctx_lookup : forall Δ T Γ n,
    length Δ = n ->
    (Δ ++ ce_ass T :: Γ) ∋ #n : T[wk_shiftn (S n)]ʷ.
Proof.
  induction Δ; intros * <-; simpl.
  - rewrite <- wk_shiftn_succ, wk_shiftn_zero, wk_compose_id_left.
    constructor.
  - rewrite <- wk_shiftn_succ, <- exp_wk_wk.
    constructor; apply IHΔ; reflexivity.
Qed.

Lemma app_ctx_vlookup : forall Θ Δ T Γ n,
    ⊢ Θ ⍮ (Δ ++ ce_ass T :: Γ) ->
    length Δ = n ->
    Θ ⍮ (Δ ++ ce_ass T :: Γ) ⊢ #n : T[wk_shiftn (S n)]ʷ.
Proof.
  intros; econstructor; [ assumption | apply app_ctx_lookup; assumption ].
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
