(** * Context Refinement

    [⊢ Ψ ⍮ Δ ⊆ Γ] transports a judgment from [Γ] to [Δ].  It is inductive, because
    the gluing model recurses on it — but unlike the presentation
    with explicit substitutions, the transport lemmas are *not* proved by that
    induction.  [ctx_sub_escape] turns a refinement into [Ψ ⍮ Δ ⊢s Id : Γ]
    once and for all, and then [sub_preserves_wf] at [Id] does the transport:
    that is
    [ctxsub_exp] and friends in [System.Lemmas], all stated for [Id].

    The length equation that comes with the inductive shape is the one thing
    [Ψ ⍮ Δ ⊢s Id : Γ] does *not* give: [Ψ ⍮ ⋅ ▹ ℕ ⊢s Id : ⋅] holds, since
    [⋅] has no binding to inhabit.  The Kripke weakenings of soundness read a de
    Bruijn *level* off the length of their domain, so they need a refinement that
    preserves it. *)

From Stdlib Require Import RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations Wk_Notations.

Reserved Notation "⊢ Ψ ⍮ Δ ⊆ Γ" (at level 70, Ψ at level 69, Γ at level 69).

Inductive ctx_sub (Ψ : gctx) : ctx -> ctx -> Prop :=
| ctx_sub_empty : ⊢ Ψ ⍮ ⋅ ⊆ ⋅
| ctx_sub_extend : forall Δ Γ A A' i,
    ⊢ Ψ ⍮ Δ ⊆ Γ ->
    Ψ ⍮ Γ ⊢ A : Type@i ->
    Ψ ⍮ Δ ⊢ A' : Type@i ->
    Ψ ⍮ Δ ⊢ A' ⊆ A ->
    ⊢ Ψ ⍮ Δ ▹ A' ⊆ Γ ▹ A
where "⊢ Ψ ⍮ Δ ⊆ Γ" := (ctx_sub Ψ Δ Γ) : type_scope.

#[export]
Hint Constructors ctx_sub : mctt.

Lemma ctx_sub_length : forall Ψ Δ Γ, ⊢ Ψ ⍮ Δ ⊆ Γ -> length Δ = length Γ.
Proof. induction 1; simpl; congruence. Qed.

Lemma ctx_sub_dom : forall Ψ Δ Γ, ⊢ Ψ ⍮ Δ ⊆ Γ -> ⊢ Ψ ⍮ Δ.
Proof. induction 1; mauto 2. Qed.

Lemma ctx_sub_cod : forall Ψ Δ Γ, ⊢ Ψ ⍮ Δ ⊆ Γ -> ⊢ Ψ ⍮ Γ.
Proof. induction 1; mauto 2. Qed.

#[export]
Hint Resolve ctx_sub_dom ctx_sub_cod : mctt.

(** The [Var] case of [ctx_sub_escape], by induction on the lookup rather than
    on the refinement: the [here] case is where [A' ⊆ A] is used, and the
    [there] case is plain weakening. *)
Lemma ctx_sub_vlookup : forall Ψ Γ x A,
    Γ ∋ #x : A ->
    forall Δ, ⊢ Ψ ⍮ Δ ⊆ Γ -> Ψ ⍮ Δ ⊢ #x : A.
Proof.
  induction 1; intros * HΔ; dependent destruction HΔ.

  - assert (⊢ Ψ ⍮ Δ ▹ A') by mauto 3.
    assert (Ψ ⍮ Δ ▹ A' ⊢w ↑ : Δ) by mauto 3.
    assert (Ψ ⍮ Δ ▹ A' ⊢ A'⟨↑⟩ ⊆ A⟨↑⟩) by mauto 3.
    mauto 3.

  - assert (Ψ ⍮ Δ ⊢ #n : A) by mauto 3.
    assert (⊢ Ψ ⍮ Δ ▹ A') by mauto 3.
    assert (Ψ ⍮ Δ ▹ A' ⊢ #n⟨↑⟩ : A⟨↑⟩) by mauto 3.
    assumption.
Qed.

Lemma ctx_sub_escape : forall Ψ Δ Γ, ⊢ Ψ ⍮ Δ ⊆ Γ -> Ψ ⍮ Δ ⊢s Id : Γ.
Proof.
  intros * HΔ.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite exp_sub_id.
  eauto using ctx_sub_vlookup.
Qed.

#[export]
Hint Resolve ctx_sub_escape : mctt.

Lemma ctx_sub_refl : forall Ψ Γ, ⊢ Ψ ⍮ Γ -> ⊢ Ψ ⍮ Γ ⊆ Γ.
Proof. induction 1; mauto 3. Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Lemma ctx_sub_trans : forall Ψ Γ0 Γ1,
    ⊢ Ψ ⍮ Γ0 ⊆ Γ1 ->
    forall Γ2,
      ⊢ Ψ ⍮ Γ1 ⊆ Γ2 ->
      ⊢ Ψ ⍮ Γ0 ⊆ Γ2.
Proof.
  induction 1; intros * HΓ2; dependent destruction HΓ2; [ constructor | ].
  rename A into A1. rename A0 into A2. rename A' into A0.
  (** The two steps ascribe unrelated levels to the middle type, so both have to
      be raised before the refinements can be composed. *)
  assert (Ψ ⍮ Δ ⊢s Id : Γ) by mauto 2.
  assert (Ψ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
  eapply ctx_sub_extend with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
Hint Resolve ctx_sub_trans : mctt.

#[export]
Instance ctx_sub_Transitive Ψ : Transitive (ctx_sub Ψ).
Proof. intros ? ? ?; eauto using ctx_sub_trans. Qed.

Corollary ctx_sub_extend_eq : forall Ψ Γ A A' i,
    Ψ ⍮ Γ ⊢ A : Type@i ->
    Ψ ⍮ Γ ⊢ A' : Type@i ->
    Ψ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    ⊢ Ψ ⍮ Γ ▹ A' ⊆ Γ ▹ A.
Proof. intros; eapply ctx_sub_extend; mauto 3. Qed.

#[export]
Hint Resolve ctx_sub_extend_eq : mctt.

Ltac saturate_ctx_sub :=
  match_by_head ctx_sub ltac:(fun H => pose proof (ctx_sub_escape _ _ _ H);
                                       pose proof (ctx_sub_dom _ _ _ H);
                                       pose proof (ctx_sub_cod _ _ _ H);
                                       pose proof (ctx_sub_length _ _ _ H));
  clear_dups.
