(** * Context Refinement

    [Θ ⍮ Ξ ⊢ Δ ⊆ Γ] transports a judgment from [Γ] to [Δ].  It is inductive
    because the gluing model recurses on it, but the transport lemmas are not
    proved by that induction: [ctx_sub_escape] turns a refinement into
    [Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ], and [sub_preserves_wf] at [Id] does the transport
    ([ctxsub_exp] and related lemmas in [System.Lemmas]).

    The inductive shape also preserves length, which [Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ] does
    not: [Θ ⍮ Ξ ⍮ ⋅ ▹ ℕ ⊢s Id : ⋅] holds, since [⋅] has no binding to inhabit.
    The Kripke weakenings of soundness read a de Bruijn level off the length of
    their domain, so they need a refinement that preserves it. *)

From Stdlib Require Import RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations Wk_Notations.

Reserved Notation "Θ ⍮ Ξ ⊢ Δ ⊆ Γ" (at level 70, Ξ at level 69, Δ at level 69, Γ at level 69).

Inductive ctx_sub (Θ : gdeps) (Ξ : gstack) : ctx -> ctx -> Prop :=
(** As with [wf_ctx_empty], the base case carries what the judgment is relative
    to. *)
| ctx_sub_empty :
    ⊢g Θ ⍮ Ξ ->
    Θ ⍮ Ξ ⊢ ⋅ ⊆ ⋅
| ctx_sub_extend : forall Δ Γ A A' i,
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⊢ Δ ▹ A' ⊆ Γ ▹ A
where "Θ ⍮ Ξ ⊢ Δ ⊆ Γ" := (ctx_sub Θ Ξ Δ Γ) : type_scope.

#[export]
Hint Constructors ctx_sub : mctt.

Lemma ctx_sub_length : forall Θ Ξ Δ Γ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> length Δ = length Γ.
Proof. induction 1; simpl; congruence. Qed.

Lemma ctx_sub_dom : forall Θ Ξ Δ Γ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ.
Proof. induction 1; mauto 2. Qed.

Lemma ctx_sub_cod : forall Θ Ξ Δ Γ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof. induction 1; mauto 2. Qed.

#[export]
Hint Resolve ctx_sub_dom ctx_sub_cod : mctt.

(** The [Var] case of [ctx_sub_escape], by induction on the lookup rather than
    on the refinement: the [here] case is where [A' ⊆ A] is used, and the
    [there] case is plain weakening. *)
Lemma ctx_sub_vlookup : forall Θ Ξ Γ x A,
    Γ ∋ #x : A ->
    forall Δ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ #x : A.
Proof.
  induction 1; intros * HΔ; dependent destruction HΔ.

  - assert (⊢ Θ ⍮ Ξ ⍮ Δ ▹ A') by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢w ↑ : Δ) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢ A'[↑]ʷ ⊆ A[↑]ʷ) by mauto 3.
    mauto 3.

  - assert (Θ ⍮ Ξ ⍮ Δ ⊢ #n : A) by mauto 3.
    assert (⊢ Θ ⍮ Ξ ⍮ Δ ▹ A') by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢ #n[↑]ʷ : A[↑]ʷ) by mauto 3.
    assumption.
Qed.

Lemma ctx_sub_escape : forall Θ Ξ Δ Γ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ.
Proof.
  intros * HΔ.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite exp_sub_id.
  eauto using ctx_sub_vlookup.
Qed.

#[export]
Hint Resolve ctx_sub_escape : mctt.

(** The induction is on [Γ], not on the derivation: [wf_ctx_extend] has no
    context premise, so an induction on [⊢ Γ ▹ A] yields no hypothesis about
    [Γ]. *)
Lemma ctx_sub_refl : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⊢ Γ ⊆ Γ.
Proof.
  intros Θ Ξ Γ; induction Γ as [| A Γ IH]; intros HΓ; inversion_clear HΓ;
    mauto 3 using presup_exp_ctx.
  econstructor; mauto 3 using presup_exp_ctx.
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Lemma ctx_sub_trans : forall Θ Ξ Γ0 Γ1,
    Θ ⍮ Ξ ⊢ Γ0 ⊆ Γ1 ->
    forall Γ2,
      Θ ⍮ Ξ ⊢ Γ1 ⊆ Γ2 ->
      Θ ⍮ Ξ ⊢ Γ0 ⊆ Γ2.
Proof.
  induction 1; intros * HΓ2; dependent destruction HΓ2; [ now constructor | ].
  rename A into A1. rename A0 into A2. rename A' into A0.
  (** The two steps ascribe unrelated levels to the middle type, so both have to
      be raised before the refinements can be composed. *)
  assert (Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
  eapply ctx_sub_extend with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
Hint Resolve ctx_sub_trans : mctt.

#[export]
Instance ctx_sub_Transitive Θ Ξ : Transitive (ctx_sub Θ Ξ).
Proof. intros ? ? ?; eauto using ctx_sub_trans. Qed.

Corollary ctx_sub_extend_eq : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⊢ Γ ▹ A' ⊆ Γ ▹ A.
Proof. intros; eapply ctx_sub_extend; mauto 3. Qed.

#[export]
Hint Resolve ctx_sub_extend_eq : mctt.

Ltac saturate_ctx_sub :=
  match_by_head ctx_sub ltac:(fun H => pose proof (ctx_sub_escape _ _ _ _ H);
                                       pose proof (ctx_sub_dom _ _ _ _ H);
                                       pose proof (ctx_sub_cod _ _ _ _ H);
                                       pose proof (ctx_sub_length _ _ _ _ H));
  clear_dups.
