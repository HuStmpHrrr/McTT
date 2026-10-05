(** * Context Refinement

    [⊢ Θ ⍮ Δ ⊆ Γ] transports a judgment from [Γ] to [Δ].  It is inductive
    because the gluing model recurses on it, but the transport lemmas are not
    proved by that induction: [ctx_sub_escape] turns a refinement into
    [Θ ⍮ Δ ⊢s Id : Γ], and [sub_preserves_wf] at [Id] does the transport
    ([ctxsub_exp] and related lemmas in [System.Lemmas]).

    The inductive shape also preserves length, which [Θ ⍮ Δ ⊢s Id : Γ] does
    not: [Θ ⍮ ⋅ ▹ ℕ ⊢s Id : ⋅] holds, since [⋅] has no binding to inhabit.
    The Kripke weakenings of soundness read a de Bruijn level off the length of
    their domain, so they need a refinement that preserves it. *)

From Stdlib Require Import RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations Wk_Notations.

Reserved Notation "⊢ Θ ⍮ Δ ⊆ Γ" (at level 70, Θ at level 69, Γ at level 69).

Inductive ctx_sub (Θ : gctx) : ctx -> ctx -> Prop :=
(** As with [wf_ctx_empty], the base case carries what the judgment is relative
    to. *)
| ctx_sub_empty :
    ⊢g Θ ->
    ⊢ Θ ⍮ ⋅ ⊆ ⋅
| ctx_sub_extend : forall Δ Γ A A' i,
    ⊢ Θ ⍮ Δ ⊆ Γ ->
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Δ ⊢ A' ⊆ A ->
    ⊢ Θ ⍮ Δ ▹ A' ⊆ Γ ▹ A
(** A definition refines a definition of a supertype with an equal body. *)
| ctx_sub_extend_def : forall Δ Γ A A' M M' i,
    ⊢ Θ ⍮ Δ ⊆ Γ ->
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Δ ⊢ M' ≈ M : A ->
    ⊢ Θ ⍮ Δ ▸ A' ≔ M' ⊆ Γ ▸ A ≔ M
(** Knowing a definition refines knowing only its type. *)
| ctx_sub_forget : forall Δ Γ A A' M' i,
    ⊢ Θ ⍮ Δ ⊆ Γ ->
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Δ ⊢ M' : A' ->
    ⊢ Θ ⍮ Δ ▸ A' ≔ M' ⊆ Γ ▹ A
(** A module slot refines a slot of the same unit. *)
| ctx_sub_extend_mod : forall Δ Γ U,
    ⊢ Θ ⍮ Δ ⊆ Γ ->
    Θ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Δ ⊢ᵘ U ≈ U ->
    ⊢ Θ ⍮ Δ ▹ₘ U ⊆ Γ ▹ₘ U
where "⊢ Θ ⍮ Δ ⊆ Γ" := (ctx_sub Θ Δ Γ) : type_scope.

#[export]
Hint Constructors ctx_sub : mctt.

Lemma ctx_sub_length : forall Θ Δ Γ, ⊢ Θ ⍮ Δ ⊆ Γ -> length Δ = length Γ.
Proof. induction 1; simpl; congruence. Qed.

Lemma ctx_sub_dom : forall Θ Δ Γ, ⊢ Θ ⍮ Δ ⊆ Γ -> ⊢ Θ ⍮ Δ.
Proof. induction 1; mauto 2. Qed.

Lemma ctx_sub_cod : forall Θ Δ Γ, ⊢ Θ ⍮ Δ ⊆ Γ -> ⊢ Θ ⍮ Γ.
Proof. induction 1; mauto 2. Qed.

#[export]
Hint Resolve ctx_sub_dom ctx_sub_cod : mctt.

(** Each rule is one of the identity refinements of [Structural]. *)
Lemma ctx_sub_escape : forall Θ Δ Γ, ⊢ Θ ⍮ Δ ⊆ Γ -> Θ ⍮ Δ ⊢s Id : Γ.
Proof.
  induction 1;
    [ apply wf_sub_id; mauto 2
    | eapply wf_sub_id_extend
    | eapply wf_sub_id_extend_def
    | eapply wf_sub_id_forget
    | eapply wf_sub_id_extend_mod ]; eassumption.
Qed.

#[export]
Hint Resolve ctx_sub_escape : mctt.

Lemma ctx_sub_vlookup : forall Θ Γ x A,
    Γ ∋ #x : A ->
    forall Δ, ⊢ Θ ⍮ Δ ⊆ Γ -> Θ ⍮ Δ ⊢ #x : A.
Proof.
  intros; eapply ctxsub_vlookup; mauto 2.
Qed.

(** The induction is on [Γ], not on the derivation: [wf_ctx_extend] has no
    context premise, so an induction on [⊢ Γ ▹ A] yields no hypothesis about
    [Γ]. *)
Lemma ctx_sub_refl : forall Θ Γ, ⊢ Θ ⍮ Γ -> ⊢ Θ ⍮ Γ ⊆ Γ.
Proof.
  intros Θ Γ; induction Γ as [| [A | A M | U] Γ IH]; intros HΓ; inversion_clear HΓ;
    mauto 3 using presup_exp_ctx.
  - econstructor; mauto 3 using presup_exp_ctx.
  - eapply ctx_sub_extend_def; mauto 3 using presup_exp_ctx.
  - eapply ctx_sub_extend_mod; mauto 3 using presup_unit_eq_ctx.
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Lemma ctx_sub_trans : forall Θ Γ0 Γ1,
    ⊢ Θ ⍮ Γ0 ⊆ Γ1 ->
    forall Γ2,
      ⊢ Θ ⍮ Γ1 ⊆ Γ2 ->
      ⊢ Θ ⍮ Γ0 ⊆ Γ2.
Proof.
  induction 1; intros * HΓ2; dependent destruction HΓ2; [ now constructor | | | | |].
  (** The two steps ascribe unrelated levels to the middle type, so both have to
      be raised before the refinements can be composed. *)
  all: assert (Θ ⍮ Δ ⊢s Id : Γ) by mauto 2.
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_extend with (i := max i i0);
      mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - (** Two definitions: the bodies are equal at the outer type. *)
    rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    assert (Θ ⍮ Δ ⊢ A0 ⊆ A2) by mauto 3.
    assert (Θ ⍮ Δ ⊢ M ≈ M0 : A2) by mauto 3.
    eapply ctx_sub_extend_def with (i := max i i0);
      mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_forget with (i := max i i0);
      mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_forget with (i := max i i0);
      mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - eapply ctx_sub_extend_mod; eauto.
Qed.

#[export]
Hint Resolve ctx_sub_trans : mctt.

#[export]
Instance ctx_sub_Transitive Θ : Transitive (ctx_sub Θ).
Proof. intros ? ? ?; eauto using ctx_sub_trans. Qed.

Corollary ctx_sub_extend_eq : forall Θ Γ A A' i,
    Θ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    ⊢ Θ ⍮ Γ ▹ A' ⊆ Γ ▹ A.
Proof. intros; eapply ctx_sub_extend; mauto 3. Qed.

#[export]
Hint Resolve ctx_sub_extend_eq : mctt.

Ltac saturate_ctx_sub :=
  match_by_head ctx_sub ltac:(fun H => pose proof (ctx_sub_escape _ _ _ H);
                                       pose proof (ctx_sub_dom _ _ _ H);
                                       pose proof (ctx_sub_cod _ _ _ H);
                                       pose proof (ctx_sub_length _ _ _ H));
  clear_dups.
