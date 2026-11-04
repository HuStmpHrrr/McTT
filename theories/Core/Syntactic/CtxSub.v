(** * Context Refinement

    [Θ ⍮ Ξ ⊢ Δ ⊆ Γ] transports a judgment from [Γ] to [Δ].  It is inductive
    because the gluing model recurses on it, but the transport lemmas are not
    proved by that induction: [ctx_sub_escape] turns a refinement into
    [Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ], and [sub_preserves_wf] at [Id] does the transport
    ([ctxsub_exp] and related lemmas in [System.Lemmas]).

    The inductive shape also preserves length, which [Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ] does
    not: [Θ ⍮ Ξ ⍮ ⋅ ▹ ℕ ⊢ˢ Id : ⋅] holds, since [⋅] has no binding to inhabit.
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
    ⊢ᵍ Θ ⍮ Ξ ->
    Θ ⍮ Ξ ⊢ ⋅ ⊆ ⋅
(** An assumption refines one of a supertype at the same kind, each a
    type of its own sort of that kind. *)
| ctx_sub_extend : forall Δ Γ κ A A' Srt Srt',
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Srt' ->
    sort_kind Srt' κ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⊢ Δ ▹{κ} A' ⊆ Γ ▹{κ} A
(** A definition refines a definition of a supertype with an equal body. *)
| ctx_sub_extend_def : forall Δ Γ A A' M M' Srt Srt',
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Srt' ->
    type_sort Srt' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' ≈ M : A ->
    Θ ⍮ Ξ ⊢ Δ ▸ A' ≔ M' ⊆ Γ ▸ A ≔ M
(** Knowing a definition refines knowing only its type, an assumption of
    the kind of that type's sort. *)
| ctx_sub_forget : forall Δ Γ κ A A' M' Srt Srt',
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Srt' ->
    type_sort Srt' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⊢ Δ ▸ A' ≔ M' ⊆ Γ ▹{κ} A
(** A module slot refines a slot of the same unit. *)
| ctx_sub_extend_mod : forall Δ Γ U,
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⊢ Δ ▹ₘ U ⊆ Γ ▹ₘ U
(** A definition with a module part refines one of a supertype with an
    equal body and the same unit; its types are of a large universe, as
    such definitions are relevant. *)
| ctx_sub_extend_dm : forall Δ Γ A A' M M' U i,
    Θ ⍮ Ξ ⊢ Δ ⊆ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' ≈ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⊢ Δ ▸ₘ A' ≔ M' ‖ U ⊆ Γ ▸ₘ A ≔ M ‖ U
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

(** Each rule is one of the identity refinements of [Structural]. *)
Lemma ctx_sub_escape : forall Θ Ξ Δ Γ, Θ ⍮ Ξ ⊢ Δ ⊆ Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ.
Proof.
  induction 1;
    [ apply wf_sub_id; mauto 2
    | eapply wf_sub_id_extend
    | eapply wf_sub_id_extend_def
    | eapply wf_sub_id_forget
    | eapply wf_sub_id_extend_mod
    | eapply wf_sub_id_extend_dm ]; eassumption.
Qed.

#[export]
Hint Resolve ctx_sub_escape : mctt.

(** The induction is on [Γ], not on the derivation: [wf_ctx_extend] has no
    context premise, so an induction on [⊢ Γ ▹ A] yields no hypothesis about
    [Γ]. *)
Lemma ctx_sub_refl : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⊢ Γ ⊆ Γ.
Proof.
  intros Θ Ξ Γ; induction Γ as [| [κ A | A M | U | A M U] Γ IH]; intros HΓ; inversion_clear HΓ;
    mauto 3 using presup_exp_ctx.
  - eapply ctx_sub_extend; [ mauto 3 using presup_exp_ctx | exact H | exact H0 | exact H | exact H0
                           | eapply wf_subtyp_refl_typ; [ exact H | exact (sort_kind_type_sort _ _ H0) ] ].
  - eapply ctx_sub_extend_def;
      [ mauto 3 using presup_exp_ctx | exact H | exact H0 | exact H | exact H0 | eapply wf_subtyp_refl_typ; eassumption
      | eassumption | eassumption | mauto 3 ].
  - eapply ctx_sub_extend_mod; mauto 3 using presup_unit_eq_ctx.
  - eapply ctx_sub_extend_dm;
      [ mauto 3 using presup_exp_ctx | exact H | exact H | eapply wf_subtyp_refl_typ; [ exact H | constructor ]
      | eassumption | eassumption | mauto 3 | eassumption | eassumption ].
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Lemma ctx_sub_trans : forall Θ Ξ Γ0 Γ1,
    Θ ⍮ Ξ ⊢ Γ0 ⊆ Γ1 ->
    forall Γ2,
      Θ ⍮ Ξ ⊢ Γ1 ⊆ Γ2 ->
      Θ ⍮ Ξ ⊢ Γ0 ⊆ Γ2.
Proof.
  induction 1; intros * HΓ2; dependent destruction HΓ2; [ now constructor | | | | | |].
  (** Each type keeps its own sort: the outer type's from the second step,
      the inner one's from the first, and the refinements chain. *)
  all: assert (Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ) by mauto 2.
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_extend; [ eauto | eassumption | eassumption | eassumption | eassumption | mauto 3 ].
  - (** Two definitions: the bodies are equal at the outer type. *)
    rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A0 ⊆ A2) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M0 : A2) by mauto 3.
    eapply ctx_sub_extend_def; [ eauto | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | mauto 3 ].
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_forget; [ eauto | eassumption | eassumption | eassumption | eassumption | mauto 3 | eassumption ].
  - rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    eapply ctx_sub_forget; [ eauto | eassumption | eassumption | eassumption | eassumption | mauto 3 | eassumption ].
  - eapply ctx_sub_extend_mod; eauto.
  - (** Two definitions with a module part: as two definitions, the units
        the same. *)
    rename A into A1. rename A0 into A2. rename A' into A0.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A1 ⊆ A2) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ A0 ⊆ A2) by mauto 3.
    assert (Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M0 : A2) by mauto 3.
    eapply ctx_sub_extend_dm with (i := max i i0); [ | | | | | | | | ];
      mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
Hint Resolve ctx_sub_trans : mctt.

#[export]
Instance ctx_sub_Transitive Θ Ξ : Transitive (ctx_sub Θ Ξ).
Proof. intros ? ? ?; eauto using ctx_sub_trans. Qed.

Corollary ctx_sub_extend_eq : forall Θ Ξ Γ κ A A' Srt,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Srt ->
    sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt ->
    Θ ⍮ Ξ ⊢ Γ ▹{κ} A' ⊆ Γ ▹{κ} A.
Proof.
  intros * HA HA' HS HAA; eapply ctx_sub_extend; [ mauto 3 | exact HA | exact HS | exact HA' | exact HS |].
  eapply wf_subtyp_refl; [ exact HA | exact (sort_kind_type_sort _ _ HS) | apply wf_exp_eq_sym; exact HAA ].
Qed.

#[export]
Hint Resolve ctx_sub_extend_eq : mctt.

Ltac saturate_ctx_sub :=
  match_by_head ctx_sub ltac:(fun H => pose proof (ctx_sub_escape _ _ _ _ H);
                                       pose proof (ctx_sub_dom _ _ _ _ H);
                                       pose proof (ctx_sub_cod _ _ _ _ H);
                                       pose proof (ctx_sub_length _ _ _ _ H));
  clear_dups.
