(** * The Semantic Judgments

    The judgments are defined in four layers — weakenings, substitutions, terms, subtyping — and then packaged
    by an inductive [⊨ Γ].

    Each of the middle two layers states its conclusion as a *four-value
    pattern* (see [Core/Semantic/PER/Chain.v]):

      {⟦M[σ]⟧(ρ), ⟦M⟧(⟦σ⟧(ρ)), ⟦M'⟧(⟦σ'⟧(ρ')), ⟦M'[σ']⟧(ρ')} ⊆ R

    whose three consecutive links are, in order, the *commutation* obligation on
    the left, the *relatedness* obligation in the middle, and the commutation
    obligation on the right.  With explicit substitutions the two commutations
    are reflexivity, because [⟦M[σ]⟧(ρ)] and [⟦M⟧(⟦σ⟧(ρ))] are then the same
    derivation; with substitution as an operation they are not even equal, and discharging them at every case of the fundamental theorem is the
    price of the operational presentation. *)

From Stdlib Require Import List Relations.
Import ListNotations.

From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
Import Domain_Notations.
Import Wk_Notations.

Reserved Notation "Γ ⊨w φ : Δ" (in custom judg at level 80, Γ custom exp, φ constr at level 0, Δ custom exp).

(** * Semantic Weakening

    Because a weakening is an operation, related environments are not
    automatically related after it is applied; the semantic judgment for
    weakenings simply demands it.  Stripped of its two context witnesses this is
    just [Proper (R ==> R') (eval_wk φ)], and that is the form the proofs use. *)

Definition rel_wk (φ : wk) (R R' : relation env) : Prop :=
  forall ρ ρ',
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom ⟦ φ ⟧w ρ ≈ ⟦ φ ⟧w ρ' ∈ R' }}.

Definition rel_wk_under_ctx Γ φ Δ : Prop :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }})
     env_rel' (_ : {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_rel' }}),
    rel_wk φ env_rel env_rel'.

Notation "Γ ⊨w φ : Δ" := (rel_wk_under_ctx Γ φ Δ) (in custom judg) : type_scope.

(** * Semantic Substitution Equality

    [σ] and [σ'] must stay related after an arbitrary semantic weakening [φ] —
    the Kripke-like quantification that makes the judgment usable under context
    extension.  The four environments are the two ways of evaluating each side:
    [σ[φ]] in [ρ] (the substitution [sb_wk σ φ], which is [σ] postcomposed with
    [φ]) against [σ] in [⟦φ⟧w ρ]. *)

Inductive rel_sub (σ : sub) (φ : wk) (ρ : env) (σ' : sub) (ρ' : env) (R : relation env) : Prop :=
| mk_rel_sub : forall ρσφ ρσ ρ'σ' ρ'σ'φ,
    {{ ⟦ ^(sb_wk σ φ) ⟧s ρ ↘ ρσφ }} ->
    {{ ⟦ σ ⟧s ⟦ φ ⟧w ρ ↘ ρσ }} ->
    {{ ⟦ σ' ⟧s ⟦ φ ⟧w ρ' ↘ ρ'σ' }} ->
    {{ ⟦ ^(sb_wk σ' φ) ⟧s ρ' ↘ ρ'σ'φ }} ->
    rel_chain R [ρσφ; ρσ; ρ'σ'; ρ'σ'φ] ->
    rel_sub σ φ ρ σ' ρ' R.
#[global]
Arguments mk_rel_sub {_ _ _ _ _ _}.
#[export]
Hint Constructors rel_sub : mctt.

Definition rel_sub_under_ctx Γ Δ σ σ' : Prop :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }})
     env_rel_o (_ : {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_rel_o }}),
  forall Γ' env_rel' (_ : {{ EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' }}) φ,
    rel_wk φ env_rel' env_rel ->
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_rel' }} ->
      rel_sub σ φ ρ σ' ρ' env_rel_o.

Definition valid_sub_under_ctx Γ Δ σ := rel_sub_under_ctx Γ Δ σ σ.
#[global]
Arguments valid_sub_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_sub_under_ctx : mctt.
#[export]
Hint Unfold valid_sub_under_ctx : mctt.

(** * Semantic Judgment for Terms

    Terms are asked to be stable under semantic *substitutions* rather than
    weakenings.  [rel_exp] is the four-value pattern of one expression pair; the
    two environments [ρσ] and [ρ'σ'] are parameters rather than existentials
    because the type chain and the term chain must be read in the *same* pair of
    environments — an environment carries into closures, so replacing it by a
    pointwise-equal one changes the values. *)

Inductive rel_exp (M : exp) (σ : sub) (ρ ρσ : env) (M' : exp) (σ' : sub) (ρ' ρ'σ' : env) (R : relation domain) : Prop :=
| mk_rel_exp : forall mσ m m' m'σ',
    {{ ⟦ M[σ] ⟧ ρ ↘ mσ }} ->
    {{ ⟦ M ⟧ ρσ ↘ m }} ->
    {{ ⟦ M' ⟧ ρ'σ' ↘ m' }} ->
    {{ ⟦ M'[σ'] ⟧ ρ' ↘ m'σ' }} ->
    rel_chain R [mσ; m; m'; m'σ'] ->
    rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R.
#[global]
Arguments mk_rel_exp {_ _ _ _ _ _ _ _ _}.
#[export]
Hint Constructors rel_exp : mctt.

(** The same pattern one universe up: the four values of a *type* are related in
    [per_univ_elem i R], which additionally pins down the element PER [R] that
    the term chain then lives in. *)
Definition rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R :=
  rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ_elem i R).
Arguments rel_typ _ _ _ _ _ _ _ _ _ _ /.
#[export]
Hint Transparent rel_typ : mctt.
#[export]
Hint Unfold rel_typ : mctt.

(** The notation [⟦σ⟧(ρ)] for the environment [σ] evaluates to suggests that
    evaluation is a metafunction.  Here it is a relation, and
    [functional_eval_sub] pins its result down only up to [env_eq] — which is
    *not* enough to substitute one witness for another, since evaluation does not
    respect [env_eq] (a closure captures its environment).  So the two
    environments are quantified **universally**, over evaluation witnesses
    supplied by the caller, rather than existentially: any two proofs that [σ]
    evaluates at [ρ] are then interchangeable by construction.

    Nothing is lost.  The judgment no longer *claims* that [σ] evaluates at [ρ],
    but that claim is already part of [rel_sub_under_ctx Γ' Γ σ σ'], which every
    instantiation must supply anyway.  And nothing is gained for free: each case
    of the fundamental theorem must now produce its values at whatever
    environment the caller names.  That it can is exactly what makes the
    inductive cases fit together — a premise's values arrive in the *same*
    environment as the conclusion's, so two instantiations of one judgment
    genuinely share values instead of merely being pointwise equal, and
    [rel_chain_merge] applies. *)
Definition rel_exp_under_ctx Γ A M M' : Prop :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
  forall Γ' env_rel' (_ : {{ EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' }}) σ σ',
    rel_sub_under_ctx Γ' Γ σ σ' ->
    forall ρ ρ' ρσ ρ'σ',
      {{ Dom ρ ≈ ρ' ∈ env_rel' }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
      {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
      exists (elem_rel : relation domain),
        rel_typ i A σ ρ ρσ A σ' ρ' ρ'σ' elem_rel /\
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' elem_rel.

Definition valid_exp_under_ctx Γ A M := rel_exp_under_ctx Γ A M M.
#[global]
Arguments valid_exp_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_exp_under_ctx : mctt.
#[export]
Hint Unfold valid_exp_under_ctx : mctt.

(** * Semantic Judgment for Subtyping

    Not a four-value chain: [per_subtyp] has no symmetry, so the two commutation
    obligations are stated on their own sides and the subtyping obligation
    relates the two inner values only. *)

Definition subtyp_under_ctx Γ A A' : Prop :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
  forall Γ' env_rel' (_ : {{ EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' }}) σ σ',
    rel_sub_under_ctx Γ' Γ σ σ' ->
    forall ρ ρ' ρσ ρ'σ',
      {{ Dom ρ ≈ ρ' ∈ env_rel' }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
      {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
      exists aσ a a'σ' a',
          {{ ⟦ A[σ] ⟧ ρ ↘ aσ }} /\
          {{ ⟦ A ⟧ ρσ ↘ a }} /\
          {{ ⟦ A'[σ'] ⟧ ρ' ↘ a'σ' }} /\
          {{ ⟦ A' ⟧ ρ'σ' ↘ a' }} /\
          {{ Dom aσ ≈ a ∈ per_univ i }} /\
          {{ Dom a'σ' ≈ a' ∈ per_univ i }} /\
          {{ Sub a <: a' at i }}.

Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Notation "Γ ⊨ M ⊆ M'" := (subtyp_under_ctx Γ M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Notation "Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Notation "Γ ⊨s σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).

(** * Semantic Context Well-Formedness

    Unlike [valid_ctx] (which is just [per_ctx Γ Γ]), this is inductive, and each
    extension step carries both the context PER witness and the semantic
    well-formedness of the type — so [sem_ctx_per_ctx_env] reads the PER
    straight off any derivation. *)

Reserved Notation "⊨ Γ" (in custom judg at level 80, Γ custom exp).

Inductive sem_ctx : ctx -> Prop :=
| sem_ctx_nil : {{ ⊨ ⋅ }}
| sem_ctx_cons : forall Γ A i env_rel,
    {{ ⊨ Γ }} ->
    {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_rel }} ->
    {{ Γ ⊨ A ≈ A : Type@i }} ->
    {{ ⊨ Γ, A }}
where "⊨ Γ" := (sem_ctx Γ) (in custom judg) : type_scope.

#[export]
Hint Constructors sem_ctx : mctt.
