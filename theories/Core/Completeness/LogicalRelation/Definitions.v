(** * The Semantic Judgments

    All the definitions of the PER model's judgments, in four parts.

    1. The relations at one global context [GC], the building blocks:
       weakenings, substitutions, terms, subtyping and module expressions;
       semantically well-formed contexts and the parts of units
       ([rel_ctx_wf], [rel_unit_wf]), and the relations of units and extensions.
    2. Valid units and module expressions valid in what they denote
       ([valid_unit], [valid_modexp]), with lookups read at a global context [Θm ⍮ Ξm]
       that [GC] extends and values at [GC]; and the contexts whose slots
       hold valid units ([valid_ctx]).
    3. What a global context [Θm ⍮ Ξm] files and has open is worth at [GC]
       ([valid_filed_mod], [valid_filed_mods]), and a declaration ([valid_ind_decl],
       [valid_record_decl]); a sound
       embedding of [Θ1 ⍮ Ξ1] into [Θ2 ⍮ Ξ2] ([valid_gctx_embedding]).
    4. The semantic judgments: a judgment of [Θ ⍮ Ξ] is the relation of the
       first two parts at every global context [Θ ⍮ Ξ] embeds into soundly.

    The substitution and term layers state their conclusion as a four-value
    pattern (see [Core/Semantic/PER/Chain.v]):
<<
{⟦M[σ]⟧(ρ), ⟦M⟧(⟦σ⟧(ρ)), ⟦M'⟧(⟦σ'⟧(ρ')), ⟦M'[σ']⟧(ρ')} ⊆ R
>>
    Its three consecutive links are the commutation obligation on the left, the
    relatedness obligation in the middle, and the commutation obligation on the
    right.  Substitution is an operation, so [⟦M[σ]⟧(ρ)] and [⟦M⟧(⟦σ⟧(ρ))] are in
    general not equal, and every case of the fundamental theorem must discharge
    both commutations. *)

From Stdlib Require Import List Relations.
Import ListNotations.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Semantic Require Export PER.
From Mctt.Core.Semantic.Evaluation Require Import Modules.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Reserved Notation "Γ ⊨ʷ φ : Δ" (at level 70, φ constr at level 0, Δ at level 69).
Reserved Notation "⊨ Γ" (at level 70).

(** ** 1. The Relations at One Global Context *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** *** Semantic Weakening

    A weakening is an operation, so related environments need not stay related
    after it is applied; the semantic judgment for weakenings requires that they
    do.  Without its two context witnesses it is [Proper (R ==> R') (eval_wk φ)],
    for a weakening that moves no variable down: environments are lists, which is
    what makes weakenings compose on them ([eval_wk_compose]).  Every weakening
    the proofs use is built from [↑] and [wk_q], hence is of this kind. *)

Record rel_wk (φ : wk) (R R' : relation env) : Prop := mk_rel_wk
  { rel_wk_mono : WkMono φ
  ; rel_wk_app :> forall ρ ρ',
      Dom ρ ≈ ρ' ∈ R ->
      Dom ⟪φ⟫ ρ ≈ ⟪φ⟫ ρ' ∈ R' }.

#[warnings="-cannot-define-projection"]
Record rel_wk_under_ctx Γ φ Δ : Prop := mk_rel_wk_under_ctx
  { (** The relation of the source context's environments *)
    rel_wk_under_ctx_rel : relation env
  ; rel_wk_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_wk_under_ctx_rel
    (** The relation of the target context's environments *)
  ; rel_wk_under_ctx_rel' : relation env
  ; rel_wk_under_ctx_per' : EF Δ ≈ Δ ∈ per_ctx_env ↘ rel_wk_under_ctx_rel'
    (** The weakening takes the one to the other *)
  ; rel_wk_under_ctx_wk : rel_wk φ rel_wk_under_ctx_rel rel_wk_under_ctx_rel'
    (** It takes the entries of the target to entries of the source *)
  ; rel_wk_under_ctx_bound : forall x, x < List.length Δ -> φ x < List.length Γ
    (** An entry of the target is a proposition exactly when its image in
        the source is one.  Context-directed evaluation needs this to
        evaluate the substitution [ι φ ⨟ τ] at [Δ] to [⟪φ⟫ ρτ] when [τ]
        evaluates at [Γ] to [ρτ].  At a target entry that is no
        proposition it asks for the value of [τ (φ x)], which [ρτ] holds
        only when the source entry [φ x] is no proposition either; at a
        target entry that is a proposition it asks for the kept proof of
        [τ (φ x)], which [ρτ] holds only when the source entry is a
        proposition too.  It is a condition on semantic weakenings that
        their relations do not imply: the identity from [⋅ ▹ ⊤] to
        [⋅ ▹ a_placeholder_type] takes related environments to related
        ones, since the placeholder type relates all values, the proof
        among them, but the source entry is a proposition and the target
        entry is not; and a weakening from [⋅ ▹ B] to [⋅ ▹ P], [P] a
        proposition and [B] none, would ask the composite for a kept proof
        where [ρτ] holds [τ 0]'s value. *)
  ; rel_wk_under_ctx_props : forall ρ ρ', Dom ρ ≈ ρ' ∈ rel_wk_under_ctx_rel ->
      forall x, x < List.length Δ ->
      entry_propositional gc_deps gc_stack Γ ρ (φ x) <-> entry_propositional gc_deps gc_stack Δ (⟪φ⟫ ρ) x }.

Notation "Γ ⊨ʷ φ : Δ" := (rel_wk_under_ctx Γ φ Δ) : type_scope.

(** *** Semantic Substitution Equality

    [σ] and [σ'] must stay related after an arbitrary semantic weakening [φ] —
    the Kripke-like quantification that makes the judgment usable under context
    extension.  The four environments are the two ways of evaluating each side:
    [σ[φ]] in [ρ] (the substitution [sb_wk σ φ], which is [σ] postcomposed with
    [φ]) against [σ] in [⟪φ⟫ ρ].  Evaluation is directed by the target
    context [Δ], which puts the proof [⋆ᵈ] at its propositions. *)

#[warnings="-cannot-define-projection"]
Record rel_sub (Δ : ctx) (σ : sub) (φ : wk) (ρ : env) (σ' : sub) (ρ' : env) (R : relation env) : Prop := mk_rel_sub
  { (** The value of [σ[φ]] in [ρ] *)
    ρσφ : env
    (** The value of [σ] in [⟪φ⟫ ρ] *)
  ; ρσ : env
    (** The value of [σ'] in [⟪φ⟫ ρ'] *)
  ; ρ'σ' : env
    (** The value of [σ'[φ]] in [ρ'] *)
  ; ρ'σ'φ : env
    (** The evaluations, at the target [Δ] *)
  ; rel_sub_eval_wk : ⟦ (sb_wk σ φ) : Δ ⟧s ρ ↘ ρσφ
  ; rel_sub_eval : ⟦ σ : Δ ⟧s ⟪φ⟫ ρ ↘ ρσ
  ; rel_sub_eval' : ⟦ σ' : Δ ⟧s ⟪φ⟫ ρ' ↘ ρ'σ'
  ; rel_sub_eval_wk' : ⟦ (sb_wk σ' φ) : Δ ⟧s ρ' ↘ ρ'σ'φ
    (** The four are related in a chain *)
  ; rel_sub_chain : rel_chain R ([ρσφ; ρσ; ρ'σ'; ρ'σ'φ]) }.
#[global] Arguments mk_rel_sub {_ _ _ _ _ _ _}.
Hint Constructors rel_sub : mctt.

(** The entries of the two substitutions are scoped by the source [Γ],
    and the weakenings the body is taken under are bounded on [Γ]: a
    proof is kept as written ([⋆ᵈ⟨M, ρ⟩]), so its readback binds the
    entries of [ρ] up to its free bound ([proof_scope]), which the model
    knows to read back only inside the context.  For example:
    - [Δ ▹ P ⊨ˢ Id,, h : Δ ▹ P ▹ P] with [h = #0]: the head is kept as
      [⋆ᵈ⟨#0[φ]ʷ, ρ⟩], which reads [ρ] at [φ 0] only, inside the context
      [ρ] is related at because [φ] is bounded;
    - at [Γ = ⋅ ▹ ℕ], [Id,, #5] is not scoped: a proof [h #0] substituted
      by it is kept as [h #5], whose readback would read the sixth entry
      of an environment of a one-entry context. *)
#[warnings="-cannot-define-projection"]
Record rel_sub_under_ctx Γ Δ σ σ' : Prop := mk_rel_sub_under_ctx
  { (** The source's environment relation *)
    rel_sub_under_ctx_rel : relation env
    (** The source's context PER *)
  ; rel_sub_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_sub_under_ctx_rel
    (** The target's environment relation *)
  ; rel_sub_under_ctx_rel_o : relation env
    (** The target's context PER *)
  ; rel_sub_under_ctx_per_o : EF Δ ≈ Δ ∈ per_ctx_env ↘ rel_sub_under_ctx_rel_o
    (** The two substitutions related, under every bounded semantic
        weakening into [Γ] *)
  ; rel_sub_under_ctx_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') φ,
      rel_wk φ env_rel' rel_sub_under_ctx_rel ->
      (forall x, x < List.length Γ -> φ x < List.length Γ') ->
      forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        rel_sub Δ σ φ ρ σ' ρ' rel_sub_under_ctx_rel_o
    (** The entries of both substitutions are scoped by the source *)
  ; rel_sub_under_ctx_scoped : forall x, x < List.length Δ ->
      sentry_scoped (List.length Γ) (σ x) /\ sentry_scoped (List.length Γ) (σ' x) }.

Definition valid_sub_under_ctx Γ Δ σ := rel_sub_under_ctx Γ Δ σ σ.
#[global] Arguments valid_sub_under_ctx _ _ _ /.
Hint Transparent valid_sub_under_ctx : mctt.
Hint Unfold valid_sub_under_ctx : mctt.

(** The semantic substitutions and context equality have no syntactic
    judgment of the mutual block, so they keep their notations. *)
Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (at level 70, Γ' at level 69).
Notation "Γ ⊨ˢ σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (at level 70, σ at level 69, σ' at level 69, Δ at level 69).
Notation "Γ ⊨ˢ σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (at level 70, σ at level 69, Δ at level 69).

(** *** Terms

    Terms are required to be stable under semantic substitutions rather than
    weakenings.  [rel_exp] is the four-value pattern of one expression pair.  The
    two environments [ρσ] and [ρ'σ'] are parameters rather than existentials,
    because the type chain and the term chain must be read in the same pair of
    environments: closures capture their environment, so replacing it by a
    pointwise-equal one changes the values. *)

#[warnings="-cannot-define-projection"]
Record rel_exp (M : exp) (σ : sub) (ρ ρσ : env) (M' : exp) (σ' : sub) (ρ' ρ'σ' : env) (R : relation domain) : Prop := mk_rel_exp
  { mσ : domain
  ; m : domain
  ; m' : domain
  ; m'σ' : domain
  ; rel_exp_eval_sub : ⟦ M[σ] ⟧ ρ ↘ mσ
  ; rel_exp_eval : ⟦ M ⟧ ρσ ↘ m
  ; rel_exp_eval' : ⟦ M' ⟧ ρ'σ' ↘ m'
  ; rel_exp_eval_sub' : ⟦ M'[σ'] ⟧ ρ' ↘ m'σ'
  ; rel_exp_chain : rel_chain R ([mσ; m; m'; m'σ']) }.
#[global] Arguments mk_rel_exp {_ _ _ _ _ _ _ _ _}.
Hint Constructors rel_exp : mctt.

(** The same pattern one universe up: the four values of a type are related in
    [per_univ_elem i R], which also fixes the element PER [R] that the term chain
    lives in. *)
Definition rel_typ (i : nat) A σ ρ ρσ A' σ' ρ' ρ'σ' R :=
  rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ_elem i R).
#[global] Arguments rel_typ _ _ _ _ _ _ _ _ _ _ /.
Hint Transparent rel_typ : mctt.
Hint Unfold rel_typ : mctt.

(** The notation [⟦σ⟧(ρ)] suggests that evaluation of [σ] is a function.  It is
    a relation, and [functional_eval_sub] determines its result only up to
    [env_eq].  That does not allow substituting one witness for another, since
    evaluation does not respect [env_eq] (a closure captures its environment).  So
    the two environments are quantified universally, over evaluation witnesses
    supplied by the caller, rather than existentially; any two proofs that [σ]
    evaluates at [ρ] are then interchangeable.

    The relation does not itself claim that [σ] evaluates at [ρ]; that is part of
    [rel_sub_under_ctx Γ' Γ σ σ'], which every instantiation supplies.  In return,
    each case of the fundamental theorem must produce its values at whatever
    environment the caller names.  This is what makes the inductive cases fit: a
    premise's values arrive in the same environment as the conclusion's, so two
    instantiations of one relation share values rather than being pointwise
    equal, and [rel_chain_merge] applies.

    At a type whose value is a proposition ([type_propositional]) the
    terms are proofs, which evaluation never reaches, so they are related
    by their typing alone: the judgment asks nothing of their values.  One
    value of the type is enough, as the PER model relates propositions to
    propositions only. *)

(** The left substituted value of the type [A] is a proposition. *)
Definition type_propositional (A : typ) (σ : sub) (ρ : env) : Prop := rel_typ_propositional A[σ] ρ.

#[warnings="-cannot-define-projection"]
Record rel_exp_under_ctx Γ A M M' : Prop := mk_rel_exp_under_ctx
  { rel_exp_under_ctx_rel : relation env
  ; rel_exp_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_exp_under_ctx_rel
  ; rel_exp_under_ctx_lvl : nat
  ; rel_exp_under_ctx_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        exists (elem_rel : relation domain),
          rel_typ rel_exp_under_ctx_lvl A σ ρ ρσ A σ' ρ' ρ'σ' elem_rel /\
          (type_propositional A σ ρ \/ rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' elem_rel) }.

Definition valid_exp_under_ctx Γ A M := rel_exp_under_ctx Γ A M M.
#[global] Arguments valid_exp_under_ctx _ _ _ /.
Hint Transparent valid_exp_under_ctx : mctt.
Hint Unfold valid_exp_under_ctx : mctt.

(** *** Subtyping

    Not a four-value chain: [per_subtyp] has no symmetry, so the two commutation
    obligations are stated on their own sides and the subtyping obligation
    relates the two inner values only. *)

#[warnings="-cannot-define-projection"]
Record rel_subtyp (i : nat) A σ ρ ρσ A' σ' ρ' ρ'σ' : Prop := mk_rel_subtyp
  { rel_subtyp_aσ : domain
  ; rel_subtyp_a : domain
  ; rel_subtyp_a'σ' : domain
  ; rel_subtyp_a' : domain
  ; rel_subtyp_eval_aσ : ⟦ A[σ] ⟧ ρ ↘ rel_subtyp_aσ
  ; rel_subtyp_eval_a : ⟦ A ⟧ ρσ ↘ rel_subtyp_a
  ; rel_subtyp_eval_a'σ' : ⟦ A'[σ'] ⟧ ρ' ↘ rel_subtyp_a'σ'
  ; rel_subtyp_eval_a' : ⟦ A' ⟧ ρ'σ' ↘ rel_subtyp_a'
  ; rel_subtyp_left : Dom rel_subtyp_aσ ≈ rel_subtyp_a ∈ per_univ i
  ; rel_subtyp_right : Dom rel_subtyp_a'σ' ≈ rel_subtyp_a' ∈ per_univ i
  ; rel_subtyp_sub : Sub rel_subtyp_a <: rel_subtyp_a' at i }.

#[warnings="-cannot-define-projection"]
Record rel_subtyp_under_ctx Γ A A' : Prop := mk_rel_subtyp_under_ctx
  { rel_subtyp_under_ctx_rel : relation env
  ; rel_subtyp_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_subtyp_under_ctx_rel
  ; rel_subtyp_under_ctx_lvl : nat
  ; rel_subtyp_under_ctx_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_subtyp rel_subtyp_under_ctx_lvl A σ ρ ρσ A' σ' ρ' ρ'σ' }.

Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (at level 70, M at level 69, M' at level 69, A at level 69).
Notation "Γ ⊨ M ⊆ M'" := (rel_subtyp_under_ctx Γ M M') (at level 70, M at level 69, M' at level 69).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (at level 70, M at level 69, A at level 69).

(** *** Types of Either Sort

    Two types related at the index [i]: their four values related in
    [per_univ i], whatever their sort.  A type of a universe is one
    ([Γ ⊨ A ≈ A' : Typeω@i] relates relevant types, the elements of the
    universe), and so is a proposition ([Γ ⊨ A ≈ A' : Prop] relates
    propositions, which are types of every index).  This is what an
    extension of a context, and the domain of a [Π], need of a type. *)
#[warnings="-cannot-define-projection"]
Record rel_type_under_ctx Γ (i : nat) A A' : Prop := mk_rel_type_under_ctx
  { (** The relation of the context's environments *)
    rel_type_under_ctx_rel : relation env
  ; rel_type_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_type_under_ctx_rel
    (** At every semantic substitution, the four values related *)
  ; rel_type_under_ctx_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i) }.

Notation "Γ ⊨ᵗ A ≈ A' 'at' i" := (rel_type_under_ctx Γ i A A') (at level 70, A at level 69, A' at level 69, i at level 69).

(** *** Module Expressions

    A module expression is related when its four values are related in the
    module PER, as a term's are in its type's element PER.  A unit [U] is
    represented by the literal [me_lit U], whose value is its closure. *)

#[warnings="-cannot-define-projection"]
Record rel_modexp (H : modexp) (σ : sub) (ρ ρσ : env) (H' : modexp) (σ' : sub) (ρ' ρ'σ' : env) : Prop := mk_rel_modexp
  { hσ : dmod
  ; h : dmod
  ; h' : dmod
  ; h'σ' : dmod
  ; rel_modexp_eval_sub : ⟦ H[σ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ hσ
  ; rel_modexp_eval : ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρσ ↘ h
  ; rel_modexp_eval' : ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ'σ' ↘ h'
  ; rel_modexp_eval_sub' : ⟦ H'[σ']ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h'σ'
  ; rel_modexp_chain : rel_chain per_dmod ([hσ; h; h'; h'σ']) }.
#[global] Arguments mk_rel_modexp {_ _ _ _ _ _ _ _}.
Hint Constructors rel_modexp : mctt.

#[warnings="-cannot-define-projection"]
Record rel_modexp_under_ctx Γ H H' : Prop := mk_rel_modexp_under_ctx
  { rel_modexp_under_ctx_rel : relation env
  ; rel_modexp_under_ctx_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rel_modexp_under_ctx_rel
  ; rel_modexp_under_ctx_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_modexp H σ ρ ρσ H' σ' ρ' ρ'σ' }.

Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).

(** *** The Sorts of a Body's Definitions

    Each term part of the body [Φ] over [D] is of the sort its kind tag
    says ([entry_kind], [abs_kind_sort]): a type of a universe when it is
    tagged [ak_relevant], a type of levels ([LevelSort]) when it is tagged
    [ak_level], a proposition when it is tagged [ak_propositional], in the
    context the entries before it make, as [wf_gentry_def] asks.  A body's environment
    is read by the tags ([eval_body_env]), while the context PER of its
    context ([body_ctx]) reads the sorts of the types, so the two agree
    only under this.  For example, in a body [def h : P := p] with
    [P : Prop] tagged relevant, [eval_body_env] stores the value of [p] at
    [h], while the context PER relates only kept proofs there.  And in
    [module K (u : Level) where def w : Level ≔ u end], the type of [w] is
    a type of levels, of no universe. *)
Fixpoint body_sorts_valid (Φ : gmod) (D : ctx) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ0 _ E =>
      body_sorts_valid Φ0 D /\
      forall A M, entry_tm E = Some (A, M) ->
        exists i, body_ctx Φ0 ++ D ⊨ A : abs_kind_sort (entry_kind E) Typeω@i
  (* read on expansions only ([body_xp]), which have no open *)
  | gm_open Φ0 _ _ _ => body_sorts_valid Φ0 D
  end.

(** *** Contexts

    An inductive relation whose extension step carries both the context PER
    witness and the semantic well-formedness of the head (and, for a
    definition, of its body; for a module slot, of its unit; for a
    definition with a module part, of both), so
    [rel_ctx_wf_per_ctx_env] reads the PER off any derivation.  The validity of
    a unit's parts ([rel_unit_wf]) is defined with it, since a body unit's
    parts form a context.  An assumption is of a type of a sort at its
    kind ([sort_kind]), as in [wf_ctx_extend]; a definition is of a type
    of a sort ([type_sort]), as in [wf_ctx_extend_def]; a definition with
    a module part is of a type of a universe. *)

Inductive rel_ctx_wf : ctx -> Prop :=
(** The empty context *)
| rel_ctx_wf_nil : ⊨ ⋅
(** An assumption of a type of the sort [Srt], at the kind of its types *)
| rel_ctx_wf_cons : forall Γ κ A Srt env_rel,
    ⊨ Γ ->
    EF Γ ▹{κ} A ≈ Γ ▹{κ} A ∈ per_ctx_env ↘ env_rel ->
    sort_kind Srt κ ->
    Γ ⊨ A ≈ A : Srt ->
    ⊨ Γ ▹{κ} A
(** A definition of a type of the sort [Srt], its body valid at it *)
| rel_ctx_wf_cons_def : forall Γ A M Srt env_rel,
    ⊨ Γ ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ env_rel ->
    type_sort Srt ->
    Γ ⊨ A ≈ A : Srt ->
    Γ ⊨ M ≈ M : A ->
    ⊨ Γ ▸ A ≔ M
(** A module slot: its unit valid *)
| rel_ctx_wf_cons_mod : forall Γ U env_rel,
    ⊨ Γ ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    rel_unit_wf Γ U ->
    ⊨ Γ ▹ₘ U
(** A definition with a module part: its term part valid as a definition,
    its unit as a slot *)
| rel_ctx_wf_cons_dm : forall Γ A M U i env_rel,
    ⊨ Γ ->
    EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ M ≈ M : A ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    rel_unit_wf Γ U ->
    ⊨ Γ ▸ₘ A ≔ M ‖ U
with rel_unit_wf : ctx -> gunit -> Prop :=
| rel_unit_wf_body : forall Γ Δ Φ Φx,
    tele_ass Δ ->
    body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx ->
    body_shape Φ Φ ->
    body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Δ ++ Γ ->
    body_sorts_valid Φx (Δ ++ Γ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    rel_unit_wf Γ (gu_open Δ Φ)
| rel_unit_wf_alias : forall Γ Δ E,
    tele_ass Δ ->
    ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ᵐ E ≈ E ->
    rel_unit_wf Γ (gu_mk Δ (md_alias E))
where "⊨ Γ" := (rel_ctx_wf Γ) : type_scope.

Hint Constructors rel_ctx_wf rel_unit_wf : mctt.

(** Two units are equivalent when their closures are related and each is
    valid in its parts.  Two extensions of a context are equivalent when
    both extended contexts are semantically well formed and related. *)
Record rel_unit_under_ctx Γ U U' : Prop := mk_rel_unit_under_ctx
  { rel_unit_under_ctx_lit : Γ ⊨ᵐ me_lit U ≈ me_lit U'
  ; rel_unit_under_ctx_left : rel_unit_wf Γ U
  ; rel_unit_under_ctx_right : rel_unit_wf Γ U' }.

Record rel_ext_under_ctx Γ Ψ Ψ' : Prop := mk_rel_ext_under_ctx
  { rel_ext_under_ctx_left : ⊨ Ψ ++ Γ
  ; rel_ext_under_ctx_right : ⊨ Ψ' ++ Γ
  ; rel_ext_under_ctx_eq : ⊨ Ψ ++ Γ ≈ Ψ' ++ Γ }.

Notation "Γ ⊨ᵘ U ≈ U'" := (rel_unit_under_ctx Γ U U') (at level 70, U at level 69, U' at level 69).
Notation "Γ ⊨ˣ Ψ ≈ Ψ'" := (rel_ext_under_ctx Γ Ψ Ψ') (at level 70, Ψ at level 69, Ψ' at level 69).

End Fixed_GCtx.

Notation "Γ ⊨ʷ φ : Δ" := (rel_wk_under_ctx Γ φ Δ) : type_scope.
Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (at level 70, Γ' at level 69).
Notation "Γ ⊨ˢ σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (at level 70, σ at level 69, σ' at level 69, Δ at level 69).
Notation "Γ ⊨ˢ σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (at level 70, σ at level 69, Δ at level 69).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (at level 70, M at level 69, M' at level 69, A at level 69).
Notation "Γ ⊨ M ⊆ M'" := (rel_subtyp_under_ctx Γ M M') (at level 70, M at level 69, M' at level 69).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (at level 70, M at level 69, A at level 69).
Notation "Γ ⊨ᵗ A ≈ A' 'at' i" := (rel_type_under_ctx Γ i A A') (at level 70, A at level 69, A' at level 69, i at level 69).
Notation "⊨ Γ" := (rel_ctx_wf Γ) : type_scope.
Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).
Notation "Γ ⊨ᵘ U ≈ U'" := (rel_unit_under_ctx Γ U U') (at level 70, U at level 69, U' at level 69).
Notation "Γ ⊨ˣ Ψ ≈ Ψ'" := (rel_ext_under_ctx Γ Ψ Ψ') (at level 70, Ψ at level 69, Ψ' at level 69).

(** [rel_param_typed Γ A l]: the parameter type [A] over [Γ] is, in the
    PER model, a type of the universe at [l] or a type of levels: the
    counterpart of [param_typed].  For example, the parameter type [Level]
    of [module M (l : Level) := ...] is a type of levels. *)
Definition rel_param_typed {GC : GCtx} (Γ : ctx) (A : typ) (l : nat) : Prop :=
  Γ ⊨ A : Typeω@l \/ Γ ⊨ A : LevelSort.

(** [rel_params_relevant Γ Δ l]: every parameter of the telescope [Δ]
    over [Γ] is, in the PER model, a type of the universe at [l] or a type
    of levels ([rel_param_typed]), in the context of the parameters after
    it.  It is the counterpart of [params_relevant]: modules take relevant
    parameters, as the typing of units and of module application asks.
    For example, the parameter [X] of [module M (X : Typeω@0) := ...] is a
    type of [Typeω@1], so
    [rel_params_relevant Γ (ce_ass ak_relevant (Typeω@0) :: nil) 1]
    holds, while a proposition [P : Prop] as a parameter is not of any
    universe. *)
Definition rel_params_relevant {GC : GCtx} (Γ Δ : ctx) (l : nat) : Prop :=
  forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> rel_param_typed (Δ2 ++ Γ) A l.

(** ** 2. Valid Units, and Contexts with Valid Slots

    Lookups are read at [Θm ⍮ Ξm], a global context [GC] extends. *)

Section Valid.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).

(** [valid_args Γ T Ns]: the arguments [Ns] fill, in order, the outermost
    parameters of the closed telescope [T], each valid in [Γ] at its
    parameter's type instantiated by the arguments before it, as
    [args_ok] says syntactically. *)
#[warnings="-cannot-define-projection"]
Record valid_args (Γ : ctx) (T : ctx) (Ns : list exp) : Prop := mk_valid_args
  { valid_args_rest : ctx
  ; valid_args_filled : ctx
  ; valid_args_split : T = valid_args_rest ++ valid_args_filled
  ; valid_args_length : List.length valid_args_filled = List.length Ns
  ; valid_args_ass : tele_ass valid_args_filled
  ; valid_args_scoped : ctx_scoped 0 valid_args_filled
  ; valid_args_args : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts valid_args_filled Id Ns) k = Some A ->
      Γ ⊨ N : A
    (** The types of the arguments are of a relevant sort, a universe or
        the types of levels: the parameters of modules are relevant, as
        application asks ([wf_me_app]) *)
  ; valid_args_relevant : forall k A, nth_error (tele_insts valid_args_filled Id Ns) k = Some A ->
      exists Srt, relevant_sort Srt /\ Γ ⊨ A : Srt }.

(** A unit is valid when its parts are ([valid_unit]): a filed module at
    arguments valid against its telescope ([valid_args]); a local body whose
    context, read as its expansion, is valid, whose submodules (the module
    parts of its entries, [entry_unit]) are valid units in the context the
    body before each makes, and whose opens'
    targets are valid; an alias whose target is.  A module expression is
    valid in what it denotes ([valid_modexp]) when it is equal, in the PER model, to
    a valid unit denoting the same module part: the semantic counterpart of
    lookup soundness. *)
Inductive valid_unit : ctx -> modexp -> Prop :=
(** A filed module at arguments valid against its telescope *)
| valid_unit_filed : forall Γ p T Φ Ns,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ -> valid_args Γ T Ns ->
    valid_unit Γ (me_apps (qname_mod p) Ns)
(** A local body, its parts valid.  The unit's own parameters are relevant
    in the PER model ([rel_params_relevant]): the member closures of the
    unit lacking them relate at a relevant domain only.  For example, in
    [module M (A : Typeω@0) := { def x : A -> A := fun a => a }], the
    member [M.x] read without an argument is a member closure, related to
    [λ a. a] because [A]'s value is relevant. *)
| valid_unit_body : forall Γ Δ Φ Φx,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> tele_ass Δ -> (exists l : nat, rel_params_relevant Γ Δ l) ->
    ⊨ Γ -> ⊨ body_ctx Φx ++ Δ ++ Γ -> body_sorts_valid Φx (Δ ++ Γ) ->
    (forall y Φ0 E U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       valid_unit (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U)) ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    Γ ⊨ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> valid_modexp (Ψ ++ Δ ++ Γ) H) ->
    valid_unit Γ (me_lit (gu_open Δ Φ))
(** An alias, its target valid.  The unit's own parameters are relevant in
    the PER model, as for [valid_unit_body] *)
| valid_unit_alias : forall Γ Δ E,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    tele_ass Δ -> (exists l : nat, rel_params_relevant Γ Δ l) -> ⊨ Γ -> ⊨ Δ ++ Γ ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    Δ ++ Γ ⊨ᵐ E ≈ E -> valid_modexp (Δ ++ Γ) E ->
    valid_unit Γ (me_lit (gu_mk Δ (md_alias E)))
(** [valid_modexp Γ H]: [H] is equal to a valid unit that denotes its module part. *)
with valid_modexp : ctx -> modexp -> Prop :=
(** [H] and the valid unit [K] denote the same module part *)
| valid_modexp_intro : forall Γ H R Rm K RK,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θm Ξm Γ H R -> mdesc_mod R = Some Rm ->
    Γ ⊨ᵐ H ≈ K -> valid_unit Γ K -> mdenote Θm Ξm Γ K RK -> mdesc_mod RK = Some Rm ->
    valid_modexp Γ H.

Scheme valid_unit_mut_ind := Induction for valid_unit Sort Prop
with valid_modexp_mut_ind := Induction for valid_modexp Sort Prop.
Combined Scheme valid_unit_modexp_ind from valid_unit_mut_ind, valid_modexp_mut_ind.

(** A context is semantically well formed with valid slots ([valid_ctx])
    when each extension is semantically well formed, and the unit of each
    slot is valid in the context before it. *)
Inductive valid_ctx : ctx -> Prop :=
| valid_ctx_nil : valid_ctx ⋅
| valid_ctx_ass : forall Γ κ A, valid_ctx Γ -> ⊨ Γ ▹{κ} A -> valid_ctx (Γ ▹{κ} A)
| valid_ctx_def : forall Γ A M, valid_ctx Γ -> ⊨ Γ ▸ A ≔ M -> valid_ctx (Γ ▸ A ≔ M)
| valid_ctx_mod : forall Γ U, valid_ctx Γ -> ⊨ Γ ▹ₘ U -> valid_unit Γ (me_lit U) -> valid_ctx (Γ ▹ₘ U)
(** A definition with a module part: semantically well formed, its unit
    valid as a slot's is *)
| valid_ctx_dm : forall Γ A M U, valid_ctx Γ -> ⊨ Γ ▸ₘ A ≔ M ‖ U -> valid_unit Γ (me_lit U) ->
    valid_ctx (Γ ▸ₘ A ≔ M ‖ U).

End Valid.

(** ** 3. Valid Global Contexts

    What the filed modules and open frames of [Θm ⍮ Ξm] are worth, at [GC]:
    each is a stored body there, its path evaluates to it, and its telescope
    is valid; each of its entries has the kind of its entry there, and so
    has each module stored under it; each of its term entries is the member
    of a type over its telescope, of a value related to itself there, with
    its δ-reduct at arguments for the outer part of the telescope, if it has
    one, a term over that part instantiated, valid there, whose value at
    arguments is the member's value applied to them (an inductive type's
    reduct, its type former at the arguments, is not a [λ]); each alias
    entry is a valid unit in any valid context. *)

Section Filed.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).

(** The member kind of an entry: a definition is a term of the kind it is
    tagged with, a module a module, and an entry with a term part and a
    module part (an inductive type, a definition with a module part, a
    record type) is both ([member_kind_dm]). *)
Definition entry_member_kind (E : gentry) : member_kind :=
  match E with
  | ge_def _ _ r _ _ => member_kind_term r
  | ge_mod _ _ => member_kind_mod
  | _ => member_kind_dm
  end.

(** A value [g] related to itself at the value of the closed type
    [ctx_pi_at r T A0], into the kind [r]; asked of members of an
    evaluated kind only ([valid_filed_value_self]). *)
#[warnings="-cannot-define-projection"]
Record rel_self (r : abs_kind) (T : ctx) (A0 : exp) (g : domain) : Prop := mk_rel_self
  { (** The universe index of the type *)
    rel_self_lvl : universe_index
    (** The relation of its elements *)
  ; rel_self_rel : relation domain
    (** Its value *)
  ; rel_self_typ : domain
    (** The type evaluates to it *)
  ; rel_self_eval : ⟦ ctx_pi_at r T A0 ⟧ nil ↘ rel_self_typ
    (** It is a type of the index, of that relation *)
  ; rel_self_per : per_univ_elem rel_self_lvl rel_self_rel rel_self_typ rel_self_typ
    (** [g] is related to itself at it *)
  ; rel_self_elem : rel_self_rel g g }.

(** The value of the term member [x], of an evaluated kind, of the filed
    module [p], of type [A0] over its telescope [T], read as [R0].  Its δ-reduct at
    arguments for the outer part of [T], if it has one, has a value at
    arguments related at the type there to the member's value applied to
    them: the value applied evaluates its body at its arguments stored at
    the values of the domains ([eval_app_fn]), the reduct at the
    telescope's closures ([env_tele]), and a proof kept in the body keeps
    the environment it is met in, so the two values are related, not
    equal. *)
#[warnings="-cannot-define-projection"]
Record valid_filed_value (p : qname) (T : ctx) (x : String.string) (R0 : mdesc) (A0 : exp) : Prop := mk_valid_filed_value
  { (** The member's value *)
    valid_filed_value_val : domain
    (** The reading at arguments for the outer part of the telescope, as
        [valid_filed_term_reads], restated with the reduct's value: a
        reduct is a term instantiated, which does not determine the term,
        and [filed_mem] needs one term with both its validity and its
        value *)
  ; valid_filed_value_reads : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns ->
      mdesc_term_part_ats R0 Ns = Some R1 ->
      mdesc_type R1 = Some (ctx_pi_at (mdesc_kind R0) T1 A0)[sb_of_list Id Ns] /\
      (mdesc_reduct R1 = None \/
       exists M1, mdesc_reduct R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi_at (mdesc_kind R0) T1 A0 /\
         forall ns m, List.length ns = List.length T2 -> per_gargs (rev T2) nil nil ns ns ->
           ⟦ M1 ⟧ env_tele nil (rev T2) ns ↘ m ->
           exists v, $*| valid_filed_value_val & ns | gc_deps ⍮ gc_stack ↘ v /\
             Dom m ≈ v ∈ per_head (ctx_pi_at (mdesc_kind R0) T1 A0) (ctx_pi_at (mdesc_kind R0) T1 A0)
                               (env_tele nil (rev T2) ns) (env_tele nil (rev T2) ns))
    (** The value is the member's stored value, closed over the telescope,
        which selection at arguments for all of it applies to them
        ([eval_sel_global_apps]); not the member closure that selection
        at fewer arguments gives ([eval_sel_global_unsat]) *)
  ; valid_filed_value_sel : global_member_value gc_deps gc_stack p x valid_filed_value_val
    (** The value is related to itself at the closed type *)
  ; valid_filed_value_self : rel_self (mdesc_kind R0) T A0 valid_filed_value_val }.

(** The term member [x] of the filed module [p], over its telescope [T],
    read as [R0]: of a type over [T] of the sort of the member's kind
    [mdesc_kind R0] ([abs_kind_sort]), as [wf_gentry_def] asks, and so are
    the [Π]s over the telescope into the kind; with its δ-reduct at
    arguments for the outer part of [T] (read as a filed entry's term part
    is, [mdesc_term_part_ats]), if it has one, a term over that part
    instantiated, valid there; and, if of an evaluated kind, of a value
    ([valid_filed_value]).  A member tagged [ak_propositional] stores no
    value: selection keeps it as written ([eval_sel_global_proof]), so
    nothing is asked of its value or its reduct's. *)
#[warnings="-cannot-define-projection"]
Record valid_filed_term (p : qname) (T : ctx) (x : String.string) (R0 : mdesc) : Prop := mk_valid_filed_term
  { (** The member's type over the telescope *)
    valid_filed_term_typ : exp
    (** A universe index: the member's type is of [Typeω@valid_filed_term_level]
        at [ak_relevant]; at the other kinds the sort ([Prop], [LevelSort])
        does not mention it ([abs_kind_sort]) *)
  ; valid_filed_term_level : nat
    (** The type is a valid type of the sort of the member's kind: a
        universe, [Prop], or the types of levels ([def v : Level ≔ zero]) *)
  ; valid_filed_term_typed : T ⊨ valid_filed_term_typ : abs_kind_sort (mdesc_kind R0) Typeω@valid_filed_term_level
    (** The reading at arguments for the outer part of the telescope: the
        type, and the reduct, if any, valid *)
  ; valid_filed_term_reads : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> mdesc_term_part_ats R0 Ns = Some R1 ->
      mdesc_type R1 = Some (ctx_pi_at (mdesc_kind R0) T1 valid_filed_term_typ)[sb_of_list Id Ns] /\
      (mdesc_reduct R1 = None \/
       exists M1, mdesc_reduct R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi_at (mdesc_kind R0) T1 valid_filed_term_typ)
    (** The value of a member of an evaluated kind *)
  ; valid_filed_term_value : evaluated_kind (mdesc_kind R0) -> valid_filed_value p T x R0 valid_filed_term_typ
    (** The [Π]s over the telescope into the member's kind are formed
        ([pi_kinds]): at [ak_level] every parameter is a level
        ([level_sorted_parameters], as [wf_gentry_def] asks); at the other
        kinds any parameter is *)
  ; valid_filed_term_pi_kinds : forall Δ1 κ A Δ2, T = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ (mdesc_kind R0) }.

Record valid_filed_mod (p : qname) (T : ctx) (Φ : gmod) : Prop := mk_valid_filed_mod
  { valid_filed_mod_stored : exists Φ', gc_loc gc_deps gc_stack p = Some (T, Φ')
  ; valid_filed_mod_path : forall ρ, ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p nil
  ; valid_filed_mod_tele_wf : ⊨ T
  ; valid_filed_mod_tele_ass : tele_ass T
  ; valid_filed_mod_tele_scoped : ctx_scoped 0 T
  ; valid_filed_mod_kinds : forall x Φ0 E, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      dmod_member_kind gc_deps gc_stack (dm_global p nil) (x :: nil) (entry_member_kind E)
    (** A body stored below it is a module, unless it is the module of a
        member with a term part (whose kind is that member's) *)
  ; valid_filed_mod_sub_kinds : forall x TΦ, gc_loc Θm Ξm (qname_app p (x :: nil)) = Some TΦ ->
      ~ dm_path gc_deps gc_stack (qname_app p (x :: nil)) ->
      dmod_member_kind gc_deps gc_stack (dm_global p nil) (x :: nil) member_kind_mod
  ; valid_filed_mod_terms : forall x Φ0 E R0, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      entry_term (Some (qname_in p x)) E = Some R0 ->
      valid_filed_term p T x R0
    (** The open frame of a member's module under it is its type former,
        as a filed member's entry is *)
  ; valid_filed_mod_ind_frames : forall x pq k D Mk, gs_find_ind Ξm (qname_in p x) = Some (pq, k, D) -> ind_member D k = Some Mk ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (im_params D Mk) (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) (Some (a_ind pq k)))
    (** So is the open frame of a record type's module under it *)
  ; valid_filed_mod_record_frames : forall x R, gs_find_record Ξm (qname_in p x) = Some R ->
      valid_filed_term p T x (mdesc_term ak_relevant (ctx_pi (record_params R) (record_sort R)) (Some (a_record (qname_in p x))))
  ; valid_filed_mod_aliases : forall y Φ0 E Ua, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
      gc_module gc_deps gc_stack (qname_in p y) = Some (mr_alias Ua) /\
      forall Γ, ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ -> valid_unit Θm Ξm Γ (me_lit Ua)
    (** The parameters of the telescope are types of a universe, at one
        level: modules take relevant parameters, as the typing of units
        and of modules asks ([params_relevant]) *)
  ; valid_filed_mod_tele_relevant : exists l : nat, rel_params_relevant nil T l }.

Definition valid_filed_mods : Prop :=
  forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) -> valid_filed_mod p T Φ.

(** A group is semantically valid at its core: the telescopes and types
    of each of its members, read in the PER model.  These are the group's
    own, which never mention it, a view's too.  [nparams_prefix M k] is
    the context of the first [k] non-uniform parameters of a member [M],
    [nonrec_args_prefix gs k] that of the first [k] non-recursive
    arguments of a constructor. *)
Definition nparams_prefix (M : imember) (k : nat) : ctx := List.rev (List.firstn k (List.rev (im_nparams M))).
Definition nonrec_args_prefix (gs : list carg) (k : nat) : ctx := List.rev (List.firstn k (cargs_nonrec_tele gs)).

(** The kinds of a constructor's non-recursive arguments, in the order of
    [cargs_nonrec]. *)
Fixpoint cargs_nonrec_kinds (gs : list carg) : list abs_kind :=
  match gs with
  | nil => nil
  | ca_arg r _ :: gs => r :: cargs_nonrec_kinds gs
  | ca_rec _ :: gs => cargs_nonrec_kinds gs
  end.

(** The views of a group with its members as variables ([grp_selfs_ctx]),
    read in the PER model: [views_self_typed], each judgment semantic.  The
    instances [IsS] are the views' arguments before the group is filed;
    the filed ones are their images by [grp_sb] ([views_self_valid_link]). *)
Record views_self_valid (D : ind_decl) (IsS : nat -> list exp) : Prop := mk_views_self_valid
  { (** Each view's uniform arguments are its [IsS] instance with the
        members sent to the group's own type formers ([grp_sb]) *)
    views_self_valid_link : forall mp, ind_mpath D 0 = Some mp ->
      forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)
    (** Each instance argument is valid at the container's uniform
        telescope, over the members as variables *)
  ; views_self_valid_is : forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> nth_error (IsS k) j = Some I ->
      nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
      grp_selfs_ctx D ⊨ I : T
    (** The view a view maps a container view to has, as instance, the
        container view's arguments at this view's instance *)
  ; views_self_valid_view_is : forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      ind_lookup gc_deps gc_stack q'' = Some D'' ->
      nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      nth_error (IsS v) j' = Some C ->
      nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
      nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
      grp_selfs_ctx D ⊨ C ≈ C' : T[sb_of_list Id (IsS k)]
    (** A mapped member's non-uniform parameters are the container
        member's at the instance *)
  ; views_self_valid_nparams : forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      grp_selfs_ctx D ⊨ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))
    (** A mapped member's constructor arguments are the container
        member's at the instance *)
  ; views_self_valid_args : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
        ⊨ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs
    (** The shapes' domains of corresponding recursive arguments agree at
        the instance *)
  ; views_self_valid_doms : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      d < ptyp_depth t ->
      exists i : nat, tele_wk (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                  ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
        ⊨ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
        ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i
    (** The parameters of corresponding recursive arguments agree at the
        instance *)
  ; views_self_valid_ps : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
      ind_member D (ptyp_mem t) = Some Mj ->
      nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
      nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                   (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
      tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
        ⊨ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
        ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
        : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
    (** The container's sort at the instance is below the group's *)
  ; views_self_valid_sort : forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' ->
      grp_selfs_ctx D ⊨ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ
    (** Each record view's instance is its [IsS] instance with the members
        sent to the group's own type formers *)
  ; views_self_valid_record_link : forall mp, ind_mpath D 0 = Some mp ->
      forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)
    (** Each record view's instance argument is valid at the record's
        parameters, over the members as variables *)
  ; views_self_valid_record_instances : forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      record_lookup gc_deps gc_stack qr = Some R -> nth_error (IsS k) j = Some I ->
      nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
      grp_selfs_ctx D ⊨ I : T
    (** The record's fields at a record view's instance are the view's
        classified ones (the record view equations) *)
  ; views_self_valid_record_fields : forall k Mk qr Is fl R c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      record_lookup gc_deps gc_stack qr = Some R -> im_cons Mk = (c, gs) :: nil ->
      grp_selfs_ctx D ⊨ˣ tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k)) ≈ self_cargs_ctx D IsS Mk gs
    (** A record view's type is in the group's sort *)
  ; views_self_valid_record_type : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      grp_selfs_ctx D ⊨ apps_exp (a_record qr) (IsS k) : (ind_sort D)[self_wk D 0]ʷ }.

(** A semantically valid group (see above). *)
Record valid_ind_decl (D : ind_decl) : Prop := mk_valid_ind_decl
{ (** The uniform parameters are a valid context *)
  valid_ind_decl_uparams : ⊨ ind_uparams D
(** Each uniform parameter is a type of a universe or a type of levels
    ([rel_param_typed]), under those outside it: parameters are relevant
    ([params_relevant], read semantically), for example the [l : Level] of
    [Vec (l : Level) (A : Type@l)].  The type former and the constructors
    take their parameters as relevant arguments ([arg_kind] of
    [d_ind], and of [d_con] before its arguments), so their values are
    relevant only when the parameters' types are *)
; valid_ind_decl_uparams_relevant : exists l, rel_params_relevant ⋅ (ind_uparams D) l
(** The sort is a valid type over them *)
; valid_ind_decl_sort : exists i, ind_uparams D ⊨ ind_sort D : Typeω@i
(** The level of the sort, a level ([decl_typed_sort_lvl]): a small sort is below
    the large universes. *)
; valid_ind_decl_sort_lvl : exists n, ind_uparams D ⊨ ind_sort_lvl (ind_sort D) : Level@n
(** Each member's parameters are a valid context *)
; valid_ind_decl_params : forall k Mk, ind_member D k = Some Mk -> ⊨ im_params D Mk
(** Each member's type is a valid closed type *)
; valid_ind_decl_ty : forall k Mk, ind_member D k = Some Mk -> exists i, ⋅ ⊨ ind_ty D Mk : Typeω@i
(** Each non-uniform parameter is a valid type of the sort, and a type,
    over those before it *)
; valid_ind_decl_nparams : forall k Mk j κ A, ind_member D k = Some Mk -> List.nth_error (List.rev (im_nparams Mk)) j = Some (ce_ass κ A) ->
    nparams_prefix Mk j ++ ind_uparams D ⊨ A : (ind_sort D)[wk_shiftn j]ʷ /\
    exists i, nparams_prefix Mk j ++ ind_uparams D ⊨ A : Typeω@i
(** Each non-uniform parameter is relevant, as the sort is a universe
    ([wf_gentry_ind]) *)
; valid_ind_decl_nparams_kind : forall k Mk j κ A, ind_member D k = Some Mk ->
    List.nth_error (List.rev (im_nparams Mk)) j = Some (ce_ass κ A) -> κ = ak_relevant
(** Each prefix of a constructor's non-recursive arguments is a valid
    context *)
; valid_ind_decl_strat : forall k Mk c gs j, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> j <= List.length (cargs_nonrec gs) ->
    ⊨ nonrec_args_prefix gs j ++ im_params D Mk
(** Each non-recursive argument is a valid type of the sort, or a
    proposition, as its kind [r] says ([abs_kind_sort]), and a type of
    that sort, over those before it *)
; valid_ind_decl_arg : forall k Mk c gs j r A, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.nth_error (cargs_nonrec gs) j = Some A -> List.nth_error (cargs_nonrec_kinds gs) j = Some r ->
    nonrec_args_prefix gs j ++ im_params D Mk ⊨ A : abs_kind_sort r (ind_sort D)[wk_shiftn (j + im_nn Mk)]ʷ /\
    exists i, nonrec_args_prefix gs j ++ im_params D Mk ⊨ A : abs_kind_sort r Typeω@i
(** No non-recursive argument is of a type of levels ([carg_kind]) *)
; valid_ind_decl_arg_kind : forall k Mk c gs j r, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.nth_error (cargs_nonrec_kinds gs) j = Some r -> carg_kind r
(** Each member's constructor names are distinct *)
; valid_ind_decl_nodup : forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))
(** Each parameter of a recursive argument's shape is valid at its
    member's telescope *)
; valid_ind_decl_rec_field : forall k Mk c gs gs1 t gs2 Mj m P T, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
    List.nth_error (ptyp_ps t) m = Some P ->
    List.nth_error (tele_insts (im_nparams Mj)
                      (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (ptyp_ps t)) m
      = Some T ->
    ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk ⊨ P : T
(** The domains of a recursive argument's shape, each over those before
    it, are types of the sort. *)
; valid_ind_decl_dom : forall k Mk c gs gs1 t gs2 j B, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
    doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
      ⊨ B : (ind_sort D)[wk_shiftn (j + List.length (cargs_nonrec gs1) + im_nn Mk)]ʷ /\
    exists i, doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
      ⊨ B : Typeω@i
(** Each recursive argument gives its member as many parameters as it
    has *)
; valid_ind_decl_params_length : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> cargs_params_length D gs
(** The contexts of a shape's domains are valid *)
; valid_ind_decl_dctx : forall k Mk c gs gs1 t gs2 j, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
    ⊨ doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
(** The views, with the group's members as variables. *)
; valid_ind_decl_views : exists IsS, views_self_valid D IsS
}.

(** A semantically valid record declaration: its parameters, its sort and
    its fields, read in the PER model. *)
Record valid_record_decl (R : record_decl) : Prop := mk_valid_record_decl
{ (** The parameters are a valid context *)
  params_valid : ⊨ record_params R
(** Each parameter is a type of a universe or a type of levels
    ([rel_param_typed]), under those outside it, for example the
    [l : Level] of [Box (l : Level)]: the record type former takes its
    parameters as relevant arguments *)
; params_relevant_valid : exists l, rel_params_relevant ⋅ (record_params R) l
(** The sort is a valid type over them *)
; sort_valid : exists i : nat, record_params R ⊨ record_sort R : Typeω@i
(** The fields, over the parameters, are a valid context *)
; field_ctx_valid : ⊨ record_fctx R (List.length (record_fields R)) ++ record_params R
(** Each field is a type of the sort, or a proposition, as its stored
    kind says ([abs_kind_sort]), over the parameters and the fields
    before it *)
; fields_valid : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
    record_fctx R k ++ record_params R ⊨ T : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ
(** No field is of a type of levels ([field_kind]) *)
; fields_kind_valid : forall k, field_kind (record_field_kind R k)
}.

End Filed.

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, and what it
    files and has open is valid there, its declarations too. *)
Record valid_gctx_embedding (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { valid_gctx_embedding_embedding : gctx_embedding Θ1 Ξ1 Θ2 Ξ2
  ; valid_gctx_embedding_wf : ⊢ᵍ Θ1 ⍮ Ξ1
  ; valid_gctx_embedding_filed : @valid_filed_mods (gc_mk Θ2 Ξ2) Θ1 Ξ1
  ; valid_gctx_embedding_ind_field : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @valid_ind_decl (gc_mk Θ2 Ξ2) D
  ; valid_gctx_embedding_record : forall p R, record_lookup Θ1 Ξ1 p = Some R -> @valid_record_decl (gc_mk Θ2 Ξ2) R
  }.

(** ** 4. The Semantic Judgments

    A semantic judgment is stated at a global context [Θ ⍮ Ξ], as the
    syntactic one is, and holds at every global context [Θ2 ⍮ Ξ2] that
    [Θ ⍮ Ξ] embeds into soundly: there it is the relation of the first two
    parts, read in the PER model of [Θ2 ⍮ Ξ2], with lookups read at
    [Θ ⍮ Ξ].  Each judgment about the members of a context also states the
    context, with valid slots ([valid_ctx]).  The units of [⊨ᵘ] are moreover
    valid ([valid_unit]), the extended contexts of [⊨ˣ] have valid slots, and the
    module expressions of [⊨ᵐ] are valid in what they denote ([valid_modexp]). *)

(** Each judgment of [Θ ⍮ Ξ], read at a target [Θ2 ⍮ Ξ2]. *)

Record sem_exp_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (A M M' : exp) : Prop :=
  mk_sem_exp_eq_at
  { sem_exp_eq_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_exp_eq_at_rel : @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M' }.

Record sem_subtyp_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (A A' : typ) : Prop :=
  mk_sem_subtyp_at
  { sem_subtyp_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_subtyp_at_rel : @rel_subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A' }.

(** A universe: large, or small at a valid level. *)
Record sem_is_univ_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop :=
  mk_sem_is_univ_at
  { sem_is_univ_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_is_univ_at_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (Level@n) L L) }.

Record sem_ext_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ Ψ Ψ' : ctx) : Prop := mk_sem_ext_eq_at
  { sem_ext_eq_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_ext_eq_at_rel : @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ'
  ; sem_ext_eq_at_ext : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ (Ψ ++ Γ)
  ; sem_ext_eq_at_ext' : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ (Ψ' ++ Γ) }.

Record sem_unit_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U U' : gunit) : Prop :=
  mk_sem_unit_eq_at
  { sem_unit_eq_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_unit_eq_at_rel : @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U'
  ; sem_unit_eq_at_valid : @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U)
  ; sem_unit_eq_at_valid' : @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U') }.

(** Module expressions: related, and valid in what they denote. *)
Record sem_modexp_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (H H' : modexp) : Prop :=
  mk_sem_modexp_eq_at
  { sem_modexp_eq_at_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sem_modexp_eq_at_rel : @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H'
  ; sem_modexp_eq_at_valid : @valid_modexp (gc_mk Θ2 Ξ2) Θ Ξ Γ H
  ; sem_modexp_eq_at_valid' : @valid_modexp (gc_mk Θ2 Ξ2) Θ Ξ Γ H' }.

Arguments sem_exp_eq_at_ctx {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments sem_exp_eq_at_rel {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments sem_subtyp_at_ctx {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments sem_subtyp_at_rel {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments sem_is_univ_at_ctx {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments sem_is_univ_at_univ {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments sem_ext_eq_at_ctx {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sem_ext_eq_at_rel {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sem_ext_eq_at_ext {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sem_ext_eq_at_ext' {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sem_unit_eq_at_ctx {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sem_unit_eq_at_rel {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sem_unit_eq_at_valid {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sem_unit_eq_at_valid' {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sem_modexp_eq_at_ctx {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sem_modexp_eq_at_rel {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sem_modexp_eq_at_valid {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sem_modexp_eq_at_valid' {Θ Ξ Θ2 Ξ2 Γ H H'}.

(** The judgments. *)

Definition sem_ctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ.

Definition sem_exp_eq Θ Ξ Γ A M M' : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_exp_eq_at Θ Ξ Θ2 Ξ2 Γ A M M'.

Definition sem_exp Θ Ξ Γ A M : Prop := sem_exp_eq Θ Ξ Γ A M M.

Definition sem_subtyp Θ Ξ Γ A A' : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_subtyp_at Θ Ξ Θ2 Ξ2 Γ A A'.

Definition sem_is_univ Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_is_univ_at Θ Ξ Θ2 Ξ2 Γ U.

Definition sem_ext_eq Θ Ξ Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_ext_eq_at Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'.

Definition sem_unit_eq Θ Ξ Γ U U' : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_unit_eq_at Θ Ξ Θ2 Ξ2 Γ U U'.

Definition sem_modexp_eq Θ Ξ Γ H H' : Prop :=
  forall Θ2 Ξ2, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> sem_modexp_eq_at Θ Ξ Θ2 Ξ2 Γ H H'.

Notation "⊨ Θ ⍮ Ξ ⍮ Γ" := (sem_ctx Θ Ξ Γ)
  (at level 70, Θ at next level, Ξ at level 69, Γ at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A" := (sem_exp_eq Θ Ξ Γ A M M')
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, M' at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ M : A" := (sem_exp Θ Ξ Γ A M)
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A'" := (sem_subtyp Θ Ξ Γ A A')
  (at level 70, Ξ at level 69, Γ at level 69, A at level 69, A' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U" := (sem_is_univ Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ'" := (sem_ext_eq Θ Ξ Γ Ψ Ψ')
  (at level 70, Ξ at level 69, Γ at level 69, Ψ at level 69, Ψ' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U'" := (sem_unit_eq Θ Ξ Γ U U')
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69, U' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'" := (sem_modexp_eq Θ Ξ Γ H H')
  (at level 70, Ξ at level 69, Γ at level 69, H at level 69, H' at level 69) : type_scope.

#[export]
Hint Constructors rel_sub : mctt.
#[export]
Hint Transparent valid_sub_under_ctx : mctt.
#[export]
Hint Unfold valid_sub_under_ctx : mctt.
#[export]
Hint Constructors rel_exp : mctt.
#[export]
Hint Transparent rel_typ : mctt.
#[export]
Hint Unfold rel_typ : mctt.
#[export]
Hint Transparent valid_exp_under_ctx : mctt.
#[export]
Hint Unfold valid_exp_under_ctx : mctt.
#[export]
Hint Constructors rel_ctx_wf rel_unit_wf rel_modexp : mctt.

(** A semantic weakening in scope says its weakening moves no variable
    down. *)
Existing Class rel_wk.
#[export] Existing Instance rel_wk_mono.

Existing Class rel_wk_under_ctx.

#[export] Instance rel_wk_under_ctx_mono {GC : GCtx} {Γ φ Δ} (Hφ : Γ ⊨ʷ φ : Δ) : WkMono φ.
Proof. destruct Hφ as [? ? ? ? []]; assumption. Qed.
