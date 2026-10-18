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
       ([valid_filed_mod], [valid_filed_mods]), and a declaration ([valid_ind_decl]); a sound
       embedding of [Θ1 ⍮ Ξ1] into [Θ2 ⍮ Ξ2] ([valid_emb]).
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
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Semantic Require Export PER.
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
  { rwu_rel : relation env
  ; rwu_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rwu_rel
  ; rwu_rel' : relation env
  ; rwu_per' : EF Δ ≈ Δ ∈ per_ctx_env ↘ rwu_rel'
  ; rwu_wk : rel_wk φ rwu_rel rwu_rel' }.

Notation "Γ ⊨ʷ φ : Δ" := (rel_wk_under_ctx Γ φ Δ) : type_scope.

(** *** Semantic Substitution Equality

    [σ] and [σ'] must stay related after an arbitrary semantic weakening [φ] —
    the Kripke-like quantification that makes the judgment usable under context
    extension.  The four environments are the two ways of evaluating each side:
    [σ[φ]] in [ρ] (the substitution [sb_wk σ φ], which is [σ] postcomposed with
    [φ]) against [σ] in [⟪φ⟫ ρ]. *)

#[warnings="-cannot-define-projection"]
Record rel_sub (σ : sub) (φ : wk) (ρ : env) (σ' : sub) (ρ' : env) (R : relation env) : Prop := mk_rel_sub
  { ρσφ : env
  ; ρσ : env
  ; ρ'σ' : env
  ; ρ'σ'φ : env
  ; rs_eval_wk : ⟦ (sb_wk σ φ) ⟧s ρ ↘ ρσφ
  ; rs_eval : ⟦ σ ⟧s ⟪φ⟫ ρ ↘ ρσ
  ; rs_eval' : ⟦ σ' ⟧s ⟪φ⟫ ρ' ↘ ρ'σ'
  ; rs_eval_wk' : ⟦ (sb_wk σ' φ) ⟧s ρ' ↘ ρ'σ'φ
  ; rs_chain : rel_chain R ([ρσφ; ρσ; ρ'σ'; ρ'σ'φ]) }.
#[global] Arguments mk_rel_sub {_ _ _ _ _ _}.
Hint Constructors rel_sub : mctt.

#[warnings="-cannot-define-projection"]
Record rel_sub_under_ctx Γ Δ σ σ' : Prop := mk_rel_sub_under_ctx
  { rsu_rel : relation env
  ; rsu_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rsu_rel
  ; rsu_rel_o : relation env
  ; rsu_per_o : EF Δ ≈ Δ ∈ per_ctx_env ↘ rsu_rel_o
  ; rsu_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') φ,
      rel_wk φ env_rel' rsu_rel ->
      forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        rel_sub σ φ ρ σ' ρ' rsu_rel_o }.

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
  ; re_eval_sub : ⟦ M[σ] ⟧ ρ ↘ mσ
  ; re_eval : ⟦ M ⟧ ρσ ↘ m
  ; re_eval' : ⟦ M' ⟧ ρ'σ' ↘ m'
  ; re_eval_sub' : ⟦ M'[σ'] ⟧ ρ' ↘ m'σ'
  ; re_chain : rel_chain R ([mσ; m; m'; m'σ']) }.
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
    equal, and [rel_chain_merge] applies. *)
#[warnings="-cannot-define-projection"]
Record rel_exp_under_ctx Γ A M M' : Prop := mk_rel_exp_under_ctx
  { reu_rel : relation env
  ; reu_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ reu_rel
  ; reu_lvl : nat
  ; reu_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        exists (elem_rel : relation domain),
          rel_typ reu_lvl A σ ρ ρσ A σ' ρ' ρ'σ' elem_rel /\
          rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' elem_rel }.

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
  { rst_aσ : domain
  ; rst_a : domain
  ; rst_a'σ' : domain
  ; rst_a' : domain
  ; rst_eval_aσ : ⟦ A[σ] ⟧ ρ ↘ rst_aσ
  ; rst_eval_a : ⟦ A ⟧ ρσ ↘ rst_a
  ; rst_eval_a'σ' : ⟦ A'[σ'] ⟧ ρ' ↘ rst_a'σ'
  ; rst_eval_a' : ⟦ A' ⟧ ρ'σ' ↘ rst_a'
  ; rst_left : Dom rst_aσ ≈ rst_a ∈ per_univ i
  ; rst_right : Dom rst_a'σ' ≈ rst_a' ∈ per_univ i
  ; rst_sub : Sub rst_a <: rst_a' at i }.

#[warnings="-cannot-define-projection"]
Record rel_subtyp_under_ctx Γ A A' : Prop := mk_rel_subtyp_under_ctx
  { rstu_rel : relation env
  ; rstu_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rstu_rel
  ; rstu_lvl : nat
  ; rstu_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_subtyp rstu_lvl A σ ρ ρσ A' σ' ρ' ρ'σ' }.

Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (at level 70, M at level 69, M' at level 69, A at level 69).
Notation "Γ ⊨ M ⊆ M'" := (rel_subtyp_under_ctx Γ M M') (at level 70, M at level 69, M' at level 69).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (at level 70, M at level 69, A at level 69).

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
  ; rm_eval_sub : ⟦ H[σ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ hσ
  ; rm_eval : ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρσ ↘ h
  ; rm_eval' : ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ'σ' ↘ h'
  ; rm_eval_sub' : ⟦ H'[σ']ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h'σ'
  ; rm_chain : rel_chain per_dmod ([hσ; h; h'; h'σ']) }.
#[global] Arguments mk_rel_modexp {_ _ _ _ _ _ _ _}.
Hint Constructors rel_modexp : mctt.

#[warnings="-cannot-define-projection"]
Record rel_modexp_under_ctx Γ H H' : Prop := mk_rel_modexp_under_ctx
  { rmu_rel : relation env
  ; rmu_per : EF Γ ≈ Γ ∈ per_ctx_env ↘ rmu_rel
  ; rmu_body : forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_modexp H σ ρ ρσ H' σ' ρ' ρ'σ' }.

Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).

(** *** Contexts

    An inductive relation whose extension step carries both the context PER
    witness and the semantic well-formedness of the head (and, for a
    definition, of its body; for a module slot, of its unit), so
    [rel_ctx_wf_per_ctx_env] reads the PER off any derivation.  The validity of
    a unit's parts ([rel_unit_wf]) is defined with it, since a body unit's
    parts form a context. *)

Inductive rel_ctx_wf : ctx -> Prop :=
| rel_ctx_wf_nil : ⊨ ⋅
| rel_ctx_wf_cons : forall Γ A i env_rel,
    ⊨ Γ ->
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Typeω@i ->
    ⊨ Γ ▹ A
| rel_ctx_wf_cons_def : forall Γ A M i env_rel,
    ⊨ Γ ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ M ≈ M : A ->
    ⊨ Γ ▸ A ≔ M
| rel_ctx_wf_cons_mod : forall Γ U env_rel,
    ⊨ Γ ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    rel_unit_wf Γ U ->
    ⊨ Γ ▹ₘ U
with rel_unit_wf : ctx -> gunit -> Prop :=
| rel_unit_wf_body : forall Γ Δ Φ Φx,
    tele_ass Δ ->
    body_xp gc_deps gc_stack (Δ ++ Γ) Φ Φx ->
    body_shape Φ Φ ->
    body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Δ ++ Γ ->
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
  { ruu_lit : Γ ⊨ᵐ me_lit U ≈ me_lit U'
  ; ruu_left : rel_unit_wf Γ U
  ; ruu_right : rel_unit_wf Γ U' }.

Record rel_ext_under_ctx Γ Ψ Ψ' : Prop := mk_rel_ext_under_ctx
  { rxu_left : ⊨ Ψ ++ Γ
  ; rxu_right : ⊨ Ψ' ++ Γ
  ; rxu_eq : ⊨ Ψ ++ Γ ≈ Ψ' ++ Γ }.

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
Notation "⊨ Γ" := (rel_ctx_wf Γ) : type_scope.
Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).
Notation "Γ ⊨ᵘ U ≈ U'" := (rel_unit_under_ctx Γ U U') (at level 70, U at level 69, U' at level 69).
Notation "Γ ⊨ˣ Ψ ≈ Ψ'" := (rel_ext_under_ctx Γ Ψ Ψ') (at level 70, Ψ at level 69, Ψ' at level 69).

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
  { va_rest : ctx
  ; va_filled : ctx
  ; va_split : T = va_rest ++ va_filled
  ; va_length : List.length va_filled = List.length Ns
  ; va_ass : tele_ass va_filled
  ; va_scoped : ctx_scoped 0 va_filled
  ; va_args : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts va_filled Id Ns) k = Some A ->
      Γ ⊨ N : A }.

(** A unit is valid when its parts are ([valid_unit]): a filed module at
    arguments valid against its telescope ([valid_args]); a local body whose
    context, read as its expansion, is valid, whose submodules are valid
    units in the context the body before each makes, and whose opens'
    targets are valid; an alias whose target is.  A module expression is
    valid in what it denotes ([valid_modexp]) when it is equal, in the PER model, to
    a valid unit denoting the same module part: the semantic counterpart of
    lookup soundness. *)
Inductive valid_unit : ctx -> modexp -> Prop :=
| valid_unit_filed : forall Γ p T Φ Ns,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ -> valid_args Γ T Ns ->
    valid_unit Γ (me_apps (qname_mod p) Ns)
| valid_unit_body : forall Γ Δ Φ Φx,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> tele_ass Δ -> ⊨ Γ -> ⊨ body_ctx Φx ++ Δ ++ Γ ->
    (forall y Φ0 pv U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
       valid_unit (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U)) ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    Γ ⊨ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> valid_modexp (Ψ ++ Δ ++ Γ) H) ->
    valid_unit Γ (me_lit (gu_open Δ Φ))
| valid_unit_alias : forall Γ Δ E,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    tele_ass Δ -> ⊨ Γ -> ⊨ Δ ++ Γ ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    Δ ++ Γ ⊨ᵐ E ≈ E -> valid_modexp (Δ ++ Γ) E ->
    valid_unit Γ (me_lit (gu_mk Δ (md_alias E)))
(** [valid_modexp Γ H]: [H] is equal to a valid unit that denotes its module part. *)
with valid_modexp : ctx -> modexp -> Prop :=
| valid_modexp_intro : forall Γ H R Rm K RK,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θm Ξm Γ H R -> ds_mod Θm Ξm R = Some Rm ->
    Γ ⊨ᵐ H ≈ K -> valid_unit Γ K -> mdenote Θm Ξm Γ K RK -> ds_mod Θm Ξm RK = Some Rm ->
    valid_modexp Γ H.

Scheme valid_unit_mut_ind := Induction for valid_unit Sort Prop
with valid_modexp_mut_ind := Induction for valid_modexp Sort Prop.
Combined Scheme valid_unit_modexp_ind from valid_unit_mut_ind, valid_modexp_mut_ind.

(** A context is semantically well formed with valid slots ([valid_ctx])
    when each extension is semantically well formed, and the unit of each
    slot is valid in the context before it. *)
Inductive valid_ctx : ctx -> Prop :=
| valid_ctx_nil : valid_ctx ⋅
| valid_ctx_ass : forall Γ A, valid_ctx Γ -> ⊨ Γ ▹ A -> valid_ctx (Γ ▹ A)
| valid_ctx_def : forall Γ A M, valid_ctx Γ -> ⊨ Γ ▸ A ≔ M -> valid_ctx (Γ ▸ A ≔ M)
| valid_ctx_mod : forall Γ U, valid_ctx Γ -> ⊨ Γ ▹ₘ U -> valid_unit Γ (me_lit U) -> valid_ctx (Γ ▹ₘ U).

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

(** The kind of an entry. *)
Definition entry_kind (E : gentry) : mkind :=
  match E with
  | ge_def _ _ _ _ => mk_term
  | _ => mk_mod
  end.

(** A value [g] related to itself at the value of the closed type
    [ctx_pi T A0]. *)
#[warnings="-cannot-define-projection"]
Record rel_self (T : ctx) (A0 : exp) (g : domain) : Prop := mk_rel_self
  { rsl_lvl : uidx
  ; rsl_rel : relation domain
  ; rsl_typ : domain
  ; rsl_eval : ⟦ ctx_pi T A0 ⟧ nil ↘ rsl_typ
  ; rsl_per : per_univ_elem rsl_lvl rsl_rel rsl_typ rsl_typ
  ; rsl_elem : rsl_rel g g }.

(** The term member [x] of the filed module [p], over its telescope [T],
    read as [R0]: of a type over [T], of a value related to itself, with
    its δ-reduct at arguments for the outer part of [T], if it has one, a
    term over that part instantiated, valid there, whose value at arguments
    is the member's value applied to them. *)
#[warnings="-cannot-define-projection"]
Record valid_filed_term (p : qname) (T : ctx) (x : String.string) (R0 : mdesc) : Prop := mk_valid_filed_term
  { vft_typ : exp
  ; vft_lvl : nat
  ; vft_val : domain
  ; vft_typed : T ⊨ vft_typ : Typeω@vft_lvl
  ; vft_reads : forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> ds_ats R0 Ns = Some R1 ->
      ds_ty Θm Ξm R1 = Some (ctx_pi T1 vft_typ)[sb_of_list Id Ns] /\
      (ds_red R1 = None \/
       exists M1, ds_red R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi T1 vft_typ /\
         forall ns m, List.length ns = List.length T2 -> ⟦ M1 ⟧ env_args nil ns ↘ m ->
           $*| vft_val & ns | gc_deps ⍮ gc_stack ↘ m)
  ; vft_sel : dm_global p nil ·ₜ x gc_deps ⍮ gc_stack ↘ vft_val
  ; vft_self : rel_self T vft_typ vft_val }.

Record valid_filed_mod (p : qname) (T : ctx) (Φ : gmod) : Prop := mk_valid_filed_mod
  { vfm_stored : exists Φ', gc_loc gc_deps gc_stack p = Some (T, Φ')
  ; vfm_path : forall ρ, ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p nil
  ; vfm_tele_wf : ⊨ T
  ; vfm_tele_ass : tele_ass T
  ; vfm_tele_scoped : ctx_scoped 0 T
  ; vfm_kinds : forall x Φ0 E, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      dkind gc_deps gc_stack (dm_global p nil) (x :: nil) (entry_kind E)
  ; vfm_sub_kinds : forall x TΦ, gc_loc Θm Ξm (qname_app p (x :: nil)) = Some TΦ ->
      dkind gc_deps gc_stack (dm_global p nil) (x :: nil) mk_mod
  ; vfm_terms : forall x Φ0 E R0, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_term E = Some R0 ->
      valid_filed_term p T x R0
  ; vfm_aliases : forall y Φ0 E Ua, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
      gc_module gc_deps gc_stack (qname_in p y) = Some (mr_alias Ua) /\
      forall Γ, ⊨ Γ -> ⊢ Θm ⍮ Ξm ⍮ Γ -> valid_unit Θm Ξm Γ (me_lit Ua) }.

Definition valid_filed_mods : Prop :=
  forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) -> valid_filed_mod p T Φ.

(** A declaration is semantically valid at its core: its telescopes and
    types, read in the PER model.  [nparams_prefix D k] is the context of the first
    [k] non-uniform parameters, [nonrec_args_prefix gs k] that of the first [k]
    non-recursive arguments of a constructor. *)
Definition nparams_prefix (D : ind_decl) (k : nat) : ctx := List.rev (List.firstn k (List.rev (ind_nparams D))).
Definition nonrec_args_prefix (gs : list carg) (k : nat) : ctx := List.rev (List.firstn k (List.map ce_ass (cargs_nonrec gs))).

Record valid_ind_decl (D : ind_decl) : Prop := mk_valid_ind_decl
{ vid_params : ⊨ ind_params D
; vid_sort : exists i, ind_uparams D ⊨ ind_sort D : Typeω@i
; vid_ty : exists i, ⋅ ⊨ ind_ty D : Typeω@i
; vid_npar : forall k A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
    nparams_prefix D k ++ ind_uparams D ⊨ A : (ind_sort D)[wk_shiftn k]ʷ /\
    exists j, nparams_prefix D k ++ ind_uparams D ⊨ A : Typeω@j
; vid_strat : forall c gs k, ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
    ⊨ nonrec_args_prefix gs k ++ ind_params D
; vid_arg : forall c gs k A, ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
    nonrec_args_prefix gs k ++ ind_params D ⊨ A : (ind_sort D)[wk_shiftn (k + ind_nn D)]ʷ /\
    exists j, nonrec_args_prefix gs k ++ ind_params D ⊨ A : Typeω@j
; vid_nodup : List.NoDup (List.map fst (ind_cons D))
; vid_rec : forall c gs gs1 t gs2 m P T, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (ptyp_ps t) m = Some P ->
    List.nth_error (tele_insts (ind_nparams D)
                      (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + ind_nn D))) (ptyp_ps t)) m
      = Some T ->
    ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D ⊨ P : T
(** The domains of a recursive argument's shape, each over those before
    it, are types of the sort. *)
; vid_dom : forall c gs gs1 t gs2 k B, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (ptyp_doms t) k = Some B ->
    doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
      ⊨ B : (ind_sort D)[wk_shiftn (k + List.length (cargs_nonrec gs1) + ind_nn D)]ʷ /\
    exists j, doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
      ⊨ B : Typeω@j
; vid_simple : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> ptyp_simple t = true
; vid_plen : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> List.length (ptyp_ps t) = ind_nn D
; vid_dctx : forall c gs gs1 t gs2 k, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    k <= List.length (ptyp_doms t) ->
    ⊨ doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
}.

End Filed.

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, and what it
    files and has open is valid there, its declarations too. *)
Record valid_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { vem_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; vem_wf : ⊢ᵍ Θ1 ⍮ Ξ1
  ; vem_filed : @valid_filed_mods (gc_mk Θ2 Ξ2) Θ1 Ξ1
  ; vem_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @valid_ind_decl (gc_mk Θ2 Ξ2) D
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
  { sea_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sea_rel : @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M' }.

Record sem_subtyp_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (A A' : typ) : Prop :=
  mk_sem_subtyp_at
  { ssa_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; ssa_rel : @rel_subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A' }.

(** A universe: large, or small at a valid level. *)
Record sem_is_univ_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop :=
  mk_sem_is_univ_at
  { sua_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sua_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (Level@n) L L) }.

Record sem_ext_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ Ψ Ψ' : ctx) : Prop := mk_sem_ext_eq_at
  { sxa_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sxa_rel : @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ'
  ; sxa_ext : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ (Ψ ++ Γ)
  ; sxa_ext' : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ (Ψ' ++ Γ) }.

Record sem_unit_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U U' : gunit) : Prop :=
  mk_sem_unit_eq_at
  { sna_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sna_rel : @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U'
  ; sna_valid : @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U)
  ; sna_valid' : @valid_unit (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U') }.

(** Module expressions: related, and valid in what they denote. *)
Record sem_modexp_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (H H' : modexp) : Prop :=
  mk_sem_modexp_eq_at
  { sma_ctx : @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ
  ; sma_rel : @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H'
  ; sma_valid : @valid_modexp (gc_mk Θ2 Ξ2) Θ Ξ Γ H
  ; sma_valid' : @valid_modexp (gc_mk Θ2 Ξ2) Θ Ξ Γ H' }.

Arguments sea_ctx {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments sea_rel {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments ssa_ctx {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments ssa_rel {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments sua_ctx {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments sua_univ {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments sxa_ctx {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sxa_rel {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sxa_ext {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sxa_ext' {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments sna_ctx {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sna_rel {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sna_valid {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sna_valid' {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments sma_ctx {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sma_rel {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sma_valid {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments sma_valid' {Θ Ξ Θ2 Ξ2 Γ H H'}.

(** The judgments. *)

Definition sem_ctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> @valid_ctx (gc_mk Θ2 Ξ2) Θ Ξ Γ.

Definition sem_exp_eq Θ Ξ Γ A M M' : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_exp_eq_at Θ Ξ Θ2 Ξ2 Γ A M M'.

Definition sem_exp Θ Ξ Γ A M : Prop := sem_exp_eq Θ Ξ Γ A M M.

Definition sem_subtyp Θ Ξ Γ A A' : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_subtyp_at Θ Ξ Θ2 Ξ2 Γ A A'.

Definition sem_is_univ Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_is_univ_at Θ Ξ Θ2 Ξ2 Γ U.

Definition sem_ext_eq Θ Ξ Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_ext_eq_at Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'.

Definition sem_unit_eq Θ Ξ Γ U U' : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_unit_eq_at Θ Ξ Θ2 Ξ2 Γ U U'.

Definition sem_modexp_eq Θ Ξ Γ H H' : Prop :=
  forall Θ2 Ξ2, valid_emb Θ Ξ Θ2 Ξ2 -> sem_modexp_eq_at Θ Ξ Θ2 Ξ2 Γ H H'.

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
