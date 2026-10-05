(** * The Semantic Judgments

    The judgments are defined in four layers (weakenings, substitutions, terms,
    subtyping) and packaged by an inductive [⊨ Γ].

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
From Mctt.Core.Semantic Require Export PER.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Reserved Notation "Γ ⊨w φ : Δ" (at level 70, φ constr at level 0, Δ at level 69).
Reserved Notation "⊨ Γ" (at level 70).

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** * Semantic Weakening

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

Definition rel_wk_under_ctx Γ φ Δ : Prop :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel)
     env_rel' (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_rel'),
    rel_wk φ env_rel env_rel'.

Notation "Γ ⊨w φ : Δ" := (rel_wk_under_ctx Γ φ Δ) : type_scope.

(** * Semantic Substitution Equality

    [σ] and [σ'] must stay related after an arbitrary semantic weakening [φ] —
    the Kripke-like quantification that makes the judgment usable under context
    extension.  The four environments are the two ways of evaluating each side:
    [σ[φ]] in [ρ] (the substitution [sb_wk σ φ], which is [σ] postcomposed with
    [φ]) against [σ] in [⟪φ⟫ ρ]. *)

Inductive rel_sub (σ : sub) (φ : wk) (ρ : env) (σ' : sub) (ρ' : env) (R : relation env) : Prop :=
| mk_rel_sub : forall ρσφ ρσ ρ'σ' ρ'σ'φ,
    ⟦ (sb_wk σ φ) ⟧s ρ ↘ ρσφ ->
    ⟦ σ ⟧s ⟪φ⟫ ρ ↘ ρσ ->
    ⟦ σ' ⟧s ⟪φ⟫ ρ' ↘ ρ'σ' ->
    ⟦ (sb_wk σ' φ) ⟧s ρ' ↘ ρ'σ'φ ->
    rel_chain R ([ρσφ; ρσ; ρ'σ'; ρ'σ'φ]) ->
    rel_sub σ φ ρ σ' ρ' R.
#[global] Arguments mk_rel_sub {_ _ _ _ _ _}.
Hint Constructors rel_sub : mctt.

Definition rel_sub_under_ctx Γ Δ σ σ' : Prop :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel)
     env_rel_o (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_rel_o),
  forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') φ,
    rel_wk φ env_rel' env_rel ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel' ->
      rel_sub σ φ ρ σ' ρ' env_rel_o.

Definition valid_sub_under_ctx Γ Δ σ := rel_sub_under_ctx Γ Δ σ σ.
#[global] Arguments valid_sub_under_ctx _ _ _ /.
Hint Transparent valid_sub_under_ctx : mctt.
Hint Unfold valid_sub_under_ctx : mctt.

(** * Semantic Judgment for Terms

    Terms are required to be stable under semantic substitutions rather than
    weakenings.  [rel_exp] is the four-value pattern of one expression pair.  The
    two environments [ρσ] and [ρ'σ'] are parameters rather than existentials,
    because the type chain and the term chain must be read in the same pair of
    environments: closures capture their environment, so replacing it by a
    pointwise-equal one changes the values. *)

Inductive rel_exp (M : exp) (σ : sub) (ρ ρσ : env) (M' : exp) (σ' : sub) (ρ' ρ'σ' : env) (R : relation domain) : Prop :=
| mk_rel_exp : forall mσ m m' m'σ',
    ⟦ M[σ] ⟧ ρ ↘ mσ ->
    ⟦ M ⟧ ρσ ↘ m ->
    ⟦ M' ⟧ ρ'σ' ↘ m' ->
    ⟦ M'[σ'] ⟧ ρ' ↘ m'σ' ->
    rel_chain R ([mσ; m; m'; m'σ']) ->
    rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R.
#[global] Arguments mk_rel_exp {_ _ _ _ _ _ _ _ _}.
Hint Constructors rel_exp : mctt.

(** The same pattern one universe up: the four values of a type are related in
    [per_univ_elem i R], which also fixes the element PER [R] that the term chain
    lives in. *)
Definition rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R :=
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

    The judgment does not itself claim that [σ] evaluates at [ρ]; that is part of
    [rel_sub_under_ctx Γ' Γ σ σ'], which every instantiation supplies.  In return,
    each case of the fundamental theorem must produce its values at whatever
    environment the caller names.  This is what makes the inductive cases fit: a
    premise's values arrive in the same environment as the conclusion's, so two
    instantiations of one judgment share values rather than being pointwise
    equal, and [rel_chain_merge] applies. *)
Definition rel_exp_under_ctx Γ A M M' : Prop :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel) i,
  forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
    rel_sub_under_ctx Γ' Γ σ σ' ->
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_rel' ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      exists (elem_rel : relation domain),
        rel_typ i A σ ρ ρσ A σ' ρ' ρ'σ' elem_rel /\
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' elem_rel.

Definition valid_exp_under_ctx Γ A M := rel_exp_under_ctx Γ A M M.
#[global] Arguments valid_exp_under_ctx _ _ _ /.
Hint Transparent valid_exp_under_ctx : mctt.
Hint Unfold valid_exp_under_ctx : mctt.

(** * Semantic Judgment for Subtyping

    Not a four-value chain: [per_subtyp] has no symmetry, so the two commutation
    obligations are stated on their own sides and the subtyping obligation
    relates the two inner values only. *)

Definition subtyp_under_ctx Γ A A' : Prop :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel) i,
  forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
    rel_sub_under_ctx Γ' Γ σ σ' ->
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_rel' ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      exists aσ a a'σ' a',
          ⟦ A[σ] ⟧ ρ ↘ aσ /\
          ⟦ A ⟧ ρσ ↘ a /\
          ⟦ A'[σ'] ⟧ ρ' ↘ a'σ' /\
          ⟦ A' ⟧ ρ'σ' ↘ a' /\
          Dom aσ ≈ a ∈ per_univ i /\
          Dom a'σ' ≈ a' ∈ per_univ i /\
          Sub a <: a' at i.

Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (at level 70, Γ' at level 69).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (at level 70, M at level 69, M' at level 69, A at level 69).
Notation "Γ ⊨ M ⊆ M'" := (subtyp_under_ctx Γ M M') (at level 70, M at level 69, M' at level 69).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (at level 70, M at level 69, A at level 69).
Notation "Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (at level 70, σ at level 69, σ' at level 69, Δ at level 69).
Notation "Γ ⊨s σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (at level 70, σ at level 69, Δ at level 69).

(** * Semantic Judgments for Module Expressions and Units

    A module expression is valid when its four values are related in the
    module PER, as a term's are in its type's element PER.  A unit [U] is
    represented by the literal [me_lit U], whose value is its closure.  A unit
    is moreover valid in its parts: a body unit's extension of the context is
    semantically well formed, and an alias's target is valid under its
    parameters; this is what the members of its closure are read off. *)

Inductive rel_mod (H : modexp) (σ : sub) (ρ ρσ : env) (H' : modexp) (σ' : sub) (ρ' ρ'σ' : env) : Prop :=
| mk_rel_mod : forall hσ h h' h'σ',
    eval_modexp gc_ctx H[σ]ᵐ ρ hσ ->
    eval_modexp gc_ctx H ρσ h ->
    eval_modexp gc_ctx H' ρ'σ' h' ->
    eval_modexp gc_ctx H'[σ']ᵐ ρ' h'σ' ->
    rel_chain per_dmod ([hσ; h; h'; h'σ']) ->
    rel_mod H σ ρ ρσ H' σ' ρ' ρ'σ'.
#[global] Arguments mk_rel_mod {_ _ _ _ _ _ _ _}.
Hint Constructors rel_mod : mctt.

Definition rel_modexp_under_ctx Γ H H' : Prop :=
  exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
  forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
    rel_sub_under_ctx Γ' Γ σ σ' ->
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_rel' ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      rel_mod H σ ρ ρσ H' σ' ρ' ρ'σ'.

Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).

(** * Semantic Context Well-Formedness

    An inductive judgment whose extension step carries both the context PER
    witness and the semantic well-formedness of the type (and, for a
    definition, of its body; for a module slot, of its unit), so
    [sem_ctx_per_ctx_env] reads the PER off any derivation.  The validity of a
    unit's parts ([sem_unit]) is defined with it, since a body unit's parts
    form a context. *)

Inductive sem_ctx : ctx -> Prop :=
| sem_ctx_nil : ⊨ ⋅
| sem_ctx_cons : forall Γ A i env_rel,
    ⊨ Γ ->
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Type@i ->
    ⊨ Γ ▹ A
| sem_ctx_cons_def : forall Γ A M i env_rel,
    ⊨ Γ ->
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ A ≈ A : Type@i ->
    Γ ⊨ M ≈ M : A ->
    ⊨ Γ ▸ A ≔ M
| sem_ctx_cons_mod : forall Γ U env_rel,
    ⊨ Γ ->
    EF Γ ▹ₘ U ≈ Γ ▹ₘ U ∈ per_ctx_env ↘ env_rel ->
    Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    sem_unit Γ U ->
    ⊨ Γ ▹ₘ U
with sem_unit : ctx -> gunit -> Prop :=
| sem_unit_body : forall Γ Δ Φ,
    tele_ass Δ ->
    ⊨ Δ ++ Γ ->
    sem_body (Δ ++ Γ) Φ ->
    sem_unit Γ (gu_body Δ Φ)
| sem_unit_alias : forall Γ Δ E,
    tele_ass Δ ->
    ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ᵐ E ≈ E ->
    sem_unit Γ (gu_mk Δ (md_alias E))
(** The entries of a body over [Γ0], each valid under its self slot. *)
with sem_body : ctx -> gmod -> Prop :=
| sem_body_nil : forall Γ0, sem_body Γ0 gm_nil
| sem_body_def : forall Γ0 Φ x pv A M i,
    sem_body Γ0 Φ ->
    ⊨ self_ent Φ :: Γ0 ->
    self_ent Φ :: Γ0 ⊨ A ≈ A : Type@i ->
    self_ent Φ :: Γ0 ⊨ M ≈ M : A ->
    sem_body Γ0 (gm_ext Φ x (ge_def pv A (Some M)))
| sem_body_mod : forall Γ0 Φ x pv U,
    sem_body Γ0 Φ ->
    ⊨ self_ent Φ :: Γ0 ->
    self_ent Φ :: Γ0 ⊨ᵐ me_lit U ≈ me_lit U ->
    sem_unit (self_ent Φ :: Γ0) U ->
    sem_body Γ0 (gm_ext Φ x (ge_mod pv U))
where "⊨ Γ" := (sem_ctx Γ) : type_scope.

Hint Constructors sem_ctx sem_unit sem_body : mctt.

(** Two units are equivalent when their closures are related and each is valid
    in its parts.  Two extensions of a context are equivalent when both
    extended contexts are semantically well formed and related. *)
Definition rel_unit_under_ctx Γ U U' : Prop :=
  Γ ⊨ᵐ me_lit U ≈ me_lit U' /\ sem_unit Γ U /\ sem_unit Γ U'.

Definition rel_ext_under_ctx Γ Ψ Ψ' : Prop :=
  ⊨ Ψ ++ Γ /\ ⊨ Ψ' ++ Γ /\ ⊨ Ψ ++ Γ ≈ Ψ' ++ Γ.

Notation "Γ ⊨ᵘ U ≈ U'" := (rel_unit_under_ctx Γ U U') (at level 70, U at level 69, U' at level 69).
Notation "Γ ⊨ˣ Ψ ≈ Ψ'" := (rel_ext_under_ctx Γ Ψ Ψ') (at level 70, Ψ at level 69, Ψ' at level 69).

End Fixed_GCtx.

Notation "Γ ⊨w φ : Δ" := (rel_wk_under_ctx Γ φ Δ) : type_scope.
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
Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (at level 70, Γ' at level 69).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (at level 70, M at level 69, M' at level 69, A at level 69).
Notation "Γ ⊨ M ⊆ M'" := (subtyp_under_ctx Γ M M') (at level 70, M at level 69, M' at level 69).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (at level 70, M at level 69, A at level 69).
Notation "Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (at level 70, σ at level 69, σ' at level 69, Δ at level 69).
Notation "Γ ⊨s σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (at level 70, σ at level 69, Δ at level 69).
Notation "⊨ Γ" := (sem_ctx Γ) : type_scope.
#[export]
Hint Constructors sem_ctx sem_unit sem_body rel_mod : mctt.
Notation "Γ ⊨ᵐ H ≈ H'" := (rel_modexp_under_ctx Γ H H') (at level 70, H at level 69, H' at level 69).
Notation "Γ ⊨ᵘ U ≈ U'" := (rel_unit_under_ctx Γ U U') (at level 70, U at level 69, U' at level 69).
Notation "Γ ⊨ˣ Ψ ≈ Ψ'" := (rel_ext_under_ctx Γ Ψ Ψ') (at level 70, Ψ at level 69, Ψ' at level 69).

(** A semantic weakening in scope says its weakening moves no variable
    down. *)
Existing Class rel_wk.
#[export] Existing Instance rel_wk_mono.

Existing Class rel_wk_under_ctx.

#[export] Instance rel_wk_under_ctx_mono {GC : GCtx} {Γ φ Δ} (Hφ : Γ ⊨w φ : Δ) : WkMono φ.
Proof. destruct Hφ as [? [? [? [? []]]]]; assumption. Qed.

