(** * The Syntactic Judgments

    This file corresponds to Section 3 of the paper.

    Because substitution is a meta-level *operation* rather than a syntactic
    constructor, this presentation differs from a calculus of explicit
    substitutions in three ways.

    - There is no [wf_exp_sub] rule and there are no [_sub] computation rules in
      the equational theory.  The equations they used to postulate — how a
      substitution distributes over each term former, how substitutions compose,
      what the identity does — are theorems about [exp_sub], proved in
      [Core.Syntactic.Substitution].  What used to be a derivation step is now a
      [rewrite].

    - Consequently only four judgments are mutually defined: context
      well-formedness, typing, term equality and subtyping.

    - Weakening and substitution typing are *derived* judgments: not inductive
      types, but statements that an operation maps every binding of one context
      to something of the right type in the other (Sections 3.3 and 3.4).
      Their algebraic closure properties — identity, extension, lifting,
      composition — are lemmas rather than constructors, and live in [Core.Syntactic.System.Lemmas].

    Two rules are stated slightly more generally than in the paper, both times
    following the presentation this development already had:

    - [wf_exp_eq_natrec_cong] also allows the motive to vary.  The paper keeps it
      fixed; allowing it to vary is strictly stronger and is what the algorithmic
      equality of [Algorithmic] compares.
    - [wf_subtyp_pi] checks the codomains in [Γ , A'] rather than the paper's
      [Γ , A].  The two are interderivable given the premise [Γ ⊢ A ≈ A' : Type@i]
      and context conversion, and [Γ , A'] is what the soundness proof wants. *)

From Stdlib Require Import List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution.
Import Syntax_Notations Wk_Notations.

Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Γ ⊢ A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Γ ⊢w φ : Δ" (in custom judg at level 80, Γ custom exp, φ constr at level 60, Δ custom exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢s σ ≈ σ' : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).

Generalizable All Variables.

(** ** Context Lookup

    A lookup carries the weakenings that separate the binding from the top of
    the context, so [Var] below needs no shifting of its own.  The shift here is
    the *weakening* [↑], not the substitution [Wk]: everything that has to move a
    looked-up type past a lifted operation does so with [exp_wk_shift_wk_q] or
    [exp_wk_shift_sub_q], both of which are stated for [↑]. *)

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `({{ #0 : A⟨↑⟩ ∈ Γ , A }})
  | there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A⟨↑⟩ ∈ Γ , B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

(** ** The Four Mutually Defined Judgments *)

Inductive wf_ctx : ctx -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ ⊢ Γ , A }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

with wf_exp : ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Type@i : Type@(S i) }} )
| wf_nat :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ ℕ : Type@0 }} )
| wf_zero :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ zero : ℕ }} )
| wf_succ :
  `( {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ succ M : ℕ }} )
| wf_natrec :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk⨟Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )
| wf_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ Π A B : Type@i }} )
| wf_fn :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ M : B }} ->
     {{ Γ ⊢ λ A M : Π A B }} )
| wf_app :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ M N : B[Id,,N] }} )
| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )
| wf_exp_subtyp :
  `( {{ Γ ⊢ M : A }} ->
     (** We have this extra argument for soundness.
         Note that we need to keep it asymmetric:
         only [A'] is checked. If we check A as well,
         we cannot even construct something like
         [{{ Γ ⊢ Type@0⟨↑⟩ : Type@1 }}] with the current
         rules. Under the symmetric rule, the example requires
         [{{ Γ ⊢ Type@1⟨↑⟩ : Type@2 }}] to apply weakening,
         which requires [{{ Γ ⊢ Type@2⟨↑⟩ : Type@3 }}], and so on.
      *)
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ ⊢ M : A' }} )
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

with wf_exp_eq : ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules (Section 3.7) *)
| wf_exp_eq_typ_cong :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Type@i ≈ Type@i : Type@(S i) }} )
| wf_exp_eq_nat_cong :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ ℕ ≈ ℕ : Type@0 }} )
| wf_exp_eq_zero_cong :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ zero ≈ zero : ℕ }} )
| wf_exp_eq_succ_cong :
  `( {{ Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Γ ⊢ succ M ≈ succ M' : ℕ }} )
| wf_exp_eq_natrec_cong :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ , ℕ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS ≈ MS' : A[Wk⨟Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_pi_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ B ≈ B' : Type@i }} ->
     {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }} )
| wf_exp_eq_fn_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ M ≈ M' : B }} ->
     {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }} )
| wf_exp_eq_app_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : Π A B }} ->
     {{ Γ ⊢ N ≈ N' : A }} ->
     {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x ≈ #x : A }} )
(** *** Computation rules (Section 3.8) *)
| wf_exp_eq_pi_beta :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ , A ⊢ M : B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_nat_beta_zero :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk⨟Wk,,succ(#1)] }} ->
     {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk⨟Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )
(** *** Uniqueness rule (Section 3.9) *)
| wf_exp_eq_fn_eta :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ M ≈ λ A (M⟨↑⟩ #0) : Π A B }} )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     (** This extra argument is here to be consistent with
         [wf_exp_subtyp].
      *)
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M'' : A }} ->
     {{ Γ ⊢ M ≈ M'' : A }} )
where "Γ ⊢ M ≈ M' : A" := (wf_exp_eq Γ A M M') (in custom judg) : type_scope

(** *** Subtyping (Section 3.5) *)
with wf_subtyp : ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the presupposition
      lemmas independently.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( {{ Γ ⊢ M' : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : Type@i }} ->
     {{ Γ ⊢ M ⊆ M' }} )
| wf_subtyp_trans :
  `( {{ Γ ⊢ M ⊆ M' }} ->
     {{ Γ ⊢ M' ⊆ M'' }} ->
     {{ Γ ⊢ M ⊆ M'' }} )
| wf_subtyp_univ :
  `( {{ ⊢ Γ }} ->
     i < j ->
     {{ Γ ⊢ Type@i ⊆ Type@j }} )
| wf_subtyp_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ , A' ⊢ B' : Type@i }} ->
     {{ Γ , A' ⊢ B ⊆ B' }} ->
     {{ Γ ⊢ Π A B ⊆ Π A' B' }} )
where "Γ ⊢ A ⊆ A'" := (wf_subtyp Γ A A') (in custom judg) : type_scope.

(** The schemes are [Minimality], not [Induction]: nothing in this development
    is proved by a statement that mentions the derivation itself, and dropping
    the derivation arguments keeps the goals of a mutual induction readable and
    within reach of [mauto]. *)

Scheme wf_ctx_mut_ind := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind := Minimality for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_subtyp_mut_ind.

(** The three-way scheme is the shape of [wk_preserves_wf], [sub_preserves_wf]
    and [sub_eq_preserves_exp]: each of them
    transports the three judgments *about a fixed context* along an operation,
    and says nothing about context well-formedness.  Generating it as a scheme
    in its own right (rather than combining the four-way one) means it takes
    exactly three predicates: the [⊢ Γ] premises of rules like [wf_typ] survive
    as ordinary hypotheses. *)

Scheme wf_exp_mind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mind := Minimality for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_exp_mind,
  wf_exp_eq_mind,
  wf_subtyp_mind.

(** The two-way scheme is the shape of the soundness fundamental theorem: the
    gluing model relates contexts and terms, and its
    subtyping case consumes [{{ Γ ⊢ A ⊆ A' }}] syntactically, so neither of the
    two equality judgments needs a predicate. *)

Scheme wf_ctx_mind' := Minimality for wf_ctx Sort Prop
with wf_exp_mind' := Minimality for wf_exp Sort Prop.
Combined Scheme syntactic_wf_ctx_exp_mut_ind from
  wf_ctx_mind',
  wf_exp_mind'.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp ctx_lookup : mctt.

(** ** Weakening and Substitution Typing

    These are the derived judgments of Sections 3.3 and 3.4.
    They are records, not inductive relations: a weakening or a substitution is
    well-typed exactly when it sends each binding of its source context to
    something of the correspondingly transported type in its target.  Nothing
    here is recursive, so none of it belongs in the mutual block above; the
    price is that closure under the operations ([Id], [_,,_], [q], [_⨟_]) has to
    be proved, which is what [wf_wk_id]–[wf_wk_compose] and
    [wf_sub_id]–[wf_sub_q] do. *)

Record wf_wk (Γ Δ : ctx) (φ : wk) : Prop := wf_wk_intro
{ wf_wk_dom : {{ ⊢ Γ }}
; wf_wk_cod : {{ ⊢ Δ }}
; wf_wk_lookup : forall x A, {{ #x : A ∈ Δ }} -> {{ #(φ x) : A⟨φ⟩ ∈ Γ }}
}.
Notation "Γ ⊢w φ : Δ" := (wf_wk Γ Δ φ) (in custom judg) : type_scope.

Record wf_sub (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : {{ ⊢ Γ }}
; wf_sub_cod : {{ ⊢ Δ }}
; wf_sub_apply : forall x A, {{ #x : A ∈ Δ }} -> {{ Γ ⊢ ^(σ x) : A[σ] }}
}.
Notation "Γ ⊢s σ : Δ" := (wf_sub Γ Δ σ) (in custom judg) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : {{ Γ ⊢s σ : Δ }}
; wf_sub_eq_right : {{ Γ ⊢s σ' : Δ }}
; wf_sub_eq_apply : forall x A, {{ #x : A ∈ Δ }} -> {{ Γ ⊢ ^(σ x) ≈ ^(σ' x) : A[σ] }}
}.
Notation "Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Γ Δ σ σ') (in custom judg) : type_scope.

(** The projections are deliberately *not* registered in [mctt]: each of them
    has a conclusion ([⊢ Γ], [Γ ⊢s σ : Δ]) that the corresponding introduction
    rule also produces, so the pair would let [eauto] cycle. [Lemmas.v] states
    the presuppositions it actually wants as separate lemmas. *)

(** [wf_wk], [wf_sub] and [wf_sub_eq] are all invariant under pointwise equality
    of the operation: the operation only ever occurs applied to an index or
    applied to an expression, and both of those respect pointwise equality
    ([exp_wk_Proper], [exp_sub_Proper]). *)

#[export]
Instance wf_wk_Proper Γ Δ : Proper (wk_eq ==> iff) (wf_wk Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> {{ Γ ⊢w φ : Δ }} -> {{ Γ ⊢w ψ : Δ }}) as Himp.
  {
    intros φ ψ Heq [? ? Hlk].
    econstructor; try eassumption.
    intros x A ?.
    replace (ψ x) with (φ x) by apply Heq.
    rewrite <- Heq.
    now apply Hlk.
  }
  intros φ ψ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

#[export]
Instance wf_sub_Proper Γ Δ : Proper (sb_eq ==> iff) (wf_sub Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s τ : Δ }}) as Himp.
  {
    intros σ τ Heq [? ? Hap].
    econstructor; try eassumption.
    intros x A ?.
    replace (τ x) with (σ x) by apply Heq.
    rewrite <- Heq.
    now apply Hap.
  }
  intros σ τ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

(** ** Immediate & Independent Presuppositions *)

Lemma presup_subtyp_right : forall {Γ A B}, {{ Γ ⊢ A ⊆ B }} -> exists i, {{ Γ ⊢ B : Type@i }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** ** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Γ A A' M,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Γ A A' M M',
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mctt.
#[export]
Remove Hints wf_exp_eq_subtyp : mctt.

(** ** Term Equality is a PER

    Reflexivity at a well-typed term is *not* available here — it needs an
    induction over typing, so it lives in [Core.Syntactic.System.Lemmas]
    together with the [PERElem] instance that lets [saturate_refl] use it.  The
    same goes for [wf_sub_eq], whose symmetry and transitivity need
    [sub_eq_preserves_exp] to move between the types [A[σ]] and [A[σ']]. *)

#[export]
Instance wf_exp_eq_PER Γ A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_subtyp_Transitive Γ : Transitive (wf_subtyp Γ).
Proof.
  hnf; mauto.
Qed.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature eq ==> wf_exp_eq Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.
