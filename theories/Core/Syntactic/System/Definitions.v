(** * The Syntactic Judgments

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
      to something of the right type in the other.
      Their algebraic closure properties — identity, extension, lifting,
      composition — are lemmas rather than constructors, and live in [Core.Syntactic.System.Lemmas].

    Two rules are stated slightly more generally than in the paper, both times
    following the presentation this development already had:

    - [wf_exp_eq_natrec_cong] also allows the motive to vary.  The paper keeps it
      fixed; allowing it to vary is strictly stronger and is what the algorithmic
      equality of [Algorithmic] compares.
    - [wf_subtyp_pi] checks the codomains in [Γ ▹ A'] rather than the paper's
      [Γ ▹ A].  The two are interderivable given the premise [Γ ⊢ A ≈ A' : Type@i]
      and context conversion, and [Γ ▹ A'] is what the soundness proof wants.

    Every judgment reads a global context [Ψ], which [a_glob] resolves into.  [Ψ]
    is a *parameter*: no rule changes it, and the well-formedness of [Ψ] itself
    ([⊢g Ψ], below) is therefore not an induction on [Ψ]. *)

From Stdlib Require Import List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export GlobalCtx Substitution.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

Reserved Notation "⊢ Ψ ⍮ Γ" (at level 70, Ψ at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢ M : A" (at level 70, Γ at level 69, M at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢ M ≈ M' : A" (at level 70, Γ at level 69, M at level 69, M' at level 69, A at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢ A ⊆ A'" (at level 70, Γ at level 69, A at level 69, A' at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢w φ : Δ" (at level 70, Γ at level 69, φ constr at level 60, Δ at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢s σ : Δ" (at level 70, Γ at level 69, σ at level 69, Δ at level 69).
Reserved Notation "Ψ ⍮ Γ ⊢s σ ≈ σ' : Δ" (at level 70, Γ at level 69, σ at level 69, σ' at level 69, Δ at level 69).
Reserved Notation "Γ ∋ '#' x : A" (at level 70, x constr at level 0, A at level 69).
Reserved Notation "⊢g Ψ" (at level 70).
Reserved Notation "Ψ ⊢e E" (at level 70, E at level 69).
Reserved Notation "Ψ ⊢m Φ" (at level 70, Φ at level 69).
Reserved Notation "Ψ ⊢u U" (at level 70, U at level 69).
Reserved Notation "Ψ ⊢t T" (at level 70, T at level 69).

Generalizable All Variables.

(** ** Closed Expressions

    A global's recorded type and body are closed — members are stored fully
    generalized over their module's parameters — which is what lets [wf_glob]
    use them in any [Γ], and what lets weakening and substitution pass through a
    global without knowing that [Ψ] is well formed.  Stated as the two equations
    it is used as, so that no new inductive and no [⊢g Ψ] hypothesis is needed. *)

Definition exp_closed (M : exp) : Prop :=
  (forall φ, M⟨φ⟩ = M) /\ (forall σ, M[σ] = M).

Lemma exp_closed_wk : forall {M}, exp_closed M -> forall φ, M⟨φ⟩ = M.
Proof. now intros ? []. Qed.

Lemma exp_closed_sub : forall {M}, exp_closed M -> forall σ, M[σ] = M.
Proof. now intros ? []. Qed.

(** ** Context Lookup

    A lookup carries the weakenings that separate the binding from the top of
    the context, so [Var] below needs no shifting of its own.  The shift here is
    the *weakening* [↑], not the substitution [Wk]: everything that has to move a
    looked-up type past a lifted operation does so with [exp_wk_shift_wk_q] or
    [exp_wk_shift_sub_q], both of which are stated for [↑]. *)

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `(Γ ▹ A ∋ #0 : A⟨↑⟩)
  | there : `(Γ ∋ #n : A -> Γ ▹ B ∋ #(S n) : A⟨↑⟩)
where "Γ ∋ '#' x : A" := (ctx_lookup x A Γ) : type_scope.

(** ** The Four Mutually Defined Judgments *)

Inductive wf_ctx (Ψ : gctx) : ctx -> Prop :=
| wf_ctx_empty : ⊢ Ψ ⍮ ⋅
| wf_ctx_extend :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ A : Type@i ->
     ⊢ Ψ ⍮ Γ ▹ A )
where "⊢ Ψ ⍮ Γ" := (wf_ctx Ψ Γ) : type_scope

with wf_exp (Ψ : gctx) : ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ Type@i : Type@(S i) )
| wf_nat :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ ℕ : Type@0 )
| wf_zero :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ zero : ℕ )
| wf_succ :
  `( Ψ ⍮ Γ ⊢ M : ℕ ->
     Ψ ⍮ Γ ⊢ succ M : ℕ )
| wf_natrec :
  `( Ψ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Ψ ⍮ Γ ⊢ M : ℕ ->
     Ψ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] )
| wf_pi :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ⊢ Π A B : Type@i )
| wf_fn :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ M : B ->
     Ψ ⍮ Γ ⊢ λ A M : Π A B )
| wf_app :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ⊢ M : Π A B ->
     Ψ ⍮ Γ ⊢ N : A ->
     Ψ ⍮ Γ ⊢ M $ N : B[Id,,N] )
| wf_vlookup :
  `( ⊢ Ψ ⍮ Γ ->
     Γ ∋ #x : A ->
     Ψ ⍮ Γ ⊢ #x : A )
(** A global is used at the type recorded for it, which needs neither a
    substitution nor the module's telescope here.  The two extra arguments play
    the same role as the one of [wf_exp_subtyp]: the first gives the
    presupposition directly, the second is what weakening and substitution
    rewrite with. *)
| wf_glob :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     exp_closed A ->
     Ψ ∋ᵍ p ⇒ ge_def b A B ->
     Ψ ⍮ Γ ⊢ a_glob p : A )
| wf_exp_subtyp :
  `( Ψ ⍮ Γ ⊢ M : A ->
     (** We have this extra argument for soundness.
         Note that we need to keep it asymmetric:
         only [A'] is checked. If we check A as well,
         we cannot even construct something like
         [Γ ⊢ Type@0⟨↑⟩ : Type@1] with the current
         rules. Under the symmetric rule, the example requires
         [Γ ⊢ Type@1⟨↑⟩ : Type@2] to apply weakening,
         which requires [Γ ⊢ Type@2⟨↑⟩ : Type@3], and so on.
      *)
     Ψ ⍮ Γ ⊢ A' : Type@i ->
     Ψ ⍮ Γ ⊢ A ⊆ A' ->
     Ψ ⍮ Γ ⊢ M : A' )
where "Ψ ⍮ Γ ⊢ M : A" := (wf_exp Ψ Γ A M) : type_scope

with wf_exp_eq (Ψ : gctx) : ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules *)
| wf_exp_eq_typ_cong :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ Type@i ≈ Type@i : Type@(S i) )
| wf_exp_eq_nat_cong :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@0 )
| wf_exp_eq_zero_cong :
  `( ⊢ Ψ ⍮ Γ ->
     Ψ ⍮ Γ ⊢ zero ≈ zero : ℕ )
| wf_exp_eq_succ_cong :
  `( Ψ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Ψ ⍮ Γ ⊢ succ M ≈ succ M' : ℕ )
| wf_exp_eq_natrec_cong :
  `( Ψ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Type@i ->
     Ψ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
     Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
     Ψ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Ψ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] )
| wf_exp_eq_pi_cong :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@i ->
     Ψ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@i )
| wf_exp_eq_fn_cong :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
     Ψ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B )
| wf_exp_eq_app_cong :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ⊢ M ≈ M' : Π A B ->
     Ψ ⍮ Γ ⊢ N ≈ N' : A ->
     Ψ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N] )
| wf_exp_eq_var :
  `( ⊢ Ψ ⍮ Γ ->
     Γ ∋ #x : A ->
     Ψ ⍮ Γ ⊢ #x ≈ #x : A )
| wf_exp_eq_glob :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     exp_closed A ->
     Ψ ∋ᵍ p ⇒ ge_def b A B ->
     Ψ ⍮ Γ ⊢ a_glob p ≈ a_glob p : A )
(** *** Computation rules *)
| wf_exp_eq_pi_beta :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ M : B ->
     Ψ ⍮ Γ ⊢ N : A ->
     Ψ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] )
| wf_exp_eq_nat_beta_zero :
  `( Ψ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Ψ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] )
| wf_exp_eq_nat_beta_succ :
  `( Ψ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Ψ ⍮ Γ ⊢ M : ℕ ->
     Ψ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] )
(** [δ]: a transparent definition unfolds.  An [abstract] one ([b = false]) and
    an axiom ([B = None]) do not. *)
| wf_exp_eq_glob_unfold :
  `( Ψ ⍮ Γ ⊢ M : A ->
     exp_closed A ->
     exp_closed M ->
     Ψ ∋ᵍ p ⇒ ge_def true A (Some M) ->
     Ψ ⍮ Γ ⊢ a_glob p ≈ M : A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ⊢ M : Π A B ->
     Ψ ⍮ Γ ⊢ M ≈ λ A M⟨↑⟩ $ #0 : Π A B )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Ψ ⍮ Γ ⊢ M ≈ M' : A ->
     Ψ ⍮ Γ ⊢ A' : Type@i ->
     (** This extra argument is here to be consistent with
         [wf_exp_subtyp].
      *)
     Ψ ⍮ Γ ⊢ A ⊆ A' ->
     Ψ ⍮ Γ ⊢ M ≈ M' : A' )
| wf_exp_eq_sym :
  `( Ψ ⍮ Γ ⊢ M ≈ M' : A ->
     Ψ ⍮ Γ ⊢ M' ≈ M : A )
| wf_exp_eq_trans :
  `( Ψ ⍮ Γ ⊢ M ≈ M' : A ->
     Ψ ⍮ Γ ⊢ M' ≈ M'' : A ->
     Ψ ⍮ Γ ⊢ M ≈ M'' : A )
where "Ψ ⍮ Γ ⊢ M ≈ M' : A" := (wf_exp_eq Ψ Γ A M M') : type_scope

(** *** Subtyping *)
with wf_subtyp (Ψ : gctx) : ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the presupposition
      lemmas independently.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( Ψ ⍮ Γ ⊢ M' : Type@i ->
     Ψ ⍮ Γ ⊢ M ≈ M' : Type@i ->
     Ψ ⍮ Γ ⊢ M ⊆ M' )
| wf_subtyp_trans :
  `( Ψ ⍮ Γ ⊢ M ⊆ M' ->
     Ψ ⍮ Γ ⊢ M' ⊆ M'' ->
     Ψ ⍮ Γ ⊢ M ⊆ M'' )
| wf_subtyp_univ :
  `( ⊢ Ψ ⍮ Γ ->
     i < j ->
     Ψ ⍮ Γ ⊢ Type@i ⊆ Type@j )
| wf_subtyp_pi :
  `( Ψ ⍮ Γ ⊢ A : Type@i ->
     Ψ ⍮ Γ ⊢ A' : Type@i ->
     Ψ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Ψ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Ψ ⍮ Γ ▹ A' ⊢ B' : Type@i ->
     Ψ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
     Ψ ⍮ Γ ⊢ Π A B ⊆ Π A' B' )
where "Ψ ⍮ Γ ⊢ A ⊆ A'" := (wf_subtyp Ψ Γ A A') : type_scope.

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
    subtyping case consumes [Γ ⊢ A ⊆ A'] syntactically, so neither of the
    two equality judgments needs a predicate. *)

Scheme wf_ctx_mind' := Minimality for wf_ctx Sort Prop
with wf_exp_mind' := Minimality for wf_exp Sort Prop.
Combined Scheme syntactic_wf_ctx_exp_mut_ind from
  wf_ctx_mind',
  wf_exp_mind'.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp ctx_lookup : mctt.

(** ** Well-formedness of the Global Context

    A member may mention any name in scope, not only the ones declared before
    it, and the imports are well formed as a whole; so every judgment below
    checks against the *same*, whole [Ψ], and [⊢g Ψ] is a conjunction about
    [Ψ]'s two halves rather than an induction on either.  Weakening along [⊑] is
    then a lemma about the fixed parameter, not a rule.

    Entries are checked in [⋅]: they are stored closed, generalized over their
    module's parameters, so [ge_mod]'s telescope is only checked to be a
    context.

    Two judgments carry the layer: [Ψ ⊢t T] for the import trie and [⊢g Ψ] for
    the context, the latter assuming the former of [Ψ]'s imports and then asking
    the same of every frame of its definition stack.  [Ψ ⊢e E], [Ψ ⊢m Φ] and
    [Ψ ⊢u U] are the machinery both of them share, since a frame of the stack and
    a unit in the trie are the same kind of thing. *)

Inductive wf_gentry (Ψ : gctx) : gentry -> Prop :=
(** An axiom: only its type is checked. *)
| wf_gentry_axiom :
  `( Ψ ⍮ ⋅ ⊢ A : Type@i ->
     Ψ ⊢e ge_def b A None )
(** A definition: its body carries the type recorded for it.  The type is
    checked separately for the same reason as in [wf_gentry_axiom] — nothing
    here may appeal to the presupposition lemmas. *)
| wf_gentry_def :
  `( Ψ ⍮ ⋅ ⊢ A : Type@i ->
     Ψ ⍮ ⋅ ⊢ M : A ->
     Ψ ⊢e ge_def b A (Some M) )
| wf_gentry_mod :
  `( ⊢ Ψ ⍮ Δ ->
     Ψ ⊢m Φ ->
     Ψ ⊢e ge_mod Δ Φ )
where "Ψ ⊢e E" := (wf_gentry Ψ E) : type_scope

with wf_gmod (Ψ : gctx) : gmod -> Prop :=
| wf_gmod_nil : Ψ ⊢m ⋄
| wf_gmod_ext :
  `( Ψ ⊢m Φ ->
     Ψ ⊢e E ->
     Ψ ⊢m Φ ⊳ x ↦ E )
where "Ψ ⊢m Φ" := (wf_gmod Ψ Φ) : type_scope.

Scheme wf_gentry_mut_ind := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind := Minimality for wf_gmod Sort Prop.
Combined Scheme global_wf_mut_ind from
  wf_gentry_mut_ind,
  wf_gmod_mut_ind.

(** A unit: its parameter telescope, and the module it declares. *)
Record wf_gunit (Ψ : gctx) (U : gunit) : Prop := wf_gunit_intro
{ wf_gunit_params : ⊢ Ψ ⍮ gu_params U
; wf_gunit_mod : Ψ ⊢m gu_mod U
}.
Notation "Ψ ⊢u U" := (wf_gunit Ψ U) : type_scope.

Inductive wf_gtree (Ψ : gctx) : gtree -> Prop :=
| wf_gtree_nil : Ψ ⊢t ∅
| wf_gtree_none :
  `( Ψ ⊢t T ->
     Ψ ⊢t T' ->
     Ψ ⊢t T ▸ x ↦ None ⊲ T' )
| wf_gtree_some :
  `( Ψ ⊢t T ->
     Ψ ⊢t T' ->
     Ψ ⊢u U ->
     Ψ ⊢t T ▸ x ↦ (Some U) ⊲ T' )
where "Ψ ⊢t T" := (wf_gtree Ψ T) : type_scope.

(** Canonicity belongs here rather than in [wf_gtree]/[wf_gmod]: it is what
    makes resolution in a well-formed context deterministic
    ([gt_lookup_det], [gc_lookup_det]), and it is a property of the whole
    half, not of one node. *)
Record wf_gctx (Ψ : gctx) : Prop := wf_gctx_intro
{ wf_gctx_imports_canon : gt_canon (gc_imports Ψ)
; wf_gctx_defs_canon : gs_canon (gc_defs Ψ)
; wf_gctx_imports : Ψ ⊢t gc_imports Ψ
; wf_gctx_defs : List.Forall (wf_gunit Ψ) (gc_defs Ψ)
}.
Notation "⊢g Ψ" := (wf_gctx Ψ) : type_scope.

#[export]
Hint Constructors wf_gentry wf_gmod wf_gtree : mctt.

(** ** Weakening and Substitution Typing

    These are the derived judgments.
    They are records, not inductive relations: a weakening or a substitution is
    well-typed exactly when it sends each binding of its source context to
    something of the correspondingly transported type in its target.  Nothing
    here is recursive, so none of it belongs in the mutual block above; the
    price is that closure under the operations ([Id], [_,,_], [q], [_⨟_]) has to
    be proved, which is what [wf_wk_id]–[wf_wk_compose] and
    [wf_sub_id]–[wf_sub_q] do. *)

Record wf_wk (Ψ : gctx) (Γ Δ : ctx) (φ : wk) : Prop := wf_wk_intro
{ wf_wk_dom : ⊢ Ψ ⍮ Γ
; wf_wk_cod : ⊢ Ψ ⍮ Δ
; wf_wk_lookup : forall x A, Δ ∋ #x : A -> Γ ∋ #(φ x) : A⟨φ⟩
}.
Notation "Ψ ⍮ Γ ⊢w φ : Δ" := (wf_wk Ψ Γ Δ φ) : type_scope.

Record wf_sub (Ψ : gctx) (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : ⊢ Ψ ⍮ Γ
; wf_sub_cod : ⊢ Ψ ⍮ Δ
; wf_sub_apply : forall x A, Δ ∋ #x : A -> Ψ ⍮ Γ ⊢ (σ x) : A[σ]
}.
Notation "Ψ ⍮ Γ ⊢s σ : Δ" := (wf_sub Ψ Γ Δ σ) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Ψ : gctx) (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : Ψ ⍮ Γ ⊢s σ : Δ
; wf_sub_eq_right : Ψ ⍮ Γ ⊢s σ' : Δ
; wf_sub_eq_apply : forall x A, Δ ∋ #x : A -> Ψ ⍮ Γ ⊢ (σ x) ≈ (σ' x) : A[σ]
}.
Notation "Ψ ⍮ Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Ψ Γ Δ σ σ') : type_scope.

(** The projections are deliberately *not* registered in [mctt]: each of them
    has a conclusion ([⊢ Γ], [Γ ⊢s σ : Δ]) that the corresponding introduction
    rule also produces, so the pair would let [eauto] cycle. [Lemmas.v] states
    the presuppositions it actually wants as separate lemmas. *)

(** [wf_wk], [wf_sub] and [wf_sub_eq] are all invariant under pointwise equality
    of the operation: the operation only ever occurs applied to an index or
    applied to an expression, and both of those respect pointwise equality
    ([exp_wk_Proper], [exp_sub_Proper]). *)

#[export]
Instance wf_wk_Proper Ψ Γ Δ : Proper (wk_eq ==> iff) (wf_wk Ψ Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> Ψ ⍮ Γ ⊢w φ : Δ -> Ψ ⍮ Γ ⊢w ψ : Δ) as Himp.
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
Instance wf_sub_Proper Ψ Γ Δ : Proper (sb_eq ==> iff) (wf_sub Ψ Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> Ψ ⍮ Γ ⊢s σ : Δ -> Ψ ⍮ Γ ⊢s τ : Δ) as Himp.
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

Lemma presup_subtyp_right : forall {Ψ Γ A B}, Ψ ⍮ Γ ⊢ A ⊆ B -> exists i, Ψ ⍮ Γ ⊢ B : Type@i.
Proof.
  induction 1; mautosolve.
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** ** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Ψ Γ A A' M,
    Ψ ⍮ Γ ⊢ M : A ->
    Ψ ⍮ Γ ⊢ A ⊆ A' ->
    Ψ ⍮ Γ ⊢ M : A'.
Proof.
  intros.
  assert (exists i, Ψ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Ψ Γ A A' M M',
    Ψ ⍮ Γ ⊢ M ≈ M' : A ->
    Ψ ⍮ Γ ⊢ A ⊆ A' ->
    Ψ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros.
  assert (exists i, Ψ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
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
Instance wf_exp_eq_PER Ψ Γ A : PER (wf_exp_eq Ψ Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_subtyp_Transitive Ψ Γ : Transitive (wf_subtyp Ψ Γ).
Proof.
  hnf; mauto.
Qed.

Add Parametric Morphism Ψ Γ T : (wf_exp_eq Ψ Γ T)
    with signature wf_exp_eq Ψ Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Ψ Γ T : (wf_exp_eq Ψ Γ T)
    with signature eq ==> wf_exp_eq Ψ Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.
