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

    - Consequently the four judgments about terms — context well-formedness,
      typing, term equality and subtyping — carry no substitution judgment.  They
      are mutually defined with the seven that make up global well-formedness.

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

    Every judgment reads the two global components [a_glob] resolves into, kept
    apart rather than bundled: the dependency levels [Θ] and the definition stack
    [Ξ], so a judgment reads [Θ ⍮ Ξ ⍮ Γ ⊢ M : A].  They are *indices*, not
    parameters: no rule about terms changes them, but a filed unit is checked
    against the levels below it and a stack frame with the frames inside it
    dropped, so [⊢g Θ ⍮ Ξ] really is an induction that varies them — exactly as
    [⊢ Γ] varies [Γ]. *)

From Stdlib Require Import List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export GlobalCtx ModSubst.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

Reserved Notation "⊢ Θ ⍮ Ξ ⍮ Γ" (at level 70, Θ at level 69, Ξ at level 69, Γ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69, M' at level 69, A at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" (at level 70, Ξ at level 69, Γ at level 69, A at level 69, A' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ" (at level 70, Ξ at level 69, Γ at level 69, φ constr at level 60, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, σ' at level 69, Δ at level 69).
Reserved Notation "Γ ∋ '#' x : A" (at level 70, x constr at level 0, A at level 69).
Reserved Notation "⊢g Θ ⍮ Ξ" (at level 70, Θ at level 69, Ξ at level 69).
Reserved Notation "Θ ⍮ Ξ ⊢e E" (at level 70, Ξ at level 69, E at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Δ ⊢m Φ" (at level 70, Ξ at level 69, Δ at level 69, Φ at level 69).
Reserved Notation "Θ ⍮ Ξ ⊢u U" (at level 70, Ξ at level 69, U at level 69).

Generalizable All Variables.

(** ** Context Lookup

    A lookup carries the weakenings that separate the binding from the top of
    the context, so [Var] below needs no shifting of its own.  The shift here is
    the *weakening* [↑], not the substitution [Wk]: everything that has to move a
    looked-up type past a lifted operation does so with [exp_wk_shift_wk_q] or
    [exp_wk_shift_sub_q], both of which are stated for [↑]. *)

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `(Γ ▹ A ∋ #0 : A[↑]ʷ)
  | there : `(Γ ∋ #n : A -> Γ ▹ B ∋ #(S n) : A[↑]ʷ)
where "Γ ∋ '#' x : A" := (ctx_lookup x A Γ) : type_scope.

(** ** The Mutually Defined Judgments

    Four about terms, seven about the global context.  All eleven are one
    [Inductive … with …]: an entry's type and body are checked by the term
    judgments, so presupposition has to be proved for all of them at once. *)

Inductive wf_ctx : gdeps -> gstack -> ctx -> Prop :=
(** The base case carries what the judgment is relative to, as [wf_gmod_nil] and
    [wf_gstack_nil] do; [wf_ctx_extend] then needs no context premise of its own,
    since typing its head presupposes one.  This is the edge that makes the block
    genuinely mutual in both directions: a term appeals to [⊢g], and [⊢g] is
    checked by the term judgments. *)
| wf_ctx_empty :
  `( ⊢g Θ ⍮ Ξ ->
     ⊢ Θ ⍮ Ξ ⍮ ⋅ )
| wf_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A )
where "⊢ Θ ⍮ Ξ ⍮ Γ" := (wf_ctx Θ Ξ Γ) : type_scope

with wf_exp : gdeps -> gstack -> ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type@i : Type@(S i) )
| wf_nat :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Type@0 )
| wf_zero :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ zero : ℕ )
| wf_succ :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succ M : ℕ )
| wf_natrec :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] )
| wf_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type@i )
| wf_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : Π A B )
| wf_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N] )
| wf_vlookup :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x : A )
(** A parameter of an open module.  Its type was checked in the frame's
    telescope, over the frames outside it: the telescope's own variables are the
    frame's parameters, and the frames outside, with their parameters and
    members, are [1 + n] further out from here.  No local variable occurs in it, so it needs no adjustment to be used
    in [Γ]. *)
| wf_param :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     List.nth_error Ξ n = Some U ->
     gu_params U ∋ #k : T ->
     Θ ⍮ Ξ ⍮ Γ ⊢ $[n, k] : T[↑ₘ (S n)]ᵐ[sb_params n] )
(** A global is used at the type resolution hands back: generalized over the
    parameters of the closed modules it is read out of, which [X.foo] is then
    applied to, and mentioning those of the open ones as parameters.  No local
    variable occurs in it, so it needs no adjustment to be used in [Γ]; nothing
    else is premised, and that it is a type is a presupposition. *)
| wf_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p : ctx_pi Δ A )
| wf_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     (** We have this extra argument for soundness.
         Note that we need to keep it asymmetric:
         only [A'] is checked. If we check A as well,
         we cannot even construct something like
         [Γ ⊢ Type@0[↑]ʷ : Type@1] with the current
         rules. Under the symmetric rule, the example requires
         [Γ ⊢ Type@1[↑]ʷ : Type@2] to apply weakening,
         which requires [Γ ⊢ Type@2[↑]ʷ : Type@3], and so on.
      *)
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" := (wf_exp Θ Ξ Γ A M) : type_scope

with wf_exp_eq : gdeps -> gstack -> ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules *)
| wf_exp_eq_typ_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type@i ≈ Type@i : Type@(S i) )
| wf_exp_eq_nat_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@0 )
| wf_exp_eq_zero_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ zero ≈ zero : ℕ )
| wf_exp_eq_succ_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succ M ≈ succ M' : ℕ )
| wf_exp_eq_natrec_cong :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] )
| wf_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@i )
| wf_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B )
| wf_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N] )
| wf_exp_eq_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ #x : A )
| wf_exp_eq_param :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     List.nth_error Ξ n = Some U ->
     gu_params U ∋ #k : T ->
     Θ ⍮ Ξ ⍮ Γ ⊢ $[n, k] ≈ $[n, k] : T[↑ₘ (S n)]ᵐ[sb_params n] )
| wf_exp_eq_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def b pv A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p ≈ a_glob p : ctx_pi Δ A )
(** *** Computation rules *)
| wf_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] )
| wf_exp_eq_nat_beta_zero :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] )
| wf_exp_eq_nat_beta_succ :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] )
(** [δ]: a transparent definition unfolds.  An [abstract] one ([b = false]) and
    an axiom ([B = None]) do not.  The body unfolds to under the same telescope
    the type is generalized over, so it is [ctx_fn], not the bare [M]. *)
| wf_exp_eq_glob_unfold :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ∋ᵍ p ⇒ Δ ⍮ ge_def true pv A (Some M) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p ≈ ctx_fn Δ M : ctx_pi Δ A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
     (** This extra argument is here to be consistent with
         [wf_exp_subtyp].
      *)
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A' )
| wf_exp_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ≈ M : A )
| wf_exp_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ≈ M'' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M'' : A )
where "Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A" := (wf_exp_eq Θ Ξ Γ A M M') : type_scope

(** *** Subtyping *)
with wf_subtyp : gdeps -> gstack -> ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the presupposition
      lemmas independently.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' )
| wf_subtyp_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ⊆ M'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M'' )
| wf_subtyp_univ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type@i ⊆ Type@j )
| wf_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ Π A' B' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" := (wf_subtyp Θ Ξ Γ A A') : type_scope

(** ** Well-formedness of the Global Context

    Part of the same mutual definition: an entry's type and body are checked by
    the term judgments, and [⊢g Θ ⍮ Ξ] is what a use of [a_glob] appeals to, so
    the two directions are genuinely interdependent and presupposition has to be
    proved for all of them at once.

    A member may mention any name in scope, not only the ones declared before it,
    so within one unit everything is checked against the same [Θ] and [Ξ].  Across
    units it is not: a level is checked against the levels below it, and a frame
    against the frames outside it, which is why both components are indices of the
    whole block.  [wf_gdep] and [wf_gdeps] mention only [Θ], and [wf_gstack] only
    [Θ] and [Ξ] — keeping the two apart is what lets each say exactly what it is
    relative to.

    A member of a parameterized module is stored *open* in that module's
    parameters — generalizing it is [ctx_pi]'s job, at the use site — so it is
    checked in the telescope it lives under, which the judgment takes as an
    argument rather than reading off the entry.  [ge_mod] records only the
    parameters it adds to that telescope; a [gunit] records the whole of it, which
    is why a unit is always checked at [⋅].

    Canonicity is part of well-formedness: [wf_gmod_ext] asks for freshness, so a
    well-formed context resolves deterministically without a separate condition,
    and the [gm_canon]/[gs_canon]/[gds_mods_canon] predicates follow
    ([wf_gmod_canon], [wf_gstack_canon], [wf_gdeps_canon] in [Lemmas]). *)

(** An entry is checked against the current module, which is the head of [Ξ]:
    that frame is what [wf_gmod_ext] pushed, and it carries the parameters and the
    members declared so far.  The local context is therefore [⋅] — an entry binds
    nothing of its own. *)

with wf_gentry : gdeps -> gstack -> gentry -> Prop :=
(** An axiom: only its type is checked, there being no body to carry it. *)
| wf_gentry_axiom :
  `( Θ ⍮ Ξ ⍮ ⋅ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⊢e ge_def b pv A None )
(** A definition: its body carries the type recorded for it, so the type needs no
    premise of its own — that is presupposition, and it is provable here because
    the term judgments are part of this same definition. *)
| wf_gentry_def :
  `( Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
     Θ ⍮ Ξ ⊢e ge_def b pv A (Some M) )
(** An internal module, under the parameters [Δ'] it declares. *)
| wf_gentry_mod :
  `( Θ ⍮ Ξ ⍮ Δ' ⊢m Φ ->
     Θ ⍮ Ξ ⊢e ge_mod Δ' Φ )
where "Θ ⍮ Ξ ⊢e E" := (wf_gentry Θ Ξ E) : type_scope

with wf_gmod : gdeps -> gstack -> ctx -> gmod -> Prop :=
(** The base case is what makes [⊢m] presuppose its telescope, which is why no
    rule above carries a [⊢ Θ ⍮ Ξ ⍮ Δ] premise. *)
| wf_gmod_nil :
  `( ⊢ Θ ⍮ Ξ ⍮ Δ ->
     Θ ⍮ Ξ ⍮ Δ ⊢m ⋄ )
(** The entry is checked against the members declared *before* it: the module so
    far is [gu_mk Δ Φ], and pushing it as the innermost frame is what makes a
    [qu_rel] reference inside [E] reach its earlier siblings — and nothing later,
    nor itself. *)
| wf_gmod_ext :
  `( Θ ⍮ Ξ ⍮ Δ ⊢m Φ ->
     Θ ⍮ gu_mk Δ Φ :: Ξ ⊢e E ->
     gm_fresh x Φ ->
     Θ ⍮ Ξ ⍮ Δ ⊢m Φ ⊳ x ↦ E )
where "Θ ⍮ Ξ ⍮ Δ ⊢m Φ" := (wf_gmod Θ Ξ Δ Φ) : type_scope

(** A unit: its parameters are its *whole* telescope, whether it has been filed
    or is still open on the stack, so there is no ambient one to extend. *)

with wf_gunit : gdeps -> gstack -> gunit -> Prop :=
| wf_gunit_intro :
  `( Θ ⍮ Ξ ⍮ gu_params U ⊢m gu_mod U ->
     Θ ⍮ Ξ ⊢u U )
where "Θ ⍮ Ξ ⊢u U" := (wf_gunit Θ Ξ U) : type_scope

(** One dependency level, checked against the levels [Θ] below it: a filed unit
    is a finished compilation unit, so it sees no stack, and not its own level
    either.  Its path is fresh both in [Θ] and in the part of this level already
    filed, so a path is filed exactly once in the whole of [gdeps].  No ambient
    global context appears — [Θ] is all a level is relative to. *)

with wf_gdep : gdeps -> gdep -> Prop :=
(** As with [wf_gmod_nil], the base case is what makes the judgment presuppose
    what it is relative to. *)
| wf_gdep_nil :
  `( wf_gdeps Θ ->
     wf_gdep Θ nil )
| wf_gdep_cons :
  `( wf_gdep Θ d ->
     Θ ⍮ nil ⊢u U ->
     gds_fresh fp Θ ->
     gd_fresh fp d ->
     wf_gdep Θ ((fp, U) :: d) )

(** The levels, accumulated one at a time, each checked against those already
    piled up — so the newest level is at the front, as the newest frame is in a
    [gstack].  A unit can therefore only mention units at strictly lower levels,
    and *that* is where cycle freedom comes from: it is the shape of this
    judgment, not a proposition about the levels. *)

with wf_gdeps : gdeps -> Prop :=
| wf_gdeps_nil : wf_gdeps nil
| wf_gdeps_cons :
  `( wf_gdeps Θ ->
     wf_gdep Θ d ->
     wf_gdeps (d :: Θ) )

(** The definition stack, innermost frame first, relative to the levels.  Read
    exactly like [wf_gdep_cons], and for the same reason: a frame is checked
    against the frames *outside* it, so it cannot see itself, and a [qu_rel] index
    occurring inside it counts outward from there. *)

with wf_gstack : gdeps -> gstack -> Prop :=
| wf_gstack_nil :
  `( wf_gdeps Θ ->
     wf_gstack Θ nil )
| wf_gstack_cons :
  `( wf_gstack Θ Ξ ->
     Θ ⍮ Ξ ⊢u U ->
     wf_gstack Θ (U :: Ξ) )

with wf_gctx : gdeps -> gstack -> Prop :=
| wf_gctx_intro :
  `( wf_gstack Θ Ξ ->
     ⊢g Θ ⍮ Ξ )
where "⊢g Θ ⍮ Ξ" := (wf_gctx Θ Ξ) : type_scope.

(** The schemes are [Minimality], not [Induction]: nothing in this development
    is proved by a statement that mentions the derivation itself, and dropping
    the derivation arguments keeps the goals of a mutual induction readable and
    within reach of [mauto].

    A [Scheme] may name any *subset* of the block, and the judgments it leaves
    out survive as ordinary hypotheses in the cases that mention them.  That is
    what keeps the four-, three- and two-way principles below the same shape they
    had when the global layer was declared separately. *)

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

(** The global subset: the shape of [wf_global_canon] and
    [gsub_preserves_global]. *)

Scheme wf_gentry_mut_ind := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind := Minimality for wf_gmod Sort Prop.
Combined Scheme global_wf_mut_ind from
  wf_gentry_mut_ind,
  wf_gmod_mut_ind.

(** The whole block, for a statement that has to cross between the two
    directions — the term judgments appeal to [⊢g Θ ⍮ Ξ] and the global ones to
    typing, so presupposition is proved here or not at all. *)

Scheme wf_ctx_mut_ind_all := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind_all := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind_all := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind_all := Minimality for wf_subtyp Sort Prop
with wf_gentry_mut_ind_all := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind_all := Minimality for wf_gmod Sort Prop
with wf_gunit_mut_ind_all := Minimality for wf_gunit Sort Prop
with wf_gdep_mut_ind_all := Minimality for wf_gdep Sort Prop
with wf_gdeps_mut_ind_all := Minimality for wf_gdeps Sort Prop
with wf_gstack_mut_ind_all := Minimality for wf_gstack Sort Prop
with wf_gctx_mut_ind_all := Minimality for wf_gctx Sort Prop.
Combined Scheme wf_mut_ind_all from
  wf_ctx_mut_ind_all,
  wf_exp_mut_ind_all,
  wf_exp_eq_mut_ind_all,
  wf_subtyp_mut_ind_all,
  wf_gentry_mut_ind_all,
  wf_gmod_mut_ind_all,
  wf_gunit_mut_ind_all,
  wf_gdep_mut_ind_all,
  wf_gdeps_mut_ind_all,
  wf_gstack_mut_ind_all,
  wf_gctx_mut_ind_all.

(** The projections the [Record]s used to provide.  Two of the old four are
    presuppositions instead, so they live in [Presup]: [⊢ Θ ⍮ Ξ ⍮ gu_params U] of
    [⊢m], hence of [⊢u], and [wf_gdeps Θ] of [wf_gstack]. *)

Lemma wf_gunit_mod : forall Θ Ξ U, Θ ⍮ Ξ ⊢u U -> Θ ⍮ Ξ ⍮ gu_params U ⊢m gu_mod U.
Proof. now inversion 1. Qed.

Lemma wf_gctx_stack : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> wf_gstack Θ Ξ.
Proof. now inversion 1. Qed.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp ctx_lookup : mctt.

#[export]
Hint Constructors wf_gentry wf_gmod wf_gunit wf_gdep wf_gdeps wf_gstack : mctt.

(** ** Weakening and Substitution Typing

    These are the derived judgments.
    They are records, not inductive relations: a weakening or a substitution is
    well-typed exactly when it sends each binding of its source context to
    something of the correspondingly transported type in its target.  Nothing
    here is recursive, so none of it belongs in the mutual block above; the
    price is that closure under the operations ([Id], [_,,_], [q], [_⨟_]) has to
    be proved, which is what [wf_wk_id]–[wf_wk_compose] and
    [wf_sub_id]–[wf_sub_q] do. *)

Record wf_wk (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (φ : wk) : Prop := wf_wk_intro
{ wf_wk_dom : ⊢ Θ ⍮ Ξ ⍮ Γ
; wf_wk_cod : ⊢ Θ ⍮ Ξ ⍮ Δ
; wf_wk_lookup : forall x A, Δ ∋ #x : A -> Γ ∋ #(φ x) : A[φ]ʷ
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ" := (wf_wk Θ Ξ Γ Δ φ) : type_scope.

Record wf_sub (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : ⊢ Θ ⍮ Ξ ⍮ Γ
; wf_sub_cod : ⊢ Θ ⍮ Ξ ⍮ Δ
; wf_sub_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ (σ x) : A[σ]
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ" := (wf_sub Θ Ξ Γ Δ σ) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ
; wf_sub_eq_right : Θ ⍮ Ξ ⍮ Γ ⊢s σ' : Δ
; wf_sub_eq_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ (σ x) ≈ (σ' x) : A[σ]
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Θ Ξ Γ Δ σ σ') : type_scope.

(** The projections are deliberately *not* registered in [mctt]: each of them
    has a conclusion ([⊢ Γ], [Γ ⊢s σ : Δ]) that the corresponding introduction
    rule also produces, so the pair would let [eauto] cycle. [Lemmas.v] states
    the presuppositions it actually wants as separate lemmas. *)

(** [wf_wk], [wf_sub] and [wf_sub_eq] are all invariant under pointwise equality
    of the operation: the operation only ever occurs applied to an index or
    applied to an expression, and both of those respect pointwise equality
    ([exp_wk_Proper], [exp_sub_Proper]). *)

#[export]
Instance wf_wk_Proper Θ Ξ Γ Δ : Proper (wk_eq ==> iff) (wf_wk Θ Ξ Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢w ψ : Δ) as Himp.
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
Instance wf_sub_Proper Θ Ξ Γ Δ : Proper (sb_eq ==> iff) (wf_sub Θ Ξ Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢s τ : Δ) as Himp.
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

Lemma presup_subtyp_right : forall {Θ Ξ Γ A B}, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ B : Type@i.
Proof.
  induction 1; mautosolve.
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** ** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Θ Ξ Γ A A' M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Θ Ξ Γ A A' M M',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
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
Instance wf_exp_eq_PER Θ Ξ Γ A : PER (wf_exp_eq Θ Ξ Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_subtyp_Transitive Θ Ξ Γ : Transitive (wf_subtyp Θ Ξ Γ).
Proof.
  hnf; mauto.
Qed.

Add Parametric Morphism Θ Ξ Γ T : (wf_exp_eq Θ Ξ Γ T)
    with signature wf_exp_eq Θ Ξ Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Θ Ξ Γ T : (wf_exp_eq Θ Ξ Γ T)
    with signature eq ==> wf_exp_eq Θ Ξ Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.
