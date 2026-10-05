(** * The Syntactic Judgments

    Substitution is a meta-level operation rather than a syntactic
    constructor, so:

    - there is no [wf_exp_sub] rule and there are no [_sub] computation rules;
      how a substitution distributes over each term former, how substitutions
      compose and what the identity does are theorems about [exp_sub], proved
      in [Core.Syntactic.Substitution] and used by [rewrite];
    - the four judgments about terms (context well-formedness, typing, term
      equality and subtyping) mention no substitution judgment, and are
      mutually defined with the seven that make up global well-formedness;
    - weakening and substitution typing are derived judgments: statements that
      an operation maps every binding of one context to something of the right
      type in the other.  Their closure properties (identity, extension,
      lifting, composition) are lemmas, in [Core.Syntactic.System.Structural].

    Two rules are stated more generally than in the paper:

    - [wf_exp_eq_natrec_cong] also lets the motive vary.  This is strictly
      stronger, and is what the algorithmic equality of [Algorithmic]
      compares.
    - [wf_subtyp_pi] checks the codomains in [Γ ▹ A'] rather than [Γ ▹ A].  The
      two are interderivable given [Γ ⊢ A ≈ A' : Type@i] and context
      conversion, and [Γ ▹ A'] is what the soundness proof wants.

    Every judgment reads the two global components a global resolves in: the
    dependency levels [Θ] and the definition stack [Ξ], as in
    [Θ ⍮ Γ ⊢ M : A].  They are indices, not parameters: no rule about terms
    changes them, but a filed unit is checked against the levels below it and a
    stack frame against the frames outside it, so [⊢g Θ] is an induction
    that varies them, as [⊢ Γ] varies [Γ]. *)

From Stdlib Require Import List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution GlobalCtx Members.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

Reserved Notation "⊢ Θ ⍮ Γ" (at level 70, Θ at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ M : A" (at level 70, Γ at level 69, M at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ M ≈ M' : A" (at level 70, Γ at level 69, M at level 69, M' at level 69, A at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ A ⊆ A'" (at level 70, Γ at level 69, A at level 69, A' at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" (at level 70, Γ at level 69, Ψ at level 69, Ψ' at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ᵘ U ≈ U'" (at level 70, Γ at level 69, U at level 69, U' at level 69).
Reserved Notation "Θ ⍮ Γ ⊢ᵐ H ≈ H'" (at level 70, Γ at level 69, H at level 69, H' at level 69).
Reserved Notation "Θ ⍮ Γ ⊢w φ : Δ" (at level 70, Γ at level 69, φ constr at level 60, Δ at level 69).
Reserved Notation "Θ ⍮ Γ ⊢s σ : Δ" (at level 70, Γ at level 69, σ at level 69, Δ at level 69).
Reserved Notation "Θ ⍮ Γ ⊢s σ ≈ σ' : Δ" (at level 70, Γ at level 69, σ at level 69, σ' at level 69, Δ at level 69).
Reserved Notation "Γ ∋ '#' x : A" (at level 70, x constr at level 0, A at level 69).
Reserved Notation "Γ ∋ '#' x ≔ M : A" (at level 70, x constr at level 0, M at level 69, A at level 69).
Reserved Notation "⊢g Θ" (at level 70, Θ at level 69).

Generalizable All Variables.

(** ** Context Lookup

    A lookup carries the weakenings that separate the binding from the top of
    the context, so [Var] below needs no shifting of its own.  The shift here is
    the weakening [↑], not the substitution [Wk]: everything that has to move a
    looked-up type past a lifted operation does so with [exp_wk_shift_wk_q] or
    [exp_wk_shift_sub_q], both of which are stated for [↑]. *)

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `(Γ ▹ A ∋ #0 : A[↑]ʷ)
  | here_def : `(Γ ▸ A ≔ M ∋ #0 : A[↑]ʷ)
  | there : `(Γ ∋ #n : A -> e :: Γ ∋ #(S n) : A[↑]ʷ)
where "Γ ∋ '#' x : A" := (ctx_lookup x A Γ) : type_scope.

(** The body of a definition entry, weakened to the use site like its type. *)
Inductive ctx_lookup_def : nat -> typ -> exp -> ctx -> Prop :=
  | def_here : `(Γ ▸ A ≔ M ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ)
  | def_there : `(Γ ∋ #n ≔ M : A -> e :: Γ ∋ #(S n) ≔ M[↑]ʷ : A[↑]ʷ)
where "Γ ∋ '#' x ≔ M : A" := (ctx_lookup_def x A M Γ) : type_scope.

(** ** Shapes of Units

    A telescope of parameters has assumptions only: a module's arguments are
    terms. *)
Definition tele_ass (Δ : ctx) : Prop := List.Forall (fun e => exists A, e = ce_ass A) Δ.

(** The annotation of a local definition, if any, is the type it is checked
    at; without one, the type is any its body has. *)
Definition let_ann (oA : option typ) (A : typ) : Prop := oA = None \/ oA = Some A.

(** ** The Mutually Defined Judgments

    Four about terms, three about extensions, units and module expressions,
    and one about the global context.  All eight are one
    [Inductive … with …]: a constant's type and body and a unit's entries
    are checked by the term judgments, so presupposition has to be proved for
    all of them at once. *)

Inductive wf_ctx : gctx -> ctx -> Prop :=
(** The base case carries what the judgment is relative to; [wf_ctx_extend]
    then needs no context premise of its own,
    since typing its head presupposes one.  This is the edge that makes the block
    genuinely mutual in both directions: a term appeals to [⊢g], and [⊢g] is
    checked by the term judgments. *)
| wf_ctx_empty :
  `( ⊢g Θ ->
     ⊢ Θ ⍮ ⋅ )
| wf_ctx_extend :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     ⊢ Θ ⍮ Γ ▹ A )
| wf_ctx_extend_def :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ M : A ->
     ⊢ Θ ⍮ Γ ▸ A ≔ M )
(** A module slot holds a well-formed unit. *)
| wf_ctx_extend_mod :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊢ Θ ⍮ Γ ▹ₘ U )
where "⊢ Θ ⍮ Γ" := (wf_ctx Θ Γ) : type_scope

with wf_exp : gctx -> ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ Type@i : Type@(S i) )
| wf_nat :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ℕ : Type@0 )
| wf_zero :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ zero : ℕ )
| wf_succ :
  `( Θ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Γ ⊢ succ M : ℕ )
| wf_natrec :
  `( Θ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] )
| wf_True :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⊤ : Type@0 )
| wf_true :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⋆ : ⊤ )
| wf_False :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⊥ : Type@0 )
| wf_exfalso :
  `( Θ ⍮ Γ ▹ ⊥ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ M : ⊥ ->
     Θ ⍮ Γ ⊢ efq M return A : A[Id,,M] )
| wf_pi :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ⊢ Π A B : Type@i )
| wf_fn :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Γ ⊢ λ A M : Π A B )
| wf_app :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Γ ⊢ M $ N : B[Id,,N] )
(** A local definition, of its annotated type or of a type its body has. *)
| wf_let :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Γ ⊢ a_let (b_def oA M) B : C[Id,,M] )
(** A local module occupies one index, a slot holding its unit.  The body's
    type is premised to be a type, as the canonical type of [wf_mem] is:
    equivalent substitutions are moved through the body by [ζ], and the two
    sides then meet at that type. *)
| wf_let_mod :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Γ ▹ₘ U ⊢ C : Type@i ->
     Θ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Γ ⊢ ℓₘ U in B : C[Id ,,ₘ me_lit U] )
(** A member of a module expression with no argument, at its canonical type.
    The canonical type is a type, and the member's δ-reduct inhabits it. *)
| wf_mem :
  `( me_noargs H ->
     Θ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Γ ⊢ A : Type@i ->
     member_unfold Θ Γ H x = Some M ->
     Θ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Γ ⊢ a_mem H x : A )
(** A member of an applied module is the member of its root, applied to the
    arguments: arguments and selections commute. *)
| wf_mem_app :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Γ ⊢ a_mem H x : A )
| wf_vlookup :
  `( ⊢ Θ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Γ ⊢ #x : A )
(** A constant, at its type, which is closed.  That the type is a type is
    a presupposition. *)
| wf_const :
  `( ⊢ Θ ⍮ Γ ->
     gc_const Θ c = Some (A, oM, b) ->
     Θ ⍮ Γ ⊢ a_const c : A )
| wf_exp_subtyp :
  `( Θ ⍮ Γ ⊢ M : A ->
     (** This premise is needed for soundness.  It is asymmetric: only [A'] is
         checked.  Checking [A] as well would make even
         [Γ ⊢ Type@0[↑]ʷ : Type@1] underivable, since weakening it would require
         [Γ ⊢ Type@1[↑]ʷ : Type@2], which requires [Γ ⊢ Type@2[↑]ʷ : Type@3], and
         so on. *)
     Θ ⍮ Γ ⊢ A' : Type@i ->
     Θ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Γ ⊢ M : A' )
where "Θ ⍮ Γ ⊢ M : A" := (wf_exp Θ Γ A M) : type_scope

with wf_exp_eq : gctx -> ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules *)
| wf_exp_eq_typ_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ Type@i ≈ Type@i : Type@(S i) )
| wf_exp_eq_nat_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ℕ ≈ ℕ : Type@0 )
| wf_exp_eq_zero_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ zero ≈ zero : ℕ )
| wf_exp_eq_succ_cong :
  `( Θ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Θ ⍮ Γ ⊢ succ M ≈ succ M' : ℕ )
| wf_exp_eq_natrec_cong :
  `( Θ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
     Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Θ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] )
| wf_exp_eq_True_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Type@0 )
| wf_exp_eq_true_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⋆ ≈ ⋆ : ⊤ )
| wf_exp_eq_False_cong :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Type@0 )
| wf_exp_eq_exfalso_cong :
  `( Θ ⍮ Γ ▹ ⊥ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
     Θ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M] )
| wf_exp_eq_pi_cong :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B ≈ B' : Type@i ->
     Θ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type@i )
| wf_exp_eq_fn_cong :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
     Θ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B )
| wf_exp_eq_app_cong :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ⊢ M ≈ M' : Π A B ->
     Θ ⍮ Γ ⊢ N ≈ N' : A ->
     Θ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N] )
| wf_exp_eq_let_cong :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
     let_ann oA A ->
     let_ann oA' A' ->
     Θ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M] )
(** The right-hand side is typed in its own context, which differs from the
    left's by the unit. *)
| wf_exp_eq_let_mod_cong :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Γ ▹ₘ U ⊢ B ≈ B' : C ->
     Θ ⍮ Γ ⊢ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     Θ ⍮ Γ ⊢ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] )
(** Members of equivalent module expressions without arguments, at the
    canonical type of the left one.  A member of an applied module is the
    member of its root, applied ([wf_exp_eq_mem_app]), which is how equations
    about it are derived. *)
| wf_exp_eq_mem_cong :
  `( me_noargs H ->
     me_noargs H' ->
     Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Γ ⊢ a_mem H x : A ->
     Θ ⍮ Γ ⊢ a_mem H' x : A ->
     Θ ⍮ Γ ⊢ a_mem H x ≈ a_mem H' x : A )
| wf_exp_eq_var :
  `( ⊢ Θ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Γ ⊢ #x ≈ #x : A )
| wf_exp_eq_const :
  `( ⊢ Θ ⍮ Γ ->
     gc_const Θ c = Some (A, oM, b) ->
     Θ ⍮ Γ ⊢ a_const c ≈ a_const c : A )
(** *** Computation rules *)
| wf_exp_eq_pi_beta :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] )
| wf_exp_eq_nat_beta_zero :
  `( Θ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] )
| wf_exp_eq_nat_beta_succ :
  `( Θ ⍮ Γ ▹ ℕ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] )
(** [ζ]: a local definition is substituted into its body. *)
| wf_exp_eq_let_zeta :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M] )
(** [ζ] for local modules: the slot is replaced by the unit. *)
| wf_exp_eq_let_mod_zeta :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Γ ▹ₘ U ⊢ C : Type@i ->
     Θ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] )
(** [δ] for members: a member is its δ-reduct. *)
| wf_exp_eq_mem_delta :
  `( me_noargs H ->
     Θ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Γ ⊢ A : Type@i ->
     member_unfold Θ Γ H x = Some M ->
     Θ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Γ ⊢ a_mem H x ≈ M : A )
(** Arguments commute with selection. *)
| wf_exp_eq_mem_app :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Γ ⊢ a_mem H x ≈ apps (member_ref R (pre ++ x :: nil)) args : A )
(** [δ] for local definitions: a defined variable is its body.  It is stated
    at every depth, since weakening moves a definition arbitrarily deep. *)
| wf_exp_eq_var_delta :
  `( ⊢ Θ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Γ ⊢ #x ≈ M : A )
(** [δ]: an unsealed constant unfolds; a sealed one does not. *)
| wf_exp_eq_const_unfold :
  `( ⊢ Θ ⍮ Γ ->
     gc_const Θ c = Some (A, Some M, true) ->
     Θ ⍮ Γ ⊢ a_const c ≈ M : A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B )
| wf_exp_eq_true_eta :
  `( Θ ⍮ Γ ⊢ M : ⊤ ->
     Θ ⍮ Γ ⊢ M ≈ ⋆ : ⊤ )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Θ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Γ ⊢ A' : Type@i ->
     (** This premise mirrors the one of [wf_exp_subtyp]. *)
     Θ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Γ ⊢ M ≈ M' : A' )
| wf_exp_eq_sym :
  `( Θ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Γ ⊢ M' ≈ M : A )
| wf_exp_eq_trans :
  `( Θ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Γ ⊢ M' ≈ M'' : A ->
     Θ ⍮ Γ ⊢ M ≈ M'' : A )
where "Θ ⍮ Γ ⊢ M ≈ M' : A" := (wf_exp_eq Θ Γ A M M') : type_scope

(** *** Subtyping *)
with wf_subtyp : gctx -> ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** This premise lets the presupposition lemmas be proved independently: it
      gives presupposition for the right-hand side directly. *)
  `( Θ ⍮ Γ ⊢ M' : Type@i ->
     Θ ⍮ Γ ⊢ M ≈ M' : Type@i ->
     Θ ⍮ Γ ⊢ M ⊆ M' )
| wf_subtyp_trans :
  `( Θ ⍮ Γ ⊢ M ⊆ M' ->
     Θ ⍮ Γ ⊢ M' ⊆ M'' ->
     Θ ⍮ Γ ⊢ M ⊆ M'' )
| wf_subtyp_univ :
  `( ⊢ Θ ⍮ Γ ->
     i < j ->
     Θ ⍮ Γ ⊢ Type@i ⊆ Type@j )
| wf_subtyp_pi :
  `( Θ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Γ ⊢ A' : Type@i ->
     Θ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Γ ▹ A' ⊢ B' : Type@i ->
     Θ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
     Θ ⍮ Γ ⊢ Π A B ⊆ Π A' B' )
where "Θ ⍮ Γ ⊢ A ⊆ A'" := (wf_subtyp Θ Γ A A') : type_scope

(** ** Modules

    Equivalence of modules is pointwise: two units are equivalent when their
    entries are, one by one and in the same order, and two module expressions
    when their parts are.  Well-formedness is the reflexive instance.

    [Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'] compares two extensions of [Γ] entry by entry.  An
    entry is compared in the left extension; the right one's entry is also
    typed in the right extension, so that presupposition needs no context
    conversion. *)
with wf_ext_eq : gctx -> ctx -> ctx -> ctx -> Prop :=
| wf_ext_eq_nil :
  `( ⊢ Θ ⍮ Γ ->
     Θ ⍮ Γ ⊢ˣ ⋅ ≈ ⋅ )
| wf_ext_eq_ass :
  `( Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ψ ++ Γ ⊢ A : Type@i ->
     Θ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ψ' ++ Γ ⊢ A' : Type@i ->
     Θ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' )
| wf_ext_eq_def :
  `( Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ψ ++ Γ ⊢ A : Type@i ->
     Θ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ψ ++ Γ ⊢ M : A ->
     Θ ⍮ Ψ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ψ' ++ Γ ⊢ A' : Type@i ->
     Θ ⍮ Ψ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Γ ⊢ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' )
| wf_ext_eq_mod :
  `( Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Γ ⊢ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' )
where "Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" := (wf_ext_eq Θ Γ Ψ Ψ') : type_scope

(** Units.  A body unit's parameters are compared as an extension of [Γ],
    then its entries one by one, each in its own self context: the self slot
    holding the body before the entry, over the parameters.  That context is
    itself compared as an extension of [Γ], which checks the body before the
    entry; the right-hand entry is typed in its own self context too, so that
    presupposition needs no context conversion. *)
with wf_unit_eq : gctx -> ctx -> gunit -> gunit -> Prop :=
| wf_unit_eq_nil :
  `( Θ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     Θ ⍮ Γ ⊢ᵘ gu_body Δ ⋄ ≈ gu_body Δ' ⋄ )
| wf_unit_eq_def :
  `( Θ ⍮ Γ ⊢ˣ self_ent Φ :: Δ ≈ self_ent Φ' :: Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     gm_fresh x Φ ->
     gm_fresh x Φ' ->
     Θ ⍮ self_ent Φ :: Δ ++ Γ ⊢ A : Type@i ->
     Θ ⍮ self_ent Φ :: Δ ++ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ self_ent Φ :: Δ ++ Γ ⊢ M : A ->
     Θ ⍮ self_ent Φ :: Δ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ self_ent Φ' :: Δ' ++ Γ ⊢ A' : Type@i ->
     Θ ⍮ self_ent Φ' :: Δ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Γ ⊢ᵘ gu_body Δ (Φ ⊳ x ↦ ge_def pv A (Some M)) ≈ gu_body Δ' (Φ' ⊳ x ↦ ge_def pv A' (Some M')) )
| wf_unit_eq_mod :
  `( Θ ⍮ Γ ⊢ˣ self_ent Φ :: Δ ≈ self_ent Φ' :: Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     gm_fresh x Φ ->
     gm_fresh x Φ' ->
     Θ ⍮ self_ent Φ :: Δ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ self_ent Φ' :: Δ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Γ ⊢ᵘ gu_body Δ (Φ ⊳ x ↦ ge_mod pv U) ≈ gu_body Δ' (Φ' ⊳ x ↦ ge_mod pv U') )
| wf_unit_eq_alias :
  `( Θ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     Θ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E' ->
     Θ ⍮ Δ' ++ Γ ⊢ᵐ E' ≈ E' ->
     Θ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') )
| wf_unit_eq_sym :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Γ ⊢ᵘ U' ≈ U )
| wf_unit_eq_trans :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Γ ⊢ᵘ U' ≈ U'' ->
     Θ ⍮ Γ ⊢ᵘ U ≈ U'' )
where "Θ ⍮ Γ ⊢ᵘ U ≈ U'" := (wf_unit_eq Θ Γ U U') : type_scope

(** Module expressions.  A chain from a unit must name a module, and an
    argument is checked against the outermost parameter of the module's arity
    ([tele_view]): a module is applied to at most as many arguments as it has
    parameters.  Both arguments are typed, as the parts of an extension are,
    and so is the parameter's type. *)
with wf_modexp_eq : gctx -> ctx -> modexp -> modexp -> Prop :=
| wf_me_unit :
  `( ⊢ Θ ⍮ Γ ->
     gc_unit Θ fp = Some U ->
     Θ ⍮ Γ ⊢ᵐ me_unit fp ≈ me_unit fp )
| wf_me_var :
  `( ⊢ Θ ⍮ Γ ->
     Γ ∋ #x ⇒ₘ U ->
     Θ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x )
| wf_me_lit :
  `( Θ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U' )
| wf_me_mem :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Γ H (y :: nil) (mr_mod T) ->
     member_type Θ Γ H' (y :: nil) (mr_mod T') ->
     Θ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H' y )
| wf_me_app :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Γ H nil (mr_mod T) ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Γ ⊢ B : Type@i ->
     Θ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Γ ⊢ N ≈ N' : B ->
     member_type Θ Γ H' nil (mr_mod T') ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Γ ⊢ B' : Type@j ->
     Θ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H' N' )
| wf_me_sym :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Γ ⊢ᵐ H' ≈ H )
| wf_me_trans :
  `( Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Γ ⊢ᵐ H' ≈ H'' ->
     Θ ⍮ Γ ⊢ᵐ H ≈ H'' )
where "Θ ⍮ Γ ⊢ᵐ H ≈ H'" := (wf_modexp_eq Θ Γ H H') : type_scope

(** ** Well-formedness of the Global Context

    Part of the same mutual definition: a unit and a constant are checked by
    the term judgments, and a use of either appeals to [⊢g Θ].  Each is
    checked against the part of the global context below it, in the empty
    context, so it is closed; its name is fresh there. *)
with wf_gctx : gctx -> Prop :=
| wf_gctx_nil : ⊢g nil
| wf_gctx_unit :
  `( Θ ⍮ ⋅ ⊢ᵘ U ≈ U ->
     gc_unit Θ fp = None ->
     ⊢g gd_unit fp U :: Θ )
| wf_gctx_const :
  `( Θ ⍮ ⋅ ⊢ M : A ->
     gc_const Θ c = None ->
     ⊢g gd_const c A (Some M) b :: Θ )
(** An axiom: a constant without a body, at a type. *)
| wf_gctx_ax :
  `( Θ ⍮ ⋅ ⊢ A : Type@i ->
     gc_const Θ c = None ->
     ⊢g gd_const c A None b :: Θ )
where "⊢g Θ" := (wf_gctx Θ) : type_scope.

(** The schemes are [Minimality], not [Induction]: nothing in this development
    is proved by a statement that mentions the derivation itself, and dropping
    the derivation arguments keeps the goals of a mutual induction readable and
    within reach of [mauto].

    A [Scheme] may name any subset of the block, and the judgments it leaves
    out survive as ordinary hypotheses in the cases that mention them. *)

Scheme wf_ctx_mut_ind := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind := Minimality for wf_subtyp Sort Prop
with wf_ext_eq_mut_ind := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mut_ind := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mut_ind := Minimality for wf_modexp_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_subtyp_mut_ind,
  wf_ext_eq_mut_ind,
  wf_unit_eq_mut_ind,
  wf_modexp_eq_mut_ind.

(** The three-way scheme is the shape of [wk_preserves_wf], [sub_preserves_wf]
    and [sub_eq_preserves_exp]: each of them
    transports the three judgments about a fixed context along an operation,
    and says nothing about context well-formedness.  Generating it as a scheme
    in its own right (rather than combining the four-way one) means it takes
    exactly three predicates: the [⊢ Γ] premises of rules like [wf_typ] survive
    as ordinary hypotheses. *)

Scheme wf_exp_mind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mind := Minimality for wf_subtyp Sort Prop
with wf_ext_eq_mind := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mind := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mind := Minimality for wf_modexp_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_exp_mind,
  wf_exp_eq_mind,
  wf_subtyp_mind,
  wf_ext_eq_mind,
  wf_unit_eq_mind,
  wf_modexp_eq_mind.

(** The module judgments alone: the shape of the facts about the parts of a
    unit. *)

Scheme wf_ext_eq_mind3 := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mind3 := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mind3 := Minimality for wf_modexp_eq Sort Prop.
Combined Scheme module_wf_mut_ind from
  wf_ext_eq_mind3,
  wf_unit_eq_mind3,
  wf_modexp_eq_mind3.

(** The two-way scheme is the shape of the soundness fundamental theorem: the
    gluing model relates contexts and terms, and its
    subtyping case consumes [Γ ⊢ A ⊆ A'] syntactically, so neither of the
    two equality judgments needs a predicate. *)

Scheme wf_ctx_mind' := Minimality for wf_ctx Sort Prop
with wf_exp_mind' := Minimality for wf_exp Sort Prop.
Combined Scheme syntactic_wf_ctx_exp_mut_ind from
  wf_ctx_mind',
  wf_exp_mind'.

(** The whole block, for a statement that has to cross between the two
    directions: the term judgments appeal to [⊢g Θ] and the global context
    to typing, so presupposition is proved here or not at all. *)

Scheme wf_ctx_mut_ind_all := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind_all := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind_all := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind_all := Minimality for wf_subtyp Sort Prop
with wf_ext_eq_mut_ind_all := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mut_ind_all := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mut_ind_all := Minimality for wf_modexp_eq Sort Prop
with wf_gctx_mut_ind_all := Minimality for wf_gctx Sort Prop.
Combined Scheme wf_mut_ind_all from
  wf_ctx_mut_ind_all,
  wf_exp_mut_ind_all,
  wf_exp_eq_mut_ind_all,
  wf_subtyp_mut_ind_all,
  wf_ext_eq_mut_ind_all,
  wf_unit_eq_mut_ind_all,
  wf_modexp_eq_mut_ind_all,
  wf_gctx_mut_ind_all.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp ctx_lookup ctx_lookup_def : mctt.

Lemma let_ann_none : forall A, let_ann None A.
Proof. intros; left; reflexivity. Qed.

Lemma let_ann_some : forall A, let_ann (Some A) A.
Proof. intros; right; reflexivity. Qed.

#[export]
Hint Resolve let_ann_none let_ann_some : mctt.

Ltac solve_let_ann := first [ apply let_ann_some | eassumption | apply let_ann_none ].

(** The annotations of the local definitions in context, as the two cases. *)
Ltac destruct_let_ann :=
  repeat match goal with H : let_ann _ _ |- _ => destruct H as [-> | ->] end; cbv beta iota in *.

#[export]
Hint Constructors wf_ext_eq wf_unit_eq wf_modexp_eq : mctt.

#[export]
Hint Constructors wf_gctx : mctt.

(** ** Weakening and Substitution Typing

    These are the derived judgments.
    They are records, not inductive relations: a weakening or a substitution is
    well-typed exactly when it sends each binding of its source context to
    something of the correspondingly transported type in its target.  Nothing
    here is recursive, so none of it belongs in the mutual block above; the
    price is that closure under the operations ([Id], [_,,_], [q], [_⨟_]) has to
    be proved, which is what [wf_wk_id]–[wf_wk_compose] and
    [wf_sub_id]–[wf_sub_q] do. *)

Record wf_wk (Θ : gctx) (Γ Δ : ctx) (φ : wk) : Prop := wf_wk_intro
{ wf_wk_dom : ⊢ Θ ⍮ Γ
; wf_wk_cod : ⊢ Θ ⍮ Δ
; wf_wk_lookup : forall x A, Δ ∋ #x : A -> Γ ∋ #(φ x) : A[φ]ʷ
(** A renaming sends a definition to the same definition. *)
; wf_wk_lookup_def : forall x A M, Δ ∋ #x ≔ M : A -> Γ ∋ #(φ x) ≔ M[φ]ʷ : A[φ]ʷ
(** A renaming sends a module slot to a slot of the same unit. *)
; wf_wk_lookup_mod : forall x U, Δ ∋ #x ⇒ₘ U -> Γ ∋ #(φ x) ⇒ₘ gunit_wk U φ
}.
Notation "Θ ⍮ Γ ⊢w φ : Δ" := (wf_wk Θ Γ Δ φ) : type_scope.

Record wf_sub (Θ : gctx) (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : ⊢ Θ ⍮ Γ
; wf_sub_cod : ⊢ Θ ⍮ Δ
; wf_sub_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Γ ⊢ #x[σ] : A[σ]
(** A substitution sends a definition to something equal to its body. *)
; wf_sub_apply_def : forall x A M, Δ ∋ #x ≔ M : A -> Θ ⍮ Γ ⊢ #x[σ] ≈ M[σ] : A[σ]
(** A substitution sends a module slot to the unit it holds, transported:
    as a well-formed literal, or as a slot holding that unit. *)
; wf_sub_apply_mod : forall x U, Δ ∋ #x ⇒ₘ U ->
    (σ x = se_mod (me_lit U[σ]ᵘ) /\ Θ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) \/ exists y, σ x = se_var y /\ Γ ∋ #y ⇒ₘ U[σ]ᵘ
}.
Notation "Θ ⍮ Γ ⊢s σ : Δ" := (wf_sub Θ Γ Δ σ) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Θ : gctx) (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : Θ ⍮ Γ ⊢s σ : Δ
; wf_sub_eq_right : Θ ⍮ Γ ⊢s σ' : Δ
; wf_sub_eq_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Γ ⊢ #x[σ] ≈ #x[σ'] : A[σ]
}.
Notation "Θ ⍮ Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Θ Γ Δ σ σ') : type_scope.

(** The projections are not registered in [mctt]: each of them
    has a conclusion ([⊢ Γ], [Γ ⊢s σ : Δ]) that the corresponding introduction
    rule also produces, so the pair would let [eauto] cycle. [Lemmas.v] states
    the presuppositions it actually wants as separate lemmas. *)

(** [wf_wk], [wf_sub] and [wf_sub_eq] are all invariant under pointwise equality
    of the operation: the operation only ever occurs applied to an index or
    applied to an expression, and both of those respect pointwise equality
    ([exp_wk_Proper], [exp_sub_Proper]). *)

#[export]
Instance wf_wk_Proper Θ Γ Δ : Proper (wk_eq ==> iff) (wf_wk Θ Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> Θ ⍮ Γ ⊢w φ : Δ -> Θ ⍮ Γ ⊢w ψ : Δ) as Himp.
  {
    intros φ ψ Heq [? ? Hlk Hlkd Hlkm].
    econstructor; try eassumption.
    - intros x A ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- Heq.
      now apply Hlk.
    - intros x A M ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- !Heq.
      now apply Hlkd.
    - intros x U ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- Heq.
      now apply Hlkm.
  }
  intros φ ψ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

#[export]
Instance wf_sub_Proper Θ Γ Δ : Proper (sb_eq ==> iff) (wf_sub Θ Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> Θ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Γ ⊢s τ : Δ) as Himp.
  {
    intros σ τ Heq [? ? Hap Hapd Hapm].
    econstructor; try eassumption.
    - intros x A ?.
      rewrite <- !Heq.
      now apply Hap.
    - intros x A M ?.
      rewrite <- !Heq.
      now apply Hapd.
    - intros x U HU.
      rewrite <- (Heq x), <- (gunit_sub_sb_eq U σ τ Heq).
      now apply Hapm.
  }
  intros σ τ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

(** ** Immediate & Independent Presuppositions *)

Lemma presup_subtyp_right : forall {Θ Γ A B}, Θ ⍮ Γ ⊢ A ⊆ B -> exists i, Θ ⍮ Γ ⊢ B : Type@i.
Proof.
  induction 1; mautosolve.
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** ** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Θ Γ A A' M,
    Θ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Γ ⊢ M : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Θ Γ A A' M M',
    Θ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Γ ⊢ A' : Type@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mctt.
#[export]
Remove Hints wf_exp_eq_subtyp : mctt.

(** ** Term Equality is a PER

    Reflexivity at a well-typed term is not available here — it needs an
    induction over typing, so it lives in [Core.Syntactic.System.Lemmas]
    together with the [PERElem] instance that lets [saturate_refl] use it.  The
    same goes for [wf_sub_eq], whose symmetry and transitivity need
    [sub_eq_preserves_exp] to move between the types [A[σ]] and [A[σ']]. *)

#[export]
Instance wf_exp_eq_PER Θ Γ A : PER (wf_exp_eq Θ Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_subtyp_Transitive Θ Γ : Transitive (wf_subtyp Θ Γ).
Proof.
  hnf; mauto.
Qed.

Add Parametric Morphism Θ Γ T : (wf_exp_eq Θ Γ T)
    with signature wf_exp_eq Θ Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Θ Γ T : (wf_exp_eq Θ Γ T)
    with signature eq ==> wf_exp_eq Θ Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.
