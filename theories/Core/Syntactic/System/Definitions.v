(** * The Syntactic Judgments

    Substitution is a meta-level operation rather than a syntactic
    constructor, so:

    - there is no [wf_exp_sub] rule and there are no [_sub] computation rules;
      how a substitution distributes over each term former, how substitutions
      compose and what the identity does are theorems about [exp_sub], proved
      in [Core.Syntactic.Substitution] and used by [rewrite];
    - the four judgments about terms (context well-formedness, typing, term
      equality and subtyping) mention no substitution judgment, and are
      mutually defined with the six about units, extensions, module
      expressions and the global context;
    - weakening and substitution typing are derived judgments: statements that
      an operation maps every binding of one context to something of the right
      type in the other.  Their closure properties (identity, extension,
      lifting, composition) are lemmas, in [Core.Syntactic.System.Structural].

    Two rules are stated more generally than in the paper:

    - [wf_exp_eq_natrec_cong] also lets the motive vary.  This is strictly
      stronger, and is what the algorithmic equality of [Algorithmic]
      compares.
    - [wf_subtyp_pi] checks the codomains in [Γ ▹ A'] rather than [Γ ▹ A].  The
      two are interderivable given [Γ ⊢ A ≈ A' : Typeω@i] and context
      conversion, and [Γ ▹ A'] is what the soundness proof wants.

    Every judgment reads the two global components a global resolves in: the
    filed units [Θ] and the definition stack [Ξ], as in
    [Θ ⍮ Ξ ⍮ Γ ⊢ M : A].  They are indices, not parameters: no rule about terms
    changes them, but a filed unit is checked against the units before it and a
    stack frame against the frames outside it, so [⊢g Θ ⍮ Ξ] is an induction
    that varies them, as [⊢ Γ] varies [Γ]. *)

From Stdlib Require Import Lia List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution Members.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

Reserved Notation "⊢ Θ ⍮ Ξ ⍮ Γ" (at level 70, Θ at level 69, Ξ at level 69, Γ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69, M' at level 69, A at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" (at level 70, Ξ at level 69, Γ at level 69, A at level 69, A' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" (at level 70, Ξ at level 69, Γ at level 69, Ψ at level 69, Ψ' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'" (at level 70, Ξ at level 69, Γ at level 69, U at level 69, U' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'" (at level 70, Ξ at level 69, Γ at level 69, H at level 69, H' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ" (at level 70, Ξ at level 69, Γ at level 69, φ constr at level 60, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, σ' at level 69, Δ at level 69).
Reserved Notation "Γ ∋ '#' x : A" (at level 70, x constr at level 0, A at level 69).
Reserved Notation "Γ ∋ '#' x ≔ M : A" (at level 70, x constr at level 0, M at level 69, A at level 69).
Reserved Notation "⊢g Θ ⍮ Ξ" (at level 70, Θ at level 69, Ξ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⊢e E" (at level 70, Ξ at level 69, mp at level 69, E at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ" (at level 70, Ξ at level 69, mp at level 69, Δ at level 69, Φ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⊢u U" (at level 70, Ξ at level 69, mp at level 69, U at level 69).

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

(** Two bodies compared entry by entry: the same names and kinds in the same
    order, the same privacy, and transparent definitions with a body.  A
    local import is a pre-form the core expands before typing
    ([Imports]), so a typed body has none. *)
Definition entry_shape (E E' : gentry) : Prop :=
  match E, E' with
  | ge_def b pv _ (Some _), ge_def b' pv' _ (Some _) => b = true /\ b' = true /\ pv = pv'
  | ge_mod pv _, ge_mod pv' _ => pv = pv'
  | _, _ => False
  end.

Fixpoint body_shape (Φ Φ' : gmod) : Prop :=
  match Φ, Φ' with
  | gm_nil, gm_nil => True
  | gm_ext Φ x E, gm_ext Φ' x' E' => body_shape Φ Φ' /\ x = x' /\ entry_shape E E'
  | _, _ => False
  end.

(** The annotation of a local definition, if any, is the type it is checked
    at; without one, the type is any its body has. *)
Definition let_ann (oA : option typ) (A : typ) : Prop := oA = None \/ oA = Some A.

(** ** The Mutually Defined Judgments

    Four about terms, three about units, extensions and module expressions,
    and three about the global context.  All ten are one
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
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A )
| wf_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M )
(** A module slot holds a well-formed unit. *)
| wf_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U )
where "⊢ Θ ⍮ Ξ ⍮ Γ" := (wf_ctx Θ Ξ Γ) : type_scope

with wf_exp : gdeps -> gstack -> ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i : Typeω@(S i) )
(** A small universe at a level is in the small universe at the next one.
    The level is an arbitrary term, so a universe may be indexed by a
    variable. *)
| wf_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : Type⟨succl M⟩ )
(** Every type of levels is small, at the least level. *)
| wf_level :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : Type@0 )
(** A level is a literal, a successor, or a join.  The sort of a literal is
    not constrained here: the sorts bound the *values* of levels, which is
    what the model of [Level@n] says, and the syntax of a literal carries no
    bound of its own. *)
| wf_llit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@n )
| wf_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl M : Level@n )
| wf_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N : Level@n )
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
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] )
| wf_True :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Type@0 )
| wf_true :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ : ⊤ )
| wf_False :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Type@0 )
| wf_exfalso :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A : A[Id,,M] )
| wf_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@i )
(** A [Π] of small types at a level is small at that level.  The level is a
    term of [Γ], so the codomain's universe is its weakening: a level that
    mentions the bound variable has no universe to name here.  The premise on
    the level follows from the domain's by presupposition; it is stated so
    that weakening and substitution, which come before presupposition, can
    move the domain into a large universe and extend the context with it. *)
| wf_pi_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type⟨L⟩ )
| wf_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : Π A B )
| wf_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N] )
(** A local definition, of its annotated type or of a type its body has. *)
| wf_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : C[Id,,M] )
(** A local module occupies one index, a slot holding its unit.  The body's
    type is premised to be a type, as the canonical type of [wf_mem] is:
    equivalent substitutions are moved through the body by [ζ], and the two
    sides then meet at that type. *)
| wf_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : C[Id ,,ₘ me_lit U] )
(** A member of a module expression with no argument, at its canonical type.
    The canonical type is a type, and the member's δ-reduct inhabits it. *)
| wf_mem :
  `( me_noargs H ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Ξ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     member_unfold Θ Ξ Γ H x = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
(** A member of an applied module is the member of its root, applied to the
    arguments: arguments and selections commute. *)
| wf_mem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
| wf_vlookup :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x : A )
(** A member of a chain from a unit, a global, is used at the type
    resolution hands back, which is closed: it is generalized over the
    parameters of every module enclosing the member, and applying it to them
    is the user's business.  The chain need not be a module: it may end in an
    open frame.  Nothing else is premised; that the type is a type is a
    presupposition. *)
| wf_mem_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     mod_qname H = Some mp ->
     gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
| wf_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     (** This premise is needed for soundness.  It is asymmetric: only [A'] is
         checked.  Checking [A] as well would make even
         [Γ ⊢ Typeω@0[↑]ʷ : Typeω@1] underivable, since weakening it would require
         [Γ ⊢ Typeω@1[↑]ʷ : Typeω@2], which requires [Γ ⊢ Typeω@2[↑]ʷ : Typeω@3], and
         so on. *)
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" := (wf_exp Θ Ξ Γ A M) : type_scope

with wf_exp_eq : gdeps -> gstack -> ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules *)
| wf_exp_eq_typ_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ≈ Typeω@i : Typeω@(S i) )
| wf_exp_eq_univ_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩ )
| wf_exp_eq_level_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ≈ Level@n : Type@0 )
| wf_exp_eq_llit_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o ≈ 𝕃ᵒ o : Level@n )
| wf_exp_eq_succl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl M ≈ succl M' : Level@n )
| wf_exp_eq_maxl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ maxl M' N' : Level@n )
(** *** The Level Equations

    Levels are a join semilattice with a least element and an inflationary
    successor that distributes over the join; the literal [ω·a + b] is the
    [b]-th successor of the limit [ω·a], and a limit is above every literal
    of a lower tier.  These are the equations of Danielsson–Favier–Kubánek
    Fig. 2 and the limit rule, and they are complete for the canonical forms
    of [Core.Syntactic.Levels]: two levels are equal exactly when they have
    the same canonical form. *)
| wf_exp_eq_llit_succl :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n )
| wf_exp_eq_maxl_llit_limit :
  `( a < a' ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a', 0)) ≈ 𝕃ᵒ(a', 0) : Level@n )
| wf_exp_eq_maxl_zero :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃@0) M ≈ M : Level@n )
| wf_exp_eq_maxl_assoc :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ P : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl (maxl M N) P ≈ maxl M (maxl N P) : Level@n )
| wf_exp_eq_maxl_comm :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ maxl N M : Level@n )
| wf_exp_eq_maxl_idem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M M ≈ M : Level@n )
| wf_exp_eq_succl_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl (maxl M N) ≈ maxl (succl M) (succl N) : Level@n )
| wf_exp_eq_maxl_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M (succl M) ≈ succl M : Level@n )
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
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS ≈ MS' : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] )
| wf_exp_eq_True_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Type@0 )
| wf_exp_eq_true_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ ≈ ⋆ : ⊤ )
| wf_exp_eq_False_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Type@0 )
| wf_exp_eq_exfalso_cong :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M] )
| wf_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Typeω@i )
| wf_exp_eq_pi_cong_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨L⟩ ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type⟨L[↑]ʷ⟩ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type⟨L⟩ )
| wf_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B )
| wf_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N] )
| wf_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
     let_ann oA A ->
     let_ann oA' A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M] )
(** The right-hand side is typed in its own context, which differs from the
    left's by the unit. *)
| wf_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] )
(** Members of equivalent module expressions without arguments, at the
    canonical type of the left one.  A member of an applied module is the
    member of its root, applied ([wf_exp_eq_mem_app]), which is how equations
    about it are derived. *)
| wf_exp_eq_mem_cong :
  `( me_noargs H ->
     me_noargs H' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Ξ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem H' x : A )
| wf_exp_eq_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ #x : A )
| wf_exp_eq_mem_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     mod_qname H = Some mp ->
     gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def b pv A B) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem H x : A )
(** *** Computation rules *)
| wf_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] )
| wf_exp_eq_nat_beta_zero :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] )
| wf_exp_eq_nat_beta_succ :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ MZ : A[Id,,zero] ->
     Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] )
(** [ζ]: a local definition is substituted into its body. *)
| wf_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M] )
(** [ζ] for local modules: the slot is replaced by the unit. *)
| wf_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] )
(** [δ] for members: a member is its δ-reduct. *)
| wf_exp_eq_mem_delta :
  `( me_noargs H ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Ξ Γ H (x :: nil) (mr_term A) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     member_unfold Θ Ξ Γ H x = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ M : A )
(** Arguments commute with selection. *)
| wf_exp_eq_mem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ apps (member_ref R (pre ++ x :: nil)) args : A )
(** [δ] for local definitions: a defined variable is its body.  It is stated
    at every depth, since weakening moves a definition arbitrarily deep. *)
| wf_exp_eq_var_delta :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ M : A )
(** [δ]: a transparent global unfolds.  An [abstract] one ([b = false]) and
    an axiom ([B = None]) do not.  Both are stored closed. *)
| wf_exp_eq_mem_glob_unfold :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     mod_qname H = Some mp ->
     gc_resolve Θ Ξ (qname_app mp (x :: nil)) = Some (ge_def true pv A (Some M)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ M : A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B )
| wf_exp_eq_true_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊤ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ ⋆ : ⊤ )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     (** This premise mirrors the one of [wf_exp_subtyp]. *)
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
  (** This premise lets the presupposition lemmas be proved independently: it
      gives presupposition for the right-hand side directly. *)
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' )
| wf_subtyp_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ⊆ M'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M'' )
| wf_subtyp_univ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ Typeω@j )
(** A small universe below one at a larger level.  The order on levels is
    [maxl M M' ≈ M'], which is decidable on canonical forms
    ([Core.Syntactic.Levels.lvl_le]) and never the order on realisers. *)
| wf_subtyp_suniv :
  (** The two typings let the presupposition lemmas be proved independently,
      as in [wf_subtyp_refl]. *)
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M M' ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ⊆ Type⟨M'⟩ )
(** A type of levels is below every type of levels of a larger sort: every
    level of a sort is a level of each larger one. *)
| wf_subtyp_level :
  `( m <= n ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@m ⊆ Level@n )
(** A small universe below every large one. *)
| wf_subtyp_small_large :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ⊆ Typeω@i )
| wf_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ Π A' B' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" := (wf_subtyp Θ Ξ Γ A A') : type_scope

(** ** Modules

    Equivalence of modules is pointwise: two units are equivalent when their
    entries are, one by one and in the same order, and two module expressions
    when their parts are.  Well-formedness is the reflexive instance.

    [Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'] compares two extensions of [Γ] entry by entry.  An
    entry is compared in the left extension; the right one's entry is also
    typed in the right extension, so that presupposition needs no context
    conversion. *)
with wf_ext_eq : gdeps -> gstack -> ctx -> ctx -> ctx -> Prop :=
| wf_ext_eq_nil :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ ⋅ ≈ ⋅ )
| wf_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' )
| wf_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' )
| wf_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" := (wf_ext_eq Θ Ξ Γ Ψ Ψ') : type_scope

(** Units.  A body unit's parameters and body are compared as one extension of
    [Γ]. *)
with wf_unit_eq : gdeps -> gstack -> ctx -> gunit -> gunit -> Prop :=
| wf_unit_eq_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φ ++ Δ ≈ body_ctx Φ' ++ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     List.NoDup (gm_names Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_body Δ Φ ≈ gu_body Δ' Φ' )
| wf_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E' ->
     Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ E' ≈ E' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') )
| wf_unit_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U )
| wf_unit_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'" := (wf_unit_eq Θ Ξ Γ U U') : type_scope

(** Module expressions.  A chain from a unit must name a module, and an
    argument is checked against the outermost parameter of the module's arity
    ([tele_view]): a module is applied to at most as many arguments as it has
    parameters.  Both arguments are typed, as the parts of an extension are,
    and so is the parameter's type. *)
with wf_modexp_eq : gdeps -> gstack -> ctx -> modexp -> modexp -> Prop :=
| wf_me_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     mod_qname H = Some mp ->
     member_type Θ Ξ Γ H nil (mr_mod T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H )
| wf_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ⇒ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x )
| wf_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U' )
| wf_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Ξ Γ H (y :: nil) (mr_mod T) ->
     member_type Θ Ξ Γ H' (y :: nil) (mr_mod T') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H' y )
| wf_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Ξ Γ H nil (mr_mod T) ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B ->
     member_type Θ Ξ Γ H' nil (mr_mod T') ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Typeω@j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H' N' )
| wf_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H )
| wf_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'" := (wf_modexp_eq Θ Ξ Γ H H') : type_scope

(** ** Well-formedness of the Global Context

    Part of the same mutual definition: an entry's type and body are checked by
    the term judgments, and a use of a global appeals to [⊢g Θ ⍮ Ξ].

    A unit is checked against the units filed before it, and a frame against
    the frames outside it, which is why both components are indices of the whole
    block.

    A member of a parameterized module is checked in the telescope of
    parameters it lives under, and stored generalized over it ([ctx_pi],
    [ctx_fn]).  [ge_mod] records only the parameters it adds to that telescope;
    a [gunit] records all of it, which is why a unit is checked at [⋅].

    Canonicity is part of well-formedness: [wf_gmod_ext] asks for freshness, so a
    well-formed context resolves deterministically without a separate
    condition. *)

(** An entry is checked against the current module, which is the head of [Ξ]:
    that frame is what [wf_gmod_ext] pushed, and it carries the parameters and the
    members declared so far.  The local context is the telescope of all the
    frames' parameters, [gs_tele Ξ]: parameters are ordinary λ-variables.  A
    definition is stored generalized over that telescope, so what is filed is
    closed, and nothing has to be done to it when it is read anywhere else.  [mp]
    is the entry's own module path, which a nested module's frame is named by. *)

with wf_gentry : gdeps -> gstack -> qname -> gentry -> Prop :=
(** An axiom: only its type is checked, there being no body to carry it. *)
| wf_gentry_axiom :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_def b pv (ctx_pi (gs_tele Ξ) A) None )
(** A definition: its body carries the type recorded for it, so the type needs no
    premise of its own — that is presupposition. *)
| wf_gentry_def :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)) )
(** An internal module, under the parameters [Δ'] it declares. *)
| wf_gentry_mod :
  `( Θ ⍮ Ξ ⍮ mp ⍮ Δ' ⊢m Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_body pv Δ' Φ )
(** An alias, under the parameters [Δ] it declares.  It is filed with its
    full telescope, so that it is closed; its target is checked, and its
    arguments with it, where it is declared. *)
| wf_gentry_alias :
  `( tele_ass Δ ->
     Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E)) )
where "Θ ⍮ Ξ ⍮ mp ⊢e E" := (wf_gentry Θ Ξ mp E) : type_scope

(** The module at path [mp], with own parameters [Δ], a telescope over the
    frames' parameters [gs_tele Ξ]. *)
with wf_gmod : gdeps -> gstack -> qname -> ctx -> gmod -> Prop :=
| wf_gmod_nil :
  `( tele_ass Δ ->
     ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m ⋄ )
(** The entry is checked against the members declared before it: the module so
    far is [gu_mk Δ Φ], pushed as the innermost frame under its own path. *)
| wf_gmod_ext :
  `( Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ->
     Θ ⍮ (mp, gu_body Δ Φ) :: Ξ ⍮ qname_in mp x ⊢e E ->
     gm_fresh x Φ ->
     Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ⊳ x ↦ E )
where "Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ" := (wf_gmod Θ Ξ mp Δ Φ) : type_scope

(** The filed units [Θ] and the stack [Ξ] of open frames, innermost first.
    A frame is checked against the frames outside it, and a unit is filed by
    closing the only open frame, named by its path, after which it is checked
    against the units filed before it.  So a unit sees no stack and not
    itself, and a [qu_rel] index inside a frame counts outward from there.
    Freshness ([frame_fresh]) makes a path filed at most once. *)

with wf_gstack : gdeps -> gstack -> Prop :=
| wf_gstack_nil : ⊢g nil ⍮ nil
| wf_gstack_file :
  `( ⊢g Θ ⍮ (q_abs fp nil, U) :: nil ->
     ⊢g (fp, U) :: Θ ⍮ nil )
| wf_gstack_cons :
  `( ⊢g Θ ⍮ Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ->
     frame_fresh Θ Ξ mp ->
     ⊢g Θ ⍮ (mp, gu_body Δ Φ) :: Ξ )
where "⊢g Θ ⍮ Ξ" := (wf_gstack Θ Ξ) : type_scope.

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
with wf_ext_eq_mut_ind_all := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mut_ind_all := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mut_ind_all := Minimality for wf_modexp_eq Sort Prop
with wf_gentry_mut_ind_all := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind_all := Minimality for wf_gmod Sort Prop
with wf_gstack_mut_ind_all := Minimality for wf_gstack Sort Prop.
Combined Scheme wf_mut_ind_all from
  wf_ctx_mut_ind_all,
  wf_exp_mut_ind_all,
  wf_exp_eq_mut_ind_all,
  wf_subtyp_mut_ind_all,
  wf_ext_eq_mut_ind_all,
  wf_unit_eq_mut_ind_all,
  wf_modexp_eq_mut_ind_all,
  wf_gentry_mut_ind_all,
  wf_gmod_mut_ind_all,
  wf_gstack_mut_ind_all.

(** ** Units

    A unit filed at a level, or a frame of the stack, is a body checked by
    [⊢m]: [⊢u] is not a judgment of its own, but this definition, which the
    block states inline ([wf_gstack_cons]).  Two further
    projections are presuppositions, in [Presup]: [⊢ Θ ⍮ Ξ ⍮ gu_params U] of
    [⊢m], hence of [⊢u], and [⊢g Θ ⍮ nil] of [⊢g Θ ⍮ Ξ]. *)

Definition wf_gunit (Θ : gdeps) (Ξ : gstack) (mp : qname) (U : gunit) : Prop :=
  exists Δ Φ, U = gu_body Δ Φ /\ Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ.
Notation "Θ ⍮ Ξ ⍮ mp ⊢u U" := (wf_gunit Θ Ξ mp U) : type_scope.

Lemma wf_gunit_intro : forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> Θ ⍮ Ξ ⍮ mp ⊢u gu_body Δ Φ.
Proof. intros; do 2 eexists; split; [ reflexivity | assumption ]. Qed.

Lemma wf_gunit_mod : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> Θ ⍮ Ξ ⍮ mp ⍮ gu_params U ⊢m gu_mod U.
Proof. intros * (Δ & Φ & -> & H); exact H. Qed.

Lemma wf_gunit_body : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> exists Δ Φ, U = gu_body Δ Φ.
Proof. intros * (Δ & Φ & -> & _); eauto. Qed.

(** The unit form of the two constructors that file one. *)

Lemma wf_gstack_cons' : forall Θ Ξ mp U,
    ⊢g Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ mp ⊢u U -> frame_fresh Θ Ξ mp -> ⊢g Θ ⍮ (mp, U) :: Ξ.
Proof. intros * ? (Δ & Φ & -> & ?) ?; apply wf_gstack_cons; assumption. Qed.

Lemma wf_gstack_cons_inv : forall Θ Ξ mp U,
    ⊢g Θ ⍮ (mp, U) :: Ξ -> ⊢g Θ ⍮ Ξ /\ Θ ⍮ Ξ ⍮ mp ⊢u U /\ frame_fresh Θ Ξ mp.
Proof. inversion 1; subst; eauto using wf_gunit_intro. Qed.

(** Filing, from the premises of the frame it closes. *)
Lemma wf_gstack_file' : forall Θ fp U,
    ⊢g Θ ⍮ nil -> Θ ⍮ nil ⍮ q_abs fp nil ⊢u U -> gds_lookup Θ fp = None -> ⊢g (fp, U) :: Θ ⍮ nil.
Proof. intros * ? ? ?; apply wf_gstack_file, wf_gstack_cons'; [ assumption | assumption | split; [ assumption | reflexivity ] ]. Qed.

Lemma wf_gstack_file_inv : forall Θ fp U,
    ⊢g (fp, U) :: Θ ⍮ nil -> ⊢g Θ ⍮ nil /\ Θ ⍮ nil ⍮ q_abs fp nil ⊢u U /\ gds_lookup Θ fp = None.
Proof.
  inversion 1; subst.
  match goal with H : ⊢g _ ⍮ _ :: nil |- _ => destruct (wf_gstack_cons_inv _ _ _ _ H) as (? & ? & [? _]) end; auto.
Qed.

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
Hint Constructors wf_gentry wf_gmod wf_gstack : mctt.
#[export]
Hint Resolve wf_gunit_intro : mctt.

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
(** A renaming sends a definition to the same definition. *)
; wf_wk_lookup_def : forall x A M, Δ ∋ #x ≔ M : A -> Γ ∋ #(φ x) ≔ M[φ]ʷ : A[φ]ʷ
(** A renaming sends a module slot to a slot of the same unit. *)
; wf_wk_lookup_mod : forall x U, Δ ∋ #x ⇒ₘ U -> Γ ∋ #(φ x) ⇒ₘ gunit_wk U φ
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ" := (wf_wk Θ Ξ Γ Δ φ) : type_scope.

Record wf_sub (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : ⊢ Θ ⍮ Ξ ⍮ Γ
; wf_sub_cod : ⊢ Θ ⍮ Ξ ⍮ Δ
; wf_sub_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] : A[σ]
(** A substitution sends a definition to something equal to its body. *)
; wf_sub_apply_def : forall x A M, Δ ∋ #x ≔ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ M[σ] : A[σ]
(** A substitution sends a module slot to the unit it holds, transported:
    as a well-formed literal, or as a slot holding that unit. *)
; wf_sub_apply_mod : forall x U, Δ ∋ #x ⇒ₘ U ->
    (σ x = se_mod (me_lit U[σ]ᵘ) /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) \/ exists y, σ x = se_var y /\ Γ ∋ #y ⇒ₘ U[σ]ᵘ
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ" := (wf_sub Θ Ξ Γ Δ σ) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ
; wf_sub_eq_right : Θ ⍮ Ξ ⍮ Γ ⊢s σ' : Δ
; wf_sub_eq_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ #x[σ'] : A[σ]
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Θ Ξ Γ Δ σ σ') : type_scope.

(** The projections are not registered in [mctt]: each of them
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
Instance wf_sub_Proper Θ Ξ Γ Δ : Proper (sb_eq ==> iff) (wf_sub Θ Ξ Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢s τ : Δ) as Himp.
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

(** The two forms of a literal's typing the proofs below name: at its own
    sort, which the conclusion of the rule does not determine, and at the
    least sort for a finite one. *)
Lemma wf_llit_ord : forall {Θ Ξ Γ o},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@(fst o).
Proof. intros; apply wf_llit; assumption. Qed.

Lemma wf_llit_fin : forall {Θ Ξ Γ n},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@n : Level.
Proof. intros; apply wf_llit; assumption. Qed.

#[export]
Hint Resolve wf_llit_ord wf_llit_fin : mctt.

(** A small universe is a type of every large universe. *)
Lemma wf_univ_large_tm : forall {Θ Ξ Γ M i n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : Typeω@i.
Proof.
  intros * HΓ HM; eapply wf_exp_subtyp;
    [ eapply wf_univ, HM | apply wf_typ, HΓ | eapply wf_subtyp_small_large; [ exact HΓ | apply wf_succl, HM ] ].
Qed.

Lemma wf_univ_large : forall {Θ Ξ Γ o i},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ : Typeω@i.
Proof. intros; eapply wf_univ_large_tm; [ assumption | apply wf_llit_ord; assumption ]. Qed.

(** The base types are types of every large universe. *)
Lemma wf_nat_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_nat | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_True_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_True | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_False_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_False | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_level_large : forall {Θ Ξ Γ i n}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_level | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_level_cong_large : forall {Θ Ξ Γ i n}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ≈ Level@n : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_level_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_nat_cong_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ℕ ≈ ℕ : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_nat_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_True_cong_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_True_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_False_cong_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_False_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_univ_cong_large_tm : forall {Θ Ξ Γ M M' i n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ≈ Type⟨M'⟩ : Typeω@i.
Proof.
  intros * HΓ HMt HM; eapply wf_exp_eq_subtyp;
    [ eapply wf_exp_eq_univ_cong, HM | apply wf_typ, HΓ
    | eapply wf_subtyp_small_large; [ exact HΓ | apply wf_succl, HMt ] ].
Qed.

Lemma wf_exp_eq_univ_cong_large : forall {Θ Ξ Γ o i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ≈ Type⟨𝕃ᵒ o⟩ : Typeω@i.
Proof. intros; eapply wf_exp_eq_univ_cong_large_tm; [ assumption | apply wf_llit_ord; assumption | apply wf_exp_eq_llit_cong; assumption ]. Qed.

(** ** Literal Levels

    The literal form of the universe rules, which the closed types and the
    stage-1 statements are written with: [succl 𝕃@n] is [𝕃@(S n)] and the
    order on literals is the order on their indices, so the general rules give
    them back. *)
(** ** The Universe Congruence, Right-Hand Side

    [Type⟨M⟩ ≈ Type⟨M'⟩] is stated at [Type⟨succl M⟩], so presupposition
    for the right-hand side has to move [Type⟨M'⟩] from [Type⟨succl M'⟩]
    there.  That is a subtyping, by the level equation [maxl M' M ≈ M], which
    needs reflexivity at [M] only — and [M ≈ M] is [M ≈ M'] composed with its
    symmetry, so no induction over typing is needed here. *)
Lemma wf_exp_eq_maxl_right : forall {Θ Ξ Γ M M' n},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl M' M ≈ M : Level@n.
Proof.
  intros * HM H.
  assert (HMM : Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M : Level@n)
    by (eapply wf_exp_eq_trans; [ exact H | apply wf_exp_eq_sym, H ]).
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_sym, H | exact HMM ]
    | apply wf_exp_eq_maxl_idem, HM ].
Qed.

Lemma wf_subtyp_suniv_succl_eq : forall {Θ Ξ Γ M M' n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M'⟩ ⊆ Type⟨succl M⟩.
Proof.
  intros * HΓ HM HM' H; eapply wf_subtyp_suniv;
    [ exact HΓ | apply wf_succl, HM' | apply wf_succl, HM |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_sym, wf_exp_eq_succl_maxl; [ exact HM' | exact HM ]
    | apply wf_exp_eq_succl_cong, wf_exp_eq_maxl_right; [ exact HM | exact H ] ].
Qed.

Lemma wf_univ_cong_right : forall {Θ Ξ Γ M M' n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M'⟩ : Type⟨succl M⟩.
Proof.
  intros * HΓ HM HM' H.
  assert (HT : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M⟩ : Typeω@0)
    by (eapply wf_univ_large_tm; [ exact HΓ | apply wf_succl, HM ]).
  eapply wf_exp_subtyp;
    [ eapply wf_univ, HM' | exact HT
    | eapply wf_subtyp_suniv_succl_eq; [ exact HΓ | exact HM | exact HM' | exact H ] ].
Qed.

(** Below a literal, below its successor. *)
Lemma wf_exp_eq_maxl_succl_right : forall {Θ Ξ Γ} o o' n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (𝕃ᵒ o') ≈ 𝕃ᵒ o' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (succl (𝕃ᵒ o')) ≈ succl (𝕃ᵒ o') : Level@n.
Proof.
  intros * HΓ H.
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@n) by (apply wf_llit, HΓ).
  assert (HN : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o' : Level@n) by (apply wf_llit, HΓ).
  assert (HSN : Θ ⍮ Ξ ⍮ Γ ⊢ succl (𝕃ᵒ o') : Level@n) by (apply wf_succl, HN).
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ apply wf_exp_eq_llit_cong, HΓ
      | apply wf_exp_eq_sym, wf_exp_eq_maxl_succl, HN ] |].
  eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; [ exact HM | exact HN | exact HSN ] |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ exact H | apply wf_exp_eq_succl_cong, wf_exp_eq_llit_cong, HΓ ] |].
  apply wf_exp_eq_maxl_succl, HN.
Qed.

(** Two literals of one tier, [ω·a + b] below [ω·a + (b + d)]. *)
Lemma wf_exp_eq_maxl_llit_tier : forall {Θ Ξ Γ} a b d n,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a, d + b)) ≈ 𝕃ᵒ(a, d + b) : Level@n.
Proof.
  intros Θ Ξ Γ a b d n HΓ; induction d as [| d IH]; cbn.
  - apply wf_exp_eq_maxl_idem, wf_llit, HΓ.
  - eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_llit_cong, HΓ | apply wf_exp_eq_llit_succl, HΓ ] |].
    eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_succl_right; [ exact HΓ | exact IH ] |].
    apply wf_exp_eq_sym, wf_exp_eq_llit_succl, HΓ.
Qed.

(** A literal of a lower tier is below every literal of a higher one. *)
Lemma wf_exp_eq_maxl_llit_lower : forall {Θ Ξ Γ} a b a' d n,
    a < a' ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a', d)) ≈ 𝕃ᵒ(a', d) : Level@n.
Proof.
  intros Θ Ξ Γ a b a' d n Ha HΓ; induction d as [| d IH].
  - apply wf_exp_eq_maxl_llit_limit; [ exact Ha | exact HΓ ].
  - eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_llit_cong, HΓ | apply wf_exp_eq_llit_succl, HΓ ] |].
    eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_succl_right; [ exact HΓ | exact IH ] |].
    apply wf_exp_eq_sym, wf_exp_eq_llit_succl, HΓ.
Qed.

Lemma wf_exp_eq_maxl_llit_ole : forall {Θ Ξ Γ} o o' n,
    ole o o' ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (𝕃ᵒ o') ≈ 𝕃ᵒ o' : Level@n.
Proof.
  intros Θ Ξ Γ [a b] [a' b'] n Hle HΓ; unfold ole in Hle; cbn in Hle.
  destruct Hle as [Ha | [<- Hb]].
  - apply wf_exp_eq_maxl_llit_lower; [ exact Ha | exact HΓ ].
  - replace b' with ((b' - b) + b) by lia; apply wf_exp_eq_maxl_llit_tier, HΓ.
Qed.

Lemma wf_exp_eq_maxl_llit_le : forall {Θ Ξ Γ} n m,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    n <= m ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl 𝕃@n 𝕃@m ≈ 𝕃@m : Level.
Proof. intros; apply wf_exp_eq_maxl_llit_ole; [ apply ole_fin; assumption | assumption ]. Qed.

Lemma wf_subtyp_small_large_lit : forall {Θ Ξ Γ o i},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ⊆ Typeω@i.
Proof. intros; eapply wf_subtyp_small_large; [ assumption | apply wf_llit_ord; assumption ]. Qed.

Lemma wf_subtyp_suniv_ole : forall {Θ Ξ Γ o o'},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ole o o' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ⊆ Type⟨𝕃ᵒ o'⟩.
Proof.
  intros * HΓ Hle; eapply (wf_subtyp_suniv _ _ _ 0);
    [ assumption | apply wf_llit; assumption | apply wf_llit; assumption
    | apply wf_exp_eq_maxl_llit_ole; assumption ].
Qed.

Lemma wf_subtyp_suniv_le : forall {Θ Ξ Γ n m},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    n <= m ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@n ⊆ Type@m.
Proof. intros; apply wf_subtyp_suniv_ole; [ assumption | apply ole_fin; assumption ]. Qed.

Lemma wf_subtyp_suniv_succl : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl 𝕃ᵒ(a, b)⟩ ⊆ Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros; eapply (wf_subtyp_suniv _ _ _ 0);
    [ assumption | apply wf_succl, wf_llit; assumption | apply wf_llit; assumption |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ apply wf_exp_eq_sym, wf_exp_eq_llit_succl; assumption
      | apply wf_exp_eq_llit_cong; assumption ]
    | apply wf_exp_eq_maxl_idem, wf_llit; assumption ].
Qed.

Lemma wf_univ_lit : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros * HΓ.
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨succl 𝕃ᵒ(a, b)⟩) by (eapply (wf_univ _ _ _ 0), wf_llit, HΓ).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, S b)⟩ : Typeω@0) by (apply wf_univ_large; exact HΓ).
  eapply wf_exp_subtyp; [ exact H1 | exact H2 | apply wf_subtyp_suniv_succl, HΓ ].
Qed.

Lemma wf_exp_eq_univ_cong_lit : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ ≈ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros * HΓ.
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ ≈ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨succl 𝕃ᵒ(a, b)⟩)
    by (eapply (wf_exp_eq_univ_cong _ _ _ 0), wf_exp_eq_llit_cong, HΓ).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, S b)⟩ : Typeω@0) by (apply wf_univ_large; exact HΓ).
  eapply wf_exp_eq_subtyp; [ exact H1 | exact H2 | apply wf_subtyp_suniv_succl, HΓ ].
Qed.

#[export]
Hint Resolve wf_univ_lit wf_exp_eq_univ_cong_lit : mctt.

(** The universe at an index [u], as a term of the large universe just above
    it: [Typeω@j] is in [Typeω@(S j)], and every small universe is in
    [Typeω@0]. *)
Lemma wf_ulvl_tm : forall {Θ Ξ Γ} {u : uidx},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ulvl_tm u : Typeω@(ulvl_above u).
Proof. intros ? ? ? []; [ apply wf_univ_large | apply wf_typ ]. Qed.

Lemma wf_exp_eq_ulvl_tm_cong : forall {Θ Ξ Γ} {u : uidx},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ulvl_tm u ≈ ulvl_tm u : Typeω@(ulvl_above u).
Proof. intros ? ? ? []; [ apply wf_exp_eq_univ_cong_large | apply wf_exp_eq_typ_cong ]. Qed.

(** A universe is closed, so no substitution reaches it. *)
Lemma exp_sub_ulvl_tm : forall u σ, (ulvl_tm u)[σ] = ulvl_tm u.
Proof. intros [] ?; reflexivity. Qed.


(** As hints, these fix a large universe the goal leaves open to [Typeω@0]
    (a small one to [Type@0]), so that a search never ends with an
    uninstantiated level. *)
Ltac fix_open_level i := first [ is_evar i; first [ unify i 0 | unify i oz ] | idtac ].

(** [wf_subtyp_small_large] constrains nothing about the small level, so as a
    constructor hint it would leave it open whenever the left-hand side is;
    it applies only to a known small universe. *)
#[export]
Remove Hints wf_subtyp_small_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ ⊆ Typeω@?i) => fix_open_level i; eapply wf_subtyp_small_large : mctt.
(** The literal form of the two hints above keeps the depth of a search that
    only meets small universes at literal levels. *)
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ ⊆ Typeω@?i) => fix_open_level i; apply wf_subtyp_small_large_lit : mctt.

#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ : Typeω@?i) => fix_open_level i; eapply wf_univ_large_tm : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ : Typeω@?i) => fix_open_level i; apply wf_univ_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ℕ : Typeω@?i) => fix_open_level i; apply wf_nat_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level@_ : Typeω@?i) => fix_open_level i; apply wf_level_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level@_ ≈ Level@_ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_level_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ : Typeω@?i) => fix_open_level i; apply wf_True_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ : Typeω@?i) => fix_open_level i; apply wf_False_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ℕ ≈ ℕ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_nat_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ ≈ ⊤ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_True_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ ≈ ⊥ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_False_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ ≈ Type⟨_⟩ : Typeω@?i) => fix_open_level i; eapply wf_exp_eq_univ_cong_large_tm : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ ≈ Type⟨𝕃ᵒ _⟩ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_univ_cong_large : mctt.

Lemma presup_subtyp_right : forall {Θ Ξ Γ A B}, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i.
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
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i) as [] by mauto.
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
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i) as [] by mauto.
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
