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

    Every judgment reads the two global components [a_glob] resolves into: the
    dependency levels [Θ] and the definition stack [Ξ], as in
    [Θ ⍮ Ξ ⍮ Γ ⊢ M : A].  They are indices, not parameters: no rule about terms
    changes them, but a filed unit is checked against the levels below it and a
    stack frame against the frames outside it, so [⊢g Θ ⍮ Ξ] is an induction
    that varies them, as [⊢ Γ] varies [Γ]. *)

From Stdlib Require Import List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution GlobalCtx Members.
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
    order, the same privacy, transparent definitions with a body, and the same
    names [use]d by each import.  An [eval] has no counterpart, so a body with
    one is rejected. *)
Definition entry_shape (E E' : gentry) : Prop :=
  match E, E' with
  | ge_def b pv _ (Some _), ge_def b' pv' _ (Some _) => b = true /\ b' = true /\ pv = pv'
  | ge_mod _, ge_mod _ => True
  | _, _ => False
  end.

Definition check_shape (c c' : bcheck) : Prop :=
  match c, c' with
  | bc_import _ ns, bc_import _ ns' => ns = ns'
  | _, _ => False
  end.

Fixpoint body_shape (Φ Φ' : gmod) : Prop :=
  match Φ, Φ' with
  | gm_nil, gm_nil => True
  | gm_ext Φ x E, gm_ext Φ' x' E' => body_shape Φ Φ' /\ x = x' /\ entry_shape E E'
  | gm_check Φ c, gm_check Φ' c' => body_shape Φ Φ' /\ check_shape c c'
  | _, _ => False
  end.

(** A name an import [use]s is a public definition or a submodule. *)
Definition member_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (n : String.string) : Prop :=
  (exists A, member_type Θ Ξ Γ H (n :: nil) mk_term A) \/
  (exists A, member_type Θ Ξ Γ H (n :: nil) mk_mod A).

(** ** The Mutually Defined Judgments

    Four about terms, three about units, extensions and module expressions,
    and seven about the global context.  All fourteen are one
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
| wf_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
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
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A : A[Id,,M] )
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
| wf_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : C[Id,,M] )
(** A local module occupies one index, a slot holding its unit.  The body's
    type is premised to be a type, as the canonical type of [wf_mem] is:
    equivalent substitutions are moved through the body by [ζ], and the two
    sides then meet at that type. *)
| wf_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : C[Id ,,ₘ me_lit U] )
(** A member of a module expression with no argument, at its canonical type.
    The canonical type is a type, and the member's δ-reduct inhabits it. *)
| wf_mem :
  `( me_noargs H ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Ξ Γ H (x :: nil) mk_term A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     member_unfold Θ Ξ Γ H x = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
(** A member of an applied module is the member of its root, applied to the
    arguments: arguments and selections commute. *)
| wf_mem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
| wf_vlookup :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x : A )
(** A global is used at the type resolution hands back, which is closed: it is
    generalized over the parameters of every module enclosing the member, and
    applying it to them is the user's business.  Nothing else is premised; that
    it is a type is a presupposition. *)
| wf_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p : A )
| wf_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     (** This premise is needed for soundness.  It is asymmetric: only [A'] is
         checked.  Checking [A] as well would make even
         [Γ ⊢ Type@0[↑]ʷ : Type@1] underivable, since weakening it would require
         [Γ ⊢ Type@1[↑]ʷ : Type@2], which requires [Γ ⊢ Type@2[↑]ʷ : Type@3], and
         so on. *)
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
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M] )
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
| wf_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M] )
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
     member_type Θ Ξ Γ H (x :: nil) mk_term A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem H' x : A )
| wf_exp_eq_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ #x : A )
| wf_exp_eq_glob :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p ≈ a_glob p : A )
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
(** [ζ]: a local definition is substituted into its body. *)
| wf_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M] )
(** [ζ] for local modules: the slot is replaced by the unit. *)
| wf_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] )
(** [δ] for members: a member is its δ-reduct. *)
| wf_exp_eq_mem_delta :
  `( me_noargs H ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     member_type Θ Ξ Γ H (x :: nil) mk_term A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     member_unfold Θ Ξ Γ H x = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ M : A )
(** Arguments commute with selection. *)
| wf_exp_eq_mem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     modexp_spine H = (R, args, pre) ->
     args <> nil ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ apps (member_ref R (pre ++ x :: nil)) args : A )
(** [δ] for local definitions: a defined variable is its body.  It is stated
    at every depth, since weakening moves a definition arbitrarily deep. *)
| wf_exp_eq_var_delta :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ M : A )
(** [δ]: a transparent definition unfolds.  An [abstract] one ([b = false]) and
    an axiom ([B = None]) do not.  Both are stored closed. *)
| wf_exp_eq_glob_unfold :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_glob p ≈ M : A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B )
| wf_exp_eq_true_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊤ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ ⋆ : ⊤ )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
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
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' )
| wf_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Type@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' )
| wf_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" := (wf_ext_eq Θ Ξ Γ Ψ Ψ') : type_scope

(** Units.  A body unit's parameters and body are compared as one extension of
    [Γ].  Its imports are checked where they stand: the target is a module,
    and every name it [use]s is a public definition or a submodule. *)
with wf_unit_eq : gdeps -> gstack -> ctx -> gunit -> gunit -> Prop :=
| wf_unit_eq_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φ ++ Δ ≈ body_ctx Φ' ++ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     List.NoDup (gm_names Φ) ->
     (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks Φ) ->
        Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ᵐ E ≈ E) ->
     (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks Φ) -> List.In n ns ->
        member_ok Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) E n) ->
     (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks Φ') ->
        Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ' ++ Γ ⊢ᵐ E ≈ E) ->
     (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks Φ') -> List.In n ns ->
        member_ok Θ Ξ (body_ctx Φ0 ++ Δ' ++ Γ) E n) ->
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

(** Module expressions.  A path must name a module, and an argument is checked
    against the arity type, which must be a [Π]: a module is applied to at
    most as many arguments as it has parameters. *)
with wf_modexp_eq : gdeps -> gstack -> ctx -> modexp -> modexp -> Prop :=
| wf_me_path :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     member_type Θ Ξ Γ (me_path p) nil mk_mod A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_path p ≈ me_path p )
| wf_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ⇒ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x )
| wf_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U' )
| wf_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Ξ Γ H (y :: nil) mk_mod A ->
     member_type Θ Ξ Γ H' (y :: nil) mk_mod A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H' y )
| wf_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     member_type Θ Ξ Γ H nil mk_mod A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ Π B C : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ B ⊢ C : Type@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B ->
     member_type Θ Ξ Γ H' nil mk_mod A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ Π B' C' : Type@j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Type@j ->
     Θ ⍮ Ξ ⍮ Γ ▹ B' ⊢ C' : Type@j ->
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
    the term judgments, and a use of [a_glob] appeals to [⊢g Θ ⍮ Ξ].

    A level is checked against the levels below it, and a frame against the
    frames outside it, which is why both components are indices of the whole
    block.  [wf_gdep] and [wf_gdeps] mention only [Θ], and [wf_gstack] only [Θ]
    and [Ξ], so each says exactly what it is relative to.

    A member of a parameterized module is checked in the telescope of
    parameters it lives under, and stored generalized over it ([ctx_pi],
    [ctx_fn]).  [ge_mod] records only the parameters it adds to that telescope;
    a [gunit] records all of it, which is why a unit is checked at [⋅].

    Canonicity is part of well-formedness: [wf_gmod_ext] asks for freshness, so a
    well-formed context resolves deterministically without a separate condition,
    and the [gm_canon]/[gs_canon]/[gds_mods_canon] predicates follow
    ([wf_gmod_canon], [wf_gstack_canon], [wf_gdeps_canon] in [Lemmas]). *)

(** An entry is checked against the current module, which is the head of [Ξ]:
    that frame is what [wf_gmod_ext] pushed, and it carries the parameters and the
    members declared so far.  The local context is the telescope of all the
    frames' parameters, [gs_tele Ξ]: parameters are ordinary λ-variables.  A
    definition is stored generalized over that telescope, so what is filed is
    closed, and nothing has to be done to it when it is read anywhere else.  [mp]
    is the entry's own module path, which a nested module's frame is named by. *)

with wf_gentry : gdeps -> gstack -> path -> gentry -> Prop :=
(** An axiom: only its type is checked, there being no body to carry it. *)
| wf_gentry_axiom :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Type@i ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_def b pv (ctx_pi (gs_tele Ξ) A) None )
(** A definition: its body carries the type recorded for it, so the type needs no
    premise of its own — that is presupposition. *)
| wf_gentry_def :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)) )
(** An internal module, under the parameters [Δ'] it declares. *)
| wf_gentry_mod :
  `( Θ ⍮ Ξ ⍮ mp ⍮ Δ' ⊢m Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_body Δ' Φ )
(** An alias, under the parameters [Δ] it declares.  It is filed with its
    full telescope, so that it is closed; its target is checked, and its
    arguments with it, where it is declared. *)
| wf_gentry_alias :
  `( tele_ass Δ ->
     Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ mp ⊢e ge_mod (gu_mk (Δ ++ gs_tele Ξ) (md_alias E)) )
where "Θ ⍮ Ξ ⍮ mp ⊢e E" := (wf_gentry Θ Ξ mp E) : type_scope

(** The module at path [mp], with own parameters [Δ], a telescope over the
    frames' parameters [gs_tele Ξ]. *)
with wf_gmod : gdeps -> gstack -> path -> ctx -> gmod -> Prop :=
| wf_gmod_nil :
  `( tele_ass Δ ->
     ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m ⋄ )
(** The entry is checked against the members declared before it: the module so
    far is [gu_mk Δ Φ], pushed as the innermost frame under its own path. *)
| wf_gmod_ext :
  `( Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ->
     Θ ⍮ (mp, gu_body Δ Φ) :: Ξ ⍮ path_in mp x ⊢e E ->
     gm_fresh x Φ ->
     Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ⊳ x ↦ E )
where "Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ" := (wf_gmod Θ Ξ mp Δ Φ) : type_scope

with wf_gunit : gdeps -> gstack -> path -> gunit -> Prop :=
| wf_gunit_intro :
  `( Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢u gu_body Δ Φ )
where "Θ ⍮ Ξ ⍮ mp ⊢u U" := (wf_gunit Θ Ξ mp U) : type_scope

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
     Θ ⍮ nil ⍮ p_abs fp nil ⊢u U ->
     gds_fresh fp Θ ->
     gd_fresh fp d ->
     wf_gdep Θ ((fp, U) :: d) )

(** The levels, accumulated one at a time, each checked against those already
    piled up — so the newest level is at the front, as the newest frame is in a
    [gstack].  A unit can therefore only mention units at strictly lower levels,
    so cycle freedom comes from the shape of this judgment, not from a
    proposition about the levels. *)

with wf_gdeps : gdeps -> Prop :=
| wf_gdeps_nil : wf_gdeps nil
| wf_gdeps_cons :
  `( wf_gdeps Θ ->
     wf_gdep Θ d ->
     wf_gdeps (d :: Θ) )

(** The definition stack, innermost frame first, relative to the levels.  Read
    exactly like [wf_gdep_cons], and for the same reason: a frame is checked
    against the frames outside it, so it cannot see itself, and a [qu_rel] index
    occurring inside it counts outward from there. *)

with wf_gstack : gdeps -> gstack -> Prop :=
| wf_gstack_nil :
  `( wf_gdeps Θ ->
     wf_gstack Θ nil )
| wf_gstack_cons :
  `( wf_gstack Θ Ξ ->
     Θ ⍮ Ξ ⍮ mp ⊢u U ->
     frame_fresh Θ Ξ mp ->
     wf_gstack Θ ((mp, U) :: Ξ) )

with wf_gctx : gdeps -> gstack -> Prop :=
| wf_gctx_intro :
  `( wf_gstack Θ Ξ ->
     ⊢g Θ ⍮ Ξ )
where "⊢g Θ ⍮ Ξ" := (wf_gctx Θ Ξ) : type_scope.

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
  wf_ext_eq_mut_ind_all,
  wf_unit_eq_mut_ind_all,
  wf_modexp_eq_mut_ind_all,
  wf_gentry_mut_ind_all,
  wf_gmod_mut_ind_all,
  wf_gunit_mut_ind_all,
  wf_gdep_mut_ind_all,
  wf_gdeps_mut_ind_all,
  wf_gstack_mut_ind_all,
  wf_gctx_mut_ind_all.

(** Projections of the global judgments.  Two further ones are
    presuppositions, in [Presup]: [⊢ Θ ⍮ Ξ ⍮ gu_params U] of [⊢m], hence of
    [⊢u], and [wf_gdeps Θ] of [wf_gstack]. *)

Lemma wf_gunit_mod : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> Θ ⍮ Ξ ⍮ mp ⍮ gu_params U ⊢m gu_mod U.
Proof. inversion 1; subst; assumption. Qed.

Lemma wf_gunit_body : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> exists Δ Φ, U = gu_body Δ Φ.
Proof. inversion 1; subst; eauto. Qed.

Lemma wf_gctx_stack : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> wf_gstack Θ Ξ.
Proof. now inversion 1. Qed.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp ctx_lookup ctx_lookup_def : mctt.

#[export]
Hint Constructors wf_ext_eq wf_unit_eq wf_modexp_eq : mctt.

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
