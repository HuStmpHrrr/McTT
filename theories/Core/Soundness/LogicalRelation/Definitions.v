From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
From Mctt.Core.Semantic.Inductives Require Export IndPER.
From Mctt.Core.Semantic Require Export RecordPER.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic.System.Inductives Require Export IndCong.
From Mctt.Core.Syntactic.Levels Require Import Levels LevelEq.
From Mctt.Core.Syntactic.System.Global Require Import Presup Paths.
From Mctt.Core.Syntactic Require Export ProofAnnotation.
From Mctt.Core.Soundness.Weakening Require Export Definitions.
(** [nparams_prefix] and [nonrec_args_prefix], which [glu_ind_decl] reads
    as [valid_ind_decl] does. *)
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions.

Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Global Open Scope predicate_scope.

(** The rewrite database of [simp glu_univ_elem]. *)
Create Rewrite HintDb glu_univ_elem.

Generalizable All Variables.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
(** This type annotation distinguishes this notation from others. *)
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (at level 70, A at level 69, R constr).

Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons typ (Tcons exp (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (at level 70, M at level 69, m at level 69, R constr).

Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢ˢ σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (at level 70, σ at level 69, ρ at level 69, R constr).

Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (at level 70, a at level 69, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (at level 70, A at level 69, R constr, Sb constr).

(** The gluing predicates take the ambient universe as a *term* [U].  It is
    the large universe of the tier, [Typeω@(large_level i)]: [Typeω@i] in the large
    tier, and [Typeω@0] at every small index.  A small universe's index is the
    realiser of its level, an ordinal below ω², while the universe a small type
    is in is [Type⟨t⟩] for a level *term* [t]; no term is determined by the
    index, so the only ambient that every small type at that index shares is
    the large universe they are all below ([wf_subtyp_small_large]).

    Smallness is recorded where the level term is known: in the element
    predicate of a small universe ([suniv_glu_exp_pred']), which says that the
    element's type is [Type⟨t⟩] for a [t] glued to the level value, and that
    the element is equal to its readback at that type.  The latter is what the
    soundness theorem, and the algorithmic layer through it, needs of a small
    type's normal form; it cannot be recovered from the equation at [Typeω@0],
    since no rule moves an equation down a universe.

    A type is stated at the sort of its kind next to the ambient universe
    ([abs_kind_sort]): a proposition at [Prop], a type of levels at
    [LevelSort], which no universe contains. *)

(** ** Exact Readback Equations

    A term is glued to a value by the equation of the term with the
    value's own readback: soundness is exact, the term is equal to its
    normal form.  The readback of a proof is the proof term kept with its
    environment ([read_proof_kept]), so the equation types it.  The
    gluing is therefore NOT closed under the PERs, which relate a kept
    proof to any proof: for example, with [f : P → A] and [h : P], the
    real value of [f h] and the value of [f] at a proof [⋆ᵈ⟨𝕃@0, nil⟩]
    are related by [per_bot], but the second reads back as the untyped
    [f 𝕃@0], so only the first is glued to [f h].  A gluing moves to a
    related value only along that value's own readback.

    The equation is with the annotation of the readback
    ([nf_annotate_proofs]), which ascribes each proof its proposition:
    so a glued readback has every proof typed at its proposition, and two
    glued readbacks equal up to proofs are equal
    ([nf_annotate_proofs_upto]).  The plain readback is equal to its
    annotation when the annotation is typed. *)
Definition glu_nf_eq (Γ : ctx) (M : exp) (W : nf) (A : typ) : Prop := Γ ⊢ M ≈ nf_annotate_proofs W : A.

(** The same for neutrals. *)
Definition glu_ne_eq (Γ : ctx) (M : exp) (W : ne) (A : typ) : Prop := Γ ⊢ M ≈ ne_annotate_proofs W : A.

(** The same for a list of terms at a closed telescope ([exps_eq_at]). *)
Definition glu_nfs_eq_at (Γ : ctx) (T : ctx) (Ms : list exp) (Ws : list nf) : Prop :=
  exps_eq_at Γ T Ms (List.map nf_to_exp (List.map nf_annotate_proofs Ws)).

(** ** Levels *)

(** A type of levels is at the sort [LevelSort], whatever the ambient
    universe. *)
Definition level_glu_typ_pred (n : nat) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ Level@n : LevelSort.
#[global] Arguments level_glu_typ_pred n Γ A/.

(** A level is glued to a value by its readback, as a neutral is: evaluation of
    the level operations only flattens, so a level's syntax is tied to its
    value only through the canonical form readback computes.

    It is a definition with a [forall] head, not a one-constructor inductive:
    the shared scripts of the gluing lemmas [split] every goal they can, and
    they would then take such an inductive apart and lose the shape the lemmas
    about it are keyed on.  Membership in [per_lvl] is a separate field of
    [level_glu_exp_pred] for the same reason. *)
(** The readback of a level of sort [n] is a canonical level of sort [n]:
    its constant is of a tier at most [n], and each atom is a level of its
    own sort ([level_atoms_well_scoped]).  The atoms' sorts are read off the types of the
    neutrals, and this is what makes them reliable: the equations of a
    canonical form drop an atom by absorption, which needs it typed at its
    sort. *)
Definition nf_lvl_well_scoped (n : nat) (Δ : ctx) (L : nf) : Prop :=
  match L with
  | nf_lvl c xs => fst c <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Δ xs
  | _ => False
  end.

(** The sort is a parameter: the readback of a level value is the same at
    every sort, but the equation it satisfies is at the type the level was
    given, [Level@n]. *)
Definition glu_lvl (n : nat) (Γ : ctx) (M : exp) (m : domain) : Prop :=
  forall Δ φ L, Δ ⊢ᵏ φ : Γ -> Rnf ⇓ Levelᵈ m in length Δ ↘ L ->
    Δ ⊢ M[φ]ʷ ≈ L : Level@n /\ nf_lvl_well_scoped n Δ L.

(** An element of [Level@n]: a level glued to its value by its readback. *)
Record level_glu_exp (n : nat) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_level_glu_exp
  { (** The type is [Level@n] *)
    level_glu_exp_typ : Γ ⊢ A ≈ Level@n : LevelSort
    (** The value is a level of sort [n] *)
  ; level_glu_exp_per : Dom m ≈ m ∈ per_lvl_at n
    (** The term is its readback, a canonical level of sort [n] *)
  ; level_glu_exp_lvl : glu_lvl n Γ M m }.

Definition level_glu_exp_pred (n : nat) : glu_exp_pred := level_glu_exp n.

(** ** Propositions and Proofs

    A proposition, as a type, is glued by its readback, at [Prop]; its
    elements are the proofs of it, glued by their typing alone: any two
    proofs of it are equal ([wf_exp_eq_irrelevant]), so nothing ties a
    proof to its value but that the value is a proof that reads back
    ([per_proof]).  ⊤, ⊥, ∀, Σₚ and the neutral propositions alike, as in
    the PER model ([per_univ_elem_core_prop]); a proposition is a type of
    every index. *)
Definition prop_glu_typ_pred (a : domain) : glu_typ_pred :=
  fun Γ A => Γ ⊢ A : Propₘ /\
            (forall Δ φ W, Δ ⊢ᵏ φ : Γ -> Rtyp a in length Δ ↘ W -> glu_nf_eq Δ A[φ]ʷ W Propₘ).
#[global] Arguments prop_glu_typ_pred a Γ A/.

(** A proof of the proposition [A], glued to the proof value [m]. *)
Record proof_glu_exp (a : domain) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_proof_glu_exp
  { (** The type is glued as a proposition, at the proposition [a] *)
    proof_glu_exp_typ : Γ ⊢ A ® prop_glu_typ_pred a
    (** The term is a proof of it *)
  ; proof_glu_exp_wf : Γ ⊢ M : A
    (** The value is a proof that reads back *)
  ; proof_glu_exp_per : Dom m ≈ m ∈ per_proof
    (** At every weakening, the value's own readback, a term, is the proof *)
  ; proof_glu_exp_read : forall Δ φ R, Δ ⊢ᵏ φ : Γ -> Rprf m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ R ->
      Δ ⊢ M[φ]ʷ ≈ R : A[φ]ʷ }.

Definition proof_glu_exp_pred (a : domain) : glu_exp_pred := proof_glu_exp a.

(** [Prop], as a type, in the ambient universe [U]. *)
Definition prop_univ_glu_typ_pred (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ Propₘ : U.
#[global] Arguments prop_univ_glu_typ_pred U Γ A/.

(** An element of [Prop]: a proposition, glued as a type at its value. *)
Record prop_univ_glu_exp (U : typ) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_prop_univ_glu_exp
  { (** The type is [Prop] *)
    prop_univ_glu_exp_typ : Γ ⊢ A ≈ Propₘ : U
    (** The term is of it *)
  ; prop_univ_glu_exp_wf : Γ ⊢ M : A
    (** The value is a proposition *)
  ; prop_univ_glu_exp_per : Dom m ≈ m ∈ per_prop
    (** The term is glued as a proposition at the value *)
  ; prop_univ_glu_exp_glu : Γ ⊢ M ® prop_glu_typ_pred m }.

Definition prop_univ_glu_exp_pred (U : typ) : glu_exp_pred := prop_univ_glu_exp U.

(** ** The Sort of the Types of Levels *)

(** [LevelSort], as a type: [LevelSort] itself, in a context.  It is of
    no sort ([level_sort_untyped]), so no equation of a sort reaches it,
    and no other type is equal to it. *)
Definition level_sort_glu_typ_pred : glu_typ_pred := fun Γ A => A = LevelSort /\ ⊢ Γ.
#[global] Arguments level_sort_glu_typ_pred Γ A/.

(** An element of [LevelSort]: a type of levels, glued as a type at the
    least small index ([univ_typ]), as the PER model reads the elements of
    [LevelSort] off that index ([per_level_sort_at]). *)
Record level_sort_glu_exp (univ_typ : domain -> glu_typ_pred) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop :=
  mk_level_sort_glu_exp
  { (** The type is [LevelSort] *)
    level_sort_glu_exp_typ : A = LevelSort
    (** The term is of it *)
  ; level_sort_glu_exp_wf : Γ ⊢ M : A
    (** The value is a type of levels *)
  ; level_sort_glu_exp_code : level_code m
    (** The term is glued as a type at the value *)
  ; level_sort_glu_exp_glu : Γ ⊢ M ® univ_typ m }.

Definition level_sort_glu_exp_pred (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
  level_sort_glu_exp univ_typ.

(** ** Neutral Types

    A neutral type is of the relevant kind: a neutral proposition is glued
    as a proposition, and no variable is of [LevelSort]. *)
Definition neut_glu_typ_pred (U : typ) a : glu_typ_pred :=
  fun Γ A => Γ ⊢ A : U /\
            (forall Δ φ A', Δ ⊢ᵏ φ : Γ -> Rne a in length Δ ↘ A' -> glu_ne_eq Δ A[φ]ʷ A' U).
#[global] Arguments neut_glu_typ_pred U a Γ A/.

Variant neut_glu_exp_pred (U : typ) a : glu_exp_pred :=
(** A neutral, glued by its readback, at a neutral type *)
| mk_neut_glu_exp_pred :
  `{ Γ ⊢ A ® neut_glu_typ_pred U a ->
     Γ ⊢ M : A ->
     Dom m ≈ m ∈ per_bot ->
     (forall Δ φ M', Δ ⊢ᵏ φ : Γ ->
                   Rne m in length Δ ↘ M' ->
                   glu_ne_eq Δ M[φ]ʷ M' A[φ]ʷ) ->
     Γ ⊢ M : A ® ⇑ b m ∈ neut_glu_exp_pred U a }.

(** ** [Π]

    A [Π] out of a domain of the kind [κd] into a codomain of the kind
    [κc], each at the sort of its kind next to the ambient universe [U]
    ([wf_pi]); [κc] is evaluated, as a [Π] into propositions is a
    proposition. *)
Variant pi_glu_typ_pred (κd κc : abs_kind) (U : typ)
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (OP : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_typ_pred) : glu_typ_pred :=
(** The type is a [Π] whose domain glues at [IP], and whose codomain, at
    every glued argument, glues at [OP] *)
| mk_pi_glu_typ_pred :
  `{ Γ ⊢ A ≈ a_pi κd κc IT OT : abs_kind_sort κc U ->
     Γ ⊢ IT : abs_kind_sort κd U ->
     Γ ▹{κd} IT ⊢ OT : abs_kind_sort κc U ->
     (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ M m,
         Δ ⊢ᵏ φ : Γ ->
         Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl ->
         forall (equiv_m : Dom m ≈ m ∈ IR),
           Δ ⊢ OT[(ι φ),,M] ® OP _ equiv_m) ->
     Γ ⊢ A ® pi_glu_typ_pred κd κc U IR IP IEl OP }.

Variant pi_glu_exp_pred (κd κc : abs_kind) (U : typ)
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (elem_rel : relation domain)
  (OEl : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_exp_pred): glu_exp_pred :=
(** The term is a function of the [Π]: applied to a glued argument, its
    value applied to the argument's is glued to the application *)
| mk_pi_glu_exp_pred :
  `{ Γ ⊢ M : A ->
     Dom m ≈ m ∈ elem_rel ->
     Γ ⊢ A ≈ a_pi κd κc IT OT : abs_kind_sort κc U ->
     Γ ⊢ IT : abs_kind_sort κd U ->
     Γ ▹{κd} IT ⊢ OT : abs_kind_sort κc U ->
     (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ N n,
         Δ ⊢ᵏ φ : Γ ->
         Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl ->
         forall (equiv_n : Dom n ≈ n ∈ IR),
         exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl _ equiv_n) ->
     Γ ⊢ M : A ® m ∈ pi_glu_exp_pred κd κc U IR IP IEl elem_rel OEl }.

Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.

Definition univ_glu_typ_pred j (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ Typeω@j : U.
#[global] Arguments univ_glu_typ_pred j U Γ A/.
Transparent univ_glu_typ_pred.

(** A small universe as a type: it is the universe at some level term that is
    glued to the level value, as a level is glued to its value by its
    readback.  The term is existentially quantified because the level value's
    readback changes with the length, which [glu_lvl] takes care of; two such
    terms are equal levels ([glu_lvl_escape]), so the universes they index are
    the same type. *)
#[warnings="-cannot-define-projection"]
Record suniv_glu_typ (l : domain) (U : typ) (Γ : ctx) (A : typ) : Prop := mk_suniv_glu_typ
  { suniv_glu_typ_lvl : exp
  ; suniv_glu_typ_sort : nat
  ; suniv_glu_typ_glu : glu_lvl suniv_glu_typ_sort Γ suniv_glu_typ_lvl l
  ; suniv_glu_typ_eq : Γ ⊢ A ≈ Type⟨suniv_glu_typ_lvl⟩ : U }.

Definition suniv_glu_typ_pred (l : domain) (U : typ) : glu_typ_pred := suniv_glu_typ l U.

(** ** Inductive Types

    The uniform parameters of an inductive type are glued to their values by
    their readback, at their telescope: their types may be larger than the
    inductive type, so they have no gluing at its universe.  The non-uniform
    ones are glued at the gluing predicates of their types ([NEl], indexed
    by the position and the values before it).  The parameters' equation
    is [exps_eq_at] (Syntactic/System/Inductives/IndCong.v). *)

(** The parameters [Ps] of a type whose head is the declared member [Mh]
    of the group [Dh], glued to their values by their readback at the
    member's telescope.  The head of a view's type is the container's
    member: a view has no type former of its own. *)
Record glu_params_top (Dh : ind_decl) (Mh : imember) (Γ : ctx) (Ps : list exp) (as' : list domain) : Prop :=
  mk_glu_params_top
  { (** As many parameters as the member has *)
    glu_params_top_len : List.length Ps = im_np Dh Mh
    (** Each typed at the member's telescope *)
  ; glu_params_top_typ : forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params Dh Mh) Id Ps) k = Some A ->
      Γ ⊢ P : A
    (** At every weakening, equal to the annotated readback of the
        values *)
  ; glu_params_top_read : forall Δ φ Ms, Δ ⊢ᵏ φ : Γ -> Rps as' at List.rev (im_params Dh Mh) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms ->
      glu_nfs_eq_at Δ (im_params Dh Mh) (List.map (fun P => P[φ]ʷ) Ps) Ms }.

(** The non-uniform parameters [Ns] of the member [Mk] (the member [k] of
    the group) at the group's uniform parameters [Us], glued to the values
    [ns] at the gluings [NEl k] of their types. *)
Record glu_nparams (k : nat) (Mk : imember) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (Γ : ctx) (Us Ns : list exp) (ns : list domain) : Prop := mk_glu_nparams
  { (** One term per non-uniform parameter *)
    glu_nparams_len : List.length Ns = im_nn Mk
    (** One value per non-uniform parameter *)
  ; glu_nparams_vals_len : List.length ns = im_nn Mk
    (** Each term glued to its value at its type *)
  ; glu_nparams_glu : forall j N A n, List.nth_error Ns j = Some N ->
      List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Us) Ns) j = Some A ->
      List.nth_error ns j = Some n -> Γ ⊢ N : A ® n ∈ NEl k j (List.firstn j ns) }.

(** The type [T] of a recursive argument of shape [t], after the values
    [pre] of the shape's components, glued at the gluings [DP] of the
    shape's domains: at every weakening, its domain is glued at [DP], and
    at an element of the domain glued at [DEl] and related to itself by
    [DR], the rest of the type is the one of the rest of the shape.  The
    domains are indexed, as the PER model's ([canon_doms_rel]), by the
    values [pre] and the telescope [Ts] of the components before them,
    which grows by each domain, relevant.  At the end of the shape, the
    member [j] at the parameters [Ps], the type satisfies [SE] at the
    values and the telescope reached there, at the type's own uniform
    parameters [Us] (weakened along the domains): the type alone does not
    fix them, as the former of a view or a record view sees only its
    instance [Is[Us]] (a view at [Is := [A]] of a group over [A B] has the
    type [C A] at [Us = [A; B]] and at [Us = [A; ℕ]]). *)
Fixpoint glu_shape_typ (DR : list domain -> list centry -> exp -> relation domain)
    (DP : list domain -> list centry -> exp -> glu_typ_pred)
    (DEl : list domain -> list centry -> exp -> glu_exp_pred)
    (SE : ctx -> list exp -> list domain -> list centry -> nat -> list exp -> typ -> Prop)
    (Γ : ctx) (Us : list exp) (pre : list domain) (Ts : list centry) (t : ptyp) (T : typ) {struct t} : Prop :=
  match t with
  | pt_pi B t' => forall IT OT, T = a_pi ak_relevant ak_relevant IT OT ->
      (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP pre Ts B) /\
      (forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> DR pre Ts B c c -> Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre Ts B ->
         glu_shape_typ DR DP DEl SE Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t'
           OT[(ι φ),,b])
  | pt_self j Ps => SE Γ Us pre Ts j Ps T
  end.

(** The end of the shape of a recursive argument, the member [j] at the
    shape's parameters [Ps]: the syntactic parameters [Us ++ Q] of the
    type are glued to the values [bsr] the shape's parameters evaluate to
    after the components [pre] of the telescope [Ts] ([components_env]),
    which are related to themselves, the non-uniform ones at their types
    and all of them by their
    readback, at every weakening.  These values are the type's own, read
    off the glued components before the argument, so the readback of an
    element at them is the readback at the argument's type. *)
Record glu_self_params_at (D : ind_decl) (ups : list domain) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (Γ : ctx) (j : nat) (Mj : imember) (Us Q : list exp) (bsr : list domain) : Prop := mk_glu_self_params_at
  { (** The values are related to themselves *)
    glu_self_params_rel : tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bsr bsr
    (** The non-uniform parameters are glued to them at their types *)
  ; glu_self_params_nparams : glu_nparams j Mj NEl Γ Us Q bsr
    (** All the parameters are glued to them by their readback, at every
        weakening *)
  ; glu_self_params_top : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
      glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (ups ++ bsr) }.

(** At the type's own uniform parameters [Us] ([glu_shape_typ]), the
    non-uniform ones [Q] are fixed by the type. *)
Definition glu_self_params (p : qname) (D : ind_decl) (ups : list domain) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) (pre : list domain) (Ts : list centry) (j : nat) (Ps : list exp) (T : typ) : Prop :=
  forall Mj Q bsr, ind_member D j = Some Mj -> T = im_ty_at p j Mj Us Q ->
    ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr ->
    glu_self_params_at D ups NEl Γ j Mj Us Q bsr.

(** The types of the telescopes of the members of a group at its uniform
    parameters [Us], glued at the gluings of the clause, member by member:
    a non-uniform parameter's at the non-uniform parameters before it,
    glued, and a non-recursive argument's at all the non-uniform parameters
    and the non-recursive arguments before it, glued.  They are what moves
    an element to a lower universe (the third part of cumulativity), as the
    domain and the codomains do for a [Π]. *)
Record ind_glu_components (p : qname) (D : ind_decl) (ups : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) : Prop := mk_ind_glu_components
  { (** A non-uniform parameter's type, after glued ones before it *)
    ind_glu_components_nparams : forall m Mm k Ns ns T, ind_member D m = Some Mm -> List.length ns = k -> k < im_nn Mm ->
     List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
     (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
        List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
        List.nth_error ns j = Some n -> Γ ⊢ N : T' ® n ∈ NEl m j (List.firstn j ns)) ->
     tele_prefix_rel (canon_nparams_rel D ups m) k ns ns -> Γ ⊢ T ® NP m k ns
    (** A non-recursive argument's type, after glued ones before it *)
  ; ind_glu_components_args : forall m Mm c gs gs1 r0 A0 gs2 Ns ns As vs T, ind_member D m = Some Mm ->
     ind_con Mm c = Some gs -> gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
     glu_nparams m Mm NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
       (nonrec_arg_vals gs1 vs) ->
     Γ ⊢ T ® AP m ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
    (** A recursive argument's type, along its shape *)
  ; ind_glu_components_recs : forall m Mm c gs gs1 t gs2 Ns ns As vs T, ind_member D m = Some Mm ->
     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
     glu_nparams m Mm NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 rB B hs2 N T' v, gs1 = hs1 ++ ca_arg rB B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
       (nonrec_arg_vals gs1 vs) ->
     glu_shape_typ (canon_doms_rel D ups m) (DP m) (DEl m) (glu_self_params p D ups NEl) Γ Us (ns ++ nonrec_arg_vals gs1 vs)
       (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1) t T }.

(** A type of the declared member [Mk] (the member [k]) of a group at its
    parameters, at syntactic parameters [Ps]: glued to the values by their
    readback, its sort in the universe of the gluing, and the telescopes'
    types of every member glued, at every instance of the parameters equal
    to the given ones: two types of the same member at the same values may
    have different syntactic parameters, and lowering an element of one to
    a smaller universe needs the components at the parameters of the
    other.  The non-uniform parameters are also glued to the type's own
    values [ns] at their types ([glu_nparams]): an element is read back at
    the type's values, so its arguments' types are glued there through
    them ([ind_glu_components]).  The parts at a context are
    [ind_typ_parts]. *)
Record ind_typ_parts (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (U : typ) (Δ : ctx) (Ps : list exp) : Prop := mk_ind_typ_parts
  { (** The parameters, glued to the values by their readback *)
    ind_typ_parts_top : glu_params_top D Mk Δ Ps (ups ++ ns)
    (** The sort at them is in the ambient universe *)
  ; ind_typ_parts_sort : Δ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ps] ⊆ U
    (** The telescopes' types, glued at every equal instance *)
  ; ind_typ_parts_comps : forall Ps', exps_eq_at Δ (im_params D Mk) Ps Ps' ->
      ind_glu_components p D ups NP NEl AP AEl DP DEl Δ (List.firstn (ind_nu D) Ps')
    (** The non-uniform parameters, glued to the type's values at their
        types *)
  ; ind_typ_parts_nparams : glu_nparams k Mk NEl Δ (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ns }.

Definition ind_typ_at (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (U : typ) (Γ : ctx) (A : typ) (Ps : list exp) : Prop :=
  Γ ⊢ A ≈ apps (a_ind p k) Ps : U /\
  forall Δ φ, Δ ⊢ᵏ φ : Γ ->
    ind_typ_parts p D ups ns NP NEl AP AEl DP DEl k Mk U Δ (List.map (fun P => P[φ]ʷ) Ps).

(** The type predicate of the member [k]: a type at some syntactic
    parameters ([ind_typ_at]). *)
Definition ind_glu_typ_pred (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (U : typ) : glu_typ_pred :=
  fun Γ A => exists Ps, ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A Ps.
#[global] Arguments ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A/.

Section GluInd.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred).

  (** The elements of the member [k] of the group at the syntactic uniform
      parameters [Us] of the group and the non-uniform ones [Ns] of the
      member: their type is the member's at them ([im_ty_at]: the
      container's member at the view's arguments, at a view).  A
      constructor of the member, as the group has it, at those parameters:
      the value is the one the group stores ([im_ref]: the container's
      constructor at a view), its non-uniform parameters glued to the
      values it was built at, a non-recursive argument glued at its type,
      and a recursive one an element of the member its shape ends in, at
      the group's uniform parameters and the parameters of its type; and
      neutrals, by their readback.  A view is glued at the group's
      uniform parameters [Us], not at the container's [im_pre Mk Us]: these
      do not determine [Us], and the group's telescopes are at [Us].  The
      non-uniform parameters of a recursive argument's type are glued to
      the values they evaluate to; only those: a value related to them may
      read back to an untyped normal form.  A recursive argument is an element at every
      weakening and every instance of the parameters equal to those of its
      type, like the element itself in [ind_glu_exp_pred]: weakening
      commutes with the instances of the telescopes only for a closed
      declaration, which the model does not assume, so it is built into the
      gluing instead.  A recursive argument of a function shape ([glu_rec])
      is a function: at every weakening, applied to an element glued at a
      domain of the shape ([DEl k], indexed by the values before the domain
      and the domain), it is a recursive argument of the rest of the shape;
      its domain type is glued at [DP k]. *)
  Inductive ind_glu_elem : nat -> ctx -> list exp -> list exp -> exp -> domain -> Prop :=
  (** A constructor of the member, not a record view (whose elements are
      only [ind_glu_elem_record]'s), at glued parameters and arguments *)
  | ind_glu_elem_con :
    `{ ind_member D k = Some Mk ->
       im_is_rview Mk = false ->
       im_ref p k Mk = (hd, k') ->
       ind_con Mk c = Some gs ->
       List.length Us = ind_nu D ->
       List.length Ns = im_nn Mk ->
       List.length bs = (im_unu D Mk + im_nn Mk)%nat ->
       List.length vs = List.length gs ->
       List.length As = List.length gs ->
       Γ ⊢ M ≈ apps (a_con p k c) (Us ++ Ns ++ As) : im_ty_at p k Mk Us Ns ->
       tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) bs)
         (List.skipn (im_unu D Mk) bs) ->
       tele_rel (canon_args_rel D ups k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs)
         (nonrec_arg_vals gs vs) ->
       glu_nparams k Mk NEl Γ Us Ns (List.skipn (im_unu D Mk) bs) ->
       (forall j N A, List.nth_error As j = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some A -> Γ ⊢ N : A) ->
       (forall gs1 r0 A0 gs2 N A v, gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Γ ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))) ->
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec k Γ Us (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t A N v) ->
       ind_glu_elem k Γ Us Ns M (d_con hd k' c (bs ++ vs)) }
  (** A neutral of the member, not a record view (whose neutrals are only
      [ind_glu_elem_record]'s, by their projections), equal to its
      readback at every weakening, its annotation's non-uniform parameters
      related to themselves, and glued from some syntactic parameters at
      the element's uniform ones (the typed type it was created at): the
      stuck eliminator's motive is at those *)
  | ind_glu_elem_neut :
    `{ ind_member D k = Some Mk ->
       im_is_rview Mk = false ->
       im_ref p k Mk = (hd, k') ->
       per_bot m m ->
       (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
          glu_ne_eq Δ M[φ]ʷ M' (im_ty_at p k Mk Us Ns)[φ]ʷ) ->
       tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) (List.skipn (im_unu D Mk) as')
         (List.skipn (im_unu D Mk) as') ->
       (exists NsX, glu_nparams k Mk NEl Γ Us NsX (List.skipn (im_unu D Mk) as')) ->
       ind_glu_elem k Γ Us Ns M (⇑ (d_ind hd k' as') m) }
  (** An element of a record view, a tuple and a neutral alike (η): equal
      to the record view's constructor at the group's uniform parameters
      [Us] and fields [As] glued to the value's projections [vs] as a
      constructor's arguments are, at the view's own telescope: a
      non-recursive field at its type, a recursive one by its shape.  A
      record view has no non-uniform parameters, so the fields' values
      come right after [nil].  (By [wf_exp_eq_con_rview] the constructor
      is the tuple of [As]; for a neutral [M], [As] are its
      projections.) *)
  | ind_glu_elem_record :
    `{ (** [k] is a record view of one constructor [c] of arguments [gs] *)
       ind_member D k = Some Mk ->
       im_head Mk = mh_record qr Is fl ->
       im_cons Mk = (c, gs) :: nil ->
       (** As many parameters and fields as the view takes *)
       List.length Us = ind_nu D ->
       List.length Ns = im_nn Mk ->
       List.length As = List.length gs ->
       (** The value's projections *)
       ⟦projs fl of m ⟧ gc_deps ⍮ gc_stack ↘ vs ->
       (** [M] is the constructor at the fields [As] *)
       Γ ⊢ M ≈ apps_exp (a_con p k c) (Us ++ Ns ++ As) : im_ty_at p k Mk Us Ns ->
       (** The non-recursive projections are related to themselves *)
       tele_rel (canon_args_rel D ups k nil c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs) ->
       (** Each field is typed at the view's telescope *)
       (forall j N A, List.nth_error As j = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) j = Some A -> Γ ⊢ N : A) ->
       (** A non-recursive field is glued at its type *)
       (forall gs1 r0 A0 gs2 N A v, gs = gs1 ++ ca_arg r0 A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Γ ⊢ N : A ® v ∈ AEl k nil c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))) ->
       (** A recursive field is a recursive argument of its shape *)
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec k Γ Us (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) (cargs_nonrec_tele gs1) t A N v) ->
       ind_glu_elem k Γ Us Ns M m }
  (** A recursive argument [N] of type [A] and shape [t] of a constructor
      of the member [k], at the group's uniform parameters [Us], after the
      values [pre] of the shape's components (the uniform parameters left
      out).  At the end of the shape, the member [j] it ends in at the
      values [bsr] of the shape's parameters: [A] is the member's type at
      [Us] and parameters [Q], as many as the member takes, and [bsr] is
      related to itself.  The gluing of [Q] to the values is the type's
      ([glu_self_params] in [ind_glu_components]), at every glued prefix:
      the element's own, which the eliminator reads, and the type's, which
      readback reads ([read_shape_self], [read_nf_con_view]). *)
  with glu_rec : nat -> ctx -> list exp -> list domain -> list centry -> ptyp -> typ -> exp -> domain -> Prop :=
  (** At the end: an element of the member [j], at every weakening and
      every equal instance of its type's parameters; the shape's parameters are
      evaluated in the environment of the components [pre] of the
      telescope [Ts] ([components_env]), as [rec_arg_self] has them *)
  | glu_rec_self :
    `{ ind_member D j = Some Mj ->
       (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr ->
          A = im_ty_at p j Mj Us Q ->
          List.length Q = im_nn Mj /\ tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bsr bsr) ->
       (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups Ts pre ↘ bsr ->
          A = im_ty_at p j Mj Us Q ->
          forall Δ φ Us' Q', Δ ⊢ᵏ φ : Γ -> List.length Us' = ind_nu D ->
            exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
            ind_glu_elem j Δ Us' Q' N[φ]ʷ v) ->
       glu_rec k Γ Us pre Ts (pt_self j Ps) A N v }
  (** At a domain: a function whose domain is glued, and whose
      applications to glued elements are recursive arguments of the rest,
      after the domain, relevant *)
  | glu_rec_pi :
    `{ (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP k pre Ts B) ->
       (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> canon_doms_rel D ups k pre Ts B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre Ts B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
       (forall IT OT, A = a_pi ak_relevant ak_relevant IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> canon_doms_rel D ups k pre Ts B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre Ts B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
          glu_rec k Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t
            OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
       glu_rec k Γ Us pre Ts (pt_pi B t) A N v }.
End GluInd.

Scheme ind_glu_elem_mut_ind := Induction for ind_glu_elem Sort Prop
with glu_rec_mut_ind := Induction for glu_rec Sort Prop.
Combined Scheme ind_glu_elem_mut_ind_all from ind_glu_elem_mut_ind, glu_rec_mut_ind.

(** An element of the declared member [Mk] (the member [k]) of a group:
    typed, related to itself, and an element at every weakening and at
    every instance of the parameters equal to the type's ones there, as the
    components of [ind_typ_at] are: a constructor or an eliminator whose
    syntactic parameters differ from the ones of the type the element was
    glued at reads it at its own. *)
#[warnings="-cannot-define-projection"]
Record ind_glu_exp (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (elem_rel : relation domain) (U : typ) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop :=
  mk_ind_glu_exp
  { (** [M] is of type [A] *)
    ind_glu_exp_typ : Γ ⊢ M : A
    (** [m] is related to itself *)
  ; ind_glu_exp_per : Dom m ≈ m ∈ elem_rel
    (** The syntactic parameters of [A] *)
  ; ind_glu_exp_params : list exp
    (** [A] is the member's type at them *)
  ; ind_glu_exp_at : ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A ind_glu_exp_params
    (** At every weakening and equal instance, [M] is glued to [m] *)
  ; ind_glu_exp_glu : forall Δ φ Ps', Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) ind_glu_exp_params) Ps' ->
      ind_glu_elem p D ups NEl AEl DP DEl k Δ (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps') M[φ]ʷ m }.

(** The element predicate of the member [k]: [ind_glu_exp]. *)
Definition ind_glu_exp_pred (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (elem_rel : relation domain) (U : typ) : glu_exp_pred :=
  ind_glu_exp p D ups ns NP NEl AP AEl DP DEl k Mk elem_rel U.

(** ** Record Types

    The parameters of a record type are glued to their values by their
    readback, at their telescope, as the uniform parameters of an inductive
    type are.  Its fields are glued at the gluing predicates of their types
    ([FP], [FEl], indexed by the position and the values of the fields
    before it), each after glued earlier ones. *)

(** The parameters [Ps] at the telescope [T], glued to their values [ps] by
    their readback. *)
Record params_glu_top (T : ctx) (Γ : ctx) (Ps : list exp) (ps : list domain) : Prop := mk_params_glu_top
  { (** One term per parameter *)
    params_glu_len : List.length Ps = List.length T
    (** Each typed at the telescope *)
  ; params_glu_typ : forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts T Id Ps) k = Some A ->
      Γ ⊢ P : A
    (** At every weakening, equal to the annotated readback of the
        values *)
  ; params_glu_read : forall Δ φ Ms, Δ ⊢ᵏ φ : Γ -> Rps ps at List.rev T in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms ->
      glu_nfs_eq_at Δ T (List.map (fun P => P[φ]ʷ) Ps) Ms }.

(** The types of the fields of [R] at the parameters [Ns], glued: the type
    of a field, after terms [Ms] glued to values [ms] at the types of the
    fields before it, glues at [FP] of its position and [ms]. *)
Definition record_fields_glu (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (Γ : ctx) (Ns : list exp) : Prop :=
  forall k f T Ms ms, List.nth_error (record_fields R) k = Some (f, T) -> List.length Ms = k -> List.length ms = k ->
    (forall j g T' M m, List.nth_error (record_fields R) j = Some (g, T') -> List.nth_error Ms j = Some M ->
       List.nth_error ms j = Some m ->
       Γ ⊢ M : T'[sb_of_list Id (Ns ++ List.firstn j Ms)] ® m ∈ FEl j (List.firstn j ms)) ->
    tele_prefix_rel (canon_fields_rel R ns) k ms ms ->
    Γ ⊢ T[sb_of_list Id (Ns ++ Ms)] ® FP k ms.

(** What a record type at the syntactic parameters [Ns] is at every
    weakening [φ]: the parameters glued, the sort in the ambient universe
    [U], and the fields glued at every equal instance of the parameters. *)
Record record_typ_parts (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (U : typ) (Δ : ctx) (Ns : list exp) : Prop := mk_record_typ_parts
  { (** The parameters, glued *)
    record_typ_params : params_glu_top (record_params R) Δ Ns ns
    (** The sort at them is in the ambient universe *)
  ; record_typ_sort : Δ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ U
    (** The fields, glued at every equal instance *)
  ; record_typ_fields : forall Ns', exps_eq_at Δ (record_params R) Ns Ns' -> record_fields_glu R ns FP FEl Δ Ns' }.

(** A type of the record type [p] at its parameters, at syntactic
    parameters [Ns]: equal to [p] at them, and at every weakening its
    parts glued ([record_typ_parts]). *)
Record record_typ_at (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (U : typ) (Γ : ctx) (A : typ) (Ns : list exp) : Prop := mk_record_typ_at
  { (** [A] is the record type at [Ns] *)
    record_typ_eq : Γ ⊢ A ≈ apps_exp (a_record p) Ns : U
    (** At every weakening, its parts are glued *)
  ; record_typ_wk : forall Δ φ, Δ ⊢ᵏ φ : Γ ->
      record_typ_parts R ns FP FEl U Δ (List.map (fun N => N[φ]ʷ) Ns) }.

(** The type predicate of a record type: a type at some syntactic
    parameters ([record_typ_at]). *)
Definition record_glu_typ_pred (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred) (U : typ) : glu_typ_pred :=
  fun Γ A => exists Ns, record_typ_at p R ns FP FEl U Γ A Ns.
#[global] Arguments record_glu_typ_pred p R ns FP FEl U Γ A/.

(** An element of a record type: typed, related to itself, at some
    syntactic parameters of its type, with its projections; at every
    weakening and equal instance of the parameters, the projection of each
    field is glued to the value's at the field's type there, after the
    projections of the fields before it. *)
#[warnings="-cannot-define-projection"]
Record record_glu_exp (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (elem_rel : relation domain) (U : typ) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_record_glu_exp
  { (** [M] is of type [A] *)
    record_elem_typ : Γ ⊢ M : A
    (** [m] is related to itself *)
  ; record_elem_per : Dom m ≈ m ∈ elem_rel
    (** The syntactic parameters of [A] *)
  ; record_elem_params : list exp
    (** [A] is the record type at them *)
  ; record_elem_at : record_typ_at p R ns FP FEl U Γ A record_elem_params
    (** The projections of [m] *)
  ; record_elem_projs : list domain
    (** They are [m]'s fields *)
  ; record_elem_projs_eval : record_projs R m record_elem_projs
    (** At every weakening and equal instance, each field's projection is
        glued to [m]'s *)
  ; record_elem_fields : forall Δ φ Ns', Δ ⊢ᵏ φ : Γ ->
      exps_eq_at Δ (record_params R) (List.map (fun N => N[φ]ʷ) record_elem_params) Ns' ->
      forall k f T r, List.nth_error (record_fields R) k = Some (f, T) -> List.nth_error record_elem_projs k = Some r ->
        Δ ⊢ a_proj f M[φ]ʷ : T[sb_of_list Id (Ns' ++ record_pre R k M[φ]ʷ)] ® r
          ∈ FEl k (List.firstn k record_elem_projs) }.

(** The element predicate of a record type: [record_glu_exp]. *)
Definition record_glu_exp_pred (p : qname) (R : record_decl) (ns : list domain)
    (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
    (elem_rel : relation domain) (U : typ) : glu_exp_pred :=
  record_glu_exp p R ns FP FEl elem_rel U.

(** The gluing of a type of a small universe quotes the large universe
    [Typeω@0] (any small type is in it), so it does not say that the type is
    in the small universe; the element predicate of a small universe
    ([suniv_glu_exp_pred']) does: by its typing at its own type, and by its
    readback clause at that type. *)
(** The elements of a universe, at the ambient universe [U]: [univ_typ] is
    the entry [glu_univ_typ_rec j] of the family, passed applied so that
    [glu_univ_below_spec] can restate it.  [univ_glu_exp_pred] and
    [suniv_glu_exp_pred] are these at [glu_univ_typ]. *)
Record univ_glu_exp (U : typ) (j : nat) (univ_typ : domain -> glu_typ_pred)
  (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_univ_glu_exp
  { univ_glu_exp_typ : Γ ⊢ M : A
  ; univ_glu_exp_eq : Γ ⊢ A ≈ Typeω@j : U
  ; univ_glu_exp_glu : Γ ⊢ M ® univ_typ m }.

Definition univ_glu_exp_pred' (U : typ) (j : nat) (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
  univ_glu_exp U j univ_typ.

Record suniv_glu_exp (U : typ) (l : domain) (univ_typ : domain -> glu_typ_pred)
  (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_suniv_glu_exp
  { suniv_glu_exp_typ : Γ ⊢ M : A
  ; suniv_glu_exp_univ : Γ ⊢ A ® suniv_glu_typ_pred l U
  ; suniv_glu_exp_glu : Γ ⊢ M ® univ_typ m
  ; suniv_glu_exp_read : forall Δ φ W, Δ ⊢ᵏ φ : Γ -> Rtyp m in length Δ ↘ W -> glu_nf_eq Δ M[φ]ʷ W A[φ]ʷ }.

Definition suniv_glu_exp_pred' (U : typ) (l : domain) (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
  suniv_glu_exp U l univ_typ.

Hint Constructors level_glu_exp suniv_glu_typ univ_glu_exp suniv_glu_exp
  proof_glu_exp prop_univ_glu_exp level_sort_glu_exp : mctt.
(** The automation builds them like the existentials they replace.  The
    hint has no pattern: a pattern headed by one of these definitions is not
    found by the hint database, which unfolds it. *)
Hint Extern 1 =>
  match goal with
  | |- level_glu_exp_pred _ _ _ _ _ => econstructor
  | |- suniv_glu_typ_pred _ _ _ _ => econstructor
  | |- univ_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- proof_glu_exp_pred _ _ _ _ _ => econstructor
  | |- prop_univ_glu_exp_pred _ _ _ _ _ => econstructor
  | |- level_sort_glu_exp_pred _ _ _ _ _ => econstructor
  end : mctt.

Section Gluing.
  Variable
    (i : universe_index)
      (glu_univ_typ_rec : universe_index -> domain -> glu_typ_pred).

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : universe_index_lt (ul j) i),
          typ_rel <∙> univ_glu_typ_pred j (Typeω@(large_level i)) ->
          el_rel <∙> univ_glu_exp_pred' (Typeω@(large_level i)) j (glu_univ_typ_rec (ul j)) ->
          DG 𝕌ω@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_suniv :
    `{ forall typ_rel
         el_rel
         (lt_j_i : universe_index_lt (us (domain_level_real l)) i),
          Dom l ≈ l ∈ per_lvl ->
          typ_rel <∙> suniv_glu_typ_pred l (Typeω@(large_level i)) ->
          el_rel <∙> suniv_glu_exp_pred' (Typeω@(large_level i)) l (glu_univ_typ_rec (us (domain_level_real l))) ->
          DG 𝕌@l ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** [Level@n], at the sort [LevelSort] *)
  | glu_univ_elem_core_level :
    `{ forall typ_rel el_rel,
          typ_rel <∙> level_glu_typ_pred n ->
          el_rel <∙> level_glu_exp_pred n ->
          DG Levelᵈ@n ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** [Prop], its elements the propositions, glued as types *)
  | glu_univ_elem_core_prop_univ :
    `{ forall typ_rel el_rel,
          typ_rel <∙> prop_univ_glu_typ_pred (Typeω@(large_level i)) ->
          el_rel <∙> prop_univ_glu_exp_pred (Typeω@(large_level i)) ->
          DG Propᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** [LevelSort], at a large index, its elements the types of levels,
      glued as types at the least small index *)
  | glu_univ_elem_core_level_sort :
    `{ forall typ_rel el_rel (large_i : universe_index_large i),
          typ_rel <∙> level_sort_glu_typ_pred ->
          el_rel <∙> level_sort_glu_exp_pred (glu_univ_typ_rec (us (0, 0))) ->
          DG LevelSortᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** A [Π] at the kinds [κd] and [κc], [κc] evaluated: the domain glued,
      and the codomain glued at every related argument, as in the PER
      model *)
  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (OP : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_typ_pred)
         (OEl : forall c (equiv_c_c : Dom c ≈ c ∈ in_rel), glu_exp_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          DG a ∈ glu_univ_elem_core ↘ IP ↘ IEl ->
          DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
          (forall {c} (equiv_c : Dom c ≈ c ∈ in_rel) b,
              ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
              DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c) ->
          DF d_pi κd κc a ρ B ≈ d_pi κd κc a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          (** Not into propositions: a [Π] into propositions is a
              proposition ([glu_univ_elem_core_prop]), as for
              [per_univ_elem_core_pi] *)
          evaluated_kind κc ->
          typ_rel <∙> pi_glu_typ_pred κd κc (Typeω@(large_level i)) in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred κd κc (Typeω@(large_level i)) in_rel IP IEl elem_rel OEl ->
          DG d_pi κd κc a ρ B ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** A neutral type of the relevant kind, glued by its readback *)
  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          (** Of the relevant kind, as [per_univ_elem_core_neut] has it *)
          domain_kind (⇑ a b) = ak_relevant ->
          Dom b ≈ b ∈ per_bot ->
          typ_rel <∙> neut_glu_typ_pred (Typeω@(large_level i)) b ->
          el_rel <∙> neut_glu_exp_pred (Typeω@(large_level i)) b ->
          DG ⇑ a b ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** A declared member of a group at its parameters: the types of every
      member's non-uniform parameters glue at the related values before
      them, and so do the non-recursive arguments of each constructor of
      every member, at each related instance of the member's non-uniform
      parameters, and the domains of the shapes of its recursive ones; the
      relations are the canonical ones of
      [Core.Semantic.Inductives.IndPER]. *)
  | glu_univ_elem_core_indty :
    `{ forall (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
         (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
         (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
         (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
         typ_rel el_rel (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          group_structure D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall m Mm j κ A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b) ->
          (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
          (forall m Mm j κ A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ NP m j vs ↘ NEl m j vs) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ AP m ms c j vs ↘ AEl m ms c j vs) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
             exists b, ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                                         (ms ++ ws ++ ys) ↘ b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
             ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem_core
               ↘ DP m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B
               ↘ DEl m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B) ->
          typ_rel <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k M (Typeω@(large_level i)) ->
          el_rel <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k M elem_rel (Typeω@(large_level i)) ->
          DG d_ind p k (ups ++ ns) ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** A record type at its parameters: the type of each field glues at the
      related values of the fields before it; the relations are the
      canonical ones of [Core.Semantic.RecordPER]. *)
  | glu_univ_elem_core_record :
    `{ forall (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
         typ_rel el_rel (elem_rel : relation domain),
          record_lookup gc_deps gc_stack p = Some R ->
          DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel ->
          (forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> exists b, ⟦ T ⟧ record_fields_env R ns vs ↘ b) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ FP k vs ↘ FEl k vs) ->
          typ_rel <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(large_level i)) ->
          el_rel <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(large_level i)) ->
          DG d_record p ns ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  (** A proposition: glued as a type by its readback, its elements the
      proofs that read back.  It comes last, as its conclusion matches
      every value, as [per_univ_elem_core_prop] does. *)
  | glu_univ_elem_core_prop :
    `{ forall typ_rel el_rel,
          Dom a ≈ a ∈ per_prop ->
          typ_rel <∙> prop_glu_typ_pred a ->
          el_rel <∙> proof_glu_exp_pred a ->
          DG a ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }.
End Gluing.

Hint Constructors glu_univ_elem_core : mctt.

(** The universes below an index, indexed by theirs, as for
    [per_univ_below]: the recursion is structural, nested on the tier and the
    offset of a small index, so [glu_univ_elem] unfolds by computation. *)
Definition glu_empty : domain -> glu_typ_pred := fun _ _ _ => False.

(** A type glued at a universe: at the gluing predicates [G] gives the value
    [x], it is glued at the type predicate. *)
#[warnings="-cannot-define-projection"]
Record glu_typ_at (G : glu_typ_pred -> glu_exp_pred -> domain -> Prop) (x : domain) (Γ : ctx) (A : typ) : Prop :=
  mk_glu_typ_at
  { glu_typ_at_typ : glu_typ_pred
  ; glu_typ_at_exp : glu_exp_pred
  ; glu_typ_at_elem : G glu_typ_at_typ glu_typ_at_exp x
  ; glu_typ_at_glu : Γ ⊢ A ® glu_typ_at_typ }.

Definition glu_rec_at (a : nat) (lower : nat -> nat -> domain -> glu_typ_pred) (inner : nat -> domain -> glu_typ_pred)
  : universe_index -> domain -> glu_typ_pred :=
  fun v => match v with
        | us (a', b') => if a' <? a then lower a' b' else if a' =? a then inner b' else glu_empty
        | ul _ => glu_empty
        end.

Fixpoint glu_univ_below_in (a : nat) (lower : nat -> nat -> domain -> glu_typ_pred) (b : nat)
  : nat -> domain -> glu_typ_pred :=
  match b with
  | 0 => fun _ => glu_empty
  | S b' => fun m =>
      if Nat.eqb m b'
      then glu_typ_at (glu_univ_elem_core (us (a, b')) (glu_rec_at a lower (glu_univ_below_in a lower b')))
      else glu_univ_below_in a lower b' m
  end.

Definition glu_tier (a : nat) (lower : nat -> nat -> domain -> glu_typ_pred) (b : nat) : domain -> glu_typ_pred :=
  glu_typ_at (glu_univ_elem_core (us (a, b)) (glu_rec_at a lower (glu_univ_below_in a lower b))).

Fixpoint glu_tiers_below (a : nat) : nat -> nat -> domain -> glu_typ_pred :=
  match a with
  | 0 => fun _ _ => glu_empty
  | S a' => fun a'' => if Nat.eqb a'' a' then glu_tier a' (glu_tiers_below a') else glu_tiers_below a' a''
  end.

Definition glu_univ_rec_s (j : o2) : universe_index -> domain -> glu_typ_pred :=
  glu_rec_at (fst j) (glu_tiers_below (fst j)) (glu_univ_below_in (fst j) (glu_tiers_below (fst j)) (snd j)).

Definition glu_suniv (m : o2) : domain -> glu_typ_pred :=
  glu_tier (fst m) (glu_tiers_below (fst m)) (snd m).

Fixpoint glu_univ_below_l (n : nat) : nat -> domain -> glu_typ_pred :=
  match n with
  | 0 => fun _ => glu_empty
  | S n' => fun m =>
      if Nat.eqb m n'
      then glu_typ_at (glu_univ_elem_core (ul n')
                         (fun v => match v with us k => glu_suniv k | ul k => glu_univ_below_l n' k end))
      else glu_univ_below_l n' m
  end.

Definition glu_univ_below (u : universe_index) : universe_index -> domain -> glu_typ_pred :=
  match u with
  | us j => glu_univ_rec_s j
  | ul n => fun v => match v with us k => glu_suniv k | ul k => glu_univ_below_l n k end
  end.

Definition glu_univ_elem (i : universe_index) : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  glu_univ_elem_core i (glu_univ_below i).
#[global] Arguments glu_univ_elem : simpl never.

Lemma glu_univ_elem_equation_1 : forall i,
    glu_univ_elem i = glu_univ_elem_core i (glu_univ_below i).
Proof. reflexivity. Qed.

Hint Rewrite glu_univ_elem_equation_1 : glu_univ_elem.

Definition glu_univ_typ (i : universe_index) (a : domain) : glu_typ_pred := glu_typ_at (glu_univ_elem i) a.

Hint Constructors glu_typ_at : mctt.
Hint Extern 1 => match goal with |- glu_univ_typ _ _ _ _ => econstructor end : mctt.

Lemma glu_univ_below_spec : forall i j,
    universe_index_lt j i ->
    glu_univ_below i j = glu_univ_typ j.
Proof.
  assert (Hin : forall a lower b m, m < b -> glu_univ_below_in a lower b m = glu_tier a lower m).
  { intros a lower b; induction b as [| b IHb]; intros m Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec m b) as [-> | Hneq]; [reflexivity |].
    apply IHb; lia. }
  assert (Htiers : forall a a', a' < a -> glu_tiers_below a a' = glu_tier a' (glu_tiers_below a')).
  { induction a as [| a IHa]; intros a' Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec a' a) as [-> | Hneq]; [reflexivity |].
    apply IHa; lia. }
  assert (Htier : forall a b, glu_tier a (glu_tiers_below a) b = glu_univ_typ (us (a, b))).
  { reflexivity. }
  assert (Hl : forall n m, m < n -> glu_univ_below_l n m = glu_univ_typ (ul m)).
  { induction n as [| n IHn]; intros m Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec m n) as [-> | Hneq]; [reflexivity |].
    apply IHn; lia. }
  intros [[a b] | n] [[a' b'] | m] Hlt; cbn in Hlt; try contradiction.
  - unfold glu_univ_below, glu_univ_rec_s, glu_rec_at; cbn [fst snd].
    unfold ordinal_lt in Hlt; cbn [fst snd] in Hlt.
    destruct (Nat.ltb_spec a' a) as [Ha | Ha].
    + rewrite Htiers by exact Ha; apply Htier.
    + destruct (Nat.eqb_spec a' a) as [-> | Hne]; [| lia ].
      rewrite Hin by lia; apply Htier.
  - reflexivity.
  - apply Hl; assumption.
Qed.

Definition univ_glu_exp_pred j (U : typ) : glu_exp_pred := univ_glu_exp_pred' U j (glu_univ_typ j).

Definition suniv_glu_exp_pred (l : domain) (U : typ) : glu_exp_pred :=
  suniv_glu_exp_pred' U l (glu_univ_typ (us (domain_level_real l))).

Hint Extern 1 =>
  match goal with
  | |- univ_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred _ _ _ _ _ _ => econstructor
  end : mctt.

(** The two tiers' universe predicates, at an index: the predicates of the
    universe [universe_index_value u], which is [𝕌ω@j] in the large tier and the small
    universe at the literal level [n] in the small one.  Stating them by cases
    lets the gluing of the universe at an index be stated once for both
    tiers ([glu_univ_elem_univ_at]). *)
Definition univ_glu_typ_pred_at (u : universe_index) (U : typ) : glu_typ_pred :=
  match u with
  | us n => suniv_glu_typ_pred (domain_level_lit n) U
  | ul j => univ_glu_typ_pred j U
  end.

Definition univ_glu_exp_pred_at (u : universe_index) (U : typ) : glu_exp_pred :=
  match u with
  | us n => suniv_glu_exp_pred (domain_level_lit n) U
  | ul j => univ_glu_exp_pred j U
  end.

Section GluingInduction.
  Hypothesis
    (motive : universe_index -> glu_typ_pred -> glu_exp_pred -> domain -> Prop)

      (case_univ :
        forall i j
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : universe_index_lt (ul j) i),
          (forall P' El' a, DG a ∈ glu_univ_elem j ↘ P' ↘ El' -> motive j P' El' a) ->
          P <∙> univ_glu_typ_pred j (Typeω@(large_level i)) ->
          El <∙> univ_glu_exp_pred j (Typeω@(large_level i)) ->
          motive i P El 𝕌ω@j)

      (case_suniv :
        forall i l
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : universe_index_lt (us (domain_level_real l)) i),
          Dom l ≈ l ∈ per_lvl ->
          (forall P' El' a, DG a ∈ glu_univ_elem (us (domain_level_real l)) ↘ P' ↘ El' ->
                            motive (us (domain_level_real l)) P' El' a) ->
          P <∙> suniv_glu_typ_pred l (Typeω@(large_level i)) ->
          El <∙> suniv_glu_exp_pred l (Typeω@(large_level i)) ->
          motive i P El 𝕌@l)

      (case_level :
        forall i n (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> level_glu_typ_pred n ->
          El <∙> level_glu_exp_pred n ->
          motive i P El (Levelᵈ@n))

      (case_prop_univ :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> prop_univ_glu_typ_pred (Typeω@(large_level i)) ->
          El <∙> prop_univ_glu_exp_pred (Typeω@(large_level i)) ->
          motive i P El Propᵈ)

      (case_level_sort :
        forall i (P : glu_typ_pred) (El : glu_exp_pred) (large_i : universe_index_large i),
          (forall P' El' a, DG a ∈ glu_univ_elem (us (0, 0)) ↘ P' ↘ El' -> motive (us (0, 0)) P' El' a) ->
          P <∙> level_sort_glu_typ_pred ->
          El <∙> level_sort_glu_exp_pred (glu_univ_typ (us (0, 0))) ->
          motive i P El LevelSortᵈ)

      (case_pi :
        forall i κd κc a B (ρ : env) (in_rel : relation domain) (IP : glu_typ_pred)
          (IEl : glu_exp_pred) (OP : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_typ_pred)
          (OEl : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_exp_pred) (P : glu_typ_pred) (El : glu_exp_pred)
          (elem_rel : relation domain),
          DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
          motive i IP IEl a ->
          DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
              DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c) ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a ↘ b ->
              motive i (OP c equiv_c) (OEl c equiv_c) b) ->
          DF d_pi κd κc a ρ B ≈ d_pi κd κc a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          evaluated_kind κc ->
          P <∙> pi_glu_typ_pred κd κc (Typeω@(large_level i)) in_rel IP IEl OP ->
          El <∙> pi_glu_exp_pred κd κc (Typeω@(large_level i)) in_rel IP IEl elem_rel OEl ->
          motive i P El (d_pi κd κc a ρ B))

      (case_prop :
        forall i a (P : glu_typ_pred) (El : glu_exp_pred),
          Dom a ≈ a ∈ per_prop ->
          P <∙> prop_glu_typ_pred a ->
          El <∙> proof_glu_exp_pred a ->
          motive i P El a)

      (case_neut :
        forall i b a
          (P : glu_typ_pred)
          (El : glu_exp_pred),
          domain_kind (⇑ a b) = ak_relevant ->
          Dom b ≈ b ∈ per_bot ->
          P <∙> neut_glu_typ_pred (Typeω@(large_level i)) b ->
          El <∙> neut_glu_exp_pred (Typeω@(large_level i)) b ->
          motive i P El ⇑ a b)

      (case_indty :
        forall i p D k M pm ups ns (NP : nat -> nat -> list domain -> glu_typ_pred)
          (NEl : nat -> nat -> list domain -> glu_exp_pred)
          (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
          (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
          (DP : nat -> list domain -> list centry -> exp -> glu_typ_pred) (DEl : nat -> list domain -> list centry -> exp -> glu_exp_pred)
          (P : glu_typ_pred) (El : glu_exp_pred) (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          group_structure D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall m Mm j κ A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b) ->
          (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             exists b, ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b) ->
          (forall m Mm j κ A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b ->
             DG b ∈ glu_univ_elem i ↘ NP m j vs ↘ NEl m j vs) ->
          (forall m Mm j κ A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass κ A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ b ->
             motive i (NP m j vs) (NEl m j vs) b) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs ->
             ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ b ->
             motive i (AP m ms c j vs) (AEl m ms c j vs) b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
             exists b, ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                                         (ms ++ ws ++ ys) ↘ b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
             ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem i
               ↘ DP m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B
               ↘ DEl m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) j ys ys ->
             ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ b ->
             motive i (DP m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B)
               (DEl m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t)) B) b) ->
          P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k M (Typeω@(large_level i)) ->
          El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k M elem_rel (Typeω@(large_level i)) ->
          motive i P El (d_ind p k (ups ++ ns)))

      (case_record :
        forall i p R ns (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
          (P : glu_typ_pred) (El : glu_exp_pred) (elem_rel : relation domain),
          record_lookup gc_deps gc_stack p = Some R ->
          DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel ->
          (forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> exists b, ⟦ T ⟧ record_fields_env R ns vs ↘ b) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
             DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ record_fields_env R ns vs ↘ b ->
             motive i (FP k vs) (FEl k vs) b) ->
          P <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(large_level i)) ->
          El <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(large_level i)) ->
          motive i P El (d_record p ns))
  .

  Lemma glu_univ_elem_ind i P El a
    (H : glu_univ_elem i P El a) : motive i P El a.
  Proof.
    revert P El a H.
    induction i as [i IHi] using (well_founded_ind universe_index_wf).
    intros P El a H.
    induction H.
    - rewrite glu_univ_below_spec in * by assumption.
      eapply case_univ; eauto.
    - rewrite glu_univ_below_spec in * by assumption.
      eapply case_suniv; eauto.
    - eapply case_level; eassumption.
    - eapply case_prop_univ; eassumption.
    - rewrite glu_univ_below_spec in * by (apply universe_index_large_above_small; assumption).
      eapply case_level_sort; eauto.
      intros; apply IHi; [ apply universe_index_large_above_small; assumption | assumption ].
    - eapply case_pi; eassumption.
    - eapply case_neut; eassumption.
    - eapply case_indty; eassumption.
    - eapply case_record; eassumption.
    - eapply case_prop; eassumption.
  Qed.
End GluingInduction.

#[warnings="-cannot-define-projection"]
Record glu_elem_bot i a Γ A M m : Prop := glu_elem_bot_make
  { P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_elem_bot_wf : Γ ⊢ M : A
  ; glu_elem_bot_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_elem_bot_typ : Γ ⊢ A ® P
    (** A neutral of [a], as the PER has it ([neutral_at]): [a] is not
        [LevelSort], and at a type of levels the neutral is free of
        proofs *)
  ; glu_elem_bot_per : Dom m ≈ m ∈ neutral_at a
  ; glu_elem_bot_read : forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in length Δ ↘ M' -> glu_ne_eq Δ M[φ]ʷ M' A[φ]ʷ }.
Hint Constructors glu_elem_bot : mctt.

#[warnings="-cannot-define-projection"]
Record glu_elem_top i a Γ A M m : Prop := glu_elem_top_make
  { P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_elem_top_wf : Γ ⊢ M : A
  ; glu_elem_top_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_elem_top_typ : Γ ⊢ A ® P
  ; glu_elem_top_per : Dom ⇓ a m ≈ ⇓ a m ∈ per_top
  ; glu_elem_top_read : forall Δ φ w, Δ ⊢ᵏ φ : Γ -> Rnf ⇓ a m in length Δ ↘ w -> glu_nf_eq Δ M[φ]ʷ w A[φ]ʷ }.
Hint Constructors glu_elem_top : mctt.

(** A type glued at the index [i]: at the sort of its value's kind next to
    the large universe of [i], equal to its readback up to proofs. *)
Record glu_typ_top (i : universe_index) a Γ A : Prop := glu_typ_top_make
  { (** It is a type of that sort *)
    glu_typ_top_wf : Γ ⊢ A : abs_kind_sort (domain_kind a) Typeω@(large_level i)
    (** Its value reads back *)
  ; glu_typ_top_per : Dom a ≈ a ∈ per_top_typ
    (** It is equal to its readback, up to proofs, at every weakening *)
  ; glu_typ_top_read : forall Δ φ A', Δ ⊢ᵏ φ : Γ -> Rtyp a in length Δ ↘ A' ->
      glu_nf_eq Δ A[φ]ʷ A' (abs_kind_sort (domain_kind a) Typeω@(large_level i)) }.
Hint Constructors glu_typ_top : mctt.

#[warnings="-cannot-define-projection"]
Record glu_rel_typ_with_sub (i : nat) Δ A σ ρ : Prop := mk_glu_rel_typ_with_sub
  { a : domain
  ; P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_rel_typ_with_sub_eval : ⟦ A ⟧ ρ ↘ a
  ; glu_rel_typ_with_sub_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_rel_typ_with_sub_typ : Δ ⊢ A[σ] ® P }.

(** The value of the term [M] in [ρ], at a type of the kind [κ]: at a
    proposition the proof kept as it is, [⋆ᵈ⟨M, ρ⟩], as evaluation keeps
    a proof wherever it stands; at an evaluated kind its value. *)
Definition glu_term_value (M : exp) (ρ : env) (κ : abs_kind) (m : domain) : Prop :=
  match κ with ak_propositional => m = ⋆ᵈ⟨M, ρ⟩ | _ => ⟦ M ⟧ ρ ↘ m end.

#[warnings="-cannot-define-projection"]
Record glu_rel_exp_with_sub (i : nat) Δ M A σ ρ : Prop := mk_glu_rel_exp_with_sub
  { a : domain
  ; m : domain
  ; P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_rel_exp_with_sub_eval_typ : ⟦ A ⟧ ρ ↘ a
    (** The term's value, kept at a proposition *)
  ; glu_rel_exp_with_sub_eval : glu_term_value M ρ (domain_kind a) m
  ; glu_rel_exp_with_sub_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_rel_exp_with_sub_exp : Δ ⊢ M[σ] : A[σ] ® m ∈ El }.

(** ** Module Values

    A module value is glued as the module expression it is the value of,
    as [per_dmod] relates module values: a saturated body by its term
    members and its submodules, a value lacking a parameter by its values
    at glued arguments, a saturated global module by its arguments.  The
    types members are glued at are read off the value, as [per_body]
    reads them.  The module expression is [H0[σ0]], for [H0] over a
    context [Γ0] and [σ0] from [Δ] into it, and the syntactic types are
    those [mdenote] reads off [H0] in [Γ0], at [σ0]: so that the gluing
    moves along [σ0 ≈ σ0'] and along weakenings of [Δ] by the
    substitution lemmas alone.  A member of a proposition is not glued here: the value of
    a proof is the proof kept ([glu_term_value]), whose readback is the
    proof at the substitution ([glu_kept_proof_read]), so a slot's
    proofs need nothing of its module value.  The definition mentions no
    context gluing, so the context gluing glues the values of its slots
    with it ([cons_mod_glu_sub_pred]). *)

(** The type [T] glued at the type value [a], at the index [i] with the
    predicates [P] and [El]. *)
Record glu_type_at (Δ : ctx) (T : typ) (a : domain) (i : nat) (P : glu_typ_pred) (El : glu_exp_pred) : Prop := mk_glu_type_at
  { (** The type value is glued *)
    glu_type_at_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
    (** The type is glued at it *)
  ; glu_type_at_typ : Δ ⊢ T ® P }.

(** The term [M] of the type [T] glued to the value [m] at the type
    value [a], at the index [i] with the predicates [P] and [El]. *)
Record glu_elem_at (Δ : ctx) (T M : exp) (a m : domain) (i : nat) (P : glu_typ_pred) (El : glu_exp_pred) : Prop := mk_glu_elem_at
  { (** The type value is glued *)
    glu_elem_at_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
    (** The type is glued at it *)
  ; glu_elem_at_typ : Δ ⊢ T ® P
    (** The term is glued at it to the value *)
  ; glu_elem_at_term : Δ ⊢ M : T ® m ∈ El }.

(** [glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1]: [σ0] weakened by the Kripke
    weakening [φ] factors, up to equality, through the substitution [ζ]
    from [Γ1] into [Γ0], as [ζ ⨟ σ1].  The members of a glued module
    value are glued at every such factorization, so that they are read
    at whatever context the module expression is substituted into: a
    slot's unit at the slot's tail is read at the whole context through
    the weakening past the slot. *)
Record glu_sub_through (Δ : ctx) (σ0 : sub) (Γ0 : ctx) (Δ' : ctx) (φ : wk) (Γ1 : ctx) (ζ σ1 : sub) : Prop :=
  mk_glu_sub_through
  { (** The weakening is a Kripke weakening *)
    glu_sub_through_wk : Δ' ⊢ᵏ φ : Δ
    (** The substitution through which it factors is typed *)
  ; glu_sub_through_mid : Γ1 ⊢ˢ ζ : Γ0
    (** So is the rest *)
  ; glu_sub_through_rest : Δ' ⊢ˢ σ1 : Γ1
    (** It factors so *)
  ; glu_sub_through_eq : Δ' ⊢ˢ sb_wk σ0 φ ≈ ζ ⨟ σ1 : Γ0 }.

(** The term member [x] of a saturated body, [A ≔ M], glued as the
    member of [H0[σ0]]: in the environment [ρ'] the body's entries before
    it make, its type's value is [a] and the member's value [m], its
    body's value; at every factorization of [σ0] weakened, through [ζ] as
    [ζ ⨟ σ1], and at every type [A'] a lookup of [H0[ζ].x] reads in the
    middle context, [(H0[ζ].x)[σ1]] is glued to [m] at [a], at some
    index. *)
Record glu_body_member (Δ : ctx) (σ0 : sub) (Γ0 : ctx) (H0 : modexp) (x : String.string) (A M : exp) (ρ' : env)
    (a m : domain) : Prop := mk_glu_body_member
  { (** The type evaluates to [a] there *)
    glu_body_member_eval_type : ⟦ A ⟧ ρ' ↘ a
    (** The body evaluates to the member's value there ([eval_sel_body]) *)
  ; glu_body_member_eval : ⟦ M ⟧ ρ' ↘ m
    (** At every factorization and every type a lookup of the member
        reads, the member is glued to the member's value *)
  ; glu_body_member_glu : forall Δ' φ Γ1 ζ σ1 R A' Srt, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
      mdenote gc_deps gc_stack Γ1 (me_mem H0[ζ]ᵐ x) R -> mdesc_type R = Some A' ->
      type_sort Srt -> Γ1 ⊢ A' : Srt ->
      exists (i : nat) P El, glu_elem_at Δ' A'[σ1] (a_mem H0[ζ]ᵐ x)[σ1] a m i P El }.

(** The base of the instances of a closed telescope: a closed term at
    every variable, never read by a closed telescope, and unchanged by
    weakening. *)
Definition sb_closed_base : sub := fun _ => se_exp Propₘ.

(** [glu_dmod Δ σ0 Γ0 H0 h]: the module value [h] glued as the module
    expression [H0[σ0]] over [Δ], [H0] over [Γ0]: the counterpart of
    [per_dmod].  [glu_tele_args] glues the arguments of a global module,
    as [per_tele_args] relates them.  The recursive occurrences stand
    under [forall] and [->] only, so that the induction principle covers
    them. *)
Inductive glu_dmod : ctx -> sub -> ctx -> modexp -> dmod -> Prop :=
(** A saturated global module: the stored module [H0] denotes, at
    arguments glued as the value's.  Its members are not glued here, as
    [per_dmod] relates a global value by its arguments only: a member is
    glued where it is read, from the source's reading of it, the target
    possibly storing more members than the source (an open frame grown) *)
| glu_dmod_global : forall Δ σ0 Γ0 H0 p T Φ args,
    Δ ⊢ˢ σ0 : Γ0 ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 ->
    gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    List.length args = List.length T ->
    (** Through every factorization, the module part [H0[ζ]] denotes is
        the stored module at arguments that, at [σ1], are glued as the
        value's: the arguments are read off the description, as a member
        lookup reads them, not off a module expression [H0[σ0]] is only
        equal to *)
    (forall Δ' φ Γ1 ζ σ1 RH, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
       mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH ->
       exists Ns1, mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1)) ->
    (forall Δ' φ Γ1 ζ σ1 RH Ns1, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
       mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH -> mdesc_mod RH = Some (mdesc_closed nil p T Φ Ns1) ->
       glu_tele_args Δ' (List.rev T) nil nil (List.map (fun N => N[σ1]) Ns1) args) ->
    glu_dmod Δ σ0 Γ0 H0 (dm_global p args)
(** A saturated body: each term member of an evaluated kind glued at its
    type in the environment of the entries before it, and each
    submodule's closure there glued as the selection of the submodule *)
| glu_dmod_body : forall Δ σ0 Γ0 H0 sm Φ ρ,
    Δ ⊢ˢ σ0 : Γ0 ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 ->
    (forall x Φ' E A M ρ',
        gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
        entry_tm E = Some (A, M) ->
        evaluated_kind (entry_kind E) ->
        ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
        exists a m, glu_body_member Δ σ0 Γ0 H0 x A M ρ' a m) ->
    (forall y Φ' E Δy Dy ρ' h',
        gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) ->
        entry_unit E = Some (gu_mk Δy Dy) ->
        ⟦ Φ' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ' ->
        ⟦ Δy ⊢ Dy ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' ->
        glu_dmod Δ σ0 Γ0 (me_mem H0 y) h') ->
    glu_dmod Δ σ0 Γ0 H0 (dm_local nil (md_body sm Φ) ρ)
(** A value lacking a parameter, whose next parameter's type is [a]: at
    every factorization of [σ0] weakened through [ζ] ([glu_sub_through]),
    the type of the parameter [H0[ζ]] lacks is glued at [a], at some
    index; and the value's value at an argument glued at [a], when it has
    one, is glued as [H0[ζ]] applied to the argument, at every gluing of
    [a] the parameter's type is glued at: as [H0[ζ][↑] #0] over the
    middle context extended by the parameter, at [σ1] extended by the
    argument.  That it has one is not asked: where a value is applied, at
    an environment, completeness evaluates the application. *)
| glu_dmod_fun : forall Δ σ0 Γ0 H0 h a,
    Δ ⊢ˢ σ0 : Γ0 ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ᵐ H0 ≈ H0 ->
    next_param h a ->
    (forall Δ' φ Γ1 ζ σ1 RH T B T1 Srt, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
       mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH -> mdesc_mod_tele RH = Some T -> tele_view T = Some (B, T1) ->
       type_sort Srt -> Γ1 ⊢ B : Srt -> exists (i : nat) P El, glu_type_at Δ' B[σ1] a i P El) ->
    (forall Δ' φ Γ1 ζ σ1 RH T B T1 Srt, glu_sub_through Δ σ0 Γ0 Δ' φ Γ1 ζ σ1 ->
       mdenote gc_deps gc_stack Γ1 H0[ζ]ᵐ RH -> mdesc_mod_tele RH = Some T -> tele_view T = Some (B, T1) ->
       type_sort Srt -> Γ1 ⊢ B : Srt ->
       forall N c hc (i : nat) P El, DG a ∈ glu_univ_elem i ↘ P ↘ El ->
         Δ' ⊢ B[σ1] ® P -> Δ' ⊢ N : B[σ1] ® c ∈ El ->
         $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc ->
         glu_dmod Δ' (σ1 ,, N) (Γ1 ▹{domain_kind a} B) (me_app H0[ζ]ᵐ[Wk]ᵐ #0) hc) ->
    glu_dmod Δ σ0 Γ0 H0 h
(** [glu_tele_args Δ ts ρ Ms Ns args]: the arguments [Ns] (values
    [args]) of a global module, outermost first, against the rest [ts] of
    its closed telescope, the arguments before them having the values
    [ρ] and the terms [Ms], outermost first.  A parameter's type is
    instantiated by [sb_of_list sb_closed_base Ms]: the telescope is
    closed, so the base is never read, and a closed base is unchanged by
    weakening. *)
with glu_tele_args : ctx -> list centry -> env -> list exp -> list exp -> list domain -> Prop :=
(** No more arguments *)
| glu_tele_args_nil : forall Δ ts ρ Ms,
    glu_tele_args Δ ts ρ Ms nil nil
(** An argument glued at its parameter's type, at the arguments before
    it, then the rest *)
| glu_tele_args_cons : forall Δ κ A ts ρ Ms N Ns c args a (i : nat) P El,
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ A[sb_of_list sb_closed_base Ms] ® P ->
    Δ ⊢ N : A[sb_of_list sb_closed_base Ms] ® c ∈ El ->
    glu_tele_args Δ ts (ρ ↦ c ⦂ entry_type_closure A ρ) (Ms ++ N :: nil) Ns args ->
    glu_tele_args Δ (ce_ass κ A :: ts) ρ Ms (N :: Ns) (c :: args).

Scheme glu_dmod_mut_ind := Induction for glu_dmod Sort Prop
with glu_tele_args_mut_ind := Induction for glu_tele_args Sort Prop.
Combined Scheme glu_dmod_mut_ind_all from glu_dmod_mut_ind, glu_tele_args_mut_ind.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => Δ ⊢ˢ σ : ⋅.
#[global] Arguments nil_glu_sub_pred Δ σ ρ/.

(** The head of an environment glued at the stored type of its entry: the
    readback of a kept proof binds the entries of its environment at
    their stored types ([read_entry_term]), so the stored type's value is
    glued too, the head glued at it as at the declared type.  Every
    environment built stores the declared type's value.  The index is
    the stored type's own, so that two gluings of one context agree on
    it ([functional_glu_ctx_env]). *)
#[warnings="-cannot-define-projection"]
Record glu_stored_type (Δ : ctx) (σ : sub) (A : typ) (ρ : env) (t : entry_type) : Prop := mk_glu_stored_type
  { (** The index it is glued at *)
    glu_stored_index : nat
    (** The stored type's value *)
  ; glu_stored_value : domain
    (** Its type predicate *)
  ; glu_stored_P : glu_typ_pred
    (** Its element predicate *)
  ; glu_stored_El : glu_exp_pred
    (** The stored type evaluates to it *)
  ; glu_stored_eval : eval_entry_type gc_deps gc_stack t glu_stored_value
    (** It is glued *)
  ; glu_stored_univ : DG glu_stored_value ∈ glu_univ_elem glu_stored_index ↘ glu_stored_P ↘ glu_stored_El
    (** The head is glued at it *)
  ; glu_stored_glu : Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ glu_stored_El }.

(** An assumption entry glues by its head, at the gluing of its type, and
    by its tail.  The parameters come before the relation's own arguments,
    so that the predicate is a [glu_sub_pred]. *)
Variant cons_glu_sub_pred (i : nat) Γ κ A (TSb : glu_sub_pred) : glu_sub_pred :=
(** The substitution is typed, its head glues at the type's predicate and
    its tail glues by [TSb]; the head is a term entry glued at its stored
    type, and one that reads back *)
| mk_cons_glu_sub_pred :
  `{ forall P El,
        Δ ⊢ˢ σ : Γ ▹{κ} A ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        (** [A[↑]ʷ[σ]] rather than [A[Wk ⨟ σ]]: it is the direct instance of
            [Γ ▹ A ⊢ #0 : A[↑]ʷ] along [σ]. *)
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        (exists t, env_entry ρ 0 = de_term (ρ 0) t /\ glu_stored_type Δ σ A ρ t) ->
        head_readable 0 (env_entry ρ 0) ->
        Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢ˢ σ ® ρ ∈ cons_glu_sub_pred i Γ κ A TSb }.

(** A definition entry glues as an assumption entry whose head, at an
    evaluated kind, is also tied to the value of the body in the tail
    ([def_tie]); at a proposition the head is the body kept, related to
    any proof.  The syntactic half of the tie is part of
    [Δ ⊢ˢ σ : Γ ▸ A ≔ M]. *)
Variant cons_def_glu_sub_pred (i : nat) Γ A M (TSb : glu_sub_pred) : glu_sub_pred :=
(** As an assumption's, and the head's value is the body's value in the
    tail *)
| mk_cons_def_glu_sub_pred :
  `{ forall P El,
        Δ ⊢ˢ σ : Γ ▸ A ≔ M ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        (evaluated_kind (domain_kind a) -> def_tie A M ρ) ->
        (exists t, env_entry ρ 0 = de_term (ρ 0) t /\ glu_stored_type Δ σ A ρ t) ->
        head_readable 0 (env_entry ρ 0) ->
        Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢ˢ σ ® ρ ∈ cons_def_glu_sub_pred i Γ A M TSb }.

(** A module slot glues by its syntactic typing, by the tie of its value
    to the closure of its unit over the tail, which is the slot clause of
    the environment PER, and by its value, glued as the unit's literal
    over the tail at the tail of the substitution ([glu_dmod]), which is
    what the substitution sends the slot to, up to δ. *)
Variant cons_mod_glu_sub_pred Γ U (TSb : glu_sub_pred) : glu_sub_pred :=
(** The substitution is typed, the head's module is the closure of the
    unit over the tail, glued as the unit's literal, a module entry
    that reads back with its stored unit scoped by the tail, and the tail
    glues by [TSb] *)
| mk_cons_mod_glu_sub_pred :
  `{ Δ ⊢ˢ σ : Γ ▹ₘ U ->
     tie_mod (env_mod ρ 0) (me_lit U) ρ↯ ->
     glu_dmod Δ (Wk ⨟ σ) Γ (me_lit U) (env_mod ρ 0) ->
     env_entry ρ 0 = de_mod (env_mod ρ 0) U ->
     head_readable (List.length Γ) (env_entry ρ 0) ->
     Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
     Δ ⊢ˢ σ ® ρ ∈ cons_mod_glu_sub_pred Γ U TSb }.

(** A definition with a module part glues as its term part does as a
    definition, and its head's module is tied to the closure of its unit
    over the tail and glued as the component's module part, as a
    slot's. *)
Variant cons_dm_glu_sub_pred (i : nat) Γ A M U (TSb : glu_sub_pred) : glu_sub_pred :=
(** The substitution is typed, the head's term value glues at the type's
    predicate and is the body's value in the tail, the head's module is the
    closure of the unit over the tail, and the tail glues by [TSb] *)
| mk_cons_dm_glu_sub_pred :
  `{ forall P El,
        Δ ⊢ˢ σ : Γ ▸ₘ A ≔ M ‖ U ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        def_tie A M ρ ->
        tie_mod (env_mod ρ 0) (me_lit U) ρ↯ ->
        glu_dmod Δ (Wk ⨟ σ) Γ (me_lit U) (env_mod ρ 0) ->
        (exists t, env_entry ρ 0 = de_dm (ρ 0) t (env_mod ρ 0) U /\ glu_stored_type Δ σ A ρ t) ->
        head_readable (List.length Γ) (env_entry ρ 0) ->
        Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢ˢ σ ® ρ ∈ cons_dm_glu_sub_pred i Γ A M U TSb }.

(** As with [wf_ctx_empty], the base case carries what the judgment is relative
    to: without it, [⊢ ⋅] would not follow ([glu_ctx_env_wf_ctx]). *)
Inductive glu_ctx_env : glu_sub_pred -> ctx -> Prop :=
| glu_ctx_env_nil :
  `{ forall Sb,
        Sb <∙> nil_glu_sub_pred ->
        ⊢ᵍ gc_deps ⍮ gc_stack ->
        EG ⋅ ∈ glu_ctx_env ↘ Sb }
(** An assumption, of a type of the sort of its kind next to the large
    universe of the gluing's index [i] *)
| glu_ctx_env_cons :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : abs_kind_sort κ Typeω@i ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred i Γ κ A TSb ->
        EG Γ ▹{κ} A ∈ glu_ctx_env ↘ Sb }
(** A definition, of a type of the sort of a kind [κ] next to the large
    universe of the gluing's index [i] *)
| glu_ctx_env_cons_def :
  `{ forall i κ TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : abs_kind_sort κ Typeω@i ->
        Γ ⊢ M : A ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_exp_with_sub i Δ M A σ ρ) ->
        Sb <∙> cons_def_glu_sub_pred i Γ A M TSb ->
        EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb }
(** A module slot: its unit well formed, and the closure of its literal
    glued as the literal at every glued environment of the context, as an
    assumption's type is glued *)
| glu_ctx_env_cons_mod :
  `{ forall TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
        (forall Δ σ ρ h,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
            glu_dmod Δ σ Γ (me_lit U) h) ->
        Sb <∙> cons_mod_glu_sub_pred Γ U TSb ->
        EG Γ ▹ₘ U ∈ glu_ctx_env ↘ Sb }
(** A definition with a module part: the premises of a definition entry,
    the well-formedness of the entry, and its unit's literal glued as a
    slot's is *)
| glu_ctx_env_cons_dm :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Typeω@i ->
        Γ ⊢ M : A ->
        (** The entry is well formed: its unit an alias under no
            parameters ([wf_ctx_extend_dm]) *)
        ⊢ Γ ▸ₘ A ≔ M ‖ U ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_exp_with_sub i Δ M A σ ρ) ->
        (forall Δ σ ρ h,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h ->
            glu_dmod Δ σ Γ (me_lit U) h) ->
        Sb <∙> cons_dm_glu_sub_pred i Γ A M U TSb ->
        EG Γ ▸ₘ A ≔ M ‖ U ∈ glu_ctx_env ↘ Sb }.

Definition glu_rel_ctx Γ : Prop := exists Sb, EG Γ ∈ glu_ctx_env ↘ Sb.
#[global] Arguments glu_rel_ctx Γ/.

(** A module expression glued in a context: at every glued environment of
    the context, its value is glued as it. *)
Definition glu_modexp_at (Γ : ctx) (H : modexp) : Prop :=
  forall Sb, EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ, Δ ⊢ˢ σ ® ρ ∈ Sb ->
      exists h, ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ glu_dmod Δ σ Γ H h.

(** A term glued at its type: the gluing of the context, a universe level
    for the type, and the gluing of the term under every substitution glued
    in the context. *)
#[warnings="-cannot-define-projection"]
Record glu_rel_exp Γ M A : Prop := mk_glu_rel_exp
  { glu_rel_exp_sb : glu_sub_pred
  ; glu_rel_exp_ctx : EG Γ ∈ glu_ctx_env ↘ glu_rel_exp_sb
  ; glu_rel_exp_lvl : nat
  ; glu_rel_exp_body : forall Δ σ ρ,
      Δ ⊢ˢ σ ® ρ ∈ glu_rel_exp_sb ->
      glu_rel_exp_with_sub glu_rel_exp_lvl Δ M A σ ρ }.

Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).

(** ** The Fundamental Theorem's Judgments

    The value of a substituted term is not the value of the term at the
    substitution's value: a kept proof [⋆ᵈ⟨N[τ], ρ⟩] is not [⋆ᵈ⟨N, ρτ⟩].
    So no lemma moves a glued term along a substitution, and the
    fundamental theorem instead glues every instance of a typed term at
    substitutions of a fixed form ([glu_rel_exp_under_sub]), each instance
    at its own value.  The definitions are layered: each mentions only the
    ones before it.  The components of those substitutions are glued at
    every renaming ([glu_rel_exp_under_renaming]), which closes them under
    the weakenings binders introduce; a renaming has no components of its
    own, so the layering ends there. *)

(** A term glued at every renaming of its context into a glued one. *)
Definition glu_rel_exp_under_renaming (Γ : ctx) (M A : exp) : Prop :=
  forall Γ' φ, Γ' ⊢ʷ φ : Γ -> ⊩ Γ' -> Γ' ⊩ M[φ]ʷ : A[φ]ʷ.

(** An extension [Ψ] of [Γ] glued at every renaming of [Γ] into a glued
    context: the extended context, the extension weakened, is glued.  Only
    the entries of [Ψ] are asked for, not the base's own types: an instance
    only gives [⊩ Γ'] of its domain, so a judgment asking for the types of
    the base would not hold at the instances.  The definition is closed
    under renaming of [Γ], and it holds at each instance of [Γ] through the
    instance lifted through [Ψ] ([glu_rel_ext_under_sub]). *)
Definition glu_rel_ext_under_renaming (Γ Ψ : ctx) : Prop :=
  forall Γ' φ, Γ' ⊢ʷ φ : Γ -> ⊩ Γ' -> ⊩ (tele_wk Ψ φ ++ Γ')%list.

(** A unit glued at the context [Γ] it is closed over: a body's expansion
    ([gm_expand], as evaluation reads the body), its entries over the
    unit's parameters, is an extension of [Γ] glued at every renaming of
    [Γ], and so is each module entry's unit, recursively, at the context of
    the expanded entries before it; an alias's parameters are an extension
    glued so, and its target is glued as a module expression over them.
    The recursion is on the unit: a body's module entries, those
    of the fragments its opens store included, are its subterms. *)
Fixpoint glu_unit_at (Γ : ctx) (U : gunit) {struct U} : Prop :=
  match U with
  | gu_mk Δu (md_body _ Φ) =>
      glu_rel_ext_under_renaming Γ (body_ctx (gm_expand Φ) ++ Δu) /\ glu_gmod_units (Δu ++ Γ) Φ
  | gu_mk Δu (md_alias E) => glu_rel_ext_under_renaming Γ Δu /\ glu_modexp_at (Δu ++ Γ) E
  end
(** The module entries of a body over [Γ], each glued at the context of
    the expanded entries before it, and those of the fragment each open
    stores, which the expansion grafts after the entries before the
    open. *)
with glu_gmod_units (Γ : ctx) (Φ : gmod) {struct Φ} : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ (ge_mod _ U) =>
      glu_gmod_units Γ Φ' /\ glu_unit_at (body_ctx (gm_expand Φ') ++ Γ) U
  | gm_ext Φ' _ (ge_def_mod _ _ _ U) =>
      glu_gmod_units Γ Φ' /\ glu_unit_at (body_ctx (gm_expand Φ') ++ Γ) U
  | gm_ext Φ' _ _ => glu_gmod_units Γ Φ'
  | gm_open Φ' _ _ Φg => glu_gmod_units Γ Φ' /\ glu_gmod_units (body_ctx (gm_expand Φ') ++ Γ) Φg
  end.

(** A unit glued at every renaming of its context into a glued one. *)
Definition glu_unit_under_renaming (Γ : ctx) (U : gunit) : Prop :=
  forall Γ' φ, Γ' ⊢ʷ φ : Γ -> ⊩ Γ' -> glu_unit_at Γ' (gunit_wk U φ).

(** A substitution the fundamental theorem instantiates terms at: typed,
    out of a glued context, its term components glued at their types at
    every renaming, and the units of its module components glued at every
    renaming.  Module values are not glued: a member of a module is reached
    through its unit's body context.  The instances are closed under
    renaming, so a term glued at all of them is glued at every renaming of
    each. *)
Record glu_rel_sub_inst (Γ : ctx) (τ : sub) (Δ : ctx) : Prop := mk_glu_rel_sub_inst
  { (** The substitution is typed *)
    glu_rel_sub_inst_typed : Γ ⊢ˢ τ : Δ
    (** Its domain is glued *)
  ; glu_rel_sub_inst_ctx : ⊩ Γ
    (** Each term component is glued at its type at every renaming *)
  ; glu_rel_sub_inst_comps : forall x A, Δ ∋ #x : A -> glu_rel_exp_under_renaming Γ #x[τ] A[τ]
    (** The unit of each module component is glued at every renaming *)
  ; glu_rel_sub_inst_mods : forall x U, Δ ∋ #x ≔ₘ U -> glu_unit_under_renaming Γ U[τ]ᵘ }.

(** A glued context whose variables' types are glued at every renaming,
    each as a term of a sort of types, and whose module slots' units are
    glued at every renaming: the fundamental theorem's judgment of
    contexts.  A variable is then glued at its type at every renaming, so
    every renaming into a glued context is an instance, the identity among
    them. *)
Record glu_rel_ctx_types (Γ : ctx) : Prop := mk_glu_rel_ctx_types
  { (** The context is glued *)
    glu_rel_ctx_types_ctx : ⊩ Γ
    (** The type of each variable is glued, at every renaming, as a term
        of a sort of types *)
  ; glu_rel_ctx_types_types : forall x A, Γ ∋ #x : A ->
      exists S, type_sort S /\ glu_rel_exp_under_renaming Γ A S
    (** The unit of each module slot is glued at every renaming *)
  ; glu_rel_ctx_types_slots : forall x U, Γ ∋ #x ≔ₘ U -> glu_unit_under_renaming Γ U }.

(** A unit glued at each of its instances: the fundamental theorem's
    judgment of units. *)
Definition glu_rel_unit_under_sub (Δ : ctx) (U : gunit) : Prop :=
  forall Γ τ, glu_rel_sub_inst Γ τ Δ -> glu_unit_at Γ U[τ]ᵘ.

(** A term all of whose instances at those substitutions are glued, each
    at its own value, in a context as the fundamental theorem glues it: the
    fundamental theorem's judgment of terms.  The identity is an instance,
    so the term is glued. *)
Record glu_rel_exp_under_sub (Δ : ctx) (M A : exp) : Prop := mk_glu_rel_exp_under_sub
  { (** The context is glued with its variables' types *)
    glu_rel_exp_under_sub_ctx : glu_rel_ctx_types Δ
    (** Each instance is glued *)
  ; glu_rel_exp_under_sub_inst : forall Γ τ, glu_rel_sub_inst Γ τ Δ -> Γ ⊩ M[τ] : A[τ] }.

(** A module expression all of whose instances are glued, in a context
    as the fundamental theorem glues it: the fundamental theorem's
    judgment of module expressions. *)
Record glu_rel_modexp_under_sub (Δ : ctx) (H : modexp) : Prop := mk_glu_rel_modexp_under_sub
  { (** The context is glued with its variables' types *)
    glu_rel_modexp_under_sub_ctx : glu_rel_ctx_types Δ
    (** Each instance is glued *)
  ; glu_rel_modexp_under_sub_inst : forall Γ τ, glu_rel_sub_inst Γ τ Δ -> glu_modexp_at Γ H[τ]ᵐ }.

(** A definition entry [A ≔ M] glued at the instances of the context [Δ]
    it extends, its type at the sort [S]. *)
Record glu_rel_def_entry_under_sub (Δ : ctx) (A M : exp) (S : typ) : Prop := mk_glu_rel_def_entry_under_sub
  { (** The sort is a sort of types *)
    glu_rel_def_entry_under_sub_type_sort : type_sort S
    (** The type is glued at the instances at its sort *)
  ; glu_rel_def_entry_under_sub_type : glu_rel_exp_under_sub Δ A S
    (** The body is glued at the instances at the type *)
  ; glu_rel_def_entry_under_sub_body : glu_rel_exp_under_sub Δ M A }.

(** A definition with a module part [A ≔ M ‖ U] glued at the instances of
    the context [Δ] it extends, its type in the universe of the level [i]
    and its module part an alias of [E] under no parameters
    ([wf_ctx_extend_dm]). *)
Record glu_rel_module_def_entry_under_sub (Δ : ctx) (A M : exp) (U : gunit) (i : nat) (E : modexp) : Prop :=
  mk_glu_rel_module_def_entry_under_sub
  { (** The module part is an alias of the target under no parameters *)
    glu_rel_module_def_entry_under_sub_alias : U = gu_mk nil (md_alias E)
    (** The type is glued at the instances in its universe *)
  ; glu_rel_module_def_entry_under_sub_type : glu_rel_exp_under_sub Δ A Typeω@i
    (** The body is glued at the instances at the type *)
  ; glu_rel_module_def_entry_under_sub_body : glu_rel_exp_under_sub Δ M A
    (** The module part is well formed *)
  ; glu_rel_module_def_entry_under_sub_unit_wf : gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ U ≈ U
    (** The module part is glued at the instances *)
  ; glu_rel_module_def_entry_under_sub_unit : glu_rel_unit_under_sub Δ U }.

(** The parts of an entry glued at the instances of the context [Δ] it
    extends: an assumption's type at a sort of its kind, a definition's
    type and body, a module slot's unit, well formed, and a definition with
    a module part's type, body and alias. *)
Definition glu_rel_entry_under_sub (Δ : ctx) (e : centry) : Prop :=
  match e with
  | ce_ass κ A => exists S, sort_kind S κ /\ glu_rel_exp_under_sub Δ A S
  | ce_def A M => exists S, glu_rel_def_entry_under_sub Δ A M S
  | ce_mod U => gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ U ≈ U /\ glu_rel_unit_under_sub Δ U
  | ce_dm A M U => exists (i : nat) E, glu_rel_module_def_entry_under_sub Δ A M U i E
  end.

(** An extension [Ψ] of a context [Γ] glued at the instances: the context
    is glued with its variables' types, and each entry's parts are glued at
    the instances of the context before it.  An instance of [Γ] then lifts
    through [Ψ] and through every suffix of it ([Extensions.v]), and a term
    glued at the instances of [Ψ ++ Γ] is glued at each lifted instance, as
    a binder's body is: the fundamental theorem's judgment of extensions.
    Each entry is glued at its own prefix's instances, not only at the
    whole extension's: the unit of a module entry is read at the context
    before it, as a nested module's members are. *)
Fixpoint glu_rel_ext_under_sub (Γ Ψ : ctx) : Prop :=
  match Ψ with
  | nil => glu_rel_ctx_types Γ
  | e :: Ψ' => glu_rel_ext_under_sub Γ Ψ' /\ glu_rel_entry_under_sub (Ψ' ++ Γ)%list e
  end.

(** A weakening glued from [Γ] to [Δ], as [Γ ⊨ʷ φ : Δ] in the PER model:
    precomposed with it, a substitution glued into [Γ] at [ρ] is glued
    into [Δ] at [⟪φ⟫ ρ].  Unlike a substitution, a weakening acts on
    environments without evaluation, so the judgment can be stated; it
    weakens term judgments ([glu_rel_exp_wk]). *)
#[warnings="-cannot-define-projection"]
Record glu_rel_wk Γ φ Δ : Prop := mk_glu_rel_wk
  { (** The glued substitutions into the source *)
    glu_rel_wk_sb : glu_sub_pred
  ; glu_rel_wk_ctx : EG Γ ∈ glu_ctx_env ↘ glu_rel_wk_sb
    (** The glued substitutions into the target *)
  ; glu_rel_wk_sb' : glu_sub_pred
  ; glu_rel_wk_ctx' : EG Δ ∈ glu_ctx_env ↘ glu_rel_wk_sb'
    (** The weakening is well formed *)
  ; glu_rel_wk_typed : Γ ⊢ʷ φ : Δ
    (** The weakening is semantic: it takes related environments to related
        ones, the kinds of the entries agreeing *)
  ; glu_rel_wk_sem : Γ ⊨ʷ φ : Δ
    (** A substitution glued into the source, precomposed with the
        weakening, is glued into the target at the weakened environment *)
  ; glu_rel_wk_glu : forall Δ' σ ρ, Δ' ⊢ˢ σ ® ρ ∈ glu_rel_wk_sb -> Δ' ⊢ˢ ι φ ⨟ σ ® ⟪φ⟫ ρ ∈ glu_rel_wk_sb' }.

Notation "Γ ⊩ʷ φ : Δ" := (glu_rel_wk Γ φ Δ) (at level 70, φ constr at level 0, Δ at level 69).

(** A substitution glued from [Γ] to [Δ]: precomposed with it, a
    substitution glued into [Γ] at [ρ] is glued into [Δ] at an environment
    the context PER of [Δ] relates to the value of [τ] at [ρ].  The value
    itself stores the entries at [Δ]'s types ([ctx_retag], [centry_tag]),
    the glued environment at any related ones.  It is semantic, so the
    values of [M[τ]] at [ρ] and of [M] there are related, and term
    judgments move along it ([glu_rel_exp_sub]). *)
#[warnings="-cannot-define-projection"]
Record glu_rel_sub Γ τ Δ : Prop := mk_glu_rel_sub
  { (** The glued substitutions into the source *)
    glu_rel_sub_sb : glu_sub_pred
  ; glu_rel_sub_ctx : EG Γ ∈ glu_ctx_env ↘ glu_rel_sub_sb
    (** The glued substitutions into the target *)
  ; glu_rel_sub_sb' : glu_sub_pred
  ; glu_rel_sub_ctx' : EG Δ ∈ glu_ctx_env ↘ glu_rel_sub_sb'
    (** The substitution is well formed *)
  ; glu_rel_sub_typed : Γ ⊢ˢ τ : Δ
    (** It is semantic *)
  ; glu_rel_sub_sem : Γ ⊨ˢ τ ≈ τ : Δ
    (** A substitution glued into the source, precomposed with it, is glued
        into the target at an environment related to its value *)
  ; glu_rel_sub_glu : forall Δ' σ ρ, Δ' ⊢ˢ σ ® ρ ∈ glu_rel_sub_sb ->
      exists ρτ, Δ' ⊢ˢ τ ⨟ σ ® ρτ ∈ glu_rel_sub_sb' /\
        forall RΔ ρτ0, EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ0 -> Dom ρτ0 ≈ ρτ ∈ RΔ }.

Notation "Γ ⊩ˢ τ : Δ" := (glu_rel_sub Γ τ Δ) (at level 70, τ at level 69, Δ at level 69).

End Fixed_GCtx.

#[export]
Hint Rewrite @glu_univ_elem_equation_1 : glu_univ_elem.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (at level 70, A at level 69, R constr).
Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons typ (Tcons exp (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (at level 70, M at level 69, m at level 69, R constr).
Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢ˢ σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (at level 70, σ at level 69, ρ at level 69, R constr).
Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (at level 70, a at level 69, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (at level 70, A at level 69, R constr, Sb constr).

#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.
#[export]
Hint Constructors proof_glu_exp prop_univ_glu_exp level_sort_glu_exp : mctt.
#[export]
Hint Constructors glu_univ_elem_core : mctt.
#[export]
Hint Constructors glu_elem_bot : mctt.
#[export]
Hint Constructors glu_elem_top : mctt.
#[export]
Hint Constructors glu_typ_top : mctt.
#[export]
Hint Constructors level_glu_exp suniv_glu_typ univ_glu_exp suniv_glu_exp glu_typ_at : mctt.
#[export]
Hint Constructors glu_params_top glu_nparams ind_glu_components ind_glu_exp : mctt.
(** The automation builds the record-shaped gluing predicates like the
    existentials they replace.  The hint has no pattern: a pattern headed by
    one of these definitions is not found by the database, which unfolds it. *)
#[export]
Hint Extern 1 =>
  match goal with
  | |- level_glu_exp_pred _ _ _ _ _ => econstructor
  | |- suniv_glu_typ_pred _ _ _ _ => econstructor
  | |- univ_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- proof_glu_exp_pred _ _ _ _ _ => econstructor
  | |- prop_univ_glu_exp_pred _ _ _ _ _ => econstructor
  | |- level_sort_glu_exp_pred _ _ _ _ _ => econstructor
  | |- univ_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- glu_univ_typ _ _ _ _ => econstructor
  | |- ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => econstructor
  end : mctt.
Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).
Notation "Γ ⊩ʷ φ : Δ" := (glu_rel_wk Γ φ Δ) (at level 70, φ constr at level 0, Δ at level 69).
Notation "Γ ⊩ˢ τ : Δ" := (glu_rel_sub Γ τ Δ) (at level 70, τ at level 69, Δ at level 69).

(** [induction H using glu_univ_elem_ind] does not apply, for the reason
    [per_univ_elem_induction] explains. The tactics below perform the same
    induction. *)
Ltac glu_induction_hintro := let H := fresh "H" in intro H.

Ltac glu_univ_elem_induction_core HH ih :=
  lazymatch type of HH with
  | glu_univ_elem ?i ?P ?El ?a =>
      repeat match goal with
             | Hd : ?T |- _ =>
                 lazymatch Hd with HH => fail | i => fail | P => fail | El => fail | a => fail | _ => idtac end;
                 lazymatch T with
                 | context [i] => revert Hd | context [P] => revert Hd
                 | context [El] => revert Hd | context [a] => revert Hd
                 end
             end;
      revert HH; revert i P El a;
      refine (glu_univ_elem_ind _ _ _ _ _ _ _ _ _ _ _);
      (** In order: a large universe, a small one, [Level@n], [Prop],
          [LevelSort], [Π], a proposition, a neutral type, an inductive
          type, a record type; each case's binders, then its hypotheses. *)
      [ do 5 intro; do 3 glu_induction_hintro | do 5 intro; do 4 glu_induction_hintro
      | do 4 intro; do 2 glu_induction_hintro | do 3 intro; do 2 glu_induction_hintro
      | do 4 intro; do 3 glu_induction_hintro
      | do 14 intro; glu_induction_hintro; ih; do 7 glu_induction_hintro
      | do 4 intro; do 3 glu_induction_hintro | do 5 intro; do 4 glu_induction_hintro
      | do 17 intro; do 17 glu_induction_hintro | do 9 intro; do 7 glu_induction_hintro ]; cbv beta
  end.

(** As [induction H using glu_univ_elem_ind]: the hypothesis on the motive at
    the domain of a [Π] is [IHH]; those under a binder are [H]s, as
    [induction] does not see them as inductive hypotheses. *)
Ltac glu_univ_elem_induction H :=
  let IHn := fresh "IH" H in
  let HH := fresh "Hglue" in
  rename H into HH;
  glu_univ_elem_induction_core HH ltac:(idtac; let n := fresh IHn in intro n).

(** As [induction 1 using glu_univ_elem_ind]. *)
Ltac glu_univ_elem_induction1 :=
  intros until 1;
  match goal with
  | H : glu_univ_elem _ _ _ _ |- _ =>
      glu_univ_elem_induction_core H ltac:(idtac; let n := fresh "IH" in intro n)
  end.

(** ** Glued Declarations

    The judgments of a declaration's typing, read in the gluing model, as
    [valid_ind_decl] reads them in the PER model.  [nparams_prefix D k] is
    the context of the first [k] non-uniform parameters, [nonrec_args_prefix
    gs k] that of the first [k] non-recursive arguments of a constructor. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The judgments of a record's declaration, glued: what the rule of the
    type former premises, read in the gluing model. *)
Record glu_record_decl (R : record_decl) : Prop := mk_glu_record_decl
  { (** The parameters are a context glued with its types *)
    glued_params : glu_rel_ctx_types (record_params R)
    (** The sort is a universe, small at a level glued at its instances *)
  ; glued_sort : (exists i : nat, record_sort R = Typeω@i) \/
      (exists L (n : nat), record_sort R = Type⟨L⟩ /\ glu_rel_exp_under_sub (record_params R) L (Level@n))
    (** Each field is glued at its instances at the sort of its kind next
        to the record's sort, over the fields before it *)
  ; glued_fields : forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
      glu_rel_exp_under_sub (record_fctx R k ++ record_params R) T
        (abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ) }.

(** The views of a group with its members as variables ([grp_selfs_ctx]), as
    [views_self_valid] reads them in the PER model: each view's instance is
    [IsS] there, read at the group's own path, and is glued there.  Once
    the group is filed, a glued [grp_sb] sends the instances to the group's
    uniform parameters ([filed_view_is_glu]). *)
Record glu_views_self (D : ind_decl) (IsS : nat -> list exp) : Prop := mk_glu_views_self
  { (** Each view's uniform arguments are its [IsS] instance with the
        members sent to the group's own type formers ([grp_sb]) *)
    glu_views_self_link : forall mp, ind_mpath D 0 = Some mp ->
      forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)
    (** Each instance argument is glued at the container's uniform
        telescope at its instances over the members as variables *)
  ; glu_views_self_is : forall k Mk qc k' Is vm Dq j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> List.nth_error (IsS k) j = Some I ->
      List.nth_error (tele_insts (ind_uparams Dq) Id (IsS k)) j = Some T ->
      glu_rel_exp_under_sub (grp_selfs_ctx D) I T
    (** Each record view's instance is its [IsS] instance with the members
        sent to the group's own type formers *)
  ; glu_views_self_record_link : forall mp, ind_mpath D 0 = Some mp ->
      forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)
    (** Each record view's instance argument is glued at the record's
        parameters at its instances over the members as variables *)
  ; glu_views_self_record_instances : forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      record_lookup gc_deps gc_stack qr = Some R -> List.nth_error (IsS k) j = Some I ->
      List.nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
      glu_rel_exp_under_sub (grp_selfs_ctx D) I T
    (** Each record view's record is glued: the local counterpart of
        completeness' [valid_group_records] *)
  ; glu_views_self_records : forall k Mk qr Is fl R, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      record_lookup gc_deps gc_stack qr = Some R -> glu_record_decl R }.

(** A group glued: the judgments of its typing, read in the gluing model
    (see the section header). *)
Record glu_ind_decl (D : ind_decl) : Prop := mk_glu_ind_decl
{ (** Each member's parameters are a context glued with its types *)
  glu_ind_decl_params : forall k Mk, ind_member D k = Some Mk -> glu_rel_ctx_types (im_params D Mk)
(** The sort's level is a level glued at its instances over the uniform
    parameters *)
; glu_ind_decl_lvl : exists n, glu_rel_exp_under_sub (ind_uparams D) (ind_sort_lvl (ind_sort D)) (Level@n)
(** And over each member's parameters *)
; glu_ind_decl_lvlP : forall k Mk, ind_member D k = Some Mk ->
    exists n, glu_rel_exp_under_sub (im_params D Mk) (ind_sort_lvl (ind_sort D))[wk_shiftn (im_nn Mk)]ʷ (Level@n)
(** Each non-uniform parameter is a type of the sort glued at its
    instances, over those before it *)
; glu_ind_decl_nparams : forall k Mk j κ A, ind_member D k = Some Mk -> List.nth_error (List.rev (im_nparams Mk)) j = Some (ce_ass κ A) ->
    glu_rel_exp_under_sub (nparams_prefix Mk j ++ ind_uparams D) A (ind_sort D)[wk_shiftn j]ʷ
(** Each non-recursive argument is a type of the sort of its kind next to
    the group's sort glued at its instances, over the non-recursive
    arguments before it *)
; glu_ind_decl_arg : forall k Mk c gs j r A, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.nth_error (cargs_nonrec gs) j = Some A -> List.nth_error (cargs_nonrec_kinds gs) j = Some r ->
    glu_rel_exp_under_sub (nonrec_args_prefix gs j ++ im_params D Mk) A (abs_kind_sort r (ind_sort D)[wk_shiftn (j + im_nn Mk)]ʷ)
(** Each parameter of a recursive argument's shape is glued at its
    instances at its member's telescope *)
; glu_ind_decl_rec_field : forall k Mk c gs gs1 t gs2 Mj m P T, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
    List.nth_error (ptyp_ps t) m = Some P ->
    List.nth_error (tele_insts (im_nparams Mj)
                      (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (ptyp_ps t)) m
      = Some T ->
    glu_rel_exp_under_sub (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk) P T
(** The domains of a recursive argument's shape, each over those before
    it, are types of the sort glued at their instances. *)
; glu_ind_decl_dom : forall k Mk c gs gs1 t gs2 j B, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
    glu_rel_exp_under_sub (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
      B (ind_sort D)[wk_shiftn (j + List.length (cargs_nonrec gs1) + im_nn Mk)]ʷ
(** The contexts of a shape's domains are glued with their types *)
; glu_ind_decl_dctx : forall k Mk c gs gs1 t gs2 j, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
    glu_rel_ctx_types (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
(** The uniform arguments of a view's container, each at the instance of
    the container's telescope, over the group's members as variables. *)
; glu_ind_decl_view_self : exists IsS, glu_views_self D IsS
}.

End Fixed_GCtx.

(** ** Sound Embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, its
    declarations glue there, and so does a member of one of its stored
    bodies that is an axiom or an abstract definition, at its stored type. *)
Record glu_gctx_embedding (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { (** It grows into the target *)
    glu_gctx_embedding_embedding : gctx_embedding Θ1 Ξ1 Θ2 Ξ2
    (** Each of its groups is glued at the target *)
  ; glu_gctx_embedding_ind_field : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @glu_ind_decl (gc_mk Θ2 Ξ2) D
    (** Each of its records is glued at the target *)
  ; glu_gctx_embedding_record_field : forall p R, record_lookup Θ1 Ξ1 p = Some R -> @glu_record_decl (gc_mk Θ2 Ξ2) R
    (** An axiom or an abstract definition of a stored body glues at its
        stored type *)
  ; glu_gctx_embedding_glob : forall p T Φ x Φ0 b pv r A oM Γ,
      loc Θ1 Ξ1 p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv r A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem (qname_mod p) x) A
    (** The body of a definition of a stored body glues at its stored type,
        in the empty context: the value a member with a δ-reduct is read
        off ([eval_sel_global]) *)
  ; glu_gctx_embedding_body : forall p T Φ x Φ0 E A M,
      loc Θ1 Ξ1 p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
      entry_tm E = Some (A, M) ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ M A
    (** An alias module stored at a path of the source is glued over no
        context at the target: the closure a global alias submodule is
        selected as ([eval_selm_global_alias]) *)
  ; glu_gctx_embedding_alias : forall p U,
      gc_module Θ1 Ξ1 p = Some (mr_alias U) -> @glu_unit_at (gc_mk Θ2 Ξ2) ⋅ U
    (** The telescope of a module stored at a path of the source is a
        context glued with its types at the target: the types of the
        parameters a global module value lacks *)
  ; glu_gctx_embedding_tele : forall p T Φ,
      gc_loc Θ1 Ξ1 p = Some (T, Φ) -> @glu_rel_ctx_types (gc_mk Θ2 Ξ2) T
  }.

(** ** The Gluing Judgments

    A gluing judgment is stated at a global context [Θ ⍮ Ξ] and holds at
    every global context [Θ2 ⍮ Ξ2] that [Θ ⍮ Ξ] embeds into soundly
    ([glu_gctx_embedding]), as the gluing relation read there.  The model is unary, so
    there are three judgments: a context glues, a term glues at its type,
    and a universe is one.  Of the other judgments (equality, subtyping,
    extensions, units and module expressions), soundness states that their
    context glues. *)

(** A universe at one target, as its two cases: large, or small at a level
    that glues at every instance. *)
Record glu_is_univ_at (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop := mk_glu_is_univ_at
  { (** The context glues with its variables' types *)
    glu_is_univ_at_ctx : @glu_rel_ctx_types (gc_mk Θ2 Ξ2) Γ
    (** A large universe, or a small one at a level glued at its
        instances *)
  ; glu_is_univ_at_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @glu_rel_exp_under_sub (gc_mk Θ2 Ξ2) Γ L (Level@n)) }.

Arguments glu_is_univ_at_ctx {Θ2 Ξ2 Γ U}.
Arguments glu_is_univ_at_univ {Θ2 Ξ2 Γ U}.

(** A context glues with its variables' types, at every sound
    embedding. *)
Definition glu_ctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> @glu_rel_ctx_types (gc_mk Θ2 Ξ2) Γ.

(** A term glues at each of its instances, at every sound embedding. *)
Definition glu_exp Θ Ξ Γ A M : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> @glu_rel_exp_under_sub (gc_mk Θ2 Ξ2) Γ M A.

Definition glu_is_univ Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> glu_is_univ_at Θ2 Ξ2 Γ U.

(** A unit glues at each of its instances, at every sound embedding. *)
Definition glu_unit Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> @glu_rel_unit_under_sub (gc_mk Θ2 Ξ2) Γ U.

(** A module expression glues at each of its instances, at every sound
    embedding. *)
Definition glu_modexp Θ Ξ Γ H : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> @glu_rel_modexp_under_sub (gc_mk Θ2 Ξ2) Γ H.

(** An extension glues at each instance of its context, at every sound
    embedding. *)
Definition glu_ext Θ Ξ Γ Ψ : Prop :=
  forall Θ2 Ξ2, glu_gctx_embedding Θ Ξ Θ2 Ξ2 -> @glu_rel_ext_under_sub (gc_mk Θ2 Ξ2) Γ Ψ.

(** A unit equation glues: its context glues with its variables' types,
    and each of its units glues at the instances of the context.  It has no
    notation: [Θ ⍮ Ξ ⍮ Γ ⊩ᵘ U ≈ U'] would extend the notation
    [Θ ⍮ Ξ ⍮ Γ ⊩ᵘ U] of [glu_unit] past its end, which the parser does not
    accept beside it. *)
Record glu_unit_eq (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U U' : gunit) : Prop := mk_glu_unit_eq
  { (** The context glues *)
    glu_unit_eq_ctx : glu_ctx Θ Ξ Γ
    (** The left unit glues at the instances *)
  ; glu_unit_eq_left : glu_unit Θ Ξ Γ U
    (** The right unit glues at the instances *)
  ; glu_unit_eq_right : glu_unit Θ Ξ Γ U' }.

Notation "⊩ Θ ⍮ Ξ ⍮ Γ" := (glu_ctx Θ Ξ Γ)
  (at level 70, Θ at next level, Ξ at level 69, Γ at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ M : A" := (glu_exp Θ Ξ Γ A M)
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U" := (glu_is_univ Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ᵘ U" := (glu_unit Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ" := (glu_ext Θ Ξ Γ Ψ)
  (at level 70, Ξ at level 69, Γ at level 69, Ψ at level 69) : type_scope.