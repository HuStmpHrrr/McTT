From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER.
From Mctt.Core.Semantic.Inductives Require Export IndPER.
From Mctt.Core.Semantic Require Export RecordPER.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic.Levels Require Import Levels LevelEq.
From Mctt.Core.Syntactic.System.Global Require Import Presup Paths.
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
    the large universe of the tier, [Typeω@(ulvl i)]: [Typeω@i] in the large
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
    since no rule moves an equation down a universe. *)
Definition level_glu_typ_pred (n : nat) (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ Level@n : U.
#[global] Arguments level_glu_typ_pred n U Γ A/.

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
    own sort ([la_ws]).  The atoms' sorts are read off the types of the
    neutrals, and this is what makes them reliable: the equations of a
    canonical form drop an atom by absorption, which needs it typed at its
    sort. *)
Definition nf_lvl_ws (n : nat) (Δ : ctx) (L : nf) : Prop :=
  match L with
  | nf_lvl c xs => fst c <= n /\ @la_ws gc_deps gc_stack n Δ xs
  | _ => False
  end.

(** The sort is a parameter: the readback of a level value is the same at
    every sort, but the equation it satisfies is at the type the level was
    given, [Level@n]. *)
Definition glu_lvl (n : nat) (Γ : ctx) (M : exp) (m : domain) : Prop :=
  forall Δ φ L, Δ ⊢ᵏ φ : Γ -> Rnf ⇓ Levelᵈ m in length Δ ↘ L ->
    Δ ⊢ M[φ]ʷ ≈ L : Level@n /\ nf_lvl_ws n Δ L.

Record level_glu_exp (n : nat) (U : typ) (Γ : ctx) (A : typ) (M : exp) (m : domain) : Prop := mk_level_glu_exp
  { level_glu_exp_typ : Γ ⊢ A ≈ Level@n : U
  ; level_glu_exp_per : Dom m ≈ m ∈ per_lvl_at n
  ; level_glu_exp_lvl : glu_lvl n Γ M m }.

Definition level_glu_exp_pred (n : nat) (U : typ) : glu_exp_pred := level_glu_exp n U.

Definition True_glu_typ_pred (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊤ : U.
#[global] Arguments True_glu_typ_pred U Γ A/.

(** A term of type [⊤] is glued to every value: by η, all its terms are
    equal to [⋆], which is what every value reads back as. *)
Definition True_glu_exp_pred (U : typ) : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® True_glu_typ_pred U /\ Γ ⊢ M : ⊤.
#[global] Arguments True_glu_exp_pred U Γ A M m/.

(** [⊥] has no canonical values, so its gluing is that of its neutrals. *)
Inductive False_glu_elem : ctx -> exp -> domain -> Prop :=
| False_glu_elem_neut :
  `{ per_bot m m ->
     (forall {Δ φ M'}, Δ ⊢ᵏ φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : ⊥) ->
     False_glu_elem Γ M ⇑ a m }.

Hint Constructors False_glu_elem : mctt.

Definition False_glu_typ_pred (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊥ : U.
#[global] Arguments False_glu_typ_pred U Γ A/.

Definition False_glu_exp_pred (U : typ) : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® False_glu_typ_pred U /\ False_glu_elem Γ M m.
#[global] Arguments False_glu_exp_pred U Γ A M m/.

Definition neut_glu_typ_pred (U : typ) a : glu_typ_pred :=
  fun Γ A => Γ ⊢ A : U /\
            (forall Δ φ A', Δ ⊢ᵏ φ : Γ -> Rne a in length Δ ↘ A' -> Δ ⊢ A[φ]ʷ ≈ A' : U).
#[global] Arguments neut_glu_typ_pred U a Γ A/.

Variant neut_glu_exp_pred (U : typ) a : glu_exp_pred :=
| mk_neut_glu_exp_pred :
  `{ Γ ⊢ A ® neut_glu_typ_pred U a ->
     Γ ⊢ M : A ->
     Dom m ≈ m ∈ per_bot ->
     (forall Δ φ M', Δ ⊢ᵏ φ : Γ ->
                   Rne m in length Δ ↘ M' ->
                   Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) ->
     Γ ⊢ M : A ® ⇑ b m ∈ neut_glu_exp_pred U a }.

Variant pi_glu_typ_pred (U : typ)
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (OP : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_typ_pred) : glu_typ_pred :=
| mk_pi_glu_typ_pred :
  `{ Γ ⊢ A ≈ Π IT OT : U ->
     Γ ⊢ IT : U ->
     Γ ▹ IT ⊢ OT : U ->
     (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ M m,
         Δ ⊢ᵏ φ : Γ ->
         Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl ->
         forall (equiv_m : Dom m ≈ m ∈ IR),
           Δ ⊢ OT[(ι φ),,M] ® OP _ equiv_m) ->
     Γ ⊢ A ® pi_glu_typ_pred U IR IP IEl OP }.

Variant pi_glu_exp_pred (U : typ)
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (elem_rel : relation domain)
  (OEl : forall c (equiv_c : Dom c ≈ c ∈ IR), glu_exp_pred): glu_exp_pred :=
| mk_pi_glu_exp_pred :
  `{ Γ ⊢ M : A ->
     Dom m ≈ m ∈ elem_rel ->
     Γ ⊢ A ≈ Π IT OT : U ->
     Γ ⊢ IT : U ->
     Γ ▹ IT ⊢ OT : U ->
     (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® IP) ->
     (forall Δ φ N n,
         Δ ⊢ᵏ φ : Γ ->
         Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl ->
         forall (equiv_n : Dom n ≈ n ∈ IR),
         exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl _ equiv_n) ->
     Γ ⊢ M : A ® m ∈ pi_glu_exp_pred U IR IP IEl elem_rel OEl }.

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
    by the position and the values before it). *)
Definition exps_eq_at (Δ : ctx) (T : ctx) (Xs Ys : list exp) : Prop :=
  List.length Xs = List.length Ys /\
  forall k X Y A, List.nth_error Xs k = Some X -> List.nth_error Ys k = Some Y ->
    List.nth_error (tele_insts T Id Xs) k = Some A -> Δ ⊢ X ≈ Y : A.

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
    (** At every weakening, equal to the readback of the values *)
  ; glu_params_top_read : forall Δ φ Ms, Δ ⊢ᵏ φ : Γ -> Rps as' at List.rev (im_params Dh Mh) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms ->
      exps_eq_at Δ (im_params Dh Mh) (List.map (fun P => P[φ]ʷ) Ps) (List.map nf_to_exp Ms) }.

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
    [DR], the rest of the type is the one of the rest of the shape. *)
Fixpoint glu_shape_typ (DR : list domain -> exp -> relation domain) (DP : list domain -> exp -> glu_typ_pred)
    (DEl : list domain -> exp -> glu_exp_pred) (Γ : ctx) (pre : list domain) (t : ptyp) (T : typ) {struct t} : Prop :=
  match t with
  | pt_pi B t' => forall IT OT, T = a_pi IT OT ->
      (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP pre B) /\
      (forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> DR pre B c c -> Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B ->
         glu_shape_typ DR DP DEl Δ (pre ++ c :: nil) t' OT[(ι φ),,b])
  | _ => True
  end.

(** The types of the telescopes of the members of a group at its uniform
    parameters [Us], glued at the gluings of the clause, member by member:
    a non-uniform parameter's at the non-uniform parameters before it,
    glued, and a non-recursive argument's at all the non-uniform parameters
    and the non-recursive arguments before it, glued.  They are what moves
    an element to a lower universe (the third part of cumulativity), as the
    domain and the codomains do for a [Π]. *)
Record ind_glu_comps (p : qname) (D : ind_decl) (ups : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) : Prop := mk_ind_glu_comps
  { (** A non-uniform parameter's type, after glued ones before it *)
    ind_glu_comps_nparams : forall m Mm k Ns ns T, ind_member D m = Some Mm -> List.length ns = k -> k < im_nn Mm ->
     List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
     (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
        List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
        List.nth_error ns j = Some n -> Γ ⊢ N : T' ® n ∈ NEl m j (List.firstn j ns)) ->
     tele_prefix_rel (canon_nparams_rel D ups m) k ns ns -> Γ ⊢ T ® NP m k ns
    (** A non-recursive argument's type, after glued ones before it *)
  ; ind_glu_comps_args : forall m Mm c gs gs1 A0 gs2 Ns ns As vs T, ind_member D m = Some Mm ->
     ind_con Mm c = Some gs -> gs = gs1 ++ ca_arg A0 :: gs2 ->
     glu_nparams m Mm NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
       (nonrec_arg_vals gs1 vs) ->
     Γ ⊢ T ® AP m ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
    (** A recursive argument's type, along its shape *)
  ; ind_glu_comps_recs : forall m Mm c gs gs1 t gs2 Ns ns As vs T, ind_member D m = Some Mm ->
     ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
     glu_nparams m Mm NEl Γ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)
       (nonrec_arg_vals gs1 vs) ->
     glu_shape_typ (canon_doms_rel ups m) (DP m) (DEl m) Γ (ns ++ nonrec_arg_vals gs1 vs) t T }.

(** A type of the declared member [Mk] (the member [k]) of a group at its
    parameters, at syntactic parameters [Ps]: glued to the values by their
    readback, its sort in the universe of the gluing, and the telescopes'
    types of every member glued, at every instance of the parameters equal
    to the given ones: two types of the same member at the same values may
    have different syntactic parameters, and lowering an element of one to
    a smaller universe needs the components at the parameters of the
    other. *)
Definition ind_typ_at (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (U : typ) (Γ : ctx) (A : typ) (Ps : list exp) : Prop :=
  Γ ⊢ A ≈ apps (a_ind p k) Ps : U /\
  forall Δ φ, Δ ⊢ᵏ φ : Γ ->
    glu_params_top D Mk Δ (List.map (fun P => P[φ]ʷ) Ps) (ups ++ ns) /\
    Δ ⊢ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)] ⊆ U /\
    forall Ps', exps_eq_at Δ (im_params D Mk) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ (List.firstn (ind_nu D) Ps').

(** The type predicate of the member [k]: a type at some syntactic
    parameters ([ind_typ_at]). *)
Definition ind_glu_typ_pred (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
    (k : nat) (Mk : imember) (U : typ) : glu_typ_pred :=
  fun Γ A => exists Ps, ind_typ_at p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A Ps.
#[global] Arguments ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k Mk U Γ A/.

Section GluInd.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).

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
      every instance related to the values they evaluate to, so that
      [ind_glu_elem] does not depend on the representative [ups] of the
      uniform parameters.  A recursive argument is an element at every
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
  (** A constructor of the member, at glued parameters and arguments *)
  | ind_glu_elem_con :
    `{ ind_member D k = Some Mk ->
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
       (forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Γ ⊢ N : A ® v ∈ AEl k (List.skipn (im_unu D Mk) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))) ->
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D Mk gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec k Γ Us (List.skipn (im_unu D Mk) bs ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs)) t A N v) ->
       ind_glu_elem k Γ Us Ns M (d_con hd k' c (bs ++ vs)) }
  (** A neutral of the member, equal to its readback at every weakening *)
  | ind_glu_elem_neut :
    `{ ind_member D k = Some Mk ->
       im_ref p k Mk = (hd, k') ->
       per_bot m m ->
       (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
          Δ ⊢ M[φ]ʷ ≈ M' : (im_ty_at p k Mk Us Ns)[φ]ʷ) ->
       ind_glu_elem k Γ Us Ns M (⇑ (d_ind hd k' as') m) }
  (** A recursive argument [N] of type [A] and shape [t] of a constructor
      of the member [k], at the group's uniform parameters [Us], after the
      values [pre] of the shape's components (the uniform parameters left
      out).  At the end of the shape, the member [j] it ends in at the
      values [bsr] of the shape's parameters: [A] is the member's type at
      [Us] and parameters [Q], which are glued to [bsr], and all the
      parameters [Us ++ Q] are glued to [ups ++ bsr] at the telescope of the
      group's own member [j], as readback reads them ([read_shape_self],
      [read_nf_con_view]): at a view, not at the container's, whose uniform
      parameters [Is] evaluated at two readback-equal [ups] need not read
      back alike. *)
  with glu_rec : nat -> ctx -> list exp -> list domain -> ptyp -> typ -> exp -> domain -> Prop :=
  (** At the end: an element of the member [j] at glued parameters, at
      every weakening and every equal instance *)
  | glu_rec_self :
    `{ ind_member D j = Some Mj ->
       (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr ->
          A = im_ty_at p j Mj Us Q ->
          List.length Q = im_nn Mj /\ tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bsr bsr /\
          (forall bsr', tele_rel (canon_nparams_rel D ups j) (List.rev (im_nparams Mj)) bsr bsr' ->
             glu_nparams j Mj NEl Γ Us Q bsr' /\
             forall Δ φ, Δ ⊢ᵏ φ : Γ ->
               glu_params_top D Mj Δ (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (ups ++ bsr'))) ->
       (forall bsr Q, ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ bsr ->
          A = im_ty_at p j Mj Us Q ->
          forall Δ φ Us' Q', Δ ⊢ᵏ φ : Γ -> List.length Us' = ind_nu D ->
            exps_eq_at Δ (im_params D Mj) (List.map (fun P => P[φ]ʷ) (Us ++ Q)) (Us' ++ Q') ->
            ind_glu_elem j Δ Us' Q' N[φ]ʷ v) ->
       glu_rec k Γ Us pre (pt_self j Ps) A N v }
  (** At a domain: a function whose domain is glued, and whose
      applications to glued elements are recursive arguments of the rest *)
  | glu_rec_pi :
    `{ (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP k pre B) ->
       (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> canon_doms_rel ups k pre B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
       (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> canon_doms_rel ups k pre B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl k pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
          glu_rec k Δ (List.map (fun U => U[φ]ʷ) Us) (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
       glu_rec k Γ Us pre (pt_pi B t) A N v }.
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
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
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
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
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
    (** At every weakening, equal to the readback of the values *)
  ; params_glu_read : forall Δ φ Ms, Δ ⊢ᵏ φ : Γ -> Rps ps at List.rev T in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms ->
      exps_eq_at Δ T (List.map (fun P => P[φ]ʷ) Ps) (List.map nf_to_exp Ms) }.

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
  ; suniv_glu_exp_read : forall Δ φ W, Δ ⊢ᵏ φ : Γ -> Rtyp m in length Δ ↘ W -> Δ ⊢ M[φ]ʷ ≈ W : A[φ]ʷ }.

Definition suniv_glu_exp_pred' (U : typ) (l : domain) (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
  suniv_glu_exp U l univ_typ.

Hint Constructors level_glu_exp suniv_glu_typ univ_glu_exp suniv_glu_exp : mctt.
(** The automation builds them like the existentials they replace.  The
    hint has no pattern: a pattern headed by one of these definitions is not
    found by the hint database, which unfolds it. *)
Hint Extern 1 =>
  match goal with
  | |- level_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_typ_pred _ _ _ _ => econstructor
  | |- univ_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  end : mctt.

Section Gluing.
  Variable
    (i : uidx)
      (glu_univ_typ_rec : uidx -> domain -> glu_typ_pred).

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : uidx_lt (ul j) i),
          typ_rel <∙> univ_glu_typ_pred j (Typeω@(ulvl i)) ->
          el_rel <∙> univ_glu_exp_pred' (Typeω@(ulvl i)) j (glu_univ_typ_rec (ul j)) ->
          DG 𝕌ω@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_suniv :
    `{ forall typ_rel
         el_rel
         (lt_j_i : uidx_lt (us (dlvl_real l)) i),
          Dom l ≈ l ∈ per_lvl ->
          typ_rel <∙> suniv_glu_typ_pred l (Typeω@(ulvl i)) ->
          el_rel <∙> suniv_glu_exp_pred' (Typeω@(ulvl i)) l (glu_univ_typ_rec (us (dlvl_real l))) ->
          DG 𝕌@l ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_level :
    `{ forall typ_rel el_rel,
          typ_rel <∙> level_glu_typ_pred n (Typeω@(ulvl i)) ->
          el_rel <∙> level_glu_exp_pred n (Typeω@(ulvl i)) ->
          DG Levelᵈ@n ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_True :
    `{ forall typ_rel el_rel,
          typ_rel <∙> True_glu_typ_pred (Typeω@(ulvl i)) ->
          el_rel <∙> True_glu_exp_pred (Typeω@(ulvl i)) ->
          DG ⊤ᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_False :
    `{ forall typ_rel el_rel,
          typ_rel <∙> False_glu_typ_pred (Typeω@(ulvl i)) ->
          el_rel <∙> False_glu_exp_pred (Typeω@(ulvl i)) ->
          DG ⊥ᵈ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

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
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c) ->
          DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          typ_rel <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl ->
          DG Πᵈ a ρ B ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          Dom b ≈ b ∈ per_bot ->
          typ_rel <∙> neut_glu_typ_pred (Typeω@(ulvl i)) b ->
          el_rel <∙> neut_glu_exp_pred (Typeω@(ulvl i)) b ->
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
         (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
         typ_rel el_rel (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          grp_tele_ass D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall m Mm j A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
          (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
          (forall m Mm j A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ NP m j vs ↘ NEl m j vs) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ AP m ms c j vs ↘ AEl m ms c j vs) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
             exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ DP m (ms ++ ws ++ ys) B ↘ DEl m (ms ++ ws ++ ys) B) ->
          typ_rel <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k M (Typeω@(ulvl i)) ->
          el_rel <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k M elem_rel (Typeω@(ulvl i)) ->
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
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> exists b, ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ FP k vs ↘ FEl k vs) ->
          typ_rel <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(ulvl i)) ->
          el_rel <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(ulvl i)) ->
          DG d_record p ns ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }.
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
  : uidx -> domain -> glu_typ_pred :=
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

Definition glu_univ_rec_s (j : o2) : uidx -> domain -> glu_typ_pred :=
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

Definition glu_univ_below (u : uidx) : uidx -> domain -> glu_typ_pred :=
  match u with
  | us j => glu_univ_rec_s j
  | ul n => fun v => match v with us k => glu_suniv k | ul k => glu_univ_below_l n k end
  end.

Definition glu_univ_elem (i : uidx) : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  glu_univ_elem_core i (glu_univ_below i).
#[global] Arguments glu_univ_elem : simpl never.

Lemma glu_univ_elem_equation_1 : forall i,
    glu_univ_elem i = glu_univ_elem_core i (glu_univ_below i).
Proof. reflexivity. Qed.

Hint Rewrite glu_univ_elem_equation_1 : glu_univ_elem.

Definition glu_univ_typ (i : uidx) (a : domain) : glu_typ_pred := glu_typ_at (glu_univ_elem i) a.

Hint Constructors glu_typ_at : mctt.
Hint Extern 1 => match goal with |- glu_univ_typ _ _ _ _ => econstructor end : mctt.

Lemma glu_univ_below_spec : forall i j,
    uidx_lt j i ->
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
    unfold olt in Hlt; cbn [fst snd] in Hlt.
    destruct (Nat.ltb_spec a' a) as [Ha | Ha].
    + rewrite Htiers by exact Ha; apply Htier.
    + destruct (Nat.eqb_spec a' a) as [-> | Hne]; [| lia ].
      rewrite Hin by lia; apply Htier.
  - reflexivity.
  - apply Hl; assumption.
Qed.

Definition univ_glu_exp_pred j (U : typ) : glu_exp_pred := univ_glu_exp_pred' U j (glu_univ_typ j).

Definition suniv_glu_exp_pred (l : domain) (U : typ) : glu_exp_pred :=
  suniv_glu_exp_pred' U l (glu_univ_typ (us (dlvl_real l))).

Hint Extern 1 =>
  match goal with
  | |- univ_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred _ _ _ _ _ _ => econstructor
  end : mctt.

(** The two tiers' universe predicates, at an index: the predicates of the
    universe [ulvl_val u], which is [𝕌ω@j] in the large tier and the small
    universe at the literal level [n] in the small one.  Stating them by cases
    lets the gluing of the universe at an index be stated once for both
    tiers ([glu_univ_elem_univ_at]). *)
Definition univ_glu_typ_pred_at (u : uidx) (U : typ) : glu_typ_pred :=
  match u with
  | us n => suniv_glu_typ_pred (dlvl_lit n) U
  | ul j => univ_glu_typ_pred j U
  end.

Definition univ_glu_exp_pred_at (u : uidx) (U : typ) : glu_exp_pred :=
  match u with
  | us n => suniv_glu_exp_pred (dlvl_lit n) U
  | ul j => univ_glu_exp_pred j U
  end.

Section GluingInduction.
  Hypothesis
    (motive : uidx -> glu_typ_pred -> glu_exp_pred -> domain -> Prop)

      (case_univ :
        forall i j
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : uidx_lt (ul j) i),
          (forall P' El' a, DG a ∈ glu_univ_elem j ↘ P' ↘ El' -> motive j P' El' a) ->
          P <∙> univ_glu_typ_pred j (Typeω@(ulvl i)) ->
          El <∙> univ_glu_exp_pred j (Typeω@(ulvl i)) ->
          motive i P El 𝕌ω@j)

      (case_suniv :
        forall i l
          (P : glu_typ_pred) (El : glu_exp_pred) (lt_j_i : uidx_lt (us (dlvl_real l)) i),
          Dom l ≈ l ∈ per_lvl ->
          (forall P' El' a, DG a ∈ glu_univ_elem (us (dlvl_real l)) ↘ P' ↘ El' ->
                            motive (us (dlvl_real l)) P' El' a) ->
          P <∙> suniv_glu_typ_pred l (Typeω@(ulvl i)) ->
          El <∙> suniv_glu_exp_pred l (Typeω@(ulvl i)) ->
          motive i P El 𝕌@l)

      (case_level :
        forall i n (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> level_glu_typ_pred n (Typeω@(ulvl i)) ->
          El <∙> level_glu_exp_pred n (Typeω@(ulvl i)) ->
          motive i P El (Levelᵈ@n))

      (case_True :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> True_glu_typ_pred (Typeω@(ulvl i)) ->
          El <∙> True_glu_exp_pred (Typeω@(ulvl i)) ->
          motive i P El ⊤ᵈ)

      (case_False :
        forall i (P : glu_typ_pred) (El : glu_exp_pred),
          P <∙> False_glu_typ_pred (Typeω@(ulvl i)) ->
          El <∙> False_glu_exp_pred (Typeω@(ulvl i)) ->
          motive i P El ⊥ᵈ)

      (case_pi :
        forall i a B (ρ : env) (in_rel : relation domain) (IP : glu_typ_pred)
          (IEl : glu_exp_pred) (OP : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_typ_pred)
          (OEl : forall c : domain, Dom c ≈ c ∈ in_rel -> glu_exp_pred) (P : glu_typ_pred) (El : glu_exp_pred)
          (elem_rel : relation domain),
          DG a ∈ glu_univ_elem i ↘ IP ↘ IEl ->
          motive i IP IEl a ->
          DF a ≈ a ∈ per_univ_elem i ↘ in_rel ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c) ->
          (forall (c : domain) (equiv_c : Dom c ≈ c ∈ in_rel) (b : domain),
              ⟦ B ⟧ ρ ↦ c ↘ b ->
              motive i (OP c equiv_c) (OEl c equiv_c) b) ->
          DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel ->
          P <∙> pi_glu_typ_pred (Typeω@(ulvl i)) in_rel IP IEl OP ->
          El <∙> pi_glu_exp_pred (Typeω@(ulvl i)) in_rel IP IEl elem_rel OEl ->
          motive i P El Πᵈ a ρ B)

      (case_neut :
        forall i b a
          (P : glu_typ_pred)
          (El : glu_exp_pred),
          Dom b ≈ b ∈ per_bot ->
          P <∙> neut_glu_typ_pred (Typeω@(ulvl i)) b ->
          El <∙> neut_glu_exp_pred (Typeω@(ulvl i)) b ->
          motive i P El ⇑ a b)

      (case_indty :
        forall i p D k M pm ups ns (NP : nat -> nat -> list domain -> glu_typ_pred)
          (NEl : nat -> nat -> list domain -> glu_exp_pred)
          (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
          (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
          (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred)
          (P : glu_typ_pred) (El : glu_exp_pred) (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          grp_tele_ass D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall m Mm j A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
          (forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
          (forall m Mm j A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ NP m j vs ↘ NEl m j vs) ->
          (forall m Mm j A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
             tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             motive i (NP m j vs) (NEl m j vs) b) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ AP m ms c j vs ↘ AEl m ms c j vs) ->
          (forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
             tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             motive i (AP m ms c j vs) (AEl m ms c j vs) b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
             exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ DP m (ms ++ ws ++ ys) B ↘ DEl m (ms ++ ws ++ ys) B) ->
          (forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
             tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
             ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) j = Some B ->
             tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             motive i (DP m (ms ++ ws ++ ys) B) (DEl m (ms ++ ws ++ ys) B) b) ->
          P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl k M (Typeω@(ulvl i)) ->
          El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl k M elem_rel (Typeω@(ulvl i)) ->
          motive i P El (d_ind p k (ups ++ ns)))

      (case_record :
        forall i p R ns (FP : nat -> list domain -> glu_typ_pred) (FEl : nat -> list domain -> glu_exp_pred)
          (P : glu_typ_pred) (El : glu_exp_pred) (elem_rel : relation domain),
          record_lookup gc_deps gc_stack p = Some R ->
          DF d_record p ns ≈ d_record p ns ∈ per_univ_elem i ↘ elem_rel ->
          (forall k f T vs, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> exists b, ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ FP k vs ↘ FEl k vs) ->
          (forall k f T vs b, List.nth_error (record_fields R) k = Some (f, T) ->
             tele_prefix_rel (canon_fields_rel R ns) k vs vs -> ⟦ T ⟧ env_args nil (ns ++ vs) ↘ b ->
             motive i (FP k vs) (FEl k vs) b) ->
          P <∙> record_glu_typ_pred p R ns FP FEl (Typeω@(ulvl i)) ->
          El <∙> record_glu_exp_pred p R ns FP FEl elem_rel (Typeω@(ulvl i)) ->
          motive i P El (d_record p ns))
  .

  Lemma glu_univ_elem_ind i P El a
    (H : glu_univ_elem i P El a) : motive i P El a.
  Proof.
    revert P El a H.
    induction i as [i IHi] using (well_founded_ind uidx_wf).
    intros P El a H.
    induction H.
    - rewrite glu_univ_below_spec in * by assumption.
      eapply case_univ; eauto.
    - rewrite glu_univ_below_spec in * by assumption.
      eapply case_suniv; eauto.
    - eapply case_level; eassumption.
    - eapply case_True; eassumption.
    - eapply case_False; eassumption.
    - eapply case_pi; eassumption.
    - eapply case_neut; eassumption.
    - eapply case_indty; eassumption.
    - eapply case_record; eassumption.
  Qed.
End GluingInduction.

#[warnings="-cannot-define-projection"]
Record glu_elem_bot i a Γ A M m : Prop := glu_elem_bot_make
  { P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_elem_bot_wf : Γ ⊢ M : A
  ; glu_elem_bot_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_elem_bot_typ : Γ ⊢ A ® P
  ; glu_elem_bot_per : Dom m ≈ m ∈ per_bot
  ; glu_elem_bot_read : forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ }.
Hint Constructors glu_elem_bot : mctt.

#[warnings="-cannot-define-projection"]
Record glu_elem_top i a Γ A M m : Prop := glu_elem_top_make
  { P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_elem_top_wf : Γ ⊢ M : A
  ; glu_elem_top_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_elem_top_typ : Γ ⊢ A ® P
  ; glu_elem_top_per : Dom ⇓ a m ≈ ⇓ a m ∈ per_top
  ; glu_elem_top_read : forall Δ φ w, Δ ⊢ᵏ φ : Γ -> Rnf ⇓ a m in length Δ ↘ w -> Δ ⊢ M[φ]ʷ ≈ w : A[φ]ʷ }.
Hint Constructors glu_elem_top : mctt.

Record glu_typ_top (i : uidx) a Γ A : Prop := glu_typ_top_make
  { glu_typ_top_wf : Γ ⊢ A : Typeω@(ulvl i)
  ; glu_typ_top_per : Dom a ≈ a ∈ per_top_typ
  ; glu_typ_top_read : forall Δ φ A', Δ ⊢ᵏ φ : Γ -> Rtyp a in length Δ ↘ A' -> Δ ⊢ A[φ]ʷ ≈ A' : Typeω@(ulvl i) }.
Hint Constructors glu_typ_top : mctt.

#[warnings="-cannot-define-projection"]
Record glu_rel_typ_with_sub (i : nat) Δ A σ ρ : Prop := mk_glu_rel_typ_with_sub
  { a : domain
  ; P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_rel_typ_with_sub_eval : ⟦ A ⟧ ρ ↘ a
  ; glu_rel_typ_with_sub_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_rel_typ_with_sub_typ : Δ ⊢ A[σ] ® P }.

#[warnings="-cannot-define-projection"]
Record glu_rel_exp_with_sub (i : nat) Δ M A σ ρ : Prop := mk_glu_rel_exp_with_sub
  { a : domain
  ; m : domain
  ; P : glu_typ_pred
  ; El : glu_exp_pred
  ; glu_rel_exp_with_sub_eval_typ : ⟦ A ⟧ ρ ↘ a
  ; glu_rel_exp_with_sub_eval : ⟦ M ⟧ ρ ↘ m
  ; glu_rel_exp_with_sub_univ : DG a ∈ glu_univ_elem i ↘ P ↘ El
  ; glu_rel_exp_with_sub_exp : Δ ⊢ M[σ] : A[σ] ® m ∈ El }.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => Δ ⊢ˢ σ : ⋅.
#[global] Arguments nil_glu_sub_pred Δ σ ρ/.

(** An assumption entry glues by its head, at the gluing of its type, and
    by its tail.  The parameters come before the relation's own arguments,
    so that the predicate is a [glu_sub_pred]. *)
Variant cons_glu_sub_pred (i : nat) Γ A (TSb : glu_sub_pred) : glu_sub_pred :=
(** The substitution is typed, its head glues at the type's predicate and
    its tail glues by [TSb] *)
| mk_cons_glu_sub_pred :
  `{ forall P El,
        Δ ⊢ˢ σ : Γ ▹ A ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        (** [A[↑]ʷ[σ]] rather than [A[Wk ⨟ σ]]: it is the direct instance of
            [Γ ▹ A ⊢ #0 : A[↑]ʷ] along [σ]. *)
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢ˢ σ ® ρ ∈ cons_glu_sub_pred i Γ A TSb }.

(** A definition entry glues as an assumption entry whose head is also tied
    to the value of the body in the tail ([def_tie]).  The syntactic half of
    the tie is part of [Δ ⊢ˢ σ : Γ ▸ A ≔ M]. *)
Variant cons_def_glu_sub_pred (i : nat) Γ A M (TSb : glu_sub_pred) : glu_sub_pred :=
(** As an assumption's, and the head's value is the body's value in the
    tail *)
| mk_cons_def_glu_sub_pred :
  `{ forall P El,
        Δ ⊢ˢ σ : Γ ▸ A ≔ M ->
        ⟦ A ⟧ ρ↯ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ #0[σ] : A[↑]ʷ[σ] ® (ρ 0) ∈ El ->
        def_tie A M ρ ->
        Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
        Δ ⊢ˢ σ ® ρ ∈ cons_def_glu_sub_pred i Γ A M TSb }.

(** A module slot glues by its syntactic typing and by the tie of its value
    to the closure of its unit over the tail, which is the slot clause of the
    environment PER.  Module values themselves are not glued: their members
    are reached through δ, whose reducts are terms. *)
Variant cons_mod_glu_sub_pred Γ U (TSb : glu_sub_pred) : glu_sub_pred :=
(** The substitution is typed, the head's module is the closure of the
    unit over the tail, and the tail glues by [TSb] *)
| mk_cons_mod_glu_sub_pred :
  `{ Δ ⊢ˢ σ : Γ ▹ₘ U ->
     tie_mod (env_mod ρ 0) (me_lit U) ρ↯ ->
     Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
     Δ ⊢ˢ σ ® ρ ∈ cons_mod_glu_sub_pred Γ U TSb }.

(** A definition with a module part glues as its term part does as a
    definition, and its head's module is tied to the closure of its unit
    over the tail, as a slot's. *)
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
| glu_ctx_env_cons :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Typeω@i ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred i Γ A TSb ->
        EG Γ ▹ A ∈ glu_ctx_env ↘ Sb }
| glu_ctx_env_cons_def :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Typeω@i ->
        Γ ⊢ M : A ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_exp_with_sub i Δ M A σ ρ) ->
        Sb <∙> cons_def_glu_sub_pred i Γ A M TSb ->
        EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb }
| glu_ctx_env_cons_mod :
  `{ forall TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
        Sb <∙> cons_mod_glu_sub_pred Γ U TSb ->
        EG Γ ▹ₘ U ∈ glu_ctx_env ↘ Sb }
(** A definition with a module part: the premises of a definition entry
    and the well-formedness of the unit *)
| glu_ctx_env_cons_dm :
  `{ forall i TSb Sb,
        EG Γ ∈ glu_ctx_env ↘ TSb ->
        Γ ⊢ A : Typeω@i ->
        Γ ⊢ M : A ->
        gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_typ_with_sub i Δ A σ ρ) ->
        (forall Δ σ ρ,
            Δ ⊢ˢ σ ® ρ ∈ TSb ->
            glu_rel_exp_with_sub i Δ M A σ ρ) ->
        Sb <∙> cons_dm_glu_sub_pred i Γ A M U TSb ->
        EG Γ ▸ₘ A ≔ M ‖ U ∈ glu_ctx_env ↘ Sb }.

Definition glu_rel_ctx Γ : Prop := exists Sb, EG Γ ∈ glu_ctx_env ↘ Sb.
#[global] Arguments glu_rel_ctx Γ/.

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

(** There is no gluing judgment for substitutions, so the fundamental theorem
    has two parts. A gluing predicate is indexed by a value, and
    [⟦τ ⨟ σ⟧(ρ) = ⟦τ⟧(⟦σ⟧ρ)] is not an equation when substitution is an
    operation, so such a judgment cannot be stated. Concrete substitutions are
    handled by lemmas about [glu_rel_exp] instead, just as
    [completeness_fundamental] has no substitution part. *)

Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).

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
Hint Constructors False_glu_elem : mctt.
#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mctt.
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
Hint Constructors glu_params_top glu_nparams ind_glu_comps ind_glu_exp : mctt.
(** The automation builds the record-shaped gluing predicates like the
    existentials they replace.  The hint has no pattern: a pattern headed by
    one of these definitions is not found by the database, which unfolds it. *)
#[export]
Hint Extern 1 =>
  match goal with
  | |- level_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_typ_pred _ _ _ _ => econstructor
  | |- univ_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred' _ _ _ _ _ _ _ => econstructor
  | |- univ_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- suniv_glu_exp_pred _ _ _ _ _ _ => econstructor
  | |- glu_univ_typ _ _ _ _ => econstructor
  | |- ind_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => econstructor
  end : mctt.
Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (at level 70, M at level 69, A at level 69).

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
      refine (glu_univ_elem_ind _ _ _ _ _ _ _ _ _ _);
      (** The level case has one binder more than the other closed types: the
          sort of its type of levels. *)
      [ do 5 intro; do 3 glu_induction_hintro | do 5 intro; do 3 glu_induction_hintro
      | do 4 intro; do 2 glu_induction_hintro | do 3 intro; do 2 glu_induction_hintro
      | do 3 intro; do 2 glu_induction_hintro
      | do 12 intro; glu_induction_hintro; ih; do 6 glu_induction_hintro | do 5 intro; do 3 glu_induction_hintro
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

(** The views of a group with its members as variables ([grp_sctx]), as
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
        telescope, over the members as variables *)
  ; glu_views_self_is : forall k Mk qc k' Is vm Dq j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> List.nth_error (IsS k) j = Some I ->
      List.nth_error (tele_insts (ind_uparams Dq) Id (IsS k)) j = Some T ->
      grp_sctx D ⊩ I : T }.

(** A group glued: the judgments of its typing, read in the gluing model
    (see the section header). *)
Record glu_ind_decl (D : ind_decl) : Prop := mk_glu_ind_decl
{ (** Each member's parameters are a glued context *)
  glu_ind_decl_params : forall k Mk, ind_member D k = Some Mk -> ⊩ im_params D Mk
(** The sort's level is a glued level over the uniform parameters *)
; glu_ind_decl_lvl : exists n, ind_uparams D ⊩ ind_sort_lvl (ind_sort D) : Level@n
(** And over each member's parameters *)
; glu_ind_decl_lvlP : forall k Mk, ind_member D k = Some Mk ->
    exists n, im_params D Mk ⊩ (ind_sort_lvl (ind_sort D))[wk_shiftn (im_nn Mk)]ʷ : Level@n
(** Each non-uniform parameter is a glued type of the sort, over those
    before it *)
; glu_ind_decl_npar : forall k Mk j A, ind_member D k = Some Mk -> List.nth_error (List.rev (im_nparams Mk)) j = Some (ce_ass A) ->
    nparams_prefix Mk j ++ ind_uparams D ⊩ A : (ind_sort D)[wk_shiftn j]ʷ
(** Each non-recursive argument is a glued type of the sort, over the
    non-recursive arguments before it *)
; glu_ind_decl_arg : forall k Mk c gs j A, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    List.nth_error (cargs_nonrec gs) j = Some A ->
    nonrec_args_prefix gs j ++ im_params D Mk ⊩ A : (ind_sort D)[wk_shiftn (j + im_nn Mk)]ʷ
(** Each parameter of a recursive argument's shape is glued at its
    member's telescope *)
; glu_ind_decl_rec_field : forall k Mk c gs gs1 t gs2 Mj m P T, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
    List.nth_error (ptyp_ps t) m = Some P ->
    List.nth_error (tele_insts (im_nparams Mj)
                      (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (ptyp_ps t)) m
      = Some T ->
    ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk ⊩ P : T
(** The domains of a recursive argument's shape, each over those before
    it, are types of the sort. *)
; glu_ind_decl_dom : forall k Mk c gs gs1 t gs2 j B, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
    doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
      ⊩ B : (ind_sort D)[wk_shiftn (j + List.length (cargs_nonrec gs1) + im_nn Mk)]ʷ
(** The contexts of a shape's domains are glued *)
; glu_ind_decl_dctx : forall k Mk c gs gs1 t gs2 j, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
    ⊩ doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk
(** The uniform arguments of a view's container, each at the instance of
    the container's telescope, over the group's members as variables. *)
; glu_ind_decl_view_self : exists IsS, glu_views_self D IsS
}.

End Fixed_GCtx.

(** ** Sound Embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, its
    declarations glue there, and so does a member of one of its stored
    bodies that is an axiom or an abstract definition, at its stored type. *)
Record glu_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { glu_emb_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; glu_emb_ind_field : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @glu_ind_decl (gc_mk Θ2 Ξ2) D
  ; glu_emb_glob : forall p T Φ x Φ0 b pv A oM Γ,
      loc Θ1 Ξ1 p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem (qname_mod p) x) A
  }.

(** ** The Gluing Judgments

    A gluing judgment is stated at a global context [Θ ⍮ Ξ] and holds at
    every global context [Θ2 ⍮ Ξ2] that [Θ ⍮ Ξ] embeds into soundly
    ([glu_emb]), as the gluing relation read there.  The model is unary, so
    there are three judgments: a context glues, a term glues at its type,
    and a universe is one.  Of the other judgments (equality, subtyping,
    extensions, units and module expressions), soundness states that their
    context glues. *)

(** A universe at one target, as its two cases: large, or small at a level
    that glues. *)
Record glu_is_univ_at (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop := mk_glu_is_univ_at
  { glu_is_univ_at_ctx : @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ
  ; glu_is_univ_at_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @glu_rel_exp (gc_mk Θ2 Ξ2) Γ L (Level@n)) }.

Arguments glu_is_univ_at_ctx {Θ2 Ξ2 Γ U}.
Arguments glu_is_univ_at_univ {Θ2 Ξ2 Γ U}.

Definition glu_ctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ.

Definition glu_exp Θ Ξ Γ A M : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.

Definition glu_is_univ Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> glu_is_univ_at Θ2 Ξ2 Γ U.

Notation "⊩ Θ ⍮ Ξ ⍮ Γ" := (glu_ctx Θ Ξ Γ)
  (at level 70, Θ at next level, Ξ at level 69, Γ at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ M : A" := (glu_exp Θ Ξ Γ A M)
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U" := (glu_is_univ Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
