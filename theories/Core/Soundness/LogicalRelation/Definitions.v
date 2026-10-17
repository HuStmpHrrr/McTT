From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER IndPER.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic Require Import Levels LevelEq.
From Mctt.Core.Soundness.Weakening Require Export Definitions.

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
    about it are keyed on.  Membership in [per_lvl] is a separate conjunct of
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

Definition level_glu_exp_pred (n : nat) (U : typ) : glu_exp_pred :=
  fun Γ A M m => Γ ⊢ A ® level_glu_typ_pred n U /\ Dom m ≈ m ∈ per_lvl_at n /\ glu_lvl n Γ M m.
#[global] Arguments level_glu_exp_pred n U Γ A M m/.

Definition True_glu_typ_pred (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊤ : U.
#[global] Arguments True_glu_typ_pred U Γ A/.

(** A term of type [⊤] is glued to every value: by η, all its terms are
    equal to [⋆], which is what every value reads back as. *)
Definition True_glu_exp_pred (U : typ) : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® True_glu_typ_pred U /\ Γ ⊢ M : ⊤.
#[global] Arguments True_glu_exp_pred U Γ A M m/.

(** [⊥] has no canonical values, so its gluing is that of its neutrals. *)
Inductive glu_False : ctx -> exp -> domain -> Prop :=
| glu_False_neut :
  `{ per_bot m m ->
     (forall {Δ φ M'}, Δ ⊢ᵏ φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : ⊥) ->
     glu_False Γ M ⇑ a m }.

Hint Constructors glu_False : mctt.

Definition False_glu_typ_pred (U : typ) : glu_typ_pred := fun Γ A => Γ ⊢ A ≈ ⊥ : U.
#[global] Arguments False_glu_typ_pred U Γ A/.

Definition False_glu_exp_pred (U : typ) : glu_exp_pred := fun Γ A M m => Γ ⊢ A ® False_glu_typ_pred U /\ glu_False Γ M m.
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
Definition suniv_glu_typ_pred (l : domain) (U : typ) : glu_typ_pred :=
  fun Γ A => exists t n, glu_lvl n Γ t l /\ Γ ⊢ A ≈ Type⟨t⟩ : U.
#[global] Arguments suniv_glu_typ_pred l U Γ A/.
Transparent suniv_glu_typ_pred.

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

(** The parameters of an inductive type, glued to their values by their
    readback at the declaration's telescope. *)
Definition glu_params_top (D : ind_decl) (Γ : ctx) (Ps : list exp) (as' : list domain) : Prop :=
  List.length Ps = ind_np D /\
  (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some A -> Γ ⊢ P : A) /\
  (forall Δ φ Ms, Δ ⊢ᵏ φ : Γ -> Rps as' at List.rev (ind_params D) in gc_deps ⍮ gc_stack ⍮ nil ⍮ length Δ ↘ Ms ->
     exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Ps) (nfs_to_exps Ms)).

Definition glu_nparams (D : ind_decl) (NEl : nat -> list domain -> glu_exp_pred)
    (Γ : ctx) (Us Ns : list exp) (ns : list domain) : Prop :=
  List.length Ns = ind_nn D /\ List.length ns = ind_nn D /\
  forall k N A n, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some A ->
    List.nth_error ns k = Some n -> Γ ⊢ N : A ® n ∈ NEl k (List.firstn k ns).

(** The type [T] of a recursive argument of shape [t], after the values
    [pre] of the shape's components, glued at the gluings [DP] of the
    shape's domains: at every weakening, its domain is glued at [DP], and
    at an element of the domain glued at [DEl], the rest of the type is the
    one of the rest of the shape. *)
Fixpoint glu_shape_typ (ups : list domain) (DP : list domain -> exp -> glu_typ_pred)
    (DEl : list domain -> exp -> glu_exp_pred) (Γ : ctx) (pre : list domain) (t : ptyp) (T : typ) {struct t} : Prop :=
  match t with
  | pt_pi B t' => forall IT OT, T = a_pi IT OT ->
      (forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP pre B) /\
      (forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> ind_dr ups pre B c c -> Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B ->
         glu_shape_typ ups DP DEl Δ (pre ++ c :: nil) t' OT[(ι φ),,b])
  | _ => True
  end.

(** The types of the telescopes of an inductive type at its uniform
    parameters [Us], glued at the gluings of the clause: a non-uniform
    parameter's at the non-uniform parameters before it, glued, and a
    non-recursive argument's at all the non-uniform parameters and the
    non-recursive arguments before it, glued.  They are what moves an element
    to a lower universe (the third part of cumulativity), as the domain and
    the codomains do for a [Π]. *)
Definition ind_glu_comps (p : qname) (D : ind_decl) (ups : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (Γ : ctx) (Us : list exp) : Prop :=
  (forall k Ns ns T, List.length ns = k -> k < ind_nn D ->
     List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T ->
     (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
        List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T' ->
        List.nth_error ns j = Some n -> Γ ⊢ N : T' ® n ∈ NEl j (List.firstn j ns)) ->
     tele_pre (ind_nr D ups) k ns ns -> Γ ⊢ T ® NP k ns) /\
  (forall c gs gs1 A0 gs2 Ns ns As vs T, ind_con D c = Some gs -> gs = gs1 ++ ca_arg A0 :: gs2 ->
     glu_nparams D NEl Γ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs) (nonrec_vals gs1 vs) ->
     Γ ⊢ T ® AP ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs)) /\
  (forall c gs gs1 t gs2 Ns ns As vs T, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
     glu_nparams D NEl Γ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
     List.length vs = List.length gs1 ->
     List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
     (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
        List.nth_error vs (List.length hs1) = Some v ->
        Γ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))) ->
     tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs) (nonrec_vals gs1 vs) ->
     glu_shape_typ ups DP DEl Γ (ns ++ nonrec_vals gs1 vs) t T).

(** A type of the inductive type at its parameters, at syntactic parameters
    [Ps]: glued to the values by their readback, its sort in the universe of
    the gluing, and its telescopes' types glued, at every instance of the
    parameters equal to the given ones: two types of the same
    inductive type at the same values may have different syntactic
    parameters, and lowering an element of one to a smaller universe needs
    the components at the parameters of the other. *)
Definition ind_typ_at (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (U : typ) (Γ : ctx) (A : typ) (Ps : list exp) : Prop :=
  Γ ⊢ A ≈ apps (a_ind p) Ps : U /\
  forall Δ φ, Δ ⊢ᵏ φ : Γ ->
    glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Ps) (ups ++ ns) /\
    Δ ⊢ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id (List.map (fun P => P[φ]ʷ) Ps)] ⊆ U /\
    forall Ps', exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ (List.firstn (ind_nu D) Ps').

Definition ind_glu_typ_pred (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (U : typ) : glu_typ_pred :=
  fun Γ A => exists Ps, ind_typ_at p D ups ns NP NEl AP AEl DP DEl U Γ A Ps.
#[global] Arguments ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl U Γ A/.

Section GluInd.
  Variable (p : qname) (D : ind_decl) (ups : list domain)
    (NEl : nat -> list domain -> glu_exp_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred).

  (** The elements of the inductive type at the syntactic parameters [Ps]
      of its type: a constructor at those parameters, its non-uniform ones
      glued to the values the constructor was built at, a non-recursive
      argument glued at its type, and a recursive one an element at the
      parameters of its type; and neutrals, by their readback.  The
      non-uniform parameters of a recursive argument's type are glued to
      every instance related to the values they evaluate to, so that
      [glu_ind] does not depend on the representative [ups] of the uniform
      parameters (see [glu_ind_move]).  A recursive argument is an element
      at every weakening and every instance of the parameters equal to
      those of its type, like the element itself in [ind_glu_exp_pred]:
      weakening commutes with the instances of the telescopes only for a
      closed declaration, which the model does not assume, so it is built
      into the gluing instead.  A recursive argument of a function shape
      ([glu_rec]) is a function: at every weakening, applied to an element
      glued at a domain of the shape ([DEl], indexed by the values before
      the domain and the domain), it is a recursive argument of the rest of
      the shape; its domain type is glued at [DP]. *)
  Inductive glu_ind : ctx -> list exp -> exp -> domain -> Prop :=
  | glu_ind_con :
    `{ ind_con D c = Some gs ->
       List.length Ps = ind_np D ->
       List.length bs = ind_np D ->
       List.length vs = List.length gs ->
       List.length As = List.length gs ->
       Γ ⊢ M ≈ apps (a_con p c) (Ps ++ As) : apps (a_ind p) Ps ->
       tele_full (ind_nr D ups) (List.rev (ind_nparams D)) (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs) ->
       tele_full (ind_ar D ups (List.skipn (ind_nu D) bs) c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) ->
       glu_nparams D NEl Γ (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) (List.skipn (ind_nu D) bs) ->
       (forall k N A, List.nth_error As k = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some A -> Γ ⊢ N : A) ->
       (forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Γ ⊢ N : A ® v ∈ AEl (List.skipn (ind_nu D) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) ->
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec Γ (List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t A N v) ->
       glu_ind Γ Ps M (d_con p c (bs ++ vs)) }
  | glu_ind_neut :
    `{ per_bot m m ->
       (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
          Δ ⊢ M[φ]ʷ ≈ M' : (apps (a_ind p) Ps)[φ]ʷ) ->
       glu_ind Γ Ps M (⇑ (d_ind p as') m) }
  (** A recursive argument [N] of type [A] and shape [t], after the values
      [pre] of the shape's components (the uniform parameters left out). *)
  with glu_rec : ctx -> list domain -> ptyp -> typ -> exp -> domain -> Prop :=
  | glu_rec_self :
    `{ (forall bsr Q, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bsr ->
          A = apps (a_ind p) Q ->
          List.length Q = ind_np D /\ tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr /\
          (forall bsr', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr' ->
             glu_nparams D NEl Γ (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) bsr' /\
             forall Δ φ, Δ ⊢ᵏ φ : Γ -> glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Q) (ups ++ bsr'))) ->
       (forall bsr Q, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bsr ->
          A = apps (a_ind p) Q ->
          forall Δ φ Q', Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
            glu_ind Δ Q' N[φ]ʷ v) ->
       glu_rec Γ pre (pt_self k Ps) A N v }
  | glu_rec_pi :
    `{ (forall IT OT, A = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Γ -> Δ ⊢ IT[φ]ʷ ® DP pre B) ->
       (forall IT OT, A = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Γ -> ind_dr ups pre B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
       (forall IT OT, A = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Γ -> ind_dr ups pre B c c ->
          Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
          glu_rec Δ (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
       glu_rec Γ pre (pt_pi B t) A N v }.
End GluInd.

Scheme glu_ind_mut_ind := Induction for glu_ind Sort Prop
with glu_rec_mut_ind := Induction for glu_rec Sort Prop.
Combined Scheme glu_ind_mut_ind_all from glu_ind_mut_ind, glu_rec_mut_ind.

(** An element of the inductive type: typed, related to itself, and an
    element at every weakening and at every instance of the parameters
    equal to the type's ones there, as the components of [ind_typ_at] are:
    a constructor or an eliminator whose syntactic parameters differ from
    the ones of the type the element was glued at reads it at its own. *)
Definition ind_glu_exp_pred (p : qname) (D : ind_decl) (ups ns : list domain)
    (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
    (elem_rel : relation domain) (U : typ) : glu_exp_pred :=
  fun Γ A M m => Γ ⊢ M : A /\ Dom m ≈ m ∈ elem_rel /\
    exists Ps, ind_typ_at p D ups ns NP NEl AP AEl DP DEl U Γ A Ps /\
      forall Δ φ Ps', Δ ⊢ᵏ φ : Γ -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Ps) Ps' ->
        glu_ind p D ups NEl AEl DP DEl Δ Ps' M[φ]ʷ m.
#[global] Arguments ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel U Γ A M m/.

(** The gluing of a type of a small universe quotes the large universe
    [Typeω@0] (any small type is in it), so it does not say that the type is
    in the small universe; the element predicate of a small universe
    ([suniv_glu_exp_pred']) does: by its typing at its own type, and by its
    readback clause at that type. *)
Section Gluing.
  Variable
    (i : uidx)
      (glu_univ_typ_rec : uidx -> domain -> glu_typ_pred).

  (** [univ_typ] is the entry [glu_univ_typ_rec j] of the family, passed
      applied so that [glu_univ_below_spec] can restate it. *)
  Definition univ_glu_exp_pred' j (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\
        Γ ⊢ A ≈ Typeω@j : Typeω@(ulvl i) /\
        Γ ⊢ M ® univ_typ m.

#[global] Arguments univ_glu_exp_pred' j univ_typ Γ A M m/.

  Definition suniv_glu_exp_pred' (l : domain) (univ_typ : domain -> glu_typ_pred) : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\
        Γ ⊢ A ® suniv_glu_typ_pred l (Typeω@(ulvl i)) /\
        Γ ⊢ M ® univ_typ m /\
        (forall Δ φ W, Δ ⊢ᵏ φ : Γ -> Rtyp m in length Δ ↘ W -> Δ ⊢ M[φ]ʷ ≈ W : A[φ]ʷ).

#[global] Arguments suniv_glu_exp_pred' l univ_typ Γ A M m/.

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : uidx_lt (ul j) i),
          typ_rel <∙> univ_glu_typ_pred j (Typeω@(ulvl i)) ->
          el_rel <∙> univ_glu_exp_pred' j (glu_univ_typ_rec (ul j)) ->
          DG 𝕌ω@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }

  | glu_univ_elem_core_suniv :
    `{ forall typ_rel
         el_rel
         (lt_j_i : uidx_lt (us (dlvl_real l)) i),
          Dom l ≈ l ∈ per_lvl ->
          typ_rel <∙> suniv_glu_typ_pred l (Typeω@(ulvl i)) ->
          el_rel <∙> suniv_glu_exp_pred' l (glu_univ_typ_rec (us (dlvl_real l))) ->
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

  (** An inductive type at its parameters: the types of its non-uniform
      parameters glue at the related values before them, and so do the
      non-recursive arguments of each constructor, at each related instance
      of the non-uniform parameters; the relations are the canonical ones
      of [Core.Semantic.IndPER]. *)
  | glu_univ_elem_core_indty :
    `{ forall (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
         (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
         (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
         (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
         typ_rel el_rel (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          List.length ups = ind_nu D ->
          tele_ass (ind_params D) ->
          DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
             tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
          (forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
          (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
             tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ NP k vs ↘ NEl k vs) ->
          (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ AP ms c k vs ↘ AEl ms c k vs) ->
          (forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
             exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
          (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem_core ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B) ->
          typ_rel <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl (Typeω@(ulvl i)) ->
          el_rel <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel (Typeω@(ulvl i)) ->
          DG d_ind p (ups ++ ns) ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }.
End Gluing.

Hint Constructors glu_univ_elem_core : mctt.

(** The universes below an index, indexed by theirs, as for
    [per_univ_below]: the recursion is structural, nested on the tier and the
    offset of a small index, so [glu_univ_elem] unfolds by computation. *)
Definition glu_empty : domain -> glu_typ_pred := fun _ _ _ => False.

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
      then fun x Γ A => exists P El, DG x ∈ glu_univ_elem_core (us (a, b'))
                                  (glu_rec_at a lower (glu_univ_below_in a lower b')) ↘ P ↘ El /\ Γ ⊢ A ® P
      else glu_univ_below_in a lower b' m
  end.

Definition glu_tier (a : nat) (lower : nat -> nat -> domain -> glu_typ_pred) (b : nat) : domain -> glu_typ_pred :=
  fun x Γ A => exists P El, DG x ∈ glu_univ_elem_core (us (a, b))
                         (glu_rec_at a lower (glu_univ_below_in a lower b)) ↘ P ↘ El /\ Γ ⊢ A ® P.

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
      then fun a Γ A => exists P El, DG a ∈ glu_univ_elem_core (ul n')
                                  (fun v => match v with us k => glu_suniv k | ul k => glu_univ_below_l n' k end) ↘ P ↘ El /\ Γ ⊢ A ® P
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

Lemma glu_univ_below_spec : forall i j,
    uidx_lt j i ->
    glu_univ_below i j = fun a Γ A => exists P El, DG a ∈ glu_univ_elem j ↘ P ↘ El /\ Γ ⊢ A ® P.
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
  assert (Htier : forall a b, glu_tier a (glu_tiers_below a) b
                         = fun x Γ A => exists P El, DG x ∈ glu_univ_elem (us (a, b)) ↘ P ↘ El /\ Γ ⊢ A ® P).
  { reflexivity. }
  assert (Hl : forall n m, m < n -> glu_univ_below_l n m = fun a Γ A => exists P El, DG a ∈ glu_univ_elem (ul m) ↘ P ↘ El /\ Γ ⊢ A ® P).
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

Definition glu_univ_typ (i : uidx) (a : domain) : glu_typ_pred :=
  fun Γ A => exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El /\ Γ ⊢ A ® P.
#[global] Arguments glu_univ_typ i a Γ A/.

Definition univ_glu_exp_pred j (U : typ) : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\ Γ ⊢ A ≈ Typeω@j : U /\
        Γ ⊢ M ® glu_univ_typ j m.
#[global] Arguments univ_glu_exp_pred j U Γ A M m/.

Definition suniv_glu_exp_pred (l : domain) (U : typ) : glu_exp_pred :=
    fun Γ A M m =>
      Γ ⊢ M : A /\ Γ ⊢ A ® suniv_glu_typ_pred l U /\
        Γ ⊢ M ® glu_univ_typ (us (dlvl_real l)) m /\
        (forall Δ φ W, Δ ⊢ᵏ φ : Γ -> Rtyp m in length Δ ↘ W -> Δ ⊢ M[φ]ʷ ≈ W : A[φ]ʷ).
#[global] Arguments suniv_glu_exp_pred l U Γ A M m/.

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
        forall i p D ups ns (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
          (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
          (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
          (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred)
          (P : glu_typ_pred) (El : glu_exp_pred) (elem_rel : relation domain),
          ind_lookup gc_deps gc_stack p = Some D ->
          List.length ups = ind_nu D ->
          tele_ass (ind_params D) ->
          DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem i ↘ elem_rel ->
          (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
             tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
          (forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
          (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
             tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ NP k vs ↘ NEl k vs) ->
          (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
             tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
             motive i (NP k vs) (NEl k vs) b) ->
          (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ AP ms c k vs ↘ AEl ms c k vs) ->
          (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
             tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
             motive i (AP ms c k vs) (AEl ms c k vs) b) ->
          (forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
             exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
          (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             DG b ∈ glu_univ_elem i ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B) ->
          (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
             ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
             tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
             List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
             ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
             motive i (DP (ms ++ ws ++ ys) B) (DEl (ms ++ ws ++ ys) B) b) ->
          P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl (Typeω@(ulvl i)) ->
          El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl elem_rel (Typeω@(ulvl i)) ->
          motive i P El (d_ind p (ups ++ ns)))
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
  Qed.
End GluingInduction.

Variant glu_elem_bot i a Γ A M m : Prop :=
| glu_elem_bot_make : forall P El,
    Γ ⊢ M : A ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Dom m ≈ m ∈ per_bot ->
    (forall Δ φ M', Δ ⊢ᵏ φ : Γ -> Rne m in length Δ ↘ M' -> Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) ->
    Γ ⊢ M : A ® m ∈ glu_elem_bot i a.
Hint Constructors glu_elem_bot : mctt.

Variant glu_elem_top i a Γ A M m : Prop :=
| glu_elem_top_make : forall P El,
    Γ ⊢ M : A ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Dom ⇓ a m ≈ ⇓ a m ∈ per_top ->
    (forall Δ φ w, Δ ⊢ᵏ φ : Γ -> Rnf ⇓ a m in length Δ ↘ w -> Δ ⊢ M[φ]ʷ ≈ w : A[φ]ʷ) ->
    Γ ⊢ M : A ® m ∈ glu_elem_top i a.
Hint Constructors glu_elem_top : mctt.

Variant glu_typ_top (i : uidx) a Γ A : Prop :=
| glu_typ_top_make :
    Γ ⊢ A : Typeω@(ulvl i) ->
    Dom a ≈ a ∈ per_top_typ ->
    (forall Δ φ A', Δ ⊢ᵏ φ : Γ -> Rtyp a in length Δ ↘ A' -> Δ ⊢ A[φ]ʷ ≈ A' : Typeω@(ulvl i)) ->
    Γ ⊢ A ® glu_typ_top i a.
Hint Constructors glu_typ_top : mctt.

Variant glu_rel_typ_with_sub (i : nat) Δ A σ ρ : Prop :=
| mk_glu_rel_typ_with_sub :
  `{ forall P El,
        ⟦ A ⟧ ρ ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ A[σ] ® P ->
        glu_rel_typ_with_sub i Δ A σ ρ }.

Variant glu_rel_exp_with_sub (i : nat) Δ M A σ ρ : Prop :=
| mk_glu_rel_exp_with_sub :
  `{ forall P El,
        ⟦ A ⟧ ρ ↘ a ->
        ⟦ M ⟧ ρ ↘ m ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
        glu_rel_exp_with_sub i Δ M A σ ρ }.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => Δ ⊢ˢ σ : ⋅.
#[global] Arguments nil_glu_sub_pred Δ σ ρ/.

(** The parameters are ordered differently from the Agda version
    so that we can return [glu_sub_pred]. *)
Variant cons_glu_sub_pred (i : nat) Γ A (TSb : glu_sub_pred) : glu_sub_pred :=
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
| mk_cons_mod_glu_sub_pred :
  `{ Δ ⊢ˢ σ : Γ ▹ₘ U ->
     tie_mod (env_mod ρ 0) (me_lit U) ρ↯ ->
     Δ ⊢ˢ Wk ⨟ σ ® ρ↯ ∈ TSb ->
     Δ ⊢ˢ σ ® ρ ∈ cons_mod_glu_sub_pred Γ U TSb }.

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
        EG Γ ▹ₘ U ∈ glu_ctx_env ↘ Sb }.

Definition glu_rel_ctx Γ : Prop := exists Sb, EG Γ ∈ glu_ctx_env ↘ Sb.
#[global] Arguments glu_rel_ctx Γ/.

Definition glu_rel_exp Γ M A : Prop :=
  exists Sb,
    EG Γ ∈ glu_ctx_env ↘ Sb /\
      exists (i : nat),
      forall Δ σ ρ,
        Δ ⊢ˢ σ ® ρ ∈ Sb ->
        glu_rel_exp_with_sub i Δ M A σ ρ.
#[global] Arguments glu_rel_exp Γ M A/.

(** There is no gluing judgment for substitutions, so the fundamental theorem
    has two parts. A gluing predicate is indexed by a value, and
    [⟦τ ⨟ σ⟧(ρ) = ⟦τ⟧(⟦σ⟧ρ)] is not an equation when substitution is an
    operation, so such a judgment cannot be stated. Concrete substitutions are
    handled by lemmas about [glu_rel_exp] instead, just as
    [completeness_fundamental] has no substitution part. *)

Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70, Γ at level 69).
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
Hint Constructors glu_False : mctt.
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
Notation "⊩ Γ" := (glu_rel_ctx Γ) (at level 70, Γ at level 69).
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
      refine (glu_univ_elem_ind _ _ _ _ _ _ _ _ _);
      (** The level case has one binder more than the other closed types: the
          sort of its type of levels. *)
      [ do 5 intro; do 3 glu_induction_hintro | do 5 intro; do 3 glu_induction_hintro
      | do 4 intro; do 2 glu_induction_hintro | do 3 intro; do 2 glu_induction_hintro
      | do 3 intro; do 2 glu_induction_hintro
      | do 12 intro; glu_induction_hintro; ih; do 6 glu_induction_hintro | do 5 intro; do 3 glu_induction_hintro
      | do 14 intro; do 15 glu_induction_hintro ]; cbv beta
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
