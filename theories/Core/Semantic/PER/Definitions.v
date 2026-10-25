From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Fixed.
From Mctt.Core.Syntactic Require Export Records.
Import Domain_Notations Fixed_Notations.
From Stdlib Require String.
#[local] Open Scope list_scope.

(** The rewrite database of [simp per_univ_elem]. *)
Create Rewrite HintDb per_univ_elem.

Reserved Notation "'Sub' a <: b 'at' i" (at level 70, a at level 69, b at level 69, i constr).
Reserved Notation "'SubE' Γ <: Δ" (at level 70, Γ at level 69, Δ at level 69).

Section Fixed_GCtx.
  Context {GC : GCtx}.

Notation "'Dom' a ≈ b ∈ R" := ((R a b : Prop) : Prop) (at level 70, a at level 69, b at level 69, R constr).
Notation "'DF' a ≈ b ∈ R ↘ R'" := ((R R' a b : Prop) : Prop) (at level 70, a at level 69, b at level 69, R constr, R' constr).
Notation "'Exp' a ≈ b ∈ R" := (R a b : (Prop : Type)) (at level 70, a at level 69, b at level 69, R constr).
Notation "'EF' a ≈ b ∈ R ↘ R'" := (R R' a b : (Prop : Type)) (at level 70, a at level 69, b at level 69, R constr, R' constr).
(** The next two notations have the precedences of their standard-library
    counterparts, but are defined separately from them. *)
Notation "R ~> R'" := (subrelation R R') (at level 70, right associativity).
Notation "R <~> R'" := (relation_equivalence R R') (at level 95, no associativity).

Generalizable All Variables.

(** *** Helper Bundles *)
(** Related modulo evaluation. *)
(** Both evaluate, to values related by [R] at [R']. *)
#[warnings="-cannot-define-projection"]
Record rel_mod_eval (R : relation domain -> domain -> domain -> Prop) A ρ A' ρ' R' : Prop := mk_rel_mod_eval
  { a : domain
  ; a' : domain
  ; rme_eval : ⟦ A ⟧ ρ ↘ a
  ; rme_eval' : ⟦ A' ⟧ ρ' ↘ a'
  ; rme_rel : DF a ≈ a' ∈ R ↘ R' }.
#[global] Arguments mk_rel_mod_eval {_ _ _ _ _ _}.
Hint Constructors rel_mod_eval : mctt.
(** [per_univ_elem_core] nests through [rel_mod_eval], so generating its
    induction principle needs this scheme. *)
Scheme All for rel_mod_eval.

(** Related modulo application. *)
(** Both applications evaluate, to values related by [R]. *)
#[warnings="-cannot-define-projection"]
Record rel_mod_app f a f' a' (R : relation domain) : Prop := mk_rel_mod_app
  { fa : domain
  ; f'a' : domain
  ; rma_app : $| f & a |↘ fa
  ; rma_app' : $| f' & a' |↘ f'a'
  ; rma_rel : Dom fa ≈ f'a' ∈ R }.
#[global] Arguments mk_rel_mod_app {_ _ _ _ _}.
Hint Constructors rel_mod_app : mctt.

(** *** (Some Elements of) PER Lattice *)

Definition per_bot : relation domain_ne := fun m n => (forall s, exists L, Rne m in s ↘ L /\ Rne n in s ↘ L).
#[global] Arguments per_bot /.
Hint Transparent per_bot : mctt.
Hint Unfold per_bot : mctt.

Definition per_top : relation domain_nf := fun m n => (forall s, exists L, Rnf m in s ↘ L /\ Rnf n in s ↘ L).
#[global] Arguments per_top /.
Hint Transparent per_top : mctt.
Hint Unfold per_top : mctt.

Definition per_top_typ : relation domain := fun a b => (forall s, exists C, Rtyp a in s ↘ C /\ Rtyp b in s ↘ C).
#[global] Arguments per_top_typ /.
Hint Transparent per_top_typ : mctt.
Hint Unfold per_top_typ : mctt.

(** Two level values are related when they read back to the same canonical
    level at every length.  Evaluation of [succl] and [maxl] only flattens, so
    this is where the level equations are quotiented: readback canonicalises,
    and [lvl_canon_iff] says that two levels have the same canonical form
    exactly when they agree under every assignment to their atoms.

    It is [per_top] at [Level].  Unlike [per_bot] and [per_top] it is not
    declared transparent to the automation: a goal [R <~> per_lvl] is closed by
    the hypothesis of that shape, which unfolding would hide, and the shared
    scripts of the gluing lemmas [split] every goal they can, which an
    unfolding to a one-constructor inductive would expose. *)
Definition per_lvl : relation domain := fun m m' => Dom ⇓ Levelᵈ m ≈ ⇓ Levelᵈ m' ∈ per_top.

(** The elements of [Level@n]: levels that read back, at every length, as
    the same canonical level of sort [n] ([lvl_bnd]), below ω·(n+1).  A small
    universe is indexed by any level, so its levels are related by [per_lvl]
    alone.  Like [per_lvl] it has a [forall] head, so the shared scripts do
    not split it. *)
#[warnings="-cannot-define-projection"]
Record lvl_reads (n : nat) (m m' : domain) (s : nat) : Prop := mk_lvl_reads
  { lr_lvl : lvl
  ; lr_left : Rnf ⇓ Levelᵈ m in s ↘ nf_lvl_of lr_lvl
  ; lr_right : Rnf ⇓ Levelᵈ m' in s ↘ nf_lvl_of lr_lvl
  ; lr_bnd : lvl_bnd n lr_lvl }.

Definition per_lvl_at (n : nat) : relation domain :=
  fun m m' => forall s, lvl_reads n m m' s.

(** [l] is below [l'] when at every length their canonical forms are ordered
    by the decidable order on canonical levels.  It is the semantic
    counterpart of [maxl M M' ≈ M'], and the order the algorithmic subtyping
    of two small universes decides.  The order on realisers would be coarser:
    [max u 3] and [3] have the same realiser and are not comparable. *)
#[warnings="-cannot-define-projection"]
Record sublvl_reads (l l' : domain) (s : nat) : Prop := mk_sublvl_reads
  { slr_left_lvl : lvl
  ; slr_right_lvl : lvl
  ; slr_left : Rnf ⇓ Levelᵈ l in s ↘ nf_lvl_of slr_left_lvl
  ; slr_right : Rnf ⇓ Levelᵈ l' in s ↘ nf_lvl_of slr_right_lvl
  ; slr_le : lvl_le slr_left_lvl slr_right_lvl }.

Definition per_sublvl (l l' : domain) : Prop :=
  forall s, sublvl_reads l l' s.

(** Every pair of values is related at [⊤]: its elements are equal by η. *)
Definition per_True : relation domain := fun _ _ => True.
#[global] Arguments per_True /.
Hint Transparent per_True : mctt.
Hint Unfold per_True : mctt.

Inductive per_ne : relation domain :=
(** Neutrals that read back equally, at any types. *)
| per_ne_neut :
  `{ Dom m ≈ m' ∈ per_bot ->
     Dom ⇑ a m ≈ ⇑ a' m' ∈ per_ne }
.
Hint Constructors per_ne : mctt.

(** ** Telescopes of Inductive Types

    The parameters and the non-recursive arguments of an inductive type are
    telescopes: each type is evaluated in the environment extended by the
    values before it.  A family of relations [tr k pre] relates the [k]-th
    values, given the prefix [pre] of the left list before them (the
    relation of a pair of related types is that of the left type);
    [tele_rel] relates two whole lists, [tele_prefix_rel] two prefixes of length
    [k].  The relations are a family indexed by prefixes, not a nested
    structure, so that the clause of [per_univ_elem_core] for inductive types
    states them with [rel_mod_eval] alone, as the clause for [Π] does. *)

Fixpoint tele_rel_from (tr : nat -> list domain -> relation domain)
    (k : nat) (pre vs vs' : list domain) : Prop :=
  match vs, vs' with
  | nil, nil => True
  | v :: vs, v' :: vs' => tr k pre v v' /\ tele_rel_from tr (S k) (pre ++ v :: nil) vs vs'
  | _, _ => False
  end.

Definition tele_rel {X : Type} (tr : nat -> list domain -> relation domain) (T : list X) (vs vs' : list domain) : Prop :=
  List.length vs = List.length T /\ tele_rel_from tr 0 nil vs vs'.

Definition tele_prefix_rel (tr : nat -> list domain -> relation domain) (k : nat) (vs vs' : list domain) : Prop :=
  List.length vs = k /\ tele_rel_from tr 0 nil vs vs'.

(** The types of the non-recursive arguments of a constructor, outermost
    first, and the values at them among the arguments. *)
Fixpoint cargs_nonrec (gs : list carg) : list typ :=
  match gs with
  | nil => nil
  | ca_arg A :: gs => A :: cargs_nonrec gs
  | ca_rec _ :: gs => cargs_nonrec gs
  end.

Fixpoint nonrec_arg_vals (gs : list carg) (vs : list domain) : list domain :=
  match gs, vs with
  | ca_arg _ :: gs, v :: vs => v :: nonrec_arg_vals gs vs
  | ca_rec _ :: gs, _ :: vs => nonrec_arg_vals gs vs
  | _, _ => nil
  end.

(** Two lists of values read back equally at a telescope, at every length. *)
Definition per_top_ps (T : list centry) (vs vs' : list domain) : Prop :=
  forall s, exists Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ Ms /\ Rps vs' at T in gc_deps ⍮ gc_stack ⍮ nil ⍮ s ↘ Ms.

(** The domains [Bs] of a shape as a telescope of relations, after the
    values of the shape's components, the non-uniform parameters [ms] and
    the non-recursive arguments [ws] before it (the uniform parameters left
    out): the relation of a domain is the one [doms_rel] gives its type after
    them and the values of the domains before it. *)
Definition shape_doms_rel (doms_rel : list domain -> exp -> relation domain) (ms ws : list domain) (Bs : list exp) : nat -> list domain -> relation domain :=
  fun k ys => doms_rel (ms ++ ws ++ ys) (List.nth k Bs a_True).

(** The terms [Ps] evaluate, in [ρ] and in [ρ'], to lists related by [R]. *)
#[warnings="-cannot-define-projection"]
Record rel_evals (Ps : list exp) (ρ ρ' : env) (R : list domain -> list domain -> Prop) : Prop := mk_rel_evals
  { rev_left : list domain
  ; rev_right : list domain
  ; rev_eval_left : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ rev_left
  ; rev_eval_right : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ rev_right
  ; rev_rel : R rev_left rev_right }.

(** The relations of a group's components are indexed by the member: the
    non-uniform parameters of the member [m] ([nr m]), the non-recursive
    arguments of its constructors ([ar m]) and the domains of their shapes
    ([dr m]).  Two lists of values are related at the non-uniform parameters
    of the member [j] ([ntele_rel]). *)
Definition ntele_rel (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain) (j : nat)
    (a b : list domain) : Prop :=
  match ind_member D j with
  | Some Mj => tele_rel (nr j) (List.rev (im_nparams Mj)) a b
  | None => False
  end.

(** A type at two environments: its two values, whose variables at [s]
    are related by [R]. *)
#[warnings="-cannot-define-projection"]
Record rel_fresh_vars (A : exp) (ρ ρ' : env) (R : relation domain) (s : nat) : Prop := mk_rel_fresh_vars
  { rfv_left : domain
  ; rfv_right : domain
  ; rfv_eval_left : ⟦ A ⟧ ρ ↘ rfv_left
  ; rfv_eval_right : ⟦ A ⟧ ρ' ↘ rfv_right
  ; rfv_rel : R (⇑! rfv_left s) (⇑! rfv_right s) }.

(** A domain of a shape at two environments: its two values, whose
    applications to arguments related by [R] read back alike. *)
#[warnings="-cannot-define-projection"]
Record rel_dom_apps (B : exp) (ρ ρ' : env) (R : relation domain) : Prop := mk_rel_dom_apps
  { rda_left : domain
  ; rda_right : domain
  ; rda_eval_left : ⟦ B ⟧ ρ ↘ rda_left
  ; rda_eval_right : ⟦ B ⟧ ρ' ↘ rda_right
  ; rda_top : forall x x', R x x' -> per_top (d_dom rda_left x) (d_dom rda_right x') }.

(** ** Admissible Uniform Parameters

    Uniform parameters [ua] admissible beside [ups], at every related
    prefix: what each member's telescopes evaluate from them is related to
    what they evaluate from [ups].  A fresh variable of a non-uniform
    parameter's or an argument's type at [ua] is related to one of the type
    at [ups], the parameters of a recursive argument at [ua] to those at
    [ups], and an element of a function shape's domain at [ups] reads back
    alike at the domain at [ua].  This is a condition on the two parameters
    of a pair of types ([per_univ_elem_core_indty]); the relations are those
    of the components, never the group's own. *)
Record adm_uparams (D : ind_decl) (ups : list domain)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain)
    (ua : list domain) : Prop := mk_adm_uparams
  { (** A fresh variable of a non-uniform parameter's type at [ua] is
        related to one at [ups] *)
    adm_nparam_vars : forall m Mm k A vs vs' s, ind_member D m = Some Mm ->
      List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A) -> tele_prefix_rel (nparams_rel m) k vs vs' ->
      rel_fresh_vars A (env_args nil (ups ++ vs)) (env_args nil (ua ++ vs')) (nparams_rel m k vs) s
    (** So is one of a non-recursive argument's type *)
  ; adm_arg_vars : forall m Mm ms ms' c gs k A vs vs' s, ind_member D m = Some Mm ->
      tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
      List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (args_rel m ms c) k vs vs' ->
      rel_fresh_vars A (env_args nil (ups ++ ms ++ vs)) (env_args nil (ua ++ ms' ++ vs')) (args_rel m ms c k vs) s
    (** A recursive argument's parameters at [ua] are related to those at
        [ups], at the member its shape ends in *)
  ; adm_rec_params : forall m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys', ind_member D m = Some Mm ->
      tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ms ms' ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      tele_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
      rel_evals (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ua ++ ms' ++ ws' ++ ys'))
        (ntele_rel D nparams_rel (ptyp_mem t))
    (** An element of a function shape's domain at [ups] reads back alike
        at the domain at [ua] *)
  ; adm_shape_doms : forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
      tele_rel (nparams_rel m) (List.rev (im_nparams Mm)) ms ms' ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (args_rel m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      List.nth_error (ptyp_doms t) k = Some B ->
      tele_prefix_rel (shape_doms_rel (doms_rel m) ms ws (ptyp_doms t)) k ys ys' ->
      rel_dom_apps B (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ua ++ ms' ++ ws' ++ ys'))
        (doms_rel m (ms ++ ws ++ ys) B) }.

(** ** Admissibility at the Fresh Variables

    What the readback of a stuck eliminator makes from the uniform
    parameters [ua] of its scrutinee's type: for each member, fresh
    variables of its non-uniform parameters' types ([fresh_tele_rel]) and,
    after them, of its constructors' arguments' types ([fresh_cargs_rel]),
    each of these variables related to the one at [ups]; and at a recursive
    argument, after the domains of its shape, its parameters related at the
    member it ends in, and each domain read back alike.  The prefixes are
    the fresh variables themselves, not every related list: so the
    argument relations occur only in conclusions (model L). *)
Inductive fresh_tele_rel (tr : nat -> list domain -> relation domain) (ups ua : list domain) :
    nat -> list domain -> list domain -> nat -> list centry -> Prop :=
(** The empty telescope *)
| fresh_tele_rel_nil : forall k pre pre' s, fresh_tele_rel tr ups ua k pre pre' s nil
(** The next entry's fresh variables on each side are related, then the
    rest after them *)
| fresh_tele_rel_cons : forall k pre pre' s A T a a',
    ⟦ A ⟧ env_args nil (ups ++ pre) ↘ a ->
    ⟦ A ⟧ env_args nil (ua ++ pre') ↘ a' ->
    tr k pre (⇑! a s) (⇑! a' s) ->
    fresh_tele_rel tr ups ua (S k) (pre ++ ⇑! a s :: nil) (pre' ++ ⇑! a' s :: nil) (S s) T ->
    fresh_tele_rel tr ups ua k pre pre' s (ce_ass A :: T).

(** The arguments, after the fresh non-uniform parameters [ns] and [ns'];
    [ws] and [ws'] the fresh non-recursive arguments before, [k] of them. *)
Inductive fresh_cargs_rel (D : ind_decl) (ups ua : list domain)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> relation domain)
    (doms_rel : list domain -> exp -> relation domain) (ns ns' : list domain) :
    nat -> list domain -> list domain -> nat -> list carg -> Prop :=
(** No argument left *)
| fresh_cargs_rel_nil : forall k ws ws' s, fresh_cargs_rel D ups ua nparams_rel args_rel doms_rel ns ns' k ws ws' s nil
(** A non-recursive argument: its fresh variables are related, then the
    rest after them *)
| fresh_cargs_rel_arg : forall k ws ws' s A gs a a',
    ⟦ A ⟧ env_args nil (ups ++ ns ++ ws) ↘ a ->
    ⟦ A ⟧ env_args nil (ua ++ ns' ++ ws') ↘ a' ->
    args_rel k ws (⇑! a s) (⇑! a' s) ->
    fresh_cargs_rel D ups ua nparams_rel args_rel doms_rel ns ns' (S k) (ws ++ ⇑! a s :: nil) (ws' ++ ⇑! a' s :: nil) (S s) gs ->
    fresh_cargs_rel D ups ua nparams_rel args_rel doms_rel ns ns' k ws ws' s (ca_arg A :: gs)
(** A recursive argument: its shape's parameters related, its domains read
    back alike, then the rest *)
| fresh_cargs_rel_rec : forall k ws ws' s t gs,
    (forall ys ys', tele_rel (shape_doms_rel doms_rel ns ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
       rel_evals (ptyp_ps t) (env_args nil (ups ++ ns ++ ws ++ ys)) (env_args nil (ua ++ ns' ++ ws' ++ ys'))
         (ntele_rel D nparams_rel (ptyp_mem t))) ->
    (forall j B ys ys', List.nth_error (ptyp_doms t) j = Some B ->
       tele_prefix_rel (shape_doms_rel doms_rel ns ws (ptyp_doms t)) j ys ys' ->
       rel_dom_apps B (env_args nil (ups ++ ns ++ ws ++ ys)) (env_args nil (ua ++ ns' ++ ws' ++ ys'))
         (doms_rel (ns ++ ws ++ ys) B)) ->
    fresh_cargs_rel D ups ua nparams_rel args_rel doms_rel ns ns' k ws ws' (S s) gs ->
    fresh_cargs_rel D ups ua nparams_rel args_rel doms_rel ns ns' k ws ws' s (ca_rec t :: gs).

(** A member's type at the uniform parameters [X] of the group, as the
    end of a shape that nests through a view at [X] has it. *)
Definition mref_at (p : qname) (X : list domain) : nat -> qname -> nat -> list domain -> Prop :=
  fun j hd k py => ⟦mref j of p X ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, py).

(** The uniform parameters [ua] of a group admissible at the fresh
    variables: for each member, fresh variables of its non-uniform
    parameters' types ([fresh_tele_rel]) and, after them, of its
    constructors' arguments' types ([fresh_cargs_rel]), each related to the
    one at [ups].  A stuck eliminator is read back under these variables
    at its own uniform parameters; the universe clause's admissibility
    gives them ([adm_fresh_of_uparams]). *)
Record adm_fresh (p : qname) (D : ind_decl) (ups : list domain)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain) (ua : list domain) : Prop := mk_adm_fresh
  { (** The fresh variables of each member's non-uniform parameters *)
    afr_nparams : forall m Mm s, ind_member D m = Some Mm ->
      fresh_tele_rel (nparams_rel m) ups ua 0 nil nil s (List.rev (im_nparams Mm))
    (** The fresh variables of each constructor's arguments, after them *)
  ; afr_args : forall m Mm c gs s ns ns', ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
      Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns ->
      Ftele List.rev (im_nparams Mm) in gc_deps ⍮ gc_stack ⍮ env_args nil ua ⍮ s ↘ ns' ->
      fresh_cargs_rel D ups ua nparams_rel (args_rel m ns c) (doms_rel m) ns ns' 0 nil nil (s + im_nn Mm) gs }.

(** ** Admissible Indices

    A recursive argument's index [bs], its shape's parameters [Ps] at the
    element's own base and its own prefix [pre], is admissible when the
    index at the type's base [ups] at the same prefix is related to it, at
    the member [j] the shape ends in.  No relation of the group is
    quantified over (model L). *)
#[warnings="-cannot-define-projection"]
Record okr_at (D : ind_decl) (ups : list domain) (nparams_rel : nat -> nat -> list domain -> relation domain)
    (j : nat) (pre : list domain) (Ps : list exp) (bs : list domain) : Prop := mk_okr_at
  { (** The index at the type's base *)
    okr_idx : list domain
    (** It is what [Ps] evaluate to at [ups] and [pre] *)
  ; okr_eval : ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ pre) ↘ okr_idx
    (** It is related to [bs] at the member [j] *)
  ; okr_rel : ntele_rel D nparams_rel j okr_idx bs }.

(** A member's own uniform parameters: the group's for a declared one, the
    container's for a view. *)
Definition im_unu (D : ind_decl) (M : imember) : nat :=
  match im_head M with
  | mh_decl _ => ind_nu D
  | mh_view _ _ Is _ => List.length Is
  end.

(** ** The Elements of a Group

    The elements of the member [k] of the group [D] at [p], two-sided: [x]
    at the non-uniform parameters [ns] and [y] at [ns'], [u] and [u'] the
    uniform parameters of the two sides' types, which every member's
    elements read their shapes at: like a [Π], the relation is two-sided at
    the types' parameters, and a constructor's stored uniform parameters
    are not read.  Each element is related at its own non-uniform
    parameters, the ones it stores (a constructor's [bs], a neutral's
    annotation).  A constructor of the member, as the group has
    it ([im_ref]: the container's constructor at a view): the non-uniform
    parameters of each related to its side's index, the non-recursive
    arguments related at their types, and the recursive ones by their
    shapes, each side evaluated at its type's base and its own
    arguments, and each recursive argument's index admissible ([okr]).
    And neutrals of a member that read back equally, of the type at
    parameters that are so too (the container's member at a view): the
    eliminator carries its own uniform parameters, so a neutral's
    annotation needs no condition (model P).  Two relations are read at the left
    element's prefix only: the non-recursive arguments' [args_rel] at its
    non-uniform parameters, and a function shape's domain [doms_rel] at its
    [pre].  This is harmless: the universe clause asks both to be
    invariant along related prefixes, so the right element's prefix gives
    the same relation. *)
Inductive ind_rel (p : qname) (D : ind_decl)
    (okr : nat -> list domain -> list exp -> list domain -> Prop)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain)
  : nat -> list domain -> list domain -> list domain -> list domain -> relation domain :=
(** Two saturated constructors of the member *)
| ind_rel_con :
  `{ ind_member D k = Some Mk ->
     im_ref p k Mk = (hd, k') ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns ns' ->
     ind_con Mk c = Some gs ->
     List.length bs = (im_unu D Mk + im_nn Mk)%nat ->
     List.length bs' = (im_unu D Mk + im_nn Mk)%nat ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns (List.skipn (im_unu D Mk) bs) ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns' (List.skipn (im_unu D Mk) bs') ->
     tele_rel (args_rel k (List.skipn (im_unu D Mk) bs) c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
     con_args_rel p D okr nparams_rel args_rel doms_rel k u u'
       (List.skipn (im_unu D Mk) bs) (List.skipn (im_unu D Mk) bs') gs vs vs' ->
     ind_rel p D okr nparams_rel args_rel doms_rel k u u' ns ns' (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) }
(** Two neutrals of the member that read back equally *)
| ind_rel_neut :
  `{ ind_member D k = Some Mk ->
     im_ref p k Mk = (hd, k') ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns ns' ->
     List.length as1 = (im_unu D Mk + im_nn Mk)%nat ->
     List.length as2 = (im_unu D Mk + im_nn Mk)%nat ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns (List.skipn (im_unu D Mk) as1) ->
     tele_rel (nparams_rel k) (List.rev (im_nparams Mk)) ns' (List.skipn (im_unu D Mk) as2) ->
     Dom m ≈ m' ∈ per_bot ->
     ind_rel p D okr nparams_rel args_rel doms_rel k u u' ns ns' (⇑ (d_ind hd k' as1) m) (⇑ (d_ind hd k' as2) m') }
(** The arguments of two constructors of the member [k] at the bases [u]
    and [u'], after the values [pre] and [pre'] of their non-uniform
    parameters and the non-recursive arguments before them: a recursive
    one by its shape. *)
with con_args_rel (p : qname) (D : ind_decl)
    (okr : nat -> list domain -> list exp -> list domain -> Prop)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain)
  : nat -> list domain -> list domain -> list domain -> list domain -> list carg -> list domain -> list domain -> Prop :=
(** No argument left *)
| con_args_nil :
  `{ con_args_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' nil nil nil }
(** A non-recursive argument: it joins the prefixes (it is related by
    [ind_rel_con]) *)
| con_args_arg :
  `{ con_args_rel p D okr nparams_rel args_rel doms_rel k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs vs vs' ->
     con_args_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' (ca_arg A :: gs) (v :: vs) (v' :: vs') }
(** A recursive argument, by its shape *)
| con_args_rec :
  `{ rec_arg_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' t v v' ->
     con_args_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' gs vs vs' ->
     con_args_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' (ca_rec t :: gs) (v :: vs) (v' :: vs') }
(** A recursive argument of a shape of the member [k], after the values
    [pre] and [pre'] of its components on each side (the bases [u] and [u']
    apart): at the end elements of the member [j] the shape ends in, at
    the parameters the shape evaluates to on each side, each admissible;
    and at a domain pointwise: related arguments of the domain give related
    results, of the rest of the shape, after [pre], [pre'] and the
    arguments. *)
with rec_arg_rel (p : qname) (D : ind_decl)
    (okr : nat -> list domain -> list exp -> list domain -> Prop)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain)
  : nat -> list domain -> list domain -> list domain -> list domain -> ptyp -> domain -> domain -> Prop :=
(** At the end: elements of the member [j] at admissible parameters *)
| rec_arg_self :
  `{ ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u ++ pre) ↘ bs ->
     ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (u' ++ pre') ↘ bs' ->
     okr j pre Ps bs ->
     okr j pre' Ps bs' ->
     ind_rel p D okr nparams_rel args_rel doms_rel j u u' bs bs' v v' ->
     rec_arg_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' (pt_self j Ps) v v' }
(** At a domain: related arguments give related results *)
| rec_arg_pi :
  `{ (forall c c', doms_rel k pre B c c' ->
        rec_arg_app_rel p D okr nparams_rel args_rel doms_rel k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) t f c f' c') ->
     rec_arg_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' (pt_pi B t) f f' }
(** Two functions at two arguments: their results are related at the rest
    of the shape *)
with rec_arg_app_rel (p : qname) (D : ind_decl)
    (okr : nat -> list domain -> list exp -> list domain -> Prop)
    (nparams_rel : nat -> nat -> list domain -> relation domain)
    (args_rel : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (doms_rel : nat -> list domain -> exp -> relation domain)
  : nat -> list domain -> list domain -> list domain -> list domain -> ptyp -> domain -> domain -> domain -> domain -> Prop :=
(** The only rule *)
| rec_arg_app_mk :
  `{ $| f & c |↘ r ->
     $| f' & c' |↘ r' ->
     rec_arg_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' t r r' ->
     rec_arg_app_rel p D okr nparams_rel args_rel doms_rel k u u' pre pre' t f c f' c' }
.

Scheme ind_rel_mut_ind := Induction for ind_rel Sort Prop
with con_args_rel_mut_ind := Induction for con_args_rel Sort Prop
with rec_arg_rel_mut_ind := Induction for rec_arg_rel Sort Prop
with rec_arg_app_rel_mut_ind := Induction for rec_arg_app_rel Sort Prop.
Combined Scheme ind_rel_mut_ind_all from ind_rel_mut_ind, con_args_rel_mut_ind, rec_arg_rel_mut_ind, rec_arg_app_rel_mut_ind.

Hint Constructors ind_rel con_args_rel rec_arg_rel rec_arg_app_rel : mctt.

(** ** The Components of a Group

    What the universe clause states of the relations of a group's
    components, at each member: each is a PER at related prefixes, does not
    depend on which of two related prefixes it is read at, and is the
    relation of the component's two types at the two sides' parameters,
    [R] being the universe relation (or, in an induction, it with the
    motive).  [grp_tele_ass]: the parameters are assumptions, and a view's
    container member is declared, with as many non-uniform parameters as
    the view; the rank, the views' members and the agreement of the
    views' maps as the declaration checks them; and the parameters of every recursive argument's shape, of the
    group's constructors and of its views' containers', as many as the
    member's the shape ends in ([cargs_plen], which readback asks of the
    blocks it reads). *)

(** The member [j] of the group a view's [vm] takes the container's
    member [i'] to: as many non-uniform parameters, and the view of the
    same instance at a declared member [i'], a view at the same container
    member at a view [i']. *)
#[warnings="-cannot-define-projection"]
Record view_member_image (D : ind_decl) (qc : qname) (Is : list exp) (vm : list nat) (i' : nat) (Mi' : imember) : Prop :=
  mk_view_member_image
  { (** The member [j] *)
    image_index : nat
    (** That member *)
  ; image_member : imember
    (** [vm] takes [i'] to [j] *)
  ; image_in_view_map : List.nth_error vm i' = Some image_index
    (** [j] is a member of the group *)
  ; image_is_member : ind_member D image_index = Some image_member
    (** It has as many non-uniform parameters as [Mi'] *)
  ; image_same_nparams_count : im_nn image_member = im_nn Mi'
    (** It is the view of [i'] at the same instance when [Mi'] is
        declared, and a view of the same container member, at as many
        arguments, when [Mi'] is a view *)
  ; image_head_matches : match im_head Mi' with
               | mh_decl _ => exists vm', im_head image_member = mh_view qc i' Is vm'
               | mh_view qv kv Is'' _ => exists Is' vm', im_head image_member = mh_view qv kv Is' vm' /\ List.length Is' = List.length Is''
               end }.

(** The structural facts about a group the universe clause asks for (see
    the section header). *)
Record grp_tele_ass (D : ind_decl) : Prop := mk_grp_tele_ass
  { (** The uniform parameters are assumptions *)
    gta_uparams : tele_ass (ind_uparams D)
    (** Each member's non-uniform parameters are assumptions *)
  ; gta_nparams : forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)
    (** A view's container member exists, with as many non-uniform
        parameters as the view, at as many uniform arguments as the
        container has *)
  ; gta_views : forall v Mv qc kc Is vm, ind_member D v = Some Mv -> im_head Mv = mh_view qc kc Is vm ->
      exists Dq Mc, ind_lookup gc_deps gc_stack qc = Some Dq /\ ind_member Dq kc = Some Mc /\ im_nn Mc = im_nn Mv /\
        List.length Is = ind_nu Dq
    (** The members have a rank *)
  ; gta_rank : exists rk, view_rank_ok gc_deps gc_stack D rk
    (** Each view's map takes the container's members to members of the
        same shapes *)
  ; gta_vwrap : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      exists D', ind_lookup gc_deps gc_stack qc = Some D' /\ vwrap_ok D D' vm
    (** The views agree on their maps *)
  ; gta_view_maps_coherent : view_maps_coherent gc_deps gc_stack D
    (** Each container member has its image under a view's map *)
  ; gta_vm : forall v Mv qc kc Is vm Dq i' Mi', ind_member D v = Some Mv -> im_head Mv = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> view_member_image D qc Is vm i' Mi'
    (** Each recursive argument of the group's constructors gives its
        member as many parameters as it has *)
  ; gta_plen : forall k Mk c gs, ind_member D k = Some Mk -> List.In (c, gs) (im_cons Mk) -> cargs_plen D gs
    (** So does each of the views' containers' constructors *)
  ; gta_cplen : forall v Mv qc kc Is vm Dq i' Mi' c gs', ind_member D v = Some Mv -> im_head Mv = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> List.In (c, gs') (im_cons Mi') ->
      cargs_plen Dq gs' }.

(** The non-uniform parameters' relations are PERs at related prefixes. *)
Definition nparams_per (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm k A vs vs', ind_member D m = Some Mm ->
    List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A) -> tele_prefix_rel (nr m) k vs vs' ->
    PER (nr m k vs).

(** They do not depend on which of two related prefixes they are read
    at. *)
Definition nparams_inv (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm k A vs vs', ind_member D m = Some Mm ->
    List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A) -> tele_prefix_rel (nr m) k vs vs' ->
    (nr m k vs <~> nr m k vs').

(** Each is [R] of its type at the two sides' parameters [ups] and
    [ups']. *)
Definition nparams_evals (R : relation domain -> domain -> domain -> Prop) (D : ind_decl) (ups ups' : list domain)
    (nr : nat -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm k A vs vs', ind_member D m = Some Mm ->
    List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A) -> tele_prefix_rel (nr m) k vs vs' ->
    rel_mod_eval R A (env_args nil (ups ++ vs)) A (env_args nil (ups' ++ vs')) (nr m k vs).

(** The non-recursive arguments' relations are PERs at related
    prefixes. *)
Definition args_per (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm ms ms' c gs k A vs vs', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
    List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar m ms c) k vs vs' ->
    PER (ar m ms c k vs).

(** They do not depend on which of two related non-uniform parameters they
    are read at. *)
Definition args_inv (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm ms ms' c gs k A vs vs', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
    List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar m ms c) k vs vs' ->
    (ar m ms c k vs <~> ar m ms' c k vs').

(** Each is [R] of its type at the two sides' parameters. *)
Definition args_evals (R : relation domain -> domain -> domain -> Prop) (D : ind_decl) (ups ups' : list domain)
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain) : Prop :=
  forall m Mm ms ms' c gs k A vs vs', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
    List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar m ms c) k vs vs' ->
    rel_mod_eval R A (env_args nil (ups ++ ms ++ vs)) A (env_args nil (ups' ++ ms' ++ vs')) (ar m ms c k vs).

(** The shapes' domains' relations are PERs at related prefixes. *)
Definition doms_per (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain) : Prop :=
  forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
    ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
    List.nth_error (ptyp_doms t) k = Some B ->
    tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
    PER (dr m (ms ++ ws ++ ys) B).

(** They do not depend on which of two related prefixes they are read
    at. *)
Definition doms_inv (D : ind_decl) (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain) : Prop :=
  forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
    ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
    List.nth_error (ptyp_doms t) k = Some B ->
    tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
    (dr m (ms ++ ws ++ ys) B <~> dr m (ms' ++ ws' ++ ys') B).

(** Each is [R] of its domain at the two sides' parameters. *)
Definition doms_evals (R : relation domain -> domain -> domain -> Prop) (D : ind_decl) (ups ups' : list domain)
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain) : Prop :=
  forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
    tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
    ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
    List.nth_error (ptyp_doms t) k = Some B ->
    tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
    rel_mod_eval R B (env_args nil (ups ++ ms ++ ws ++ ys)) B (env_args nil (ups' ++ ms' ++ ws' ++ ys'))
      (dr m (ms ++ ws ++ ys) B).

(** The elements of the member [k] of a group whose type is at the
    uniform parameters [ups]: the recursive indices admissible at [ups]. *)
Definition grp_rel (p : qname) (D : ind_decl) (ups : list domain)
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain) :
    nat -> list domain -> list domain -> list domain -> list domain -> relation domain :=
  ind_rel p D (okr_at D ups nr) nr ar dr.

(** ** Records

    The fields of a record are a telescope of relations [fr k vs]: field
    [k]'s, after the left values [vs] of the fields before it.  Values carry
    no parameters: the elements of a record type are related field by field,
    their projections taken by name ([eval_proj]), each at the relation the
    universe clause gives the field's type at the type's parameters and the
    projections before it.  No condition is put on a value beyond its
    projections, and records are not recursive, so the clause has no fixed
    point. *)

(** The fields' relations are PERs at related prefixes. *)
Definition fields_per (R : record_decl) (fr : nat -> list domain -> relation domain) : Prop :=
  forall k f T vs vs', List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel fr k vs vs' ->
    PER (fr k vs).

(** They do not depend on which of two related prefixes they are read at. *)
Definition fields_inv (R : record_decl) (fr : nat -> list domain -> relation domain) : Prop :=
  forall k f T vs vs', List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel fr k vs vs' ->
    (fr k vs <~> fr k vs').

(** Each is the relation [Rel] gives the field's type, at the two sides'
    parameters and related prefixes. *)
Definition fields_evals (Rel : relation domain -> domain -> domain -> Prop) (R : record_decl) (ns ns' : list domain)
    (fr : nat -> list domain -> relation domain) : Prop :=
  forall k f T vs vs', List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel fr k vs vs' ->
    rel_mod_eval Rel T (env_args nil (ns ++ vs)) T (env_args nil (ns' ++ vs')) (fr k vs).

(** The projections [vs] of the value [v] at the fields of [R], in order. *)
Definition record_projs (R : record_decl) (v : domain) (vs : list domain) : Prop :=
  List.Forall2 (fun fT r => eval_proj gc_deps gc_stack (fst fT) v r) (record_fields R) vs.

(** Two elements of a record type: their projections, related as a
    telescope at the fields' relations. *)
#[warnings="-cannot-define-projection"]
Record record_rel (R : record_decl) (fr : nat -> list domain -> relation domain) (v v' : domain) : Prop := mk_record_rel
  { (** The left value's projections *)
    left_projs : list domain
    (** The right value's projections *)
  ; right_projs : list domain
    (** They are the left value's fields *)
  ; left_projs_eval : record_projs R v left_projs
    (** They are the right value's fields *)
  ; right_projs_eval : record_projs R v' right_projs
    (** They are related, field by field *)
  ; projs_related : tele_rel fr (record_fields R) left_projs right_projs }.

(** * Universe/Element PER *)
(** ** Universe/Element PER Definition *)

Section Per_univ_elem_core_def.
  Variable
    (i : uidx)
      (per_univ_rec : uidx -> relation domain).

  (** [per_univ_elem_core R a a']: [a] and [a'] are related types of the
      universe at [i], and [R] is the relation of their elements; the
      smaller universes are [per_univ_rec]. *)
  Inductive per_univ_elem_core : relation domain -> domain -> domain -> Prop :=
  (** A smaller large universe, its elements the types of that universe. *)
  | per_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
          (lt_j_i : uidx_lt (ul j) i),
          j = j' ->
          (elem_rel <~> per_univ_rec (ul j)) ->
          DF 𝕌ω@j ≈ 𝕌ω@j' ∈ per_univ_elem_core ↘ elem_rel }
  (** A smaller small universe, its elements the types of that universe.  Two
      small universes are the same when their levels are related ([per_lvl]),
      and the index of their elements is the realiser of the level — the only
      ordinal a level determines independently of a length. *)
  | per_univ_elem_core_suniv :
    `{ forall (elem_rel : relation domain)
          (lt_j_i : uidx_lt (us (dlvl_real l)) i),
          Dom l ≈ l' ∈ per_lvl ->
          (elem_rel <~> per_univ_rec (us (dlvl_real l))) ->
          DF 𝕌@l ≈ 𝕌@l' ∈ per_univ_elem_core ↘ elem_rel }
  (** [Level@n], its elements the related levels of sort [n]. *)
  | per_univ_elem_core_level :
    forall n (elem_rel : relation domain),
      (elem_rel <~> per_lvl_at n) ->
      DF Levelᵈ@n ≈ Levelᵈ@n ∈ per_univ_elem_core ↘ elem_rel
  (** [⊤], all of its elements related. *)
  | per_univ_elem_core_True :
    forall (elem_rel : relation domain),
      (elem_rel <~> per_True) ->
      DF ⊤ᵈ ≈ ⊤ᵈ ∈ per_univ_elem_core ↘ elem_rel
  (** [⊥] has no canonical elements, so its elements are those of a neutral
      type. *)
  | per_univ_elem_core_False :
    forall (elem_rel : relation domain),
      (elem_rel <~> per_ne) ->
      DF ⊥ᵈ ≈ ⊥ᵈ ∈ per_univ_elem_core ↘ elem_rel
  (** A [Π]: related domains, codomains related at related arguments, and functions related pointwise. *)
  | per_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
         (elem_rel : relation domain)
         (equiv_a_a' : DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel),
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
              rel_mod_eval per_univ_elem_core B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) ->
          (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
          DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem_core ↘ elem_rel }
  (** A declared member [k] of a group at its parameters.  The uniform
      parameters read back equally; the components of every member — the
      non-uniform parameters, whose types are in the sort ([nr]), the
      non-recursive arguments of each constructor at each related instance
      of the non-uniform parameters ([ar]), the domains of the shapes
      ([dr]) — are related at their types; the two sides' uniform
      parameters are admissible beside the left's.  Its elements are
      [ind_rel] at the two sides' non-uniform parameters ([grp_rel]).
      (The binders keep their short names, which the inversions name their
      hypotheses after.) *)
  | per_univ_elem_core_indty :
    `{ forall (nr : nat -> nat -> list domain -> relation domain)
         (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
         (dr : nat -> list domain -> exp -> relation domain)
         (elem_rel : relation domain),
         ind_lookup gc_deps gc_stack p = Some D ->
         grp_tele_ass D ->
         ind_member D k = Some M ->
         im_head M = mh_decl pm ->
         List.length ups = ind_nu D ->
         List.length ups' = ind_nu D ->
         per_top_ps (List.rev (ind_uparams D)) ups ups' ->
         nparams_per D nr ->
         nparams_evals per_univ_elem_core D ups ups' nr ->
         nparams_inv D nr ->
         args_per D nr ar ->
         args_evals per_univ_elem_core D ups ups' nr ar ->
         args_inv D nr ar ->
         doms_per D nr ar dr ->
         doms_evals per_univ_elem_core D ups ups' nr ar dr ->
         doms_inv D nr ar dr ->
         adm_uparams D ups nr ar dr ups' ->
         adm_uparams D ups nr ar dr ups ->
         tele_rel (nr k) (List.rev (im_nparams M)) ns ns' ->
         (elem_rel <~> grp_rel p D ups nr ar dr k ups ups' ns ns') ->
         DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem_core ↘ elem_rel }
  (** A neutral type, its elements neutrals. *)
  | per_univ_elem_core_neut :
    `{ forall (elem_rel : relation domain),
          Dom b ≈ b' ∈ per_bot ->
          (elem_rel <~> per_ne) ->
          DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ elem_rel }
  (** A record type at its parameters.  The parameters read back equally;
      the field names are distinct; the fields' types, at the two sides'
      parameters and related prefixes, are related; the elements are related
      field by field ([record_rel]). *)
  | per_univ_elem_core_record :
    `{ forall (fr : nat -> list domain -> relation domain) (elem_rel : relation domain),
         record_lookup gc_deps gc_stack p = Some R ->
         List.NoDup (List.map fst (record_fields R)) ->
         List.length ns = List.length (record_params R) ->
         List.length ns' = List.length (record_params R) ->
         per_top_ps (List.rev (record_params R)) ns ns' ->
         fields_per R fr ->
         fields_evals per_univ_elem_core R ns ns' fr ->
         fields_inv R fr ->
         (elem_rel <~> record_rel R fr) ->
         DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem_core ↘ elem_rel }
  .

  Hypothesis
    (motive : relation domain -> domain -> domain -> Prop)
      (case_U : forall {j j' elem_rel} (lt_j_i : uidx_lt (ul j) i),
          j = j' ->
          (elem_rel <~> per_univ_rec (ul j)) ->
          motive elem_rel 𝕌ω@j 𝕌ω@j')
      (case_SU : forall {l l' elem_rel} (lt_j_i : uidx_lt (us (dlvl_real l)) i),
          Dom l ≈ l' ∈ per_lvl ->
          (elem_rel <~> per_univ_rec (us (dlvl_real l))) ->
          motive elem_rel 𝕌@l 𝕌@l')
      (case_level : forall {n elem_rel},
          (elem_rel <~> per_lvl_at n) ->
          motive elem_rel (Levelᵈ@n) (Levelᵈ@n))
      (case_True : forall {elem_rel},
          (elem_rel <~> per_True) ->
          motive elem_rel ⊤ᵈ ⊤ᵈ)
      (case_False : forall {elem_rel},
          (elem_rel <~> per_ne) ->
          motive elem_rel ⊥ᵈ ⊥ᵈ)
      (case_Pi :
        forall {a ρ B a' ρ' B' in_rel}
           (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
           {elem_rel},
          DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel ->
          motive in_rel a a' ->
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
              rel_mod_eval (fun R x y => DF x ≈ y ∈ per_univ_elem_core ↘ R /\ motive R x y) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) ->
          (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
          motive elem_rel Πᵈ a ρ B Πᵈ a' ρ' B')
      (case_ne : forall {a b a' b' elem_rel},
          Dom b ≈ b' ∈ per_bot ->
          (elem_rel <~> per_ne) ->
          motive elem_rel ⇑ a b ⇑ a' b')
      (case_Ind : forall {p D k M pm ups ups' ns ns'}
          (nr : nat -> nat -> list domain -> relation domain)
          (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
          (dr : nat -> list domain -> exp -> relation domain)
          {elem_rel},
          ind_lookup gc_deps gc_stack p = Some D ->
          grp_tele_ass D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          List.length ups' = ind_nu D ->
          per_top_ps (List.rev (ind_uparams D)) ups ups' ->
          nparams_per D nr ->
          nparams_evals (fun R x y => DF x ≈ y ∈ per_univ_elem_core ↘ R /\ motive R x y) D ups ups' nr ->
          nparams_inv D nr ->
          args_per D nr ar ->
          args_evals (fun R x y => DF x ≈ y ∈ per_univ_elem_core ↘ R /\ motive R x y) D ups ups' nr ar ->
          args_inv D nr ar ->
          doms_per D nr ar dr ->
          doms_evals (fun R x y => DF x ≈ y ∈ per_univ_elem_core ↘ R /\ motive R x y) D ups ups' nr ar dr ->
          doms_inv D nr ar dr ->
          adm_uparams D ups nr ar dr ups' ->
          adm_uparams D ups nr ar dr ups ->
          tele_rel (nr k) (List.rev (im_nparams M)) ns ns' ->
          (elem_rel <~> grp_rel p D ups nr ar dr k ups ups' ns ns') ->
          motive elem_rel (d_ind p k (ups ++ ns)) (d_ind p k (ups' ++ ns')))
      (case_Rec : forall {p R ns ns'} (fr : nat -> list domain -> relation domain) {elem_rel},
          record_lookup gc_deps gc_stack p = Some R ->
          List.NoDup (List.map fst (record_fields R)) ->
          List.length ns = List.length (record_params R) ->
          List.length ns' = List.length (record_params R) ->
          per_top_ps (List.rev (record_params R)) ns ns' ->
          fields_per R fr ->
          fields_evals (fun R x y => DF x ≈ y ∈ per_univ_elem_core ↘ R /\ motive R x y) R ns ns' fr ->
          fields_inv R fr ->
          (elem_rel <~> record_rel R fr) ->
          motive elem_rel (d_record p ns) (d_record p ns')).

  #[derive(equations=no, eliminator=no)]
  Equations per_univ_elem_core_strong_ind R a b (H : DF a ≈ b ∈ per_univ_elem_core ↘ R) : DF a ≈ b ∈ motive ↘ R :=
  | R, a, b, (per_univ_elem_core_univ _ lt_j_i HE eq)                 => case_U lt_j_i HE eq;
  | R, a, b, (per_univ_elem_core_suniv _ lt_j_i HE eq)                => case_SU lt_j_i HE eq;
  | R, a, b, (per_univ_elem_core_level _ _ HE)                        => case_level HE;
  | R, a, b, (per_univ_elem_core_True _ HE)                           => case_True HE;
  | R, a, b, (per_univ_elem_core_False _ HE)                          => case_False HE;
  | R, a, b, (per_univ_elem_core_pi _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi out_rel equiv_a_a' (per_univ_elem_core_strong_ind _ _ _ equiv_a_a') per
        (fun _ _ equiv_c_c' => match HT _ _ equiv_c_c' with
                              | mk_rel_mod_eval b b' evb evb' Rel =>
                                  mk_rel_mod_eval b b' evb evb' (conj _ (per_univ_elem_core_strong_ind _ _ _ Rel))
                              end)
        HE;
  | R, a, b, (per_univ_elem_core_neut _ equiv_b_b' HE)                => case_ne equiv_b_b' HE;
  | R, a, b, (per_univ_elem_core_indty nr ar dr _ Hl Hass HM Hh Hu Hu' Hps HnP Hn HnI HaP Ha HaI HdP Hd HdI Hcl Hcd Hns HE) =>
      case_Ind nr ar dr Hl Hass HM Hh Hu Hu' Hps HnP
        (fun m Mm k A vs vs' Hm Hk Hpre => match Hn m Mm k A vs vs' Hm Hk Hpre with
                                   | mk_rel_mod_eval b b' evb evb' Rel =>
                                       mk_rel_mod_eval b b' evb evb' (conj Rel (per_univ_elem_core_strong_ind _ _ _ Rel))
                                   end)
        HnI HaP
        (fun m Mm ms ms' c gs k A vs vs' Hm Hms Hc Hk Hpre => match Ha m Mm ms ms' c gs k A vs vs' Hm Hms Hc Hk Hpre with
                                   | mk_rel_mod_eval b b' evb evb' Rel =>
                                       mk_rel_mod_eval b b' evb evb' (conj Rel (per_univ_elem_core_strong_ind _ _ _ Rel))
                                   end)
        HaI HdP
        (fun m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hms Hc Heq Hws Hk Hys =>
           match Hd m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys' Hm Hms Hc Heq Hws Hk Hys with
           | mk_rel_mod_eval b b' evb evb' Rel =>
               mk_rel_mod_eval b b' evb evb' (conj Rel (per_univ_elem_core_strong_ind _ _ _ Rel))
           end)
        HdI Hcl Hcd Hns HE;
  | R, a, b, (per_univ_elem_core_record fr _ Hl Hnd Hn Hn' Hps HfP Hf HfI HE) =>
      case_Rec fr Hl Hnd Hn Hn' Hps HfP
        (fun k f T vs vs' Hk Hpre => match Hf k f T vs vs' Hk Hpre with
                                   | mk_rel_mod_eval b b' evb evb' Rel =>
                                       mk_rel_mod_eval b b' evb evb' (conj Rel (per_univ_elem_core_strong_ind _ _ _ Rel))
                                   end)
        HfI HE.

End Per_univ_elem_core_def.

Hint Constructors per_univ_elem_core : mctt.

(** The universes below an index, indexed by theirs: the entry at [v] below
    [u] is the universe at [v], and the other entries are empty.  The
    recursion is structural, so [per_univ_elem] unfolds by computation, and
    [per_univ_below_spec] states the entries without [per_univ_below].  (A
    well-founded definition of [per_univ_elem] would need functional
    extensionality for its unfolding equation.)

    A small index is an ordinal [(a, b)] below ω² (see
    [Core.Syntactic.Levels.Ordinals]), so the small tier is built by a nested
    recursion: on the tier [a], and inside a tier on [b].  [per_rec_at a
    lower inner] is the family below an index of tier [a]: the universes of
    the lower tiers, [lower a' b'] for [a' < a], and those of tier [a] below
    it, [inner b'].  The large tier then has every small universe below it. *)
Definition empty_rel : relation domain := fun _ _ => False.

Definition per_rec_at (a : nat) (lower : nat -> nat -> relation domain) (inner : nat -> relation domain)
  : uidx -> relation domain :=
  fun v => match v with
        | us (a', b') => if a' <? a then lower a' b' else if a' =? a then inner b' else empty_rel
        | ul _ => empty_rel
        end.

(** Inside the tier [a]: the universes at [(a, m)] for [m < b]. *)
Fixpoint per_univ_below_in (a : nat) (lower : nat -> nat -> relation domain) (b : nat) : nat -> relation domain :=
  match b with
  | 0 => fun _ => empty_rel
  | S b' => fun m =>
      if Nat.eqb m b'
      then fun x y => exists R', DF x ≈ y ∈ per_univ_elem_core (us (a, b'))
                                  (per_rec_at a lower (per_univ_below_in a lower b')) ↘ R'
      else per_univ_below_in a lower b' m
  end.

(** The small universe at [(a, b)], given the tiers below [a]. *)
Definition per_tier (a : nat) (lower : nat -> nat -> relation domain) (b : nat) : relation domain :=
  fun x y => exists R', DF x ≈ y ∈ per_univ_elem_core (us (a, b))
                         (per_rec_at a lower (per_univ_below_in a lower b)) ↘ R'.

(** The tiers below [a]: the universe at [(a', b')] for every [a' < a]. *)
Fixpoint per_tiers_below (a : nat) : nat -> nat -> relation domain :=
  match a with
  | 0 => fun _ _ => empty_rel
  | S a' => fun a'' => if Nat.eqb a'' a' then per_tier a' (per_tiers_below a') else per_tiers_below a' a''
  end.

(** The small universes below the small index [j]. *)
Definition per_univ_rec_s (j : o2) : uidx -> relation domain :=
  per_rec_at (fst j) (per_tiers_below (fst j)) (per_univ_below_in (fst j) (per_tiers_below (fst j)) (snd j)).

(** The small universe at [m], the entry of every large index. *)
Definition per_suniv (m : o2) : relation domain :=
  per_tier (fst m) (per_tiers_below (fst m)) (snd m).

Fixpoint per_univ_below_l (n : nat) : nat -> relation domain :=
  match n with
  | 0 => fun _ => empty_rel
  | S n' => fun m =>
      if Nat.eqb m n'
      then fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem_core (ul n')
                                  (fun v => match v with us k => per_suniv k | ul k => per_univ_below_l n' k end) ↘ R'
      else per_univ_below_l n' m
  end.

Definition per_univ_below (u : uidx) : uidx -> relation domain :=
  match u with
  | us j => per_univ_rec_s j
  | ul n => fun v => match v with us k => per_suniv k | ul k => per_univ_below_l n k end
  end.

Definition per_univ_elem (i : uidx) : relation domain -> domain -> domain -> Prop :=
  per_univ_elem_core i (per_univ_below i).
#[global] Arguments per_univ_elem : simpl never.

Lemma per_univ_elem_equation_1 : forall i,
    per_univ_elem i = per_univ_elem_core i (per_univ_below i).
Proof. reflexivity. Qed.

Hint Rewrite per_univ_elem_equation_1 : per_univ_elem.

Lemma per_univ_below_spec : forall i j,
    uidx_lt j i ->
    per_univ_below i j = fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem j ↘ R'.
Proof.
  assert (Hin : forall a lower b m, m < b -> per_univ_below_in a lower b m = per_tier a lower m).
  { intros a lower b; induction b as [| b IHb]; intros m Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec m b) as [-> | Hneq]; [reflexivity |].
    apply IHb; lia. }
  assert (Htiers : forall a a', a' < a -> per_tiers_below a a' = per_tier a' (per_tiers_below a')).
  { induction a as [| a IHa]; intros a' Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec a' a) as [-> | Hneq]; [reflexivity |].
    apply IHa; lia. }
  assert (Htier : forall a b, per_tier a (per_tiers_below a) b
                         = fun x y => exists R', DF x ≈ y ∈ per_univ_elem (us (a, b)) ↘ R').
  { reflexivity. }
  assert (Hl : forall n m, m < n -> per_univ_below_l n m = fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem (ul m) ↘ R').
  { induction n as [| n IHn]; intros m Hlt; [lia |].
    simpl.
    destruct (Nat.eqb_spec m n) as [-> | Hneq]; [reflexivity |].
    apply IHn; lia. }
  intros [[a b] | n] [[a' b'] | m] Hlt; cbn in Hlt; try contradiction.
  - unfold per_univ_below, per_univ_rec_s, per_rec_at; cbn [fst snd].
    unfold olt in Hlt; cbn [fst snd] in Hlt.
    destruct (Nat.ltb_spec a' a) as [Ha | Ha].
    + rewrite Htiers by exact Ha; apply Htier.
    + destruct (Nat.eqb_spec a' a) as [-> | Hne]; [| lia ].
      rewrite Hin by lia; apply Htier.
  - reflexivity.
  - apply Hl; assumption.
Qed.

Definition per_univ (i : uidx) : relation domain := fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem i ↘ R'.
#[global] Arguments per_univ _ _ _ /.
Hint Transparent per_univ : mctt.
Hint Unfold per_univ : mctt.

Lemma per_univ_elem_core_univ' : forall j i elem_rel,
    uidx_lt (ul j) i ->
    (elem_rel <~> per_univ j) ->
    DF 𝕌ω@j ≈ 𝕌ω@j ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  simp per_univ_elem.
  econstructor; [eassumption | reflexivity |].
  rewrite per_univ_below_spec by assumption.
  assumption.
Qed.

Lemma per_univ_elem_core_suniv' : forall l l' i elem_rel,
    Dom l ≈ l' ∈ per_lvl ->
    uidx_lt (us (dlvl_real l)) i ->
    (elem_rel <~> per_univ (us (dlvl_real l))) ->
    DF 𝕌@l ≈ 𝕌@l' ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  simp per_univ_elem.
  eapply per_univ_elem_core_suniv; [eassumption | eassumption |].
  rewrite per_univ_below_spec by assumption.
  assumption.
Qed.

Hint Resolve per_univ_elem_core_univ' per_univ_elem_core_suniv' : mctt.

(** ** Universe/Element PER Induction Principle *)

Section Per_univ_elem_ind_def.
  Hypothesis
    (motive : uidx -> relation domain -> domain -> domain -> Prop)
      (case_U : forall i {j j' elem_rel},
          uidx_lt (ul j) i -> j = j' ->
          (elem_rel <~> per_univ j) ->
          (forall A B R, DF A ≈ B ∈ per_univ_elem j ↘ R -> motive j R A B) ->
          motive i elem_rel 𝕌ω@j 𝕌ω@j')
      (case_SU : forall i {l l' elem_rel},
          uidx_lt (us (dlvl_real l)) i ->
          Dom l ≈ l' ∈ per_lvl ->
          (elem_rel <~> per_univ (us (dlvl_real l))) ->
          (forall A B R, DF A ≈ B ∈ per_univ_elem (us (dlvl_real l)) ↘ R ->
                         motive (us (dlvl_real l)) R A B) ->
          motive i elem_rel 𝕌@l 𝕌@l')
      (case_L : forall i {n elem_rel},
          (elem_rel <~> per_lvl_at n) ->
          motive i elem_rel (Levelᵈ@n) (Levelᵈ@n))
      (case_True : forall i {elem_rel},
          (elem_rel <~> per_True) ->
          motive i elem_rel ⊤ᵈ ⊤ᵈ)
      (case_False : forall i {elem_rel},
          (elem_rel <~> per_ne) ->
          motive i elem_rel ⊥ᵈ ⊥ᵈ)
      (case_Pi :
        forall i {a ρ B a' ρ' B' in_rel}
           (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
           {elem_rel},
          DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
          motive i in_rel a a' ->
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
              rel_mod_eval (fun R x y => DF x ≈ y ∈ per_univ_elem i ↘ R /\ motive i R x y) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) ->
          (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
          motive i elem_rel Πᵈ a ρ B Πᵈ a' ρ' B')
      (case_ne : forall i {a b a' b' elem_rel},
          Dom b ≈ b' ∈ per_bot ->
          (elem_rel <~> per_ne) ->
          motive i elem_rel ⇑ a b ⇑ a' b')
      (case_Ind : forall i {p D k M pm ups ups' ns ns'}
          (nr : nat -> nat -> list domain -> relation domain)
          (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
          (dr : nat -> list domain -> exp -> relation domain)
          {elem_rel},
          ind_lookup gc_deps gc_stack p = Some D ->
          grp_tele_ass D ->
          ind_member D k = Some M ->
          im_head M = mh_decl pm ->
          List.length ups = ind_nu D ->
          List.length ups' = ind_nu D ->
          per_top_ps (List.rev (ind_uparams D)) ups ups' ->
          nparams_per D nr ->
          nparams_evals (fun R x y => DF x ≈ y ∈ per_univ_elem i ↘ R /\ motive i R x y) D ups ups' nr ->
          nparams_inv D nr ->
          args_per D nr ar ->
          args_evals (fun R x y => DF x ≈ y ∈ per_univ_elem i ↘ R /\ motive i R x y) D ups ups' nr ar ->
          args_inv D nr ar ->
          doms_per D nr ar dr ->
          doms_evals (fun R x y => DF x ≈ y ∈ per_univ_elem i ↘ R /\ motive i R x y) D ups ups' nr ar dr ->
          doms_inv D nr ar dr ->
          adm_uparams D ups nr ar dr ups' ->
          adm_uparams D ups nr ar dr ups ->
          tele_rel (nr k) (List.rev (im_nparams M)) ns ns' ->
          (elem_rel <~> grp_rel p D ups nr ar dr k ups ups' ns ns') ->
          motive i elem_rel (d_ind p k (ups ++ ns)) (d_ind p k (ups' ++ ns')))
      (case_Rec : forall i {p R ns ns'} (fr : nat -> list domain -> relation domain) {elem_rel},
          record_lookup gc_deps gc_stack p = Some R ->
          List.NoDup (List.map fst (record_fields R)) ->
          List.length ns = List.length (record_params R) ->
          List.length ns' = List.length (record_params R) ->
          per_top_ps (List.rev (record_params R)) ns ns' ->
          fields_per R fr ->
          fields_evals (fun R x y => DF x ≈ y ∈ per_univ_elem i ↘ R /\ motive i R x y) R ns ns' fr ->
          fields_inv R fr ->
          (elem_rel <~> record_rel R fr) ->
          motive i elem_rel (d_record p ns) (d_record p ns')).

  Lemma per_univ_elem_ind i a b R (H : per_univ_elem i a b R) : motive i a b R.
  Proof.
    revert a b R H.
    induction i as [i IHi] using (well_founded_ind uidx_wf).
    intros R a b H.
    refine (per_univ_elem_core_strong_ind i _ (motive i) _ _
              (fun _ _ => case_L i) (fun _ => case_True i) (fun _ => case_False i)
              _ (fun _ _ _ _ _ => case_ne i) _ (fun _ _ _ _ fr _ => case_Rec i fr) R a b H).
    - intros j j' elem_rel lt_j_i Heq HE.
      rewrite per_univ_below_spec in HE by assumption.
      eapply case_U; eauto.
    - intros l l' elem_rel lt_j_i Hper HE.
      rewrite per_univ_below_spec in HE by assumption.
      eapply case_SU; eauto.
    - intros * Ha IHa Hper HT HE.
      eapply case_Pi; eassumption.
    - intros * Hl Hass HM Hh Hu Hu' Hps HnP Hn HnI HaP Ha HaI HdP Hd HdI Hcl Hcd Hns HE.
      eapply case_Ind; eassumption.
  Qed.
End Per_univ_elem_ind_def.


(** * Universe Subtyping *)

(** [per_subtyp i a b]: the type [a] is below [b], both types of the
    universe at [i]. *)
Inductive per_subtyp : uidx -> domain -> domain -> Prop :=
(** Equal neutral types. *)
| per_subtyp_neut :
  `( Dom b ≈ b' ∈ per_bot ->
     Sub ⇑ a b <: ⇑ a' b' at i )
(** A type of levels below every type of levels of a larger sort. *)
| per_subtyp_level :
  `( m <= n ->
     Sub Levelᵈ@m <: Levelᵈ@n at i )
(** [⊤] below itself. *)
| per_subtyp_True :
  `( Sub ⊤ᵈ <: ⊤ᵈ at i )
(** [⊥] below itself. *)
| per_subtyp_False :
  `( Sub ⊥ᵈ <: ⊥ᵈ at i )
(** A universe below a larger one. *)
| per_subtyp_univ :
  `( i <= j ->
     uidx_lt (ul j) k ->
     Sub 𝕌ω@i <: 𝕌ω@j at k )
(** A small universe below a larger one: the canonical order on their levels
    ([per_sublvl]), never the order on realisers. *)
| per_subtyp_suniv :
  `( per_sublvl l l' ->
     uidx_lt (us (dlvl_real l')) k ->
     Sub 𝕌@l <: 𝕌@l' at k )
(** A small universe below a large one. *)
| per_subtyp_small_large :
  `( Dom l ≈ l ∈ per_lvl ->
     uidx_lt (ul j) k ->
     Sub 𝕌@l <: 𝕌ω@j at k )
(** A [Π] below another with an equal domain and a smaller codomain. *)
| per_subtyp_pi :
  `( forall (in_rel : relation domain) elem_rel elem_rel',
        DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
        (forall c c' b b',
            Dom c ≈ c' ∈ in_rel ->
            ⟦ B ⟧ ρ ↦ c ↘ b ->
            ⟦ B' ⟧ ρ' ↦ c' ↘ b' ->
            Sub b <: b' at i) ->
        DF Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ_elem i ↘ elem_rel ->
        DF Πᵈ a' ρ' B' ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel' ->
        Sub Πᵈ a ρ B <: Πᵈ a' ρ' B' at i)
(** An inductive type below itself: inductive types are invariant. *)
| per_subtyp_indty :
  `( forall elem_rel,
        DF d_ind p k as1 ≈ d_ind p k as2 ∈ per_univ_elem i ↘ elem_rel ->
        Sub d_ind p k as1 <: d_ind p k as2 at i)
(** A record type below itself: records are invariant. *)
| per_subtyp_record :
  `( forall elem_rel,
        DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem i ↘ elem_rel ->
        Sub d_record p ns <: d_record p ns' at i)
where "'Sub' a <: b 'at' i" := (per_subtyp i a b) : type_scope.

 Hint Constructors per_subtyp : mctt.

Definition rel_typ (i : nat) A ρ A' ρ' R' := rel_mod_eval (per_univ_elem i) A ρ A' ρ' R'.
#[global] Arguments rel_typ _ _ _ _ _ _ /.
Hint Transparent rel_typ : mctt.
Hint Unfold rel_typ : mctt.

(** Two terms evaluate to related elements. *)
Definition rel_elem M ρ M' ρ' (R : relation domain) := rel_mod_eval (fun R a a' => R a a') M ρ M' ρ' R.
#[global] Arguments rel_elem _ _ _ _ _ /.
Hint Transparent rel_elem : mctt.
Hint Unfold rel_elem : mctt.

(** * Module PER

    Module values are related extensionally in their missing parameters, as
    [Π] relates functions, and structurally once saturated:

    - Two values still lacking a parameter are related when their next
      parameters' types are, and the values at every related pair of
      arguments are related ([per_dmod_fun]).
    - Two saturated values are related when they are the same global module
      at related arguments ([per_dmod_global]), or two bodies related entry
      by entry as written, each entry seen in the environment the entries
      before it make, read through the entries their local opens generate
      ([per_dmod_body]): a definition by its type and value, a module by its
      closure, a local open by the value of its target.

    No value is a saturated alias ([eval_close]), so these are all the
    saturated values.  Two different global paths are never related.  The
    relation is not indexed by a type: the types it relates members at are
    those the units declare. *)

(** The next parameter's type a module value still lacks: a closure's
    outermost missing parameter, in its environment; a global module's
    first parameter past its arguments; a submodule closure's base's. *)
Inductive nextparam : dmod -> domain -> Prop :=
| np_local : forall Δ A D ρ a,
    ⟦ A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a ->
    nextparam (dm_local (Δ ++ ce_ass A :: nil) D ρ) a
| np_global : forall p T Φ args A a,
    gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    List.nth_error (List.rev T) (List.length args) = Some (ce_ass A) ->
    ⟦ A ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil args ↘ a ->
    nextparam (dm_global p args) a
| np_member : forall h ch a,
    nextparam h a ->
    nextparam (dm_member h ch) a.

Inductive per_dmod : dmod -> dmod -> Prop :=
(** The same saturated global module, its arguments related at its
    telescope: a body stored at [p], a closed module or an open frame. *)
| per_dmod_global :
  `{ gc_loc gc_deps gc_stack p = Some (T, Φ) ->
     List.length args = List.length T ->
     per_gargs (List.rev T) nil nil args args' ->
     per_dmod (dm_global p args) (dm_global p args') }
(** Two saturated bodies, related entry by entry as written. *)
| per_dmod_body :
  `{ per_body ρ Φ ρ' Φ' ->
     per_dmod (dm_local nil (md_body sm Φ) ρ) (dm_local nil (md_body sm' Φ') ρ') }
(** Two values lacking a parameter: related at every related pair of
    arguments. *)
| per_dmod_fun :
  `{ forall R,
       nextparam h a ->
       nextparam h' a' ->
       per_univ_elem i R a a' ->
       (forall c c', R c c' -> exists hc, $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc) ->
       (forall c c', R c c' -> exists hc', $ᵐ| h' & c' | gc_deps ⍮ gc_stack ↘ hc') ->
       (forall c c' hc hc', R c c' -> $ᵐ| h & c | gc_deps ⍮ gc_stack ↘ hc -> $ᵐ| h' & c' | gc_deps ⍮ gc_stack ↘ hc' ->
          per_dmod hc hc') ->
       per_dmod h h' }
(** Arguments of a global module, outermost first, against its telescope. *)
with per_gargs : list centry -> env -> env -> list domain -> list domain -> Prop :=
(** No more arguments. *)
| per_gargs_nil :
  `{ per_gargs ts ρ ρ' nil nil }
(** An argument related at its parameter's type, then the rest. *)
| per_gargs_cons :
  `{ forall R,
       rel_typ i A ρ A ρ' R ->
       R a a' ->
       per_gargs ts (ρ ↦ a) (ρ' ↦ a') args args' ->
       per_gargs (ce_ass A :: ts) ρ ρ' (a :: args) (a' :: args') }
(** Two bodies as written, each entry seen in the environment its
    predecessors make, read through the entries their local opens generate
    ([kbody], [eval_benv]). *)
with per_body : env -> gmod -> env -> gmod -> Prop :=
(** Two empty bodies. *)
| per_body_nil :
  `{ per_body ρ gm_nil ρ' gm_nil }
(** A definition each, with related types and values. *)
| per_body_def :
  `{ forall R,
       per_body ρ Φ ρ' Φ' ->
       kbody gc_deps gc_stack ρ Φ Φx ->
       kbody gc_deps gc_stack ρ' Φ' Φx' ->
       ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
       ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' ->
       rel_typ i A ρ1 A' ρ1' R ->
       rel_elem M ρ1 M' ρ1' R ->
       per_body ρ (gm_ext Φ y (ge_def b pv A (Some M))) ρ' (gm_ext Φ' y (ge_def b' pv' A' (Some M'))) }
(** A submodule each, with related closures. *)
| per_body_mod :
  `{ per_body ρ Φ ρ' Φ' ->
     kbody gc_deps gc_stack ρ Φ Φx ->
     kbody gc_deps gc_stack ρ' Φ' Φx' ->
     ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
     ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' ->
     ⟦ Δy ⊢ Dy ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h ->
     ⟦ Δy' ⊢ Dy' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ1' ↘ h' ->
     per_dmod h h' ->
     per_body ρ (gm_ext Φ y (ge_mod pm (gu_mk Δy Dy))) ρ' (gm_ext Φ' y (ge_mod pm' (gu_mk Δy' Dy'))) }
(** A definition with a module part each: related types and values, as a
    definition each, and related closures, as a submodule each. *)
| per_body_dm :
  `{ forall R,
       per_body ρ Φ ρ' Φ' ->
       kbody gc_deps gc_stack ρ Φ Φx ->
       kbody gc_deps gc_stack ρ' Φ' Φx' ->
       ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
       ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' ->
       rel_typ i A ρ1 A' ρ1' R ->
       rel_elem M ρ1 M' ρ1' R ->
       ⟦ Δy ⊢ Dy ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h ->
       ⟦ Δy' ⊢ Dy' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ1' ↘ h' ->
       per_dmod h h' ->
       per_body ρ (gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy))) ρ' (gm_ext Φ' y (ge_def_mod pv' A' M' (gu_mk Δy' Dy'))) }
(** A local open each, of the same items, with related targets, the
    entries each generates evaluating.  Each side's target, read again after
    the first [k] entries it generates (as the [k+1]-th entry reads it), has
    a value related to its value before them. *)
| per_body_open :
  `{ per_body ρ Φ ρ' Φ' ->
     kbody gc_deps gc_stack ρ Φ Φx ->
     kbody gc_deps gc_stack ρ' Φ' Φx' ->
     ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 ->
     ⟦ Φx' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρ1' ->
     ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ h ->
     ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ1' ↘ h' ->
     per_dmod h h' ->
     kbody gc_deps gc_stack ρ (gm_open Φ H its) Φo ->
     kbody gc_deps gc_stack ρ' (gm_open Φ' H' its) Φo' ->
     ⟦ Φo ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρo ->
     ⟦ Φo' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρo' ->
     (forall k ρk, k < List.length its ->
        ⟦ gm_dropn (List.length its - k) Φo ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρk ->
        exists hk, ⟦ modexp_wk H (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk) ->
     (forall k ρk', k < List.length its ->
        ⟦ gm_dropn (List.length its - k) Φo' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρk' ->
        exists hk', ⟦ modexp_wk H' (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk' ↘ hk') ->
     (forall k ρk hk, k < List.length its ->
        ⟦ gm_dropn (List.length its - k) Φo ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρk ->
        ⟦ modexp_wk H (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk ↘ hk -> per_dmod hk h) ->
     (forall k ρk' hk', k < List.length its ->
        ⟦ gm_dropn (List.length its - k) Φo' ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ' ↘ ρk' ->
        ⟦ modexp_wk H' (wk_shiftn k) ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρk' ↘ hk' -> per_dmod hk' h') ->
     per_body ρ (gm_open Φ H its) ρ' (gm_open Φ' H' its) }
.

Scheme per_dmod_mut_ind := Induction for per_dmod Sort Prop
with per_gargs_mut_ind := Induction for per_gargs Sort Prop
with per_body_mut_ind := Induction for per_body Sort Prop.
Combined Scheme per_dmod_mut_ind_all from
  per_dmod_mut_ind, per_gargs_mut_ind, per_body_mut_ind.

Hint Constructors nextparam per_dmod per_gargs per_body : mctt.

(** Two module expressions evaluate to related module values. *)
#[warnings="-cannot-define-projection"]
Record rel_mexp (H : modexp) (ρ : env) (H' : modexp) (ρ' : env) : Prop := mk_rel_mexp
  { rme_left : dmod
  ; rme_right : dmod
  ; rme_eval_left : ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ rme_left
  ; rme_eval_right : ⟦ H' ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ' ↘ rme_right
  ; rme_rel : per_dmod rme_left rme_right }.

(** A module value is related to the value of a module expression. *)
Definition tie_mod (m : dmod) (H : modexp) (ρ : env) : Prop :=
  exists h, ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\ per_dmod m h.

(** * Context/Environment PER *)

(** The environments a definition with a module part relates, given the
    PER of the tails and the head relation at related tails: those of a
    definition entry for its terms [M], [M'], and those of a module slot
    for its units [U], [U'], at the same head. *)
Record per_ctx_env_dm_rel (tail_rel : relation env)
    (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
    (M M' : exp) (U U' : gunit) (ρ ρ' : env) : Prop := mk_per_ctx_env_dm_rel
  { (** The tails are related *)
    per_ctx_env_dm_rel_tail : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel
    (** The heads are related at the tails' head relation *)
  ; per_ctx_env_dm_rel_head : Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel per_ctx_env_dm_rel_tail
    (** The left head is related to the value of [M] over the left tail *)
  ; per_ctx_env_dm_rel_left_term : exists m, ⟦ M ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ head_rel per_ctx_env_dm_rel_tail
    (** and to that of [M'] *)
  ; per_ctx_env_dm_rel_left_term' : exists m, ⟦ M' ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ head_rel per_ctx_env_dm_rel_tail
    (** The right head is related to the value of [M] over the right tail *)
  ; per_ctx_env_dm_rel_right_term : exists m', ⟦ M ⟧ ρ'↯ ↘ m' /\ Dom m' ≈ (ρ' 0) ∈ head_rel per_ctx_env_dm_rel_tail
    (** and to that of [M'] *)
  ; per_ctx_env_dm_rel_right_term' : exists m', ⟦ M' ⟧ ρ'↯ ↘ m' /\ Dom m' ≈ (ρ' 0) ∈ head_rel per_ctx_env_dm_rel_tail
    (** The left head's module is tied to the closure of [U] over the left tail *)
  ; per_ctx_env_dm_rel_left_unit : tie_mod (env_mod ρ 0) (me_lit U) ρ↯
    (** and to that of [U'] *)
  ; per_ctx_env_dm_rel_left_unit' : tie_mod (env_mod ρ 0) (me_lit U') ρ↯
    (** The right head's module is tied to the closure of [U] over the right tail *)
  ; per_ctx_env_dm_rel_right_unit : tie_mod (env_mod ρ' 0) (me_lit U) ρ'↯
    (** and to that of [U'] *)
  ; per_ctx_env_dm_rel_right_unit' : tie_mod (env_mod ρ' 0) (me_lit U') ρ'↯ }.

Inductive per_ctx_env : relation env -> ctx -> ctx -> Prop :=
(** The empty context, all environments related. *)
| per_ctx_env_nil :
  `{ forall env_rel,
        (env_rel <~> fun ρ ρ' => True) ->
        EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }
(** An assumption: related tails, and heads related at the type. *)
| per_ctx_env_cons :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
        env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (env_rel <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
               Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) ->
        EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_rel }
(** A definition entry: the bodies are related, and each head of the
    environment is related to the value of both bodies in that head's tail.
    Asking for both bodies on each side makes the relation invariant under
    swapping the two contexts, which is what symmetry needs. *)
| per_ctx_env_cons_def :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
        env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_elem M ρ M' ρ' (head_rel equiv_ρ_ρ')) ->
        (env_rel <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
               Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop /\
               (exists m, ⟦ M ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) /\
               (exists m, ⟦ M' ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) /\
               (exists m', ⟦ M ⟧ ρ'↯ ↘ m' /\ Dom m' ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) /\
               (exists m', ⟦ M' ⟧ ρ'↯ ↘ m' /\ Dom m' ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop)) ->
        EF Γ ▸ A ≔ M ≈ Γ' ▸ A' ≔ M' ∈ per_ctx_env ↘ env_rel }
(** A module slot: the two units, as literals, evaluate to related values
    over related tails, and each head of the environment is related to the
    values of both units over its own tail. *)
| per_ctx_env_cons_mod :
  `{ forall tail_rel env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_mexp (me_lit U) ρ (me_lit U') ρ') ->
        (env_rel <~> fun ρ ρ' =>
             (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) /\
             tie_mod (env_mod ρ 0) (me_lit U) ρ↯ /\
             tie_mod (env_mod ρ 0) (me_lit U') ρ↯ /\
             tie_mod (env_mod ρ' 0) (me_lit U) ρ'↯ /\
             tie_mod (env_mod ρ' 0) (me_lit U') ρ'↯) ->
        EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ env_rel }
(** A definition with a module part: the clauses of a definition entry for
    its term part and those of a module slot for its unit, at the same
    head. *)
| per_ctx_env_cons_dm :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
        env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_elem M ρ M' ρ' (head_rel equiv_ρ_ρ')) ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            rel_mexp (me_lit U) ρ (me_lit U') ρ') ->
        (env_rel <~> per_ctx_env_dm_rel tail_rel (@head_rel) M M' U U') ->
        EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ' ▸ₘ A' ≔ M' ‖ U' ∈ per_ctx_env ↘ env_rel }
.
Hint Constructors per_ctx_env : mctt.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env R' Γ Γ'.


(** * Context Subtyping *)

Inductive per_ctx_subtyp : ctx -> ctx -> Prop :=
(** The empty context. *)
| per_ctx_subtyp_nil :
  SubE ⋅ <: ⋅
(** An assumption of a smaller type. *)
| per_ctx_subtyp_cons :
  `{ forall tail_rel env_rel env_rel',
        SubE Γ <: Γ' ->
        EF Γ ≈ Γ ∈ per_ctx_env ↘ tail_rel ->
        (forall ρ ρ' a a'
           (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            ⟦ A ⟧ ρ ↘ a ->
            ⟦ A' ⟧ ρ' ↘ a' ->
            Sub a <: a' at (ul i)) ->
        EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ env_rel ->
        EF Γ' ▹ A' ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_rel' ->
        SubE Γ ▹ A <: Γ' ▹ A' }
(** A context ending in a definition refines another context when its
    environments are environments of the other.  This covers a definition of a
    supertype with an equal body and an assumption of a supertype. *)
| per_ctx_subtyp_def :
  `{ forall env_rel env_rel',
        SubE Γ <: Γ' ->
        EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ env_rel ->
        EF (e :: Γ')%list ≈ (e :: Γ')%list ∈ per_ctx_env ↘ env_rel' ->
        (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_rel -> Dom ρ ≈ ρ' ∈ env_rel') ->
        SubE Γ ▸ A ≔ M <: (e :: Γ')%list }
(** A slot refines a slot when its environments are environments of the
    other. *)
| per_ctx_subtyp_mod :
  `{ forall env_rel env_rel',
        SubE Γ <: Γ' ->
        EF Γ ▹ₘ U ≈ Γ ▹ₘ U ∈ per_ctx_env ↘ env_rel ->
        EF Γ' ▹ₘ U' ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ env_rel' ->
        (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_rel -> Dom ρ ≈ ρ' ∈ env_rel') ->
        SubE Γ ▹ₘ U <: Γ' ▹ₘ U' }
(** A definition with a module part refines one when its environments are
    environments of the other. *)
| per_ctx_subtyp_dm :
  `{ forall env_rel env_rel',
        SubE Γ <: Γ' ->
        EF Γ ▸ₘ A ≔ M ‖ U ≈ Γ ▸ₘ A ≔ M ‖ U ∈ per_ctx_env ↘ env_rel ->
        EF Γ' ▸ₘ A' ≔ M' ‖ U' ≈ Γ' ▸ₘ A' ≔ M' ‖ U' ∈ per_ctx_env ↘ env_rel' ->
        (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_rel -> Dom ρ ≈ ρ' ∈ env_rel') ->
        SubE Γ ▸ₘ A ≔ M ‖ U <: Γ' ▸ₘ A' ≔ M' ‖ U' }
where "'SubE' Γ <: Δ" := (per_ctx_subtyp Γ Δ) : type_scope.

Hint Constructors per_ctx_subtyp : mctt.

End Fixed_GCtx.

Notation "'Dom' a ≈ b ∈ R" := ((R a b : Prop) : Prop) (at level 70, a at level 69, b at level 69, R constr).
Notation "'DF' a ≈ b ∈ R ↘ R'" := ((R R' a b : Prop) : Prop) (at level 70, a at level 69, b at level 69, R constr, R' constr).
Notation "'Exp' a ≈ b ∈ R" := (R a b : (Prop : Type)) (at level 70, a at level 69, b at level 69, R constr).
Notation "'EF' a ≈ b ∈ R ↘ R'" := (R R' a b : (Prop : Type)) (at level 70, a at level 69, b at level 69, R constr, R' constr).
Notation "R ~> R'" := (subrelation R R') (at level 70, right associativity).
Notation "R <~> R'" := (relation_equivalence R R') (at level 95, no associativity).
#[export]
Hint Constructors rel_mod_eval : mctt.
#[export]
Hint Constructors rel_mod_app : mctt.
#[export]
Hint Transparent per_bot : mctt.
#[export]
Hint Unfold per_bot : mctt.
#[export]
Hint Transparent per_top : mctt.
#[export]
Hint Unfold per_top : mctt.
#[export]
Hint Transparent per_top_typ : mctt.
#[export]
Hint Unfold per_top_typ : mctt.
#[export]
Hint Transparent per_True : mctt.
#[export]
Hint Unfold per_True : mctt.
#[export]
Hint Constructors per_ne : mctt.
#[export]
Hint Constructors per_univ_elem_core : mctt.
#[export]
Hint Transparent per_univ : mctt.
#[export]
Hint Unfold per_univ : mctt.
#[export]
Hint Rewrite @per_univ_elem_equation_1 : per_univ_elem.
#[export]
Hint Resolve per_univ_elem_core_univ' per_univ_elem_core_suniv' : mctt.
Notation "'Sub' a <: b 'at' i" := (per_subtyp i a b) : type_scope.
#[export]
Hint Constructors per_subtyp : mctt.
#[export]
Hint Transparent rel_typ : mctt.
#[export]
Hint Unfold rel_typ : mctt.
#[export]
Hint Transparent rel_elem : mctt.
#[export]
Hint Unfold rel_elem : mctt.
#[export]
Hint Constructors nextparam per_dmod per_gargs per_body : mctt.
#[export]
Hint Constructors per_ctx_env : mctt.
Notation "'SubE' Γ <: Δ" := (per_ctx_subtyp Γ Δ) : type_scope.
#[export]
Hint Constructors per_ctx_subtyp : mctt.

(** Induction on a [per_univ_elem] hypothesis.  [induction H using
    per_univ_elem_ind] does not apply, because the instance is an argument of
    [per_univ_elem] that the eliminator does not quantify over as an index.
    This tactic moves the hypotheses about the indices into the motive, and
    each case introduces exactly its own binders. *)
Ltac per_univ_elem_induction_core HH ih :=
  lazymatch type of HH with
  | per_univ_elem ?i ?R ?a ?b =>
      repeat match goal with
             | Hd : ?T |- _ =>
                 lazymatch Hd with HH => fail | i => fail | R => fail | a => fail | b => fail | _ => idtac end;
                 lazymatch T with
                 | context [i] => revert Hd | context [R] => revert Hd
                 | context [a] => revert Hd | context [b] => revert Hd
                 end
             end;
      revert HH; revert i R a b;
      refine (per_univ_elem_ind _ _ _ _ _ _ _ _ _ _);
      (** The level case has one binder more than the other closed types: the
          sort of its type of levels. *)
      [ do 8 intro | do 8 intro | do 4 intro | do 3 intro | do 3 intro | do 11 intro; ih; do 3 intro | do 8 intro
      | do 34 intro | do 16 intro ]; cbv beta
  end.

(** The analogue of [induction H using per_univ_elem_ind]; the induction
    hypotheses are named [IHH]. *)
Ltac per_univ_elem_induction H :=
  let IHn := fresh "IH" H in
  let HH := fresh "Hpue" in
  rename H into HH;
  per_univ_elem_induction_core HH ltac:(intro IHn).

(** The analogue of [induction 1 using per_univ_elem_ind]. *)
Ltac per_univ_elem_induction1 :=
  intros until 1;
  match goal with H : per_univ_elem _ _ _ _ |- _ => per_univ_elem_induction_core H ltac:(intro) end.
