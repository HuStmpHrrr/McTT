From Stdlib Require Import String.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
#[local] Open Scope list_scope.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.

Reserved Notation "'Rnf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rne' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).
Reserved Notation "'Rprf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rlets' ρ 'at' k 'in' Θ '⍮' Ξ '⍮' s ↘ bs" (at level 70, ρ at level 69, k at level 69, Θ at level 69, Ξ at level 69, s constr, bs at level 69).
Reserved Notation "'Rent' e 'in' Θ '⍮' Ξ '⍮' s ↘ b" (at level 70, e at level 69, Θ at level 69, Ξ at level 69, s constr, b at level 69).

Reserved Notation "'Rflds' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" (at level 70, v at level 69, fl at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Fs at level 69).
Reserved Notation "'Rps' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rcargs' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rsh' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, V at level 69).
Reserved Notation "'Rbrs' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" (at level 70, Bs at level 69, cs at level 69, Mi at level 0, r at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, Mv at level 0, A at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Bs' at level 69).
Reserved Notation "'Rblks' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" (at level 70, i at level 0, Ms at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, sel at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, NBks at level 69).

Reserved Notation "'Ftele' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fcargs' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fihs' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ρm at level 0, As at level 0, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, ihs at level 69).
Reserved Notation "'⟦wihs' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ihs at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).

Generalizable All Variables.

(** ** Fresh Variables of the Telescopes of an Inductive Type

    The readback of a stuck eliminator reads its motive and its branches
    under fresh variables, of the types the declaration gives: the
    non-uniform parameters, the arguments of a constructor, and the
    recursive results.  Each type is evaluated in the environment of the
    variables before it, which holds each variable at its type; nothing is
    built.  A variable of a propositional type is a neutral proof. *)

(** A telescope, outermost first: [fresh_tele ρ T s vs] gives the variables
    from [s] on, the type of each evaluated in [ρ] extended by those
    before it. *)
Inductive fresh_tele (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> list domain -> Prop :=
(** No entry *)
| fresh_tele_nil :
  `( Ftele nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The first entry's variable at its type, then the rest with it in the
    environment *)
| fresh_tele_cons :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Ftele T in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ ⍮ S s ↘ vs ->
     Ftele ce_ass κ A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Ftele' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fresh_tele Θ Ξ ρ T s vs) : type_scope.

(** The arguments of a constructor of [p] at the uniform parameters [ups]:
    a non-recursive one of the type its declaration gives, in the
    environment of the parameters and the non-recursive arguments before
    it; a recursive one of the type of its shape there. *)
Inductive fresh_cargs (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> list domain -> Prop :=
(** No argument *)
| fresh_cargs_nil :
  `( Fcargs nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument: its variable at its declared type *)
| fresh_cargs_arg :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ ⍮ S s ↘ vs ->
     Fcargs ca_arg r A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
(** A recursive argument: its variable at its shape's type, which is
    relevant *)
| fresh_cargs_rec :
  `( ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ S s ↘ vs ->
     Fcargs ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Fcargs' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fresh_cargs Θ Ξ p ups ρ gs s vs) : type_scope.

(** The fresh variables of the recursive results along the leaf paths of
    an argument: one at each type [as] lists whose flag is [true] (a path
    of the container's, E1′), from [s] on; none where it is [false]. *)
Inductive fresh_leaf_vars : list bool -> list domain -> nat -> list domain -> Prop :=
(** No path left *)
| fresh_leaf_vars_nil : forall s, fresh_leaf_vars nil nil s nil
(** A path of the container's: a fresh variable at its type *)
| fresh_leaf_vars_fresh : forall bs a as' s vs,
    fresh_leaf_vars bs as' (S s) vs -> fresh_leaf_vars (true :: bs) (a :: as') s (⇑! a s :: vs)
(** A path nested through: none *)
| fresh_leaf_vars_skip : forall bs a as' s vs,
    fresh_leaf_vars bs as' s vs -> fresh_leaf_vars (false :: bs) (a :: as') s vs.

(** The recursive results of the arguments [vs] of kinds [gs]: one per
    leaf path of each argument recursive also in [gs'] (the kinds the
    eliminator read has them in, E1′, of the group [Dc]) that is a path of
    [Dc]'s ([leaf_in]), of the type of its recursive result, the motives
    [As] in [ρ], the shape's components in the environment [ρa] of the
    parameters and the non-recursive arguments before it, as [gs] has
    them, of the group at [p] at [ups].  A path nested through (of an
    argument recursive in [gs] only, or through a field the container's
    record view has as non-recursive) has no variable; its result is the
    eliminator's ([wrap_ihs_eval]). *)
Inductive fresh_ihs (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (p : qname) (ups : list domain) (Dc : ind_decl) :
  env -> list carg -> list carg -> list domain -> nat -> list domain -> Prop :=
(** No argument, no result *)
| fresh_ihs_nil :
  `( Fihs nil at nil nil of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ nil )
(** A non-recursive argument: none, the argument entering [ρa] *)
| fresh_ihs_arg :
  `( Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ↦ v ⦂ entry_type_closure T ρa ⍮ s ↘ ihs ->
     Fihs v :: vs at (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
(** An argument recursive in both: a fresh variable at each recursive
    result's type, along the paths of the container's *)
| fresh_ihs_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ihty v of t at p ups under ρ As ⟧ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
     fresh_leaf_vars (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s ihs1 ->
     Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ (List.length ihs1 + s) ↘ ihs ->
     Fihs v :: vs at (ca_rec t' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ++ ihs )
(** An argument recursive in [gs] only (nested through): no variable *)
| fresh_ihs_nest :
  `( Fihs vs at gs' gs of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
     Fihs v :: vs at (ca_arg ra' T' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
where "'Fihs' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" :=
  (fresh_ihs Θ Ξ ρm As p ups Dc ρ gs' gs vs s ihs) : type_scope.

(** The recursive results along the leaf paths of an argument, its
    group's [rs] and the container's variables [ihs]: the next variable at
    a path of the container's, the group's result at a path nested
    through; [ihs'] are the variables left. *)
Inductive wrap_leaf_vals : list bool -> list domain -> list domain -> list domain -> list domain -> Prop :=
(** No path left *)
| wrap_leaf_vals_nil : forall ihs, wrap_leaf_vals nil nil ihs ihs nil
(** A path of the container's: its variable *)
| wrap_leaf_vals_fresh : forall bs r rs ih ihs ihs' out,
    wrap_leaf_vals bs rs ihs ihs' out -> wrap_leaf_vals (true :: bs) (r :: rs) (ih :: ihs) ihs' (ih :: out)
(** A path nested through: the group's result *)
| wrap_leaf_vals_nest : forall bs r rs ihs ihs' out,
    wrap_leaf_vals bs rs ihs ihs' out -> wrap_leaf_vals (false :: bs) (r :: rs) ihs ihs' (r :: out).

(** The recursive results a branch of a block is read under, when the
    branch is read as one of the eliminator of the group the eliminated
    member is at (E1′): the arguments [vs] of the constructor are those of
    that group's [Dc], of kinds [gs']; the branch's group classifies them
    as [gs].  Along a path of [Dc]'s, the recursive result [ihs] gives (a
    fresh variable); along one nested through, the eliminator of the
    branch's group.  For an eliminator read as its own group's, [Dc] is
    the group, [gs'] is [gs] and the results are [ihs]. *)
Inductive wrap_ihs_eval (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock) (Dc : ind_decl) :
  list carg -> list carg -> list domain -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| wrap_ihs_eval_nil :
  `( ⟦wihs nil of nil nil of Dc with nil under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** Recursive in both: along each path, the next of [ihs] at a path of
    the container's, the eliminator at one nested through *)
| wrap_ihs_eval_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     wrap_leaf_vals (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs ihs' r1 ->
     ⟦wihs vs of gs' gs of Dc with ihs' under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihs v :: vs of (ca_rec t' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ++ r )
(** Recursive for the branch's group only: the eliminator at the
    argument, along each path *)
| wrap_ihs_eval_nest :
  `( ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihs v :: vs of (ca_arg ra' T' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ rs ++ r )
(** Non-recursive: no result *)
| wrap_ihs_eval_arg :
  `( ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihs v :: vs of (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦wihs' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧' Θ '⍮' Ξ '⍮' ρ '↘' r" :=
  (wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r) : type_scope.

#[export]
Hint Constructors fresh_tele fresh_cargs fresh_leaf_vars fresh_ihs wrap_leaf_vals wrap_ihs_eval : mctt.

(** The type value an environment's entry is stored at: the type itself, or
    its closure evaluated. *)
Inductive eval_entry_type (Θ : gdeps) (Ξ : gstack) : entry_type -> domain -> Prop :=
(** A type value *)
| eval_entry_type_value :
  `( eval_entry_type Θ Ξ (entry_type_value a) a )
(** A type in an environment *)
| eval_entry_type_closure :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     eval_entry_type Θ Ξ (entry_type_closure A ρ) a )
(** The type of a recursive argument of a shape *)
| eval_entry_type_shape :
  `( ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     eval_entry_type Θ Ξ (entry_type_shape p ups ρ t) a )
(** The type of a recursive result *)
| eval_entry_type_induction_hypothesis :
  `( ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
     List.nth_error as' i = Some a ->
     eval_entry_type Θ Ξ (entry_type_induction_hypothesis ρm As p ups ρ t v i) a ).

#[export]
Hint Constructors eval_entry_type : mctt.

(** How far past an entry the definition binding it reaches: a module
    entry is bound by its stored unit ([read_entry_mod]), written over the
    entry's tail, so it reaches the free variables of the unit; a term
    entry is bound by the readback of its value, which names no position
    of the environment.  A definition with a module part is bound by its
    term part and its stored unit ([read_entry_dm]), so it reaches the free
    variables of the unit as a module entry does. *)
Definition entry_unit_bound (e : dentry) : nat :=
  match e with
  | de_mod _ U => gunit_free_bound U
  | de_dm _ _ _ U => gunit_free_bound U
  | _ => 0
  end.

(** [proof_scope_from ρ j n]: the least scope at least [n] that is closed
    under the stored units of the entries from [j] on, [ρ] the environment
    from [j] on: the entry at [j], if inside the scope, widens it to the
    positions its unit reaches past it.  A unit reaches only into its own
    tail, so one walk outwards from the innermost entry reaches the
    closure; the recursion is on [ρ]. *)
Fixpoint proof_scope_from (ρ : env) (j n : nat) : nat :=
  match ρ with
  | nil => n
  | e :: ρ' => if Nat.ltb j n then proof_scope_from ρ' (S j) (Nat.max n (S j + entry_unit_bound e)) else n
  end.

(** The environment positions the readback of a kept proof [⋆ᵈ⟨M, ρ⟩]
    binds: those up to the largest free index of [M], so that [M] is
    copied as written, closed under the stored units of the module
    entries among them, which are copied too and may reach further into
    [ρ].  For example:
    - a proof [#0.h] selected from a global module [p] at the argument
      [3] is kept over [ρ = (3 at its parameter's type) ↦ᵐ (p 3) ⦂ p #0]
      ([eval_sel_global_proof]): the scope is [1] by [#0.h], widened to
      [2] by the unit [p #0], and the proof reads back as
      [let n : ℕ ≔ 3 in let module y ≔ p #0 in y.h];
    - under [λ x], a proof [#0.h] in [ℓₘ (F #0) in …] is kept over
      [ρ ↦ x ⦂ … ↦ᵐ h ⦂ F #0]: the scope is widened from [1] to [2], so
      that [x] is bound too. *)
Definition proof_scope (M : exp) (ρ : env) : nat := proof_scope_from ρ 0 (exp_free_bound M).

(** Readback of values into normal and neutral forms in a context with [s]
    variables.  The global context is needed to evaluate closures. *)
Inductive read_nf (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> nf -> Prop :=
| read_nf_type :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ 𝕌ω@i a in Θ ⍮ Ξ ⍮ s ↘ A )
| read_nf_stype :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ 𝕌@n a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A level reads back canonically: its atoms are read, then sorted and
    merged, and a dominated constant is dropped ([lvl_canon]).  Evaluation
    flattens only, so this is where levels equal by the level equations become
    the same normal form.  A neutral level is the single atom at offset [0],
    of the sort of its type ([domain_level_sort]), which is already canonical: the sort
    is read off the neutral's type, not off the type it is read back at.  Its
    atom is stored as read, as [lvl_canon] stores atoms. *)
| read_nf_lvl :
  `( Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnf ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
| read_nf_lvl_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ ordinal_zero (mk_level_atom 0 (domain_level_sort a) M :: nil) )
(** A value of a proposition reads back as a proof term ([read_proof]),
    with the proposition read back as a type.  This is the only rule at a
    propositional type. *)
| read_nf_proof :
  `( domain_kind a = ak_propositional ->
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ P ->
     Rprf m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ a m in Θ ⍮ Ξ ⍮ s ↘ nf_proof P M )
(** A proposition, as an element of [Prop], reads back as a type. *)
| read_nf_prop :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ Propᵈ a in Θ ⍮ Ξ ⍮ s ↘ A )
(** So does a type of levels, as an element of [LevelSort]. *)
| read_nf_at_level_sort :
  `( Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ LevelSortᵈ a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A function, η-long: its body applied to a fresh variable of its
    domain.  Its codomain is not a proposition (a function into
    propositions is a proof, [read_nf_proof]). *)
| read_nf_fn :
  `( (** The codomain's kind is not propositional. *)
     evaluated_kind κc ->
     (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     (** The normal form of the η-expanded body. *)
     $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rnf ⇓ b m' in Θ ⍮ Ξ ⍮ S s ↘ M ->

     Rnf ⇓ (d_pi κd κc a ρ B) m in Θ ⍮ Ξ ⍮ s ↘ λⁿ A M )
(** A neutral at a neutral type that is not a proposition, with the kind
    of its type *)
| read_nf_neut :
  `( evaluated_kind (domain_kind (⇑ a b)) ->
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (⇑ a b)} M )
(** A constructor at all its parameters and arguments: the parameters are
    read off the type, at the types the declaration gives them, and the
    arguments at theirs. *)
| read_nf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     Rps as' at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargs List.skipn (im_np D Mk) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (im_params D Mk)) as' ⍮ s ↘ Args ->
     Rnf ⇓ (d_ind p k as') (d_con p k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p k c (Ps ++ Args) )
(** A constructor at a view of the group at [p], a value of the
    container's member: read as the view's constructor, its parameters off
    the type at the view's parameters, its arguments at the view's own
    telescopes, so that the container's parameters at the view's arguments
    are not read: the arguments are the last [List.length gs] values. *)
| read_nf_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length vs = (n + List.length gs)%nat ->
     Rps as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargs List.skipn n vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (im_params D Mj)) as' ⍮ s ↘ Args ->
     Rnf ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** Any value at a record view of the group at [p], η-long: read as the
    view's constructor at the type's parameters, the group's uniform ones,
    its arguments the value's projections, each at the group's own
    telescope, as the view classifies the field.  The instance is not
    read: the record's own parameters at it are not, nor are the record's
    field types. *)
| read_nf_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     List.length as' = ind_nu D ->
     ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws ->
     Rps as' at List.rev (ind_uparams D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargs ws at gs of p as' in Θ ⍮ Ξ ⍮ decl_env D as' ⍮ s ↘ Args ->
     Rnf ⇓ (d_ind p j as') v in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** A neutral at a member of a group that is no record view, with the
    kind of its type (relevant) *)
| read_nf_ind_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_is_rview Mk = false ->
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf ⇓ (d_ind p k as') (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (d_ind p k as')} M )
(** Any value of a record type, η-long and type-directed: the type's
    parameters at their telescope, and each field's projection at the
    field's type at those parameters and the projections before it. *)
| read_nf_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rps ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rflds v at record_fields R in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (record_params R)) ns ⍮ s ↘ Fs ->
     Rnf ⇓ (d_record p ns) v in Θ ⍮ Ξ ⍮ s ↘ nf_tuple p Ps (List.map fst (record_fields R)) Fs )
where "'Rnf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_nf Θ Ξ s m M) : type_scope
with read_ne (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( Rne #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
| read_ne_app :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnf n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rne m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
(** Ex falso at the type [c]: the type read back, and the proof of [⊥] as
    a term. *)
| read_ne_absurd :
  `( Rtyp c in Θ ⍮ Ξ ⍮ s ↘ C ->
     Rprf p in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rne efqᵈ p return c in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return C )
| read_ne_glob :
  `( Rne d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
(** A stuck eliminator of the group at [p] at its member [j], read as the
    eliminator of the group the member is at, [pc] (E1′: the container's,
    at a view): one block per member of that group, each block that of the
    member of [p]'s group [im_sel] gives, read under fresh variables of the
    telescopes of that member of [p]'s group at uniform parameters [ups],
    each block's motive binding its own member's non-uniform parameters
    and the scrutinee ([blocks_binder_count_at D None]), the paths through the
    group's record views ending at as many parameters as those motives
    bind ([rview_leaf_arity D]).  The uniform parameters
    [ups] are the eliminator's own; the stuck eliminator carries the
    container's at them, read back ([mref], [Rps]), as the eliminator of
    the container's group does. *)
| read_ne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_binder_count_at D None Bks ->
     rview_leaf_arity D ->
     ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     Rps pre at List.rev (ind_uparams Dq) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Us ->
     Rblks 0 (ind_block_members Dq) of Dq from p ups Bks (im_sel Mj) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rne d_elim ρ Bks p ups j as' m in Θ ⍮ Ξ ⍮ s ↘ ne_elim pc Us k NBks M )
(** The field of a neutral *)
| read_ne_proj :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rne d_proj f m in Θ ⍮ Ξ ⍮ s ↘ ne_proj f M )
where "'Rne' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_ne Θ Ξ s m M) : type_scope
(** A proof, as a term.  Proofs are never evaluated, so the term is not
    normal: a neutral proof reads back as its neutral, a proof variable
    as itself; a kept proof [⋆ᵈ⟨M, ρ⟩] as [M] copied as written, under
    local definitions binding the positions of [ρ] it reads
    ([proof_scope]), outermost first, each to the readback of its entry.
    This is the one place where readback builds a term. *)
with read_proof (Θ : gdeps) (Ξ : gstack) : nat -> domain -> exp -> Prop :=
(** A neutral proof *)
| read_proof_neut :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rprf ⇑ a m in Θ ⍮ Ξ ⍮ s ↘ ne_to_exp M )
(** A kept proof *)
| read_proof_kept :
  `( Rlets ρ at proof_scope M ρ in Θ ⍮ Ξ ⍮ s ↘ bs ->
     Rprf ⋆ᵈ⟨M, ρ⟩ in Θ ⍮ Ξ ⍮ s ↘ lets_exp bs M )
where "'Rprf' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_proof Θ Ξ s m M) : type_scope
(** [Rlets ρ at k in s ↘ bs]: the definitions binding the positions
    [k - 1], …, [0] of [ρ], outermost first: each at the depth of the
    definitions before it, so that the readbacks of the entries, which
    name variables by their levels, skip them. *)
with read_lets (Θ : gdeps) (Ξ : gstack) : nat -> env -> nat -> list binding -> Prop :=
(** No position *)
| read_lets_nil :
  `( Rlets ρ at 0 in Θ ⍮ Ξ ⍮ s ↘ nil )
(** The outermost position, then the rest under it *)
| read_lets_cons :
  `( Rent env_entry ρ k in Θ ⍮ Ξ ⍮ s ↘ b ->
     Rlets ρ at k in Θ ⍮ Ξ ⍮ S s ↘ bs ->
     Rlets ρ at S k in Θ ⍮ Ξ ⍮ s ↘ b :: bs )
where "'Rlets' ρ 'at' k 'in' Θ '⍮' Ξ '⍮' s ↘ bs" := (read_lets Θ Ξ s ρ k bs) : type_scope
(** [Rent e in s ↘ b]: the definition an entry [e] is bound by: a term at
    its type, read back; a module by the unit stored for it, written over
    its tail, whatever its value (REVISIT: a definition with a module
    part is bound by its term part only). *)
with read_entry (Θ : gdeps) (Ξ : gstack) : nat -> dentry -> binding -> Prop :=
(** A term *)
| read_entry_term :
  `( eval_entry_type Θ Ξ t a ->
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ W ->
     Rent de_term v t in Θ ⍮ Ξ ⍮ s ↘ b_def A W )
(** A definition with a module part: its term part as a definition is
    read, and its module part by its stored unit, as a module is *)
| read_entry_dm :
  `( eval_entry_type Θ Ξ t a ->
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ W ->
     Rent de_dm v t h U in Θ ⍮ Ξ ⍮ s ↘ b_def_mod A W U )
(** A module, by its stored unit *)
| read_entry_mod :
  `( Rent de_mod h U in Θ ⍮ Ξ ⍮ s ↘ b_mod U )
where "'Rent' e 'in' Θ '⍮' Ξ '⍮' s ↘ b" := (read_entry Θ Ξ s e b) : type_scope
with read_typ (Θ : gdeps) (Ξ : gstack) : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( Rtyp 𝕌ω@i in Θ ⍮ Ξ ⍮ s ↘ Typeωⁿ@i )
(** A small universe reads back as the universe at the canonical form its
    level reads back as: that readback is always of the shape [nf_lvl_of L]
    (see [Core.Semantic.Levels.domain_level_canon_of_read]), and the universe takes
    the same canonical level. *)
| read_typ_suniv :
  `( Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of L ->
     Rtyp 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of L )
| read_typ_level :
  `( Rtyp Levelᵈ@n in Θ ⍮ Ξ ⍮ s ↘ Levelⁿ@n )
(** The sort of the types of levels *)
| read_typ_level_sort :
  `( Rtyp LevelSortᵈ in Θ ⍮ Ξ ⍮ s ↘ LevelSortⁿ )
(** The universe of propositions *)
| read_typ_prop :
  `( Rtyp Propᵈ in Θ ⍮ Ξ ⍮ s ↘ Propⁿ )
(** The true proposition *)
| read_typ_True :
  `( Rtyp ⊤ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊤ⁿ )
(** The false proposition *)
| read_typ_False :
  `( Rtyp ⊥ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊥ⁿ )
(** A Π type at any kinds (a function type, a universal proposition, a
    function on levels): its codomain under a fresh variable of its
    domain, the kinds kept *)
| read_typ_pi :
  `( (** The normal form of the argument type. *)
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ A ->

     (** The normal form of the return type. *)
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ S s ↘ B' ->

     Rtyp d_pi κd κc a ρ B in Θ ⍮ Ξ ⍮ s ↘ nf_pi κd κc A B')
(** A dependent conjunction: its second component under a fresh
    variable of its first, a proof variable *)
| read_typ_and :
  `( (** The normal form of the first component. *)
     Rtyp a in Θ ⍮ Ξ ⍮ s ↘ P' ->

     (** The normal form of the second component. *)
     ⟦ Q ⟧ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ S s ↘ Q' ->

     Rtyp Σₚᵈ a ρ Q in Θ ⍮ Ξ ⍮ s ↘ Σₚⁿ P' Q')
(** A neutral type, with the kind of its elements: that of the sort [a]
    it is an element of *)
| read_typ_neut :
  `( Rne b in Θ ⍮ Ξ ⍮ s ↘ B ->
     Rtyp ⇑ a b in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (⇑ a b)} B)
(** A member of a group of inductive types at all its parameters, each read
    at its type. *)
| read_typ_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length as' = im_np D Mk ->
     Rps as' at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtyp d_ind p k as' in Θ ⍮ Ξ ⍮ s ↘ nf_indty p k Ps )
(** A record type at all its parameters, each read at its type. *)
| read_typ_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rps ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtyp d_record p ns in Θ ⍮ Ξ ⍮ s ↘ nf_record p Ps )
where "'Rtyp' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (read_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one. *)
with read_level_atoms (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> list level_atom -> Prop :=
(** No atom *)
| read_level_atoms_nil :
  `( Rla nil in Θ ⍮ Ξ ⍮ s ↘ nil )
(** The first atom's neutral, then the rest *)
| read_level_atoms_cons :
  `( Rne m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rla (k, n, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ mk_level_atom k n M :: ys )
where "'Rla' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (read_level_atoms Θ Ξ s xs ys) : type_scope
(** Values at a telescope, outermost first, each at its type in the
    environment of the values before it. *)
with read_ps (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> list nf -> Prop :=
(** No value *)
| read_ps_nil :
  `( Rps nil at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The first value at its type, then the rest with it in the
    environment *)
| read_ps_cons :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rps vs at T in Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure A ρ ⍮ s ↘ Vs ->
     Rps v :: vs at ce_ass κ A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rps' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (read_ps Θ Ξ s ρ T vs Ms) : type_scope
(** The fields [fl] of a record value [v], each at its type in [ρ] (the
    type's parameters and the projections of the fields before it), its
    projection read back there. *)
with read_fields (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> list nf -> Prop :=
(** No field left *)
| read_fields_nil :
  `( Rflds v at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The next field's projection at its type, then the rest with it in the
    environment *)
| read_fields_cons :
  `( eval_proj Θ Ξ f v r ->
     ⟦ T ⟧ Θ ⍮ Ξ ⍮ ρ ↘ t ->
     Rnf ⇓ t r in Θ ⍮ Ξ ⍮ s ↘ F ->
     Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ↦ r ⦂ entry_type_closure T ρ ⍮ s ↘ Fs ->
     Rflds v at (f, T) :: fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ F :: Fs )
where "'Rflds' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" := (read_fields Θ Ξ s ρ fl v Fs) : type_scope
(** The arguments of a constructor of [p] at the uniform parameters [ups],
    each at its type: a non-recursive one at the type its declaration gives,
    a recursive one at the type itself. *)
with read_cargs (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> list nf -> Prop :=
(** No argument *)
| read_cargs_nil :
  `( Rcargs nil at nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument, at its declared type *)
| read_cargs_arg :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure A ρ ⍮ s ↘ Vs ->
     Rcargs v :: vs at ca_arg r A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
(** A recursive argument, along its shape *)
| read_cargs_rec :
  `( Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V ->
     Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs ->
     Rcargs v :: vs at ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rcargs' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (read_cargs Θ Ξ s p ups ρ gs vs Ms) : type_scope
(** A recursive argument of shape [t] in [ρ], at the uniform parameters
    [ups] of the group at [p]: a function shape under a fresh variable of
    its domain, and at the end at the member of the group the shape ends
    in, a view too ([read_nf_con_view]), at the shape's non-uniform
    parameters.  Its value is of the container's type at a view
    ([eval_shape_type]); it is read at the group's own member. *)
with read_shape (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> nf -> Prop :=
(** At the end: at the group's own member at the shape's parameters *)
| read_shape_self :
  `( ⟦ Ps ⟧* Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     Rnf ⇓ (d_ind p j (ups ++ bs)) v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rsh v at pt_self j Ps of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V )
(** At a domain: a λ, the rest read under a fresh variable of it *)
| read_shape_pi :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     Rtyp b in Θ ⍮ Ξ ⍮ s ↘ A ->
     $| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
     Rsh r at t of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! b s ⦂ entry_type_closure B ρ ⍮ S s ↘ V ->
     Rsh v at pt_pi B t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ λⁿ A V )
where "'Rsh' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" := (read_shape Θ Ξ s p ups ρ t v V) : type_scope
(** The blocks of a stuck eliminator of the group at [p], its blocks [Bks]
    closures in [ρ], read as those of the eliminator of the group the
    eliminated member is at: one per member [Mi] of that group, from the
    [i]-th on, the block of the member [Mv] of [p]'s group [elim_src sel i]
    gives: its motive under fresh variables of [Mv]'s non-uniform
    parameters at the uniform parameters [ups] and of the scrutinee, its
    branches under their own variables.  The recursive results are
    computed by the eliminator at [ups] too.  [Dc] is the group read,
    whose tables the branches' recursive results follow ([leaf_in]); a
    member of it may be a view of another group still. *)
with read_blocks (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                      option (list nat) -> nat -> list imember -> list normal_block -> Prop :=
(** No member left *)
| read_blocks_nil :
  `( Rblks i nil of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The block for the member [Mi]: the scrutinee's type, the member of
    the group read at the parameters, under the fresh variables of the
    non-uniform parameters; the motive; the branches; then the rest *)
| read_blocks_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     eb_binder_count b = S (im_nn Mi) ->
     ⟦mref elim_src sel i of p ups ⟧ Θ ⍮ Ξ ↘ (hd, k, pre) ->
     Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
     Rtyp d_ind hd k (pre ++ ns) in Θ ⍮ Ξ ⍮ (s + im_nn Mi)%nat ↘ Z' ->
     ⟦ eb_motive b ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns))
                                          (⇑! (d_ind hd k (pre ++ ns)) ((s + im_nn Mi)%nat))) ↘ a ->
     Rtyp a in Θ ⍮ Ξ ⍮ S (s + im_nn Mi)%nat ↘ A' ->
     Rbrs eb_brs b at im_cons Mi of Mi (hd, k, pre) of Dc from p ups Bks Mv (eb_motive b) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rblks (S i) Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rblks i (Mi :: Ms) of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ mk_normal_block (S (im_nn Mi)) Z' A' Bs' :: NBks )
where "'Rblks' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" := (read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks) : type_scope
(** The branches of a block, one per constructor [cs] of the member [Mi]
    of the group read in order, of kinds [gs'], the block's motive [A] and
    branches [Bs], those of the member [Mv] of the group at [p], which has
    the constructor's arguments of kinds [gs]: each under fresh variables
    of [Mv]'s non-uniform parameters and the constructor's arguments at the
    uniform parameters [ups], and of the recursive results [gs'] has, at
    the motive's instance at the constructor, the member [Mi] being the
    declared member [k] of the group at [hd] at the uniform parameters
    [pre], of the group read [Dc].  The fresh recursive results, one per
    leaf path of the group's that is one of [Dc]'s ([cargs_container_count]), are as
    many as the branch read binds ([cargs_nrec Dc]): a gate, the twin of
    [eval_elim_con]'s, that keeps the fresh variables below the length the
    branch is read at. *)
with read_brs (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                    imember -> exp -> imember -> (qname * nat * list domain) ->
                                    list (string * list carg) -> list (string * nat * exp) -> list normal_branch -> Prop :=
(** No constructor left *)
| read_brs_nil :
  `( Rbrs nil at nil of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The branch of the next constructor, under its fresh variables, at
    the motive's instance, then the rest *)
| read_brs_cons :
  `( ind_con Mv c = Some gs ->
     ind_lookup Θ Ξ p = Some D ->
     n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat ->
     n = (im_nn Mi + List.length gs' + cargs_nrec Dc gs')%nat ->
     cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_params_length D gs ->
     Ftele List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
     Fcargs gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi)%nat ↘ vs ->
     Fihs vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns
       ⍮ (s + im_nn Mi + List.length gs')%nat ↘ ihs ->
     ⟦wihs vs of gs' gs of Dc with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
     ⟦ B ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs) ↘ b ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind hd k (pre ++ ns)) (d_con hd k c (pre ++ ns ++ vs))) ↘ t ->
     Rnf ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
     Rbrs Bs at cs of Mi (hd, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rbrs (c, n0, B) :: Bs at (c, gs') :: cs of Mi (hd, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ mk_normal_branch c n B' :: Bs' )
where "'Rbrs' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" := (read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs') : type_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop
with read_level_atoms_mut_ind := Induction for read_level_atoms Sort Prop
with read_ps_mut_ind := Induction for read_ps Sort Prop
with read_cargs_mut_ind := Induction for read_cargs Sort Prop
with read_shape_mut_ind := Induction for read_shape Sort Prop
with read_blocks_mut_ind := Induction for read_blocks Sort Prop
with read_brs_mut_ind := Induction for read_brs Sort Prop
with read_fields_mut_ind := Induction for read_fields Sort Prop
with read_proof_mut_ind := Induction for read_proof Sort Prop
with read_lets_mut_ind := Induction for read_lets Sort Prop
with read_entry_mut_ind := Induction for read_entry Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind,
  read_level_atoms_mut_ind,
  read_ps_mut_ind,
  read_cargs_mut_ind,
  read_shape_mut_ind,
  read_blocks_mut_ind,
  read_brs_mut_ind,
  read_fields_mut_ind,
  read_proof_mut_ind,
  read_lets_mut_ind,
  read_entry_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ read_level_atoms read_ps read_fields read_cargs read_shape read_blocks read_brs
  read_proof read_lets read_entry : mctt.
