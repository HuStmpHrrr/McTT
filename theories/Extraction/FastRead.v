(** * The Readback the Extracted Checker Runs

    A copy of the readback relations ([Core.Semantic.Readback]) over the
    evaluation of [Extraction.FastEval]: every closure is evaluated by
    [fast_eval_exp] and its twins.  With the skip on ([SkipMode]), three
    rules differ:
    - the fresh recursive results of a branch of a stuck eliminator are
      computed only for an argument whose results the branch reads
      ([ihs_skip_at]); for one it reads none of, each variable is at
      [𝕌ω@0] ([fast_fresh_ihs_skip]), as [fast_eval_ihs_skip] stores
      [𝕌ω@0] for each result;
    - a kept proof reads back as its term, with no definitions around it
      ([fast_read_proof_kept_skipping]);
    - a type former at no argument reads back with no lookup
      ([fast_read_typ_indty_nil]).
    With it off, the relations are those of [Core.Semantic.Readback]
    ([Extraction.FastEquiv]).  [Extraction.Simulation] relates the two
    readbacks, up to proofs. *)
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback.
From Mctt.Extraction Require Import FastEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" (at level 70, xs at level 69, Θ at level 69, Ξ at level 69, s constr, ys at level 69).
Reserved Notation "'Rprfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" (at level 70, m at level 69, Θ at level 69, Ξ at level 69, s constr, M at level 69).
Reserved Notation "'Rletsᶠ' ρ 'at' k 'in' Θ '⍮' Ξ '⍮' s ↘ bs" (at level 70, ρ at level 69, k at level 69, Θ at level 69, Ξ at level 69, s constr, bs at level 69).
Reserved Notation "'Rentᶠ' e 'in' Θ '⍮' Ξ '⍮' s ↘ b" (at level 70, e at level 69, Θ at level 69, Ξ at level 69, s constr, b at level 69).
Reserved Notation "'Rfldsᶠ' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" (at level 70, v at level 69, fl at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Fs at level 69).
Reserved Notation "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rcargsᶠ' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Ms at level 69).
Reserved Notation "'Rshᶠ' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, V at level 69).
Reserved Notation "'Rbrsᶠ' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" (at level 70, Bs at level 69, cs at level 69, Mi at level 0, r at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, Mv at level 0, A at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, Bs' at level 69).
Reserved Notation "'Rblksᶠ' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" (at level 70, i at level 0, Ms at level 0, Dc at level 0, p at level 0, ups at level 0, Bks at level 0, sel at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, NBks at level 69).

Reserved Notation "'Fteleᶠ' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, T at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fcargsᶠ' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" (at level 70, gs at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, vs at level 69).
Reserved Notation "'Fihsᶠ' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'for' B 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ρm at level 0, As at level 0, p at level 0, ups at level 0, B at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, s constr, ihs at level 69).
Reserved Notation "'⟦wihsᶠ' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs' at level 0, gs at level 0, Dc at level 0, ihs at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).

Generalizable All Variables.

(** ** Fresh Variables of the Telescopes of an Inductive Type

    As [fresh_tele], [fresh_cargs], [fresh_ihs] and [wrap_ihs_eval]. *)

(** A telescope, outermost first *)
Inductive fast_fresh_tele {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : env -> list centry -> nat -> list domain -> Prop :=
(** No entry *)
| fast_fresh_tele_nil :
  `( Fteleᶠ nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The first entry's variable at its type, then the rest with it in the
    environment *)
| fast_fresh_tele_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ ⍮ S s ↘ vs ->
     Fteleᶠ ce_ass κ A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Fteleᶠ' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fast_fresh_tele Θ Ξ ρ T s vs) : type_scope.

(** The arguments of a constructor of [p] at the uniform parameters [ups] *)
Inductive fast_fresh_cargs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) (p : qname) (ups : list domain) :
  env -> list carg -> nat -> list domain -> Prop :=
(** No argument *)
| fast_fresh_cargs_nil :
  `( Fcargsᶠ nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument: its variable at its declared type *)
| fast_fresh_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_closure A ρ ⍮ S s ↘ vs ->
     Fcargsᶠ ca_arg r A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
(** A recursive argument: its variable at its shape's type *)
| fast_fresh_cargs_rec :
  `( ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ S s ↘ vs ->
     Fcargsᶠ ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ ⇑! a s :: vs )
where "'Fcargsᶠ' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ vs" := (fast_fresh_cargs Θ Ξ p ups ρ gs s vs) : type_scope.

(** The recursive results of the arguments [vs] of a branch [B] of a stuck
    eliminator, as fresh variables, as [fresh_ihs]: the types of the results
    of an argument the branch reads none of are not computed, and each of
    its variables is at [𝕌ω@0].  The results of the argument heading
    [ca_rec t :: gs], [gs] the kinds the branch's group has, are the
    variables [cargs_nrec D gs] on of [B] ([ihs_skipb]). *)
Inductive fast_fresh_ihs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) (ρ : env) (As : list exp) (p : qname) (ups : list domain) (Dc : ind_decl) (B : exp) :
  env -> list carg -> list carg -> list domain -> nat -> list domain -> Prop :=
(** No argument, no result *)
| fast_fresh_ihs_nil :
  `( Fihsᶠ nil at nil nil of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ nil )
(** A non-recursive argument: none, the argument entering [ρa] *)
| fast_fresh_ihs_arg :
  `( Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ↦ v ⦂ entry_type_closure T ρa ⍮ s ↘ ihs ->
     Fihsᶠ v :: vs at (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
(** An argument recursive in both, one of whose results the branch reads:
    a fresh variable at each recursive result's type along the paths of
    the container's *)
| fast_fresh_ihs_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skip_at skip_on (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = false ->
     ⟦ihtyᶠ v of t at p ups under ρ As ⟧ᶠ Θ ⍮ Ξ ⍮ ρa ↘ as' ->
     fresh_leaf_vars (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) as' s ihs1 ->
     Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ (List.length ihs1 + s) ↘ ihs ->
     Fihsᶠ v :: vs at (ca_rec t' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ++ ihs )
(** One the branch reads none of the results of: each variable at
    [𝕌ω@0] *)
| fast_fresh_ihs_skip :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skip_at skip_on (Some B) (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = true ->
     fresh_leaf_vars (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t))
       (List.repeat 𝕌ω@0 (List.length (shape_leaves (rview_leaves D) 0 t))) s ihs1 ->
     Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ (List.length ihs1 + s) ↘ ihs ->
     Fihsᶠ v :: vs at (ca_rec t' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ++ ihs )
(** An argument recursive in [gs] only (nested through): no variable *)
| fast_fresh_ihs_nest :
  `( Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs ->
     Fihsᶠ v :: vs at (ca_arg ra' T' :: gs') (ca_rec t :: gs) of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs )
where "'Fihsᶠ' vs 'at' gs' gs 'of' Dc 'under' ρm As 'at' p ups 'for' B 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ ihs" :=
  (fast_fresh_ihs Θ Ξ ρm As p ups Dc B ρ gs' gs vs s ihs) : type_scope.

(** The recursive results a branch of a block is read under, as
    [wrap_ihs_eval] *)
Inductive fast_wrap_ihs_eval {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) (ρ : env) (p : qname) (ups : list domain) (Bks : list eblock) (Dc : ind_decl) :
  list carg -> list carg -> list domain -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| fast_wrap_ihs_eval_nil :
  `( ⟦wihsᶠ nil of nil nil of Dc with nil under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** Recursive in both: along each path, the next of [ihs] at a path of
    the container's, the eliminator at one nested through *)
| fast_wrap_ihs_eval_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     wrap_leaf_vals (List.map (leaf_in Dc t') (shape_leaves (rview_leaves D) 0 t)) rs ihs ihs' r1 ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs' under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_rec t' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ++ r )
(** Recursive for the branch's group only: the eliminator at the
    argument, along each path *)
| fast_wrap_ihs_eval_nest :
  `( ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_arg ra' T' :: gs') (ca_rec t :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ++ r )
(** Non-recursive: no result *)
| fast_wrap_ihs_eval_arg :
  `( ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦wihsᶠ v :: vs of (ca_arg ra' T' :: gs') (ca_arg ra T :: gs) of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦wihsᶠ' vs 'of' gs' gs 'of' Dc 'with' ihs 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" :=
  (fast_wrap_ihs_eval Θ Ξ ρ p ups Bks Dc gs' gs vs ihs r) : type_scope.

#[export]
Hint Constructors fast_fresh_tele fast_fresh_cargs fast_fresh_ihs fast_wrap_ihs_eval : mctt.

(** The type value an environment's entry is stored at, as
    [eval_entry_type] *)
Inductive fast_eval_entry_type {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : entry_type -> domain -> Prop :=
(** A type value *)
| fast_eval_entry_type_value :
  `( fast_eval_entry_type Θ Ξ (entry_type_value a) a )
(** A type in an environment *)
| fast_eval_entry_type_closure :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     fast_eval_entry_type Θ Ξ (entry_type_closure A ρ) a )
(** The type of a recursive argument of a shape *)
| fast_eval_entry_type_shape :
  `( ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     fast_eval_entry_type Θ Ξ (entry_type_shape p ups ρ t) a )
(** The type of a recursive result *)
| fast_eval_entry_type_induction_hypothesis :
  `( ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ as' ->
     List.nth_error as' i = Some a ->
     fast_eval_entry_type Θ Ξ (entry_type_induction_hypothesis ρm As p ups ρ t v i) a ).

#[export]
Hint Constructors fast_eval_entry_type : mctt.

(** ** Readback

    As [read_nf] and its twins, closures evaluated by [Extraction.FastEval];
    the fresh recursive results of a branch by [fast_fresh_ihs]. *)
Inductive fast_read_nf {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> nf -> Prop :=
(** A type, as an element of a large universe *)
| fast_read_nf_type :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌ω@i a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A type, as an element of a small universe *)
| fast_read_nf_stype :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ 𝕌@n a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A level, canonically *)
| fast_read_nf_lvl :
  `( Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rnfᶠ ⇓ (Levelᵈ@n) (lvᵈ c xs) in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of (lvl_canon (c, ys)) )
(** A neutral level: one atom at offset [0] *)
| fast_read_nf_lvl_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (Levelᵈ@n) (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ lvⁿ ordinal_zero (mk_level_atom 0 (domain_level_sort a) M :: nil) )
(** A value of a proposition: a proof term, with the proposition *)
| fast_read_nf_proof :
  `( domain_kind a = ak_propositional ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ P ->
     Rprfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ a m in Θ ⍮ Ξ ⍮ s ↘ nf_proof P M )
(** A proposition, as an element of [Prop] *)
| fast_read_nf_prop :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ Propᵈ a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A type of levels, as an element of [LevelSort] *)
| fast_read_nf_at_level_sort :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ LevelSortᵈ a in Θ ⍮ Ξ ⍮ s ↘ A )
(** A function, η-long, its codomain not a proposition *)
| fast_read_nf_fn :
  `( evaluated_kind κc ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     $ᶠ| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rnfᶠ ⇓ b m' in Θ ⍮ Ξ ⍮ S s ↘ M ->
     Rnfᶠ ⇓ (d_pi κd κc a ρ B) m in Θ ⍮ Ξ ⍮ s ↘ λⁿ A M )
(** A neutral at a neutral type that is not a proposition, with the kind
    of its type *)
| fast_read_nf_neut :
  `( evaluated_kind (domain_kind (⇑ a b)) ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (⇑ a b) (⇑ c m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (⇑ a b)} M )
(** A constructor at all its parameters and arguments *)
| fast_read_nf_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length as' = im_np D Mk ->
     List.length vs = (im_np D Mk + List.length gs)%nat ->
     Rpsᶠ as' at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ List.skipn (im_np D Mk) vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (im_params D Mk)) as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p k as') (d_con p k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p k c (Ps ++ Args) )
(** A constructor at a view of the group at [p] *)
| fast_read_nf_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_con Mj c = Some gs ->
     List.length as' = im_np D Mj ->
     List.length vs = (n + List.length gs)%nat ->
     Rpsᶠ as' at List.rev (im_params D Mj) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ List.skipn n vs at gs of p (List.firstn (ind_nu D) as') in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (im_params D Mj)) as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p j as') (d_con qc k c vs) in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** Any value at a record view of the group at [p], η-long *)
| fast_read_nf_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     List.length as' = ind_nu D ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     Rpsᶠ as' at List.rev (ind_uparams D) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rcargsᶠ ws at gs of p as' in Θ ⍮ Ξ ⍮ decl_env D as' ⍮ s ↘ Args ->
     Rnfᶠ ⇓ (d_ind p j as') v in Θ ⍮ Ξ ⍮ s ↘ nf_con p j c (Ps ++ Args) )
(** A neutral at a member of a group that is no record view *)
| fast_read_nf_ind_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_is_rview Mk = false ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ ⇓ (d_ind p k as') (⇑ a m) in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (d_ind p k as')} M )
(** Any value of a record type, η-long and type-directed *)
| fast_read_nf_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rpsᶠ ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rfldsᶠ v at record_fields R in Θ ⍮ Ξ ⍮ env_tele nil (List.rev (record_params R)) ns ⍮ s ↘ Fs ->
     Rnfᶠ ⇓ (d_record p ns) v in Θ ⍮ Ξ ⍮ s ↘ nf_tuple p Ps (List.map fst (record_fields R)) Fs )
where "'Rnfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fast_read_nf Θ Ξ s m M) : type_scope
with fast_read_ne {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> ne -> Prop :=
(** A variable, by its level *)
| fast_read_ne_var :
  `( Rneᶠ #ᵈ x in Θ ⍮ Ξ ⍮ s ↘ #ⁿ (s - x - 1) )
(** An application *)
| fast_read_ne_app :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rnfᶠ n in Θ ⍮ Ξ ⍮ s ↘ N ->
     Rneᶠ m $ᵈ n in Θ ⍮ Ξ ⍮ s ↘ M $ⁿ N )
(** Ex falso at the type [c], its proof as a term *)
| fast_read_ne_absurd :
  `( Rtypᶠ c in Θ ⍮ Ξ ⍮ s ↘ C ->
     Rprfᶠ p in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ efqᵈ p return c in Θ ⍮ Ξ ⍮ s ↘ efqⁿ M return C )
(** A global without a value *)
| fast_read_ne_glob :
  `( Rneᶠ d_glob p in Θ ⍮ Ξ ⍮ s ↘ ne_glob p )
(** A stuck eliminator, read as the eliminator of the group the member is
    at *)
| fast_read_ne_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     blocks_binder_count_at D None Bks ->
     rview_leaf_arity D ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     Rpsᶠ pre at List.rev (ind_uparams Dq) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Us ->
     Rblksᶠ 0 (ind_block_members Dq) of Dq from p ups Bks (im_sel Mj) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ d_elim ρ Bks p ups j as' m in Θ ⍮ Ξ ⍮ s ↘ ne_elim pc Us k NBks M )
(** The field of a neutral *)
| fast_read_ne_proj :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rneᶠ d_proj f m in Θ ⍮ Ξ ⍮ s ↘ ne_proj f M )
where "'Rneᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fast_read_ne Θ Ξ s m M) : type_scope
(** A proof, as a term, as [read_proof] *)
with fast_read_proof {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> domain -> exp -> Prop :=
(** A neutral proof *)
| fast_read_proof_neut :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rprfᶠ ⇑ a m in Θ ⍮ Ξ ⍮ s ↘ ne_to_exp M )
(** A kept proof, with the skip off: under the definitions of the
    positions it reads, as [read_proof_kept] *)
| fast_read_proof_kept :
  `( skip_on = false ->
     Rletsᶠ ρ at proof_scope M ρ in Θ ⍮ Ξ ⍮ s ↘ bs ->
     Rprfᶠ ⋆ᵈ⟨M, ρ⟩ in Θ ⍮ Ξ ⍮ s ↘ lets_exp bs M )
(** A kept proof, with the skip on: the term as it is.  The definitions
    around it would reach the skipped results ([fast_eval_ihs_skip]);
    a normal form with a proof in it is recomputed with the skip off
    ([Extraction.NbE]), so what stands for the proof here is never an
    output. *)
| fast_read_proof_kept_skipping :
  `( skip_on = true ->
     Rprfᶠ ⋆ᵈ⟨M, ρ⟩ in Θ ⍮ Ξ ⍮ s ↘ M )
where "'Rprfᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fast_read_proof Θ Ξ s m M) : type_scope
(** The definitions binding the positions [k - 1], …, [0] of [ρ],
    outermost first, as [read_lets] *)
with fast_read_lets {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> env -> nat -> list binding -> Prop :=
(** No position *)
| fast_read_lets_nil :
  `( Rletsᶠ ρ at 0 in Θ ⍮ Ξ ⍮ s ↘ nil )
(** The outermost position, then the rest under it *)
| fast_read_lets_cons :
  `( Rentᶠ env_entry ρ k in Θ ⍮ Ξ ⍮ s ↘ b ->
     Rletsᶠ ρ at k in Θ ⍮ Ξ ⍮ S s ↘ bs ->
     Rletsᶠ ρ at S k in Θ ⍮ Ξ ⍮ s ↘ b :: bs )
where "'Rletsᶠ' ρ 'at' k 'in' Θ '⍮' Ξ '⍮' s ↘ bs" := (fast_read_lets Θ Ξ s ρ k bs) : type_scope
(** The definition an entry is bound by, as [read_entry] *)
with fast_read_entry {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> dentry -> binding -> Prop :=
(** A term *)
| fast_read_entry_term :
  `( fast_eval_entry_type Θ Ξ t a ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ W ->
     Rentᶠ de_term v t in Θ ⍮ Ξ ⍮ s ↘ b_def A W )
(** A definition with a module part, as [read_entry_dm]: its term part
    as a definition's, its stored unit as a module's *)
| fast_read_entry_dm :
  `( fast_eval_entry_type Θ Ξ t a ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ W ->
     Rentᶠ de_dm v t h U in Θ ⍮ Ξ ⍮ s ↘ b_def_mod A W U )
(** A module, by its stored unit *)
| fast_read_entry_mod :
  `( Rentᶠ de_mod h U in Θ ⍮ Ξ ⍮ s ↘ b_mod U )
where "'Rentᶠ' e 'in' Θ '⍮' Ξ '⍮' s ↘ b" := (fast_read_entry Θ Ξ s e b) : type_scope
with fast_read_typ {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> domain -> nf -> Prop :=
(** A large universe *)
| fast_read_typ_univ :
  `( Rtypᶠ 𝕌ω@i in Θ ⍮ Ξ ⍮ s ↘ Typeωⁿ@i )
(** A small universe, at the canonical form of its level *)
| fast_read_typ_suniv :
  `( Rnfᶠ ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ nf_lvl_of L ->
     Rtypᶠ 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of L )
(** A type of levels *)
| fast_read_typ_level :
  `( Rtypᶠ Levelᵈ@n in Θ ⍮ Ξ ⍮ s ↘ Levelⁿ@n )
(** The sort of the types of levels *)
| fast_read_typ_level_sort :
  `( Rtypᶠ LevelSortᵈ in Θ ⍮ Ξ ⍮ s ↘ LevelSortⁿ )
(** The universe of propositions *)
| fast_read_typ_prop :
  `( Rtypᶠ Propᵈ in Θ ⍮ Ξ ⍮ s ↘ Propⁿ )
(** The true proposition *)
| fast_read_typ_True :
  `( Rtypᶠ ⊤ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊤ⁿ )
(** The false proposition *)
| fast_read_typ_False :
  `( Rtypᶠ ⊥ᵈ in Θ ⍮ Ξ ⍮ s ↘ ⊥ⁿ )
(** A Π type at any kinds *)
| fast_read_typ_pi :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ A ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ B' ->
     Rtypᶠ d_pi κd κc a ρ B in Θ ⍮ Ξ ⍮ s ↘ nf_pi κd κc A B')
(** A dependent conjunction *)
| fast_read_typ_and :
  `( Rtypᶠ a in Θ ⍮ Ξ ⍮ s ↘ P' ->
     ⟦ Q ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⇑! a s ⦂ entry_type_value a ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ S s ↘ Q' ->
     Rtypᶠ Σₚᵈ a ρ Q in Θ ⍮ Ξ ⍮ s ↘ Σₚⁿ P' Q')
(** A neutral type, with the kind of its elements *)
| fast_read_typ_neut :
  `( Rneᶠ b in Θ ⍮ Ξ ⍮ s ↘ B ->
     Rtypᶠ ⇑ a b in Θ ⍮ Ξ ⍮ s ↘ ⇑ⁿ{domain_kind (⇑ a b)} B)
(** A type former at no argument, with the skip on: no lookup (the one
    rule [read_typ] does not have; at a member of no parameter it gives
    what [read_typ_indty] gives) *)
| fast_read_typ_indty_nil :
  `( skip_on = true ->
     Rtypᶠ d_ind p k nil in Θ ⍮ Ξ ⍮ s ↘ nf_indty p k nil )
(** A member of a group of inductive types at all its parameters, as
    [read_typ_indty] *)
| fast_read_typ_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length as' = im_np D Mk ->
     Rpsᶠ as' at List.rev (im_params D Mk) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtypᶠ d_ind p k as' in Θ ⍮ Ξ ⍮ s ↘ nf_indty p k Ps )
(** A record type at all its parameters *)
| fast_read_typ_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns = List.length (record_params R) ->
     Rpsᶠ ns at List.rev (record_params R) in Θ ⍮ Ξ ⍮ nil ⍮ s ↘ Ps ->
     Rtypᶠ d_record p ns in Θ ⍮ Ξ ⍮ s ↘ nf_record p Ps )
where "'Rtypᶠ' m 'in' Θ '⍮' Ξ '⍮' s ↘ M" := (fast_read_typ Θ Ξ s m M) : type_scope
(** The atoms of a level, read one by one *)
with fast_read_level_atoms {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * nat * domain_ne) -> list level_atom -> Prop :=
(** No atom *)
| fast_read_level_atoms_nil :
  `( Rlaᶠ nil in Θ ⍮ Ξ ⍮ s ↘ nil )
(** The first atom's neutral, then the rest *)
| fast_read_level_atoms_cons :
  `( Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M ->
     Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
     Rlaᶠ (k, n, m) :: xs in Θ ⍮ Ξ ⍮ s ↘ mk_level_atom k n M :: ys )
where "'Rlaᶠ' xs 'in' Θ '⍮' Ξ '⍮' s ↘ ys" := (fast_read_level_atoms Θ Ξ s xs ys) : type_scope
(** Values at a telescope, outermost first *)
with fast_read_ps {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> env -> list centry -> list domain -> list nf -> Prop :=
(** No value *)
| fast_read_ps_nil :
  `( Rpsᶠ nil at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The first value at its type, then the rest with it in the
    environment *)
| fast_read_ps_cons :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure A ρ ⍮ s ↘ Vs ->
     Rpsᶠ v :: vs at ce_ass κ A :: T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rpsᶠ' vs 'at' T 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (fast_read_ps Θ Ξ s ρ T vs Ms) : type_scope
(** The fields of a record value, each at its type *)
with fast_read_fields {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> env -> list (string * exp) -> domain -> list nf -> Prop :=
(** No field left *)
| fast_read_fields_nil :
  `( Rfldsᶠ v at nil in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The next field's projection at its type, then the rest with it in the
    environment *)
| fast_read_fields_cons :
  `( fast_eval_proj Θ Ξ f v r ->
     ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ t ->
     Rnfᶠ ⇓ t r in Θ ⍮ Ξ ⍮ s ↘ F ->
     Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ↦ r ⦂ entry_type_closure T ρ ⍮ s ↘ Fs ->
     Rfldsᶠ v at (f, T) :: fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ F :: Fs )
where "'Rfldsᶠ' v 'at' fl 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Fs" := (fast_read_fields Θ Ξ s ρ fl v Fs) : type_scope
(** The arguments of a constructor, each at its type *)
with fast_read_cargs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> list carg -> list domain -> list nf -> Prop :=
(** No argument *)
| fast_read_cargs_nil :
  `( Rcargsᶠ nil at nil of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** A non-recursive argument, at its declared type *)
| fast_read_cargs_arg :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     Rnfᶠ ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure A ρ ⍮ s ↘ Vs ->
     Rcargsᶠ v :: vs at ca_arg r A :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
(** A recursive argument, along its shape *)
| fast_read_cargs_rec :
  `( Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V ->
     Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs ->
     Rcargsᶠ v :: vs at ca_rec t :: gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V :: Vs )
where "'Rcargsᶠ' vs 'at' gs 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Ms" := (fast_read_cargs Θ Ξ s p ups ρ gs vs Ms) : type_scope
(** A recursive argument of a shape *)
with fast_read_shape {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> qname -> list domain -> env -> ptyp -> domain -> nf -> Prop :=
(** At the end: at the group's own member at the shape's parameters *)
| fast_read_shape_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     Rnfᶠ ⇓ (d_ind p j (ups ++ bs)) v in Θ ⍮ Ξ ⍮ s ↘ V ->
     Rshᶠ v at pt_self j Ps of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V )
(** At a domain: a λ, the rest read under a fresh variable of it *)
| fast_read_shape_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     Rtypᶠ b in Θ ⍮ Ξ ⍮ s ↘ A ->
     $ᶠ| v & ⇑! b s | Θ ⍮ Ξ ↘ r ->
     Rshᶠ r at t of p ups in Θ ⍮ Ξ ⍮ ρ ↦ ⇑! b s ⦂ entry_type_closure B ρ ⍮ S s ↘ V ->
     Rshᶠ v at pt_pi B t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ λⁿ A V )
where "'Rshᶠ' v 'at' t 'of' p ups 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ V" := (fast_read_shape Θ Ξ s p ups ρ t v V) : type_scope
(** The blocks of a stuck eliminator, as [read_blocks] *)
with fast_read_blocks {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                           option (list nat) -> nat -> list imember -> list normal_block -> Prop :=
(** No member left *)
| fast_read_blocks_nil :
  `( Rblksᶠ i nil of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The block for the member [Mi]: the scrutinee's type, the motive, the
    branches, then the rest *)
| fast_read_blocks_cons :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D (elim_src sel i) = Some Mv ->
     List.nth_error Bks (elim_src sel i) = Some b ->
     eb_binder_count b = S (im_nn Mi) ->
     ⟦mrefᶠ elim_src sel i of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pk, k, pre) ->
     Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
     Rtypᶠ d_ind pk k (pre ++ ns) in Θ ⍮ Ξ ⍮ (s + im_nn Mi)%nat ↘ Z' ->
     ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns))
                                           (⇑! (d_ind pk k (pre ++ ns)) ((s + im_nn Mi)%nat))) ↘ a ->
     Rtypᶠ a in Θ ⍮ Ξ ⍮ S (s + im_nn Mi)%nat ↘ A' ->
     Rbrsᶠ eb_brs b at im_cons Mi of Mi (pk, k, pre) of Dc from p ups Bks Mv (eb_motive b) in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rblksᶠ (S i) Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks ->
     Rblksᶠ i (Mi :: Ms) of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ mk_normal_block (S (im_nn Mi)) Z' A' Bs' :: NBks )
where "'Rblksᶠ' i Ms 'of' Dc 'from' p ups Bks sel 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ NBks" := (fast_read_blocks Θ Ξ s ρ p ups Bks Dc sel i Ms NBks) : type_scope
(** The branches of a block, as [read_brs]; the results of an argument
    the branch reads none of are at [𝕌ω@0] ([fast_fresh_ihs_skip]) *)
with fast_read_brs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : nat -> env -> qname -> list domain -> list eblock -> ind_decl ->
                                        imember -> exp -> imember -> (qname * nat * list domain) ->
                                        list (string * list carg) -> list (string * nat * exp) -> list normal_branch -> Prop :=
(** No constructor left *)
| fast_read_brs_nil :
  `( Rbrsᶠ nil at nil of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ nil )
(** The branch of the next constructor, under its fresh variables, at
    the motive's instance, then the rest *)
| fast_read_brs_cons :
  `( ind_con Mv c = Some gs ->
     ind_lookup Θ Ξ p = Some D ->
     n0 = (im_nn Mi + List.length gs' + cargs_nrec D gs)%nat ->
     n = (im_nn Mi + List.length gs' + cargs_nrec Dc gs')%nat ->
     cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' ->
     cargs_params_length D gs ->
     Fteleᶠ List.rev (im_nparams Mv) in Θ ⍮ Ξ ⍮ decl_env D ups ⍮ s ↘ ns ->
     Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns ⍮ (s + im_nn Mi)%nat ↘ vs ->
     Fihsᶠ vs at gs' gs of Dc under ρ (blocks_motives Bks) at p ups for B in Θ ⍮ Ξ ⍮ env_tele (decl_env D ups) (List.rev (im_nparams Mv)) ns
       ⍮ (s + im_nn Mi + List.length gs')%nat ↘ ihs ->
     ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ wihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mv p ups (blocks_motives Bks) ρ gs ns vs wihs) ↘ b ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mv ups ns (d_ind pk k (pre ++ ns)) (d_con pk k c (pre ++ ns ++ vs))) ↘ t ->
     Rnfᶠ ⇓ t b in Θ ⍮ Ξ ⍮ (s + n)%nat ↘ B' ->
     Rbrsᶠ Bs at cs of Mi (pk, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs' ->
     Rbrsᶠ (c, n0, B) :: Bs at (c, gs') :: cs of Mi (pk, k, pre) of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ mk_normal_branch c n B' :: Bs' )
where "'Rbrsᶠ' Bs 'at' cs 'of' Mi r 'of' Dc 'from' p ups Bks Mv A 'in' Θ '⍮' Ξ '⍮' ρ '⍮' s ↘ Bs'" :=
  (fast_read_brs Θ Ξ s ρ p ups Bks Dc Mv A Mi r cs Bs Bs') : type_scope
.

Scheme fast_read_nf_mut_ind := Induction for fast_read_nf Sort Prop
with fast_read_ne_mut_ind := Induction for fast_read_ne Sort Prop
with fast_read_typ_mut_ind := Induction for fast_read_typ Sort Prop
with fast_read_level_atoms_mut_ind := Induction for fast_read_level_atoms Sort Prop
with fast_read_ps_mut_ind := Induction for fast_read_ps Sort Prop
with fast_read_cargs_mut_ind := Induction for fast_read_cargs Sort Prop
with fast_read_shape_mut_ind := Induction for fast_read_shape Sort Prop
with fast_read_blocks_mut_ind := Induction for fast_read_blocks Sort Prop
with fast_read_brs_mut_ind := Induction for fast_read_brs Sort Prop
with fast_read_fields_mut_ind := Induction for fast_read_fields Sort Prop
with fast_read_proof_mut_ind := Induction for fast_read_proof Sort Prop
with fast_read_lets_mut_ind := Induction for fast_read_lets Sort Prop
with fast_read_entry_mut_ind := Induction for fast_read_entry Sort Prop.
Combined Scheme fast_read_mut_ind from
  fast_read_nf_mut_ind,
  fast_read_ne_mut_ind,
  fast_read_typ_mut_ind,
  fast_read_level_atoms_mut_ind,
  fast_read_ps_mut_ind,
  fast_read_cargs_mut_ind,
  fast_read_shape_mut_ind,
  fast_read_blocks_mut_ind,
  fast_read_brs_mut_ind,
  fast_read_fields_mut_ind,
  fast_read_proof_mut_ind,
  fast_read_lets_mut_ind,
  fast_read_entry_mut_ind.

#[export]
Hint Constructors fast_read_nf fast_read_ne fast_read_typ fast_read_level_atoms fast_read_ps fast_read_fields fast_read_cargs
  fast_read_shape fast_read_blocks fast_read_brs fast_read_proof fast_read_lets fast_read_entry : mctt.

(** ** Determinism *)

Section FastReadDeterminism.
  (** The mode the relations run at *)
  Context {SM : SkipMode}.

Lemma functional_fast_fresh_tele : forall {Θ Ξ} ρ T s vs1, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
    forall vs2, Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
Proof.
  induction 1; intros * H2; inversion H2; subst; [ reflexivity |].
  functional_fast_eval_rewrite_clear; f_equal; auto.
Qed.

Lemma functional_fast_fresh_cargs : forall {Θ Ξ} p ups ρ gs s vs1, Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
    forall vs2, Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
Proof.
  induction 1; intros * H2; inversion H2; subst; [ auto | |];
    functional_fast_eval_rewrite_clear; f_equal; auto.
Qed.

Lemma functional_fast_fresh_ihs : forall {Θ Ξ} ρ As p ups Dc B ρa gs' gs vs s ihs1,
    Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ->
    forall ihs2, Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs2 -> ihs1 = ihs2.
Proof.
  induction 1; intros * Hother; inversion Hother; subst; auto.
  all: repeat match goal with
         | H1 : ind_lookup ?T ?X ?p = Some _, H3 : ind_lookup ?T ?X ?p = Some _ |- _ =>
             rewrite H1 in H3; injection H3 as ?; subst
         end; try congruence.
  all: functional_fast_eval_rewrite_clear.
  all: match goal with H1 : fresh_leaf_vars ?b ?a ?s ?v1, H3 : fresh_leaf_vars ?b ?a ?s ?v2 |- _ =>
         pose proof (functional_fresh_leaf_vars _ _ _ _ H1 _ H3); subst end.
  all: f_equal; auto.
Qed.

Lemma functional_fast_wrap_ihs_eval : forall {Θ Ξ} ρ p ups Bks Dc gs' gs vs ihs r1,
    ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
    forall r2, ⟦wihsᶠ vs of gs' gs of Dc with ihs under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
Proof.
  induction 1; intros * Hother; inversion Hother; subst; auto.
  all: repeat match goal with
         | H1 : ind_lookup ?T ?X ?p = Some _, H3 : ind_lookup ?T ?X ?p = Some _ |- _ =>
             rewrite H1 in H3; injection H3 as ?; subst
         end.
  all: functional_fast_eval_rewrite_clear.
  all: try match goal with H1 : wrap_leaf_vals ?b ?r ?i _ _, H3 : wrap_leaf_vals ?b ?r ?i _ _ |- _ =>
         destruct (functional_wrap_leaf_vals _ _ _ _ _ H1 _ _ H3); subst end.
  all: f_equal; auto.
Qed.

(** The type value of an entry is one value. *)
Lemma functional_fast_eval_entry_type : forall {Θ Ξ} t a1 a2,
    fast_eval_entry_type Θ Ξ t a1 -> fast_eval_entry_type Θ Ξ t a2 -> a1 = a2.
Proof.
  intros * H1 H2; destruct H1; inversion H2; subst; functional_fast_eval_rewrite_clear; congruence.
Qed.

End FastReadDeterminism.

Ltac functional_fast_fresh_rewrite_clear :=
  repeat match goal with
    | H1 : fast_eval_entry_type ?T ?X ?t ?a1, H2 : fast_eval_entry_type ?T ?X ?t ?a2 |- _ =>
        pose proof (functional_fast_eval_entry_type _ _ _ H1 H2); subst; clear H2
    | H1 : fast_fresh_tele ?T ?X ?ρ ?L ?s ?v1, H2 : fast_fresh_tele ?T ?X ?ρ ?L ?s ?v2 |- _ =>
        pose proof (functional_fast_fresh_tele _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v1, H2 : fast_fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v2 |- _ =>
        pose proof (functional_fast_fresh_cargs _ _ _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_fresh_ihs ?T ?X ?ρ ?A ?p ?u ?Dc ?B ?ρa ?gs' ?gs ?vs ?s ?i1, H2 : fast_fresh_ihs ?T ?X ?ρ ?A ?p ?u ?Dc ?B ?ρa ?gs' ?gs ?vs ?s ?i2 |- _ =>
        pose proof (functional_fast_fresh_ihs _ _ _ _ _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?Dc ?g' ?g ?vs ?ih ?r1, H2 : fast_wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?Dc ?g' ?g ?vs ?ih ?r2 |- _ =>
        pose proof (functional_fast_wrap_ihs_eval _ _ _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
    | H1 : fast_eval_projs ?T ?X ?fl ?v ?w1, H2 : fast_eval_projs ?T ?X ?fl ?v ?w2 |- _ =>
        pose proof (functional_fast_eval_projs _ _ _ _ H1 H2); subst; clear H2
    | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
        exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
    | H1 : ⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?b1, H2 : ⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?b2 |- _ =>
        pose proof (functional_fast_eval_exps _ _ _ _ H1 H2); subst; clear H2
    | H1 : fast_eval_mref ?T ?X ?p ?ups ?j ?r1, H2 : fast_eval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
        let E := fresh "E" in
        pose proof (functional_fast_eval_mref _ _ _ _ _ H1 H2) as E; injection E; intros; subst; clear H2
    | H : (_, _) = (_, _) |- _ => injection H; intros; subst; clear H
    | H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as ?; subst
    | H1 : record_lookup ?T ?X ?p = Some _, H2 : record_lookup ?T ?X ?p = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as ?; subst
    | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as ?; subst
    | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as ?; subst
    | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
        rewrite H1 in H2; injection H2 as ?; subst
    end.

Section FastReadDeterminismMutual.
  (** The mode the relations run at *)
  Context {SM : SkipMode}.

Lemma functional_fast_read : forall {Θ Ξ},
  (forall s m M1, Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> forall M2, Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2) /\
    (forall s m M1, Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> forall M2, Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2) /\
    (forall s m M1, Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> forall M2, Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2) /\
    (forall s xs ys1, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys1 -> forall ys2, Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys2 -> ys1 = ys2) /\
    (forall s ρ T vs Vs1, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 -> forall Vs2, Rpsᶠ vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
    (forall s p ups ρ gs vs Vs1, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 ->
       forall Vs2, Rcargsᶠ vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
    (forall s p ups ρ t v V1, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V1 ->
       forall V2, Rshᶠ v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V2 -> V1 = V2) /\
    (forall s ρ p ups Bks Dc sel i Ms NBks1, Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks1 ->
       forall NBks2, Rblksᶠ i Ms of Dc from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks2 -> NBks1 = NBks2) /\
    (forall s ρ p ups Bks Dc Mv A Mi r cs Bs Bs1, Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs1 ->
       forall Bs2, Rbrsᶠ Bs at cs of Mi r of Dc from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs2 -> Bs1 = Bs2) /\
    (forall s ρ fl v Fs1, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs1 -> forall Fs2, Rfldsᶠ v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs2 -> Fs1 = Fs2) /\
    (forall s m M1, Rprfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> forall M2, Rprfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2) /\
    (forall s ρ k bs1, Rletsᶠ ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs1 -> forall bs2, Rletsᶠ ρ at k in Θ ⍮ Ξ ⍮ s ↘ bs2 -> bs1 = bs2) /\
    (forall s e b1, Rentᶠ e in Θ ⍮ Ξ ⍮ s ↘ b1 -> forall b2, Rentᶠ e in Θ ⍮ Ξ ⍮ s ↘ b2 -> b1 = b2).
Proof.
  intros Θ Ξ; apply fast_read_mut_ind; intros.
  (** The readbacks of a proof, of the definitions around it and of the
      modules it reads: the other derivation is inverted, the induction
      hypotheses decide the parts. *)
  all: try solve
    [ match goal with
      | H : fast_read_proof _ _ _ _ ?X |- _ = ?X => inversion H; subst; clear H
      | H : fast_read_lets _ _ _ _ _ ?X |- _ = ?X => inversion H; subst; clear H
      | H : fast_read_entry _ _ _ _ ?X |- _ = ?X => inversion H; subst; clear H
      end;
      try (exfalso; cbn [extend_env] in *; congruence);
      functional_fast_fresh_rewrite_clear; functional_fast_eval_rewrite_clear;
      repeat match goal with
             | IH : forall x, _ -> ?a = x, H : _ |- _ =>
                 let E := fresh "E" in pose proof (IH _ H) as E; clear IH; subst
             end;
      congruence ].
  all: progressive_inversion; functional_fast_eval_rewrite_clear;
    functional_fast_fresh_rewrite_clear; functional_fast_eval_rewrite_clear.
  all: try solve [ apply nf_univ_of_cong; eauto | repeat f_equal; solve [eauto] ].
  (** The other side is inverted here: every value type admits the proof
      rule [fast_read_nf_proof] too, and a constructor at an inductive type
      is read by one of two rules.  The proof rule excludes every other by
      the type's head ([domain_kind]), the two constructor rules each other
      by the member's head. *)
  all: try match goal with
       | H : fast_read_nf _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
       | H : fast_read_ne _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
       end.
  all: try match goal with H : domain_kind _ = _ |- _ => cbn in H; discriminate H end.
  all: try match goal with H : domain_kind _ = _ |- _ => cbn in H; subst end.
  all: try match goal with
       | H : evaluated_kind _ |- _ =>
           solve [ exfalso; apply (evaluated_kind_not_propositional _ H); first [ reflexivity | assumption | cbn; congruence ] ]
       end.
  all: functional_fast_fresh_rewrite_clear; functional_fast_eval_rewrite_clear; try congruence.
  all: try solve [ apply nf_univ_of_cong; eauto | repeat f_equal; solve [eauto] ].
  (** A block's scrutinee type: both readbacks of the same type value, the
      one the induction hypothesis decides. *)
  all: repeat match goal with
      | IH : forall M2 : nf, fast_read_typ _ _ ?n ?v M2 -> ?X = M2, H : fast_read_typ _ _ ?n ?v ?Y |- _ =>
          lazymatch X with Y => fail | _ => rewrite <- (IH _ H) in * end
      end.
  (** A type former at one argument or more: the inversion took the
      parameters apart; the induction hypothesis of the parameters decides
      them whole. *)
  all: try solve [ repeat match goal with
         | IH : forall x, _ -> ?a = x, H : _ |- _ => let E := fresh "E" in pose proof (IH _ H) as E; clear IH; subst
         end; congruence ].
  (** A type former, by its two rules: at no argument, no parameter;
      otherwise one member, the parameters as the induction hypothesis
      decides them *)
  all: try solve [ match goal with Ht : fast_read_typ _ _ _ (d_ind _ _ _) _ |- _ =>
      inversion Ht; subst;
      repeat match goal with Hp : fast_read_ps _ _ _ _ _ nil _ |- _ => inversion Hp; subst; clear Hp end;
      try reflexivity;
      repeat match goal with H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
               rewrite H1 in H2; injection H2 as <- end;
      repeat match goal with H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
               rewrite H1 in H2; injection H2 as <- end;
      f_equal; eauto
    end ].
  all: repeat match goal with
      | H1 : List.length ?v = (?a + ?g)%nat, H2 : List.length ?v = (?b + ?g)%nat |- _ =>
          assert_fails (constr_eq a b); assert (a = b) by lia; subst b
      end;
    repeat f_equal; solve [eauto].
Qed.

Corollary functional_fast_read_nf : forall {Θ Ξ} s m M1 M2,
    Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> Rnfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2.
Proof. intros Θ Ξ; pose proof (@functional_fast_read Θ Ξ); firstorder. Qed.

Corollary functional_fast_read_level_atoms : forall {Θ Ξ} s xs ys1 ys2,
    Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys1 -> Rlaᶠ xs in Θ ⍮ Ξ ⍮ s ↘ ys2 -> ys1 = ys2.
Proof. intros Θ Ξ; pose proof (@functional_fast_read Θ Ξ); firstorder. Qed.

Corollary functional_fast_read_ne : forall {Θ Ξ} s m M1 M2,
    Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> Rneᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2.
Proof. intros Θ Ξ; pose proof (@functional_fast_read Θ Ξ); firstorder. Qed.

Corollary functional_fast_read_typ : forall {Θ Ξ} s m M1 M2,
    Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> Rtypᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2.
Proof. intros Θ Ξ; pose proof (@functional_fast_read Θ Ξ); firstorder. Qed.

Corollary functional_fast_read_proof : forall {Θ Ξ} s m M1 M2,
    Rprfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M1 -> Rprfᶠ m in Θ ⍮ Ξ ⍮ s ↘ M2 -> M1 = M2.
Proof. intros Θ Ξ; pose proof (@functional_fast_read Θ Ξ); firstorder. Qed.
End FastReadDeterminismMutual.

#[export]
Hint Resolve functional_fast_read_nf functional_fast_read_ne functional_fast_read_typ functional_fast_read_level_atoms
  functional_fast_read_proof : mctt.

Ltac functional_fast_read_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_fast_read equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (Rnfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rnfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rneᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rneᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rtypᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rtypᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rlaᶠ ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rlaᶠ ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rprfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rprfᶠ ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_fast_read_rewrite_clear := repeat functional_fast_read_rewrite_clear1.

(** ** Lengths

    One fresh variable per member of a telescope, per argument, and per
    leaf path of the container's of a recursive argument. *)
Section FastReadLengths.
  (** The mode the relations run at *)
  Context {SM : SkipMode}.

Lemma fast_fresh_tele_length : forall {Θ Ξ} ρ T s vs,
    Fteleᶠ T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

Lemma fast_fresh_cargs_length : forall {Θ Ξ} p ups ρ gs s vs,
    Fcargsᶠ gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

Lemma fast_fresh_ihs_length : forall {Θ Ξ} ρ As p ups Dc B ρa gs' gs vs s ihs D, ind_lookup Θ Ξ p = Some D ->
    Fihsᶠ vs at gs' gs of Dc under ρ As at p ups for B in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> List.length ihs = cargs_container_count D Dc gs' gs.
Proof.
  intros * HD H; induction H; cbn; try congruence.
  all: match goal with H1 : ind_lookup _ _ _ = Some _, H2 : ind_lookup _ _ _ = Some _ |- _ =>
         rewrite H1 in H2; injection H2 as <- end.
  all: match goal with Hf : fresh_leaf_vars _ _ _ _ |- _ => rewrite List.length_app, (fresh_leaf_vars_length _ _ _ _ Hf) end.
  all: rewrite IHfast_fresh_ihs by assumption.
  all: unfold leaves_in_count; f_equal.
  all: clear; induction (shape_leaves (rview_leaves D) 0 t); cbn; [ reflexivity |].
  all: destruct (leaf_in Dc t' a); cbn; congruence.
Qed.
End FastReadLengths.
