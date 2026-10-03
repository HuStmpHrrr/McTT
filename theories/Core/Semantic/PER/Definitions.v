From Stdlib Require Import Lia PeanoNat Relation_Definitions RelationClasses Wf_nat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Fixed.
Import Domain_Notations Fixed_Notations.

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
Inductive rel_mod_eval (R : relation domain -> domain -> domain -> Prop) A ρ A' ρ' R' : Prop := mk_rel_mod_eval : forall a a', ⟦ A ⟧ ρ ↘ a -> ⟦ A' ⟧ ρ' ↘ a' -> DF a ≈ a' ∈ R ↘ R' -> rel_mod_eval R A ρ A' ρ' R'.
#[global] Arguments mk_rel_mod_eval {_ _ _ _ _ _}.
Hint Constructors rel_mod_eval : mctt.
(** [per_univ_elem_core] nests through [rel_mod_eval], so generating its
    induction principle needs this scheme. *)
Scheme All for rel_mod_eval.

(** Related modulo application. *)
Inductive rel_mod_app f a f' a' (R : relation domain) : Prop := mk_rel_mod_app : forall fa f'a', $| f & a |↘ fa -> $| f' & a' |↘ f'a' -> Dom fa ≈ f'a' ∈ R -> rel_mod_app f a f' a' R.
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

Inductive per_nat : relation domain :=
| per_nat_zero : Dom zeroᵈ ≈ zeroᵈ ∈ per_nat
| per_nat_succ :
  `{ Dom m ≈ n ∈ per_nat ->
     Dom succᵈ m ≈ succᵈ n ∈ per_nat }
| per_nat_neut :
  `{ Dom m ≈ n ∈ per_bot ->
     Dom ⇑ a m ≈ ⇑ b n ∈ per_nat }
.
Hint Constructors per_nat : mctt.

(** Every pair of values is related at [⊤]: its elements are equal by η. *)
Definition per_True : relation domain := fun _ _ => True.
#[global] Arguments per_True /.
Hint Transparent per_True : mctt.
Hint Unfold per_True : mctt.

Inductive per_ne : relation domain :=
| per_ne_neut :
  `{ Dom m ≈ m' ∈ per_bot ->
     Dom ⇑ a m ≈ ⇑ a' m' ∈ per_ne }
.
Hint Constructors per_ne : mctt.

(** * Universe/Element PER *)
(** ** Universe/Element PER Definition *)

Section Per_univ_elem_core_def.
  Variable
    (i : nat)
      (per_univ_rec : nat -> relation domain).

  Inductive per_univ_elem_core : relation domain -> domain -> domain -> Prop :=
  | per_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
          (lt_j_i : j < i),
          j = j' ->
          (elem_rel <~> per_univ_rec j) ->
          DF 𝕌@j ≈ 𝕌@j' ∈ per_univ_elem_core ↘ elem_rel }
  | per_univ_elem_core_nat :
    forall (elem_rel : relation domain),
      (elem_rel <~> per_nat) ->
      DF ℕᵈ ≈ ℕᵈ ∈ per_univ_elem_core ↘ elem_rel
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
  | per_univ_elem_core_neut :
    `{ forall (elem_rel : relation domain),
          Dom b ≈ b' ∈ per_bot ->
          (elem_rel <~> per_ne) ->
          DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ elem_rel }
  .

  Hypothesis
    (motive : relation domain -> domain -> domain -> Prop)
      (case_U : forall {j j' elem_rel} (lt_j_i : j < i),
          j = j' ->
          (elem_rel <~> per_univ_rec j) ->
          motive elem_rel 𝕌@j 𝕌@j')
      (case_nat : forall {elem_rel},
          (elem_rel <~> per_nat) ->
          motive elem_rel ℕᵈ ℕᵈ)
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
          motive elem_rel ⇑ a b ⇑ a' b').

  #[derive(equations=no, eliminator=no)]
  Equations per_univ_elem_core_strong_ind R a b (H : DF a ≈ b ∈ per_univ_elem_core ↘ R) : DF a ≈ b ∈ motive ↘ R :=
  | R, a, b, (per_univ_elem_core_univ _ lt_j_i HE eq)                 => case_U lt_j_i HE eq;
  | R, a, b, (per_univ_elem_core_nat _ HE)                            => case_nat HE;
  | R, a, b, (per_univ_elem_core_True _ HE)                           => case_True HE;
  | R, a, b, (per_univ_elem_core_False _ HE)                          => case_False HE;
  | R, a, b, (per_univ_elem_core_pi _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi out_rel equiv_a_a' (per_univ_elem_core_strong_ind _ _ _ equiv_a_a') per
        (fun _ _ equiv_c_c' => match HT _ _ equiv_c_c' with
                              | mk_rel_mod_eval b b' evb evb' Rel =>
                                  mk_rel_mod_eval b b' evb evb' (conj _ (per_univ_elem_core_strong_ind _ _ _ Rel))
                              end)
        HE;
  | R, a, b, (per_univ_elem_core_neut _ equiv_b_b' HE)                => case_ne equiv_b_b' HE.

End Per_univ_elem_core_def.

Hint Constructors per_univ_elem_core : mctt.

(** The universes below level [i], indexed by their level: the entry at
    [j < i] is the universe [𝕌@j], and the entries at [j >= i] are empty.  The
    recursion is structural on [i], so [per_univ_elem] unfolds by computation,
    and [per_univ_below_spec] states the entries without [per_univ_below].
    (A well-founded definition of [per_univ_elem] would need functional
    extensionality for its unfolding equation.) *)
Fixpoint per_univ_below (i : nat) : nat -> relation domain :=
  match i with
  | 0 => fun _ _ _ => False
  | S i' => fun j =>
      if Nat.eqb j i'
      then fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem_core i' (per_univ_below i') ↘ R'
      else per_univ_below i' j
  end.

Definition per_univ_elem (i : nat) : relation domain -> domain -> domain -> Prop :=
  per_univ_elem_core i (per_univ_below i).
#[global] Arguments per_univ_elem : simpl never.

Lemma per_univ_elem_equation_1 : forall i,
    per_univ_elem i = per_univ_elem_core i (per_univ_below i).
Proof. reflexivity. Qed.

Hint Rewrite per_univ_elem_equation_1 : per_univ_elem.

Lemma per_univ_below_spec : forall i j,
    j < i ->
    per_univ_below i j = fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem j ↘ R'.
Proof.
  induction i as [| i IHi]; intros j Hlt; [lia |].
  simpl.
  destruct (Nat.eqb_spec j i) as [-> | Hneq]; [reflexivity |].
  apply IHi; lia.
Qed.

Definition per_univ (i : nat) : relation domain := fun a a' => exists R', DF a ≈ a' ∈ per_univ_elem i ↘ R'.
#[global] Arguments per_univ _ _ _ /.
Hint Transparent per_univ : mctt.
Hint Unfold per_univ : mctt.

Lemma per_univ_elem_core_univ' : forall j i elem_rel,
    j < i ->
    (elem_rel <~> per_univ j) ->
    DF 𝕌@j ≈ 𝕌@j ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  simp per_univ_elem.
  econstructor; [eassumption | reflexivity |].
  rewrite per_univ_below_spec by assumption.
  assumption.
Qed.

Hint Resolve per_univ_elem_core_univ' : mctt.

(** ** Universe/Element PER Induction Principle *)

Section Per_univ_elem_ind_def.
  Hypothesis
    (motive : nat -> relation domain -> domain -> domain -> Prop)
      (case_U : forall i {j j' elem_rel},
          j < i -> j = j' ->
          (elem_rel <~> per_univ j) ->
          (forall A B R, DF A ≈ B ∈ per_univ_elem j ↘ R -> motive j R A B) ->
          motive i elem_rel 𝕌@j 𝕌@j')
      (case_N : forall i {elem_rel},
          (elem_rel <~> per_nat) ->
          motive i elem_rel ℕᵈ ℕᵈ)
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
          motive i elem_rel ⇑ a b ⇑ a' b').

  Lemma per_univ_elem_ind i a b R (H : per_univ_elem i a b R) : motive i a b R.
  Proof.
    revert a b R H.
    induction i as [i IHi] using lt_wf_ind.
    intros R a b H.
    refine (per_univ_elem_core_strong_ind i _ (motive i) _
              (fun _ => case_N i) (fun _ => case_True i) (fun _ => case_False i)
              _ (fun _ _ _ _ _ => case_ne i) R a b H).
    - intros j j' elem_rel lt_j_i Heq HE.
      rewrite per_univ_below_spec in HE by assumption.
      eapply case_U; eauto.
    - intros * Ha IHa Hper HT HE.
      eapply case_Pi; eassumption.
  Qed.
End Per_univ_elem_ind_def.


(** * Universe Subtyping *)

Inductive per_subtyp : nat -> domain -> domain -> Prop :=
| per_subtyp_neut :
  `( Dom b ≈ b' ∈ per_bot ->
     Sub ⇑ a b <: ⇑ a' b' at i )
| per_subtyp_nat :
  `( Sub ℕᵈ <: ℕᵈ at i )
| per_subtyp_True :
  `( Sub ⊤ᵈ <: ⊤ᵈ at i )
| per_subtyp_False :
  `( Sub ⊥ᵈ <: ⊥ᵈ at i )
| per_subtyp_univ :
  `( i <= j ->
     j < k ->
     Sub 𝕌@i <: 𝕌@j at k )
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
where "'Sub' a <: b 'at' i" := (per_subtyp i a b) : type_scope.

 Hint Constructors per_subtyp : mctt.

Definition rel_typ i A ρ A' ρ' R' := rel_mod_eval (per_univ_elem i) A ρ A' ρ' R'.
#[global] Arguments rel_typ _ _ _ _ _ _ /.
Hint Transparent rel_typ : mctt.
Hint Unfold rel_typ : mctt.

(** Two terms evaluate to related elements. *)
Definition rel_elem M ρ M' ρ' (R : relation domain) := rel_mod_eval (fun R a a' => R a a') M ρ M' ρ' R.
#[global] Arguments rel_elem _ _ _ _ _ /.
Hint Transparent rel_elem : mctt.
Hint Unfold rel_elem : mctt.

(** * Module PER

    Module values are related closure-style, as [Π] relates [λ]-closures:
    through what their parts evaluate to, never by comparing syntax or
    environments.

    - Two global modules are the same path with arguments related at the
      types of its telescope.
    - Two local units walk their parameters outermost first, each type
      related: supplied arguments are related, and missing ones quantified
      over related pairs.  Then their bodies are related entry by entry, with
      the same names in the same order: a definition by its type and value,
      a module by its closure; or their alias targets by their values.
    - Member closures are related componentwise.

    The relation is not indexed by a type: the types it relates members at are
    those the units declare. *)

Inductive per_dmod : dmod -> dmod -> Prop :=
| per_dmod_global :
  `{ gc_module gc_deps gc_stack p = Some (mr_body T) ->
     per_gargs (List.rev T) nil nil args args' ->
     per_dmod (dm_global p args) (dm_global p args') }
| per_dmod_local :
  `{ per_ltele (List.rev (gu_params U)) ρ (gu_def U) (List.rev (gu_params U')) ρ' (gu_def U') args args' ->
     per_dmod (dm_local ρ U args) (dm_local ρ' U' args') }
| per_dmod_member :
  `{ per_dmod h h' ->
     per_dmod (dm_member h ch) (dm_member h' ch) }
(** Arguments of a global module, outermost first, against its telescope. *)
with per_gargs : list centry -> env -> env -> list domain -> list domain -> Prop :=
| per_gargs_nil :
  `{ per_gargs ts ρ ρ' nil nil }
| per_gargs_cons :
  `{ forall R,
       rel_typ i A ρ A ρ' R ->
       R a a' ->
       per_gargs ts (ρ ↦ a) (ρ' ↦ a') args args' ->
       per_gargs (ce_ass A :: ts) ρ ρ' (a :: args) (a' :: args') }
(** The parameters of two local units, outermost first, then their contents. *)
with per_ltele : list centry -> env -> moddef -> list centry -> env -> moddef -> list domain -> list domain -> Prop :=
| per_ltele_supplied :
  `{ forall R,
       rel_typ i A ρ A' ρ' R ->
       R a a' ->
       per_ltele ts (ρ ↦ a) D ts' (ρ' ↦ a') D' args args' ->
       per_ltele (ce_ass A :: ts) ρ D (ce_ass A' :: ts') ρ' D' (a :: args) (a' :: args') }
| per_ltele_missing :
  `{ forall R,
       rel_typ i A ρ A' ρ' R ->
       (forall c c', R c c' -> per_ltele ts (ρ ↦ c) D ts' (ρ' ↦ c') D' nil nil) ->
       per_ltele (ce_ass A :: ts) ρ D (ce_ass A' :: ts') ρ' D' nil nil }
| per_ltele_done :
  `{ per_mdef ρ D ρ' D' ->
     per_ltele nil ρ D nil ρ' D' nil nil }
with per_mdef : env -> moddef -> env -> moddef -> Prop :=
| per_mdef_body :
  `{ per_body ρ Φ ρ' Φ' ->
     per_mdef ρ (md_body Φ) ρ' (md_body Φ') }
| per_mdef_alias :
  `{ eval_modexp gc_deps gc_stack E ρ h ->
     eval_modexp gc_deps gc_stack E' ρ' h' ->
     per_dmod h h' ->
     per_mdef ρ (md_alias E) ρ' (md_alias E') }
(** Two bodies, each entry seen in the environment its predecessors make. *)
with per_body : env -> gmod -> env -> gmod -> Prop :=
| per_body_nil :
  `{ per_body ρ gm_nil ρ' gm_nil }
| per_body_def :
  `{ forall R,
       per_body ρ Φ ρ' Φ' ->
       eval_benv gc_deps gc_stack ρ Φ ρ1 ->
       eval_benv gc_deps gc_stack ρ' Φ' ρ1' ->
       rel_typ i A ρ1 A' ρ1' R ->
       rel_elem M ρ1 M' ρ1' R ->
       per_body ρ (gm_ext Φ y (ge_def b pv A (Some M))) ρ' (gm_ext Φ' y (ge_def b' pv' A' (Some M'))) }
| per_body_mod :
  `{ per_body ρ Φ ρ' Φ' ->
     eval_benv gc_deps gc_stack ρ Φ ρ1 ->
     eval_benv gc_deps gc_stack ρ' Φ' ρ1' ->
     per_dmod (dm_local ρ1 Uy nil) (dm_local ρ1' Uy' nil) ->
     per_body ρ (gm_ext Φ y (ge_mod Uy)) ρ' (gm_ext Φ' y (ge_mod Uy')) }
| per_body_check :
  `{ per_body ρ Φ ρ' Φ' ->
     per_body ρ (gm_check Φ c) ρ' (gm_check Φ' c') }
.

Scheme per_dmod_mut_ind := Induction for per_dmod Sort Prop
with per_gargs_mut_ind := Induction for per_gargs Sort Prop
with per_ltele_mut_ind := Induction for per_ltele Sort Prop
with per_mdef_mut_ind := Induction for per_mdef Sort Prop
with per_body_mut_ind := Induction for per_body Sort Prop.
Combined Scheme per_dmod_mut_ind_all from
  per_dmod_mut_ind, per_gargs_mut_ind, per_ltele_mut_ind, per_mdef_mut_ind, per_body_mut_ind.

Hint Constructors per_dmod per_gargs per_ltele per_mdef per_body : mctt.

(** * Context/Environment PER *)

Inductive per_ctx_env : relation env -> ctx -> ctx -> Prop :=
| per_ctx_env_nil :
  `{ forall env_rel,
        (env_rel <~> fun ρ ρ' => True) ->
        EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }
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
(** A module slot: the two units' closures over related tails are related, and
    each head of the environment is related to the closures of both units
    over its own tail. *)
| per_ctx_env_cons_mod :
  `{ forall tail_rel env_rel
        (equiv_Γ_Γ' : EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) ->
        (env_rel <~> fun ρ ρ' =>
             (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) /\
             per_dmod (env_mod ρ 0) (dm_local ρ↯ U nil) /\
             per_dmod (env_mod ρ 0) (dm_local ρ↯ U' nil) /\
             per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U nil) /\
             per_dmod (env_mod ρ' 0) (dm_local ρ'↯ U' nil)) ->
        EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ env_rel }
.
Hint Constructors per_ctx_env : mctt.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env R' Γ Γ'.
Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.
Hint Transparent valid_ctx : mctt.
Hint Unfold valid_ctx : mctt.


(** * Context Subtyping *)

Inductive per_ctx_subtyp : ctx -> ctx -> Prop :=
| per_ctx_subtyp_nil :
  SubE ⋅ <: ⋅
| per_ctx_subtyp_cons :
  `{ forall tail_rel env_rel env_rel',
        SubE Γ <: Γ' ->
        EF Γ ≈ Γ ∈ per_ctx_env ↘ tail_rel ->
        (forall ρ ρ' a a'
           (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
            ⟦ A ⟧ ρ ↘ a ->
            ⟦ A' ⟧ ρ' ↘ a' ->
            Sub a <: a' at i) ->
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
Hint Constructors per_nat : mctt.
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
Hint Resolve per_univ_elem_core_univ' : mctt.
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
Hint Constructors per_dmod per_gargs per_ltele per_mdef per_body : mctt.
#[export]
Hint Constructors per_ctx_env : mctt.
#[export]
Hint Transparent valid_ctx : mctt.
#[export]
Hint Unfold valid_ctx : mctt.
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
      refine (per_univ_elem_ind _ _ _ _ _ _ _);
      [ do 8 intro | do 3 intro | do 3 intro | do 3 intro | do 11 intro; ih; do 3 intro | do 8 intro ]; cbv beta
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
