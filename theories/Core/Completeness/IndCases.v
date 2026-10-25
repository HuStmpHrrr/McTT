(** * Inductive Types: the Type Formers and the Constructors

    The semantic rules of the type former of a declared member and of the
    constructors of a member of a group of inductive types, of their
    congruences, and of a view's constructor as its container's.  Each
    holds because the group is valid at the target of a sound embedding
    ([valid_groups_of_emb]; [Inductives/Model.v], [Inductives/Con.v],
    [Inductives/ViewRules.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model ArgTypes.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Con.
From Mctt.Core.Completeness Require Import SubtypingCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Elim ViewRules.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

Lemma sem_ind :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     k < ind_ndecl D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p k : ind_ty D M ).
Proof.
  intros * HΓ Hl HM Hlt; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ => pose proof (valid_groups_valid _ (valid_groups_of_emb _ _ _ _ He) p D Hl) as Hg end.
  destruct (member_lt_decl _ _ _ _ _ (valid_group_typed _ _ Hg) HM Hlt) as [pm Hh].
  apply closed_weaken_valid; [ assumption |].
  exact (valid_exp_under_ctx_ind D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) (valid_group_sort _ _ Hg) p (valid_group_lookup _ _ Hg)
           (valid_group_ass _ _ Hg) k M pm HM Hh).
Qed.

Lemma sem_con :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     ind_con M c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     (forall gs1 t gs2 j, gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
        ⊨ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D M gs1 ++ im_params D M)
                  ▹ ptyp_ty p D (im_nn M) (List.repeat false j ++ cargs_pat gs1) (ptyp_skip j t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D k M gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p k c : con_ty p D k M gs ).
Proof.
  intros * HΓ Hl HM Hcon _ _ HT; sem_intro; [ assumption |].
  apply closed_weaken_valid; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ =>
    exact (valid_exp_under_ctx_con _ _ _ (valid_groups_of_emb _ _ _ _ He) Hl _ _ _ _ HM Hcon _ ltac:(eassumption)) end.
Qed.

Lemma sem_exp_eq_ind_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     k < ind_ndecl D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p k ≈ a_ind p k : ind_ty D M ).
Proof. exact @sem_ind. Qed.

Lemma sem_exp_eq_con_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     ind_con M c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D k M gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p k c ≈ a_con p k c : con_ty p D k M gs ).
Proof.
  intros * HΓ Hl HM Hcon _ HT; sem_intro; [ assumption |].
  apply closed_weaken_valid; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ =>
    exact (valid_exp_under_ctx_con _ _ _ (valid_groups_of_emb _ _ _ _ He) Hl _ _ _ _ HM Hcon _ ltac:(eassumption)) end.
Qed.

Lemma sem_exp_eq_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     List.length Us = ind_nu D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ apps_exp (a_con p j c) (Us ++ Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ apps_exp (a_con p j c) (Us ++ Ms) ≈ apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms) : A ).
Proof.
  intros * Hl HMj Hh HUl HL HR; sem_intro; [ assumption |].
  match goal with He : valid_emb _ _ _ _ |- _ =>
    exact (rel_exp_under_ctx_con_view _ _ _ (valid_groups_of_emb _ _ _ _ He) Hl _ _ _ _ _ _ _ _ _ _ _ HMj Hh HUl
             ltac:(eassumption) ltac:(eassumption)) end.
Qed.
