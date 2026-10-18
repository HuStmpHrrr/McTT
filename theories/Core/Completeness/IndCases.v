(** * Inductive Types: the Type Former and the Constructors

    The semantic rules of the type former and the constructors of an
    inductive type, and of their congruences.  Each holds because the
    declaration is valid at the target of a sound embedding
    ([Inductives/Con.v], [Inductives/Elim.v]). *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Con.
From Mctt.Core.Completeness Require Import SubtypingCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Elim.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

Lemma sem_ind :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p : ind_ty D ).
Proof. intros * HΓ Hl; sem_intro; [ assumption | eapply rel_exp_under_ctx_ind_of_emb; eassumption ]. Qed.

Lemma sem_con :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
        ⊨ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                  ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p c : con_ty p D gs ).
Proof. intros * HΓ Hl Hcon _ _ _; sem_intro; [ assumption | eapply rel_exp_under_ctx_con_of_emb; eassumption ]. Qed.

Lemma sem_exp_eq_ind_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_ind p ≈ a_ind p : ind_ty D ).
Proof. intros * HΓ Hl; sem_intro; [ assumption | eapply rel_exp_under_ctx_ind_of_emb; eassumption ]. Qed.

Lemma sem_exp_eq_con_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊨ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     Θ ⍮ Ξ ⍮ ⋅ ⊨ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_con p c ≈ a_con p c : con_ty p D gs ).
Proof. intros * HΓ Hl Hcon _ _; sem_intro; [ assumption | eapply rel_exp_under_ctx_con_of_emb; eassumption ]. Qed.
