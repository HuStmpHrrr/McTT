(** * Inductive Types in the Gluing Model: the Type Former and the Constructors

    The gluing rules of the type former and the constructors of an
    inductive type, and of their congruences.  The type former and the
    constructors are glued at the target of a sound embedding
    ([Inductives/Con.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Con.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

(** ** The Rules

    The type former and the constructors read syntactic premises of their
    rules: a declaration is typed by its derivation. *)

#[local] Generalizable All Variables.

Lemma glu_ind :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_ind p : ind_ty D ).
Proof. glu_intro; eapply glu_rel_exp_ind_of_emb; eassumption. Qed.

Lemma glu_con :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
        ⊩ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                  ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ ⋅ ⊩ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_con p c : con_ty p D gs ).
Proof. glu_intro; eapply glu_rel_exp_con_of_emb; eassumption. Qed.

Lemma glu_exp_eq_ind_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_con_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     Θ ⍮ Ξ ⍮ ⋅ ⊩ con_ty p D gs : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
