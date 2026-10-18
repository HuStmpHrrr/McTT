(** * The [ι] Rule in the Gluing Model

    The gluing rule of [ι] is the gluing of its context. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Elim.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution Instance.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Modules Require MemberTypes.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndCanon IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
Require Import Mctt.Core.Soundness.Inductives.Con.
Require Import Mctt.Core.Soundness.Inductives.Elim.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

#[local] Generalizable All Variables.

Lemma glu_exp_eq_elim_iota :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     List.length As = List.length gs ->
     (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ N : T) ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs -> ⊩ Θ ⍮ Ξ ⍮ Γ) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     brs_lookup Bs c = Some (n, B) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
