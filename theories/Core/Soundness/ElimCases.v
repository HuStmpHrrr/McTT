(** * The Eliminator in the Gluing Model

    The gluing rules of the eliminator and of its congruence.  An
    elimination is glued at the target of a sound embedding
    ([Inductives/Elim.v]). *)

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

(** ** The Rules

    The eliminator reads syntactic premises of its rule: its parts are
    typed by their derivations. *)

#[local] Generalizable All Variables.

Lemma glu_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : apps (a_ind p) Ps ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : apps (a_ind p) Ps ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_elim nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] ).
Proof. glu_intro; eapply glu_rel_exp_elim_of_emb; eassumption. Qed.

Lemma glu_exp_eq_elim_cong :
  `( ind_lookup Θ Ξ p = Some D ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊩ P : T) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs -> ⊩ Θ ⍮ Ξ ⍮ Γ) ->
     List.map fst Bs = List.map fst (Bs' : list (String.string * nat * exp)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
        ind_con D c = Some gs -> ⊩ Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
