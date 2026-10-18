(** * The [ι] Rule of an Inductive Type

    The semantic rule of [ι]: the eliminator at a constructor is its branch
    at the arguments and the recursive results.  It holds because the two
    sides are related at the target of a sound embedding
    ([Inductives/Iota.v]). *)

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
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Completeness.Inductives Require Import Iota.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

#[local] Generalizable All Variables.

Lemma sem_exp_eq_elim_iota :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     List.length Ps = ind_np D ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ P : T) ->
     List.length As = List.length gs ->
     (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊨ N : T) ->
     nm = S (ind_nn D) ->
     Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
     brs_names (ind_cons D) Bs ->
     (forall c gs, ind_con D c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊨ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
     (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
          : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
     brs_lookup Bs c = Some (n, B) ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_elim nm A Bs (apps (a_con p c) (Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs nm A Bs (sb_of_list Id Ps) gs As)]
       : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ apps (a_con p c) (Ps ++ As) :: nil)] ).
Proof. intros; sem_intro; [ assumption | eapply rel_exp_under_ctx_elim_iota_of_emb; eassumption ]. Qed.
