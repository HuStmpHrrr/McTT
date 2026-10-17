(** * Arguments Related at a Telescope

    Arguments a [per_gargs] relates, at a telescope valid over [Tb], make
    environments the context PER of the telescope over [Tb] relates. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases MemberReps.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma gargs_rel : forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' ->
    forall Tb Rb, EF Tb ≈ Tb ∈ per_ctx_env ↘ Rb -> Rb ρ ρ' -> ⊨ rev ts ++ Tb ->
    exists R, EF rev (firstn (List.length args) ts) ++ Tb ≈ rev (firstn (List.length args) ts) ++ Tb ∈ per_ctx_env ↘ R /\
      R (env_args ρ args) (env_args ρ' args').
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' R1 HA Ha Hg IH]; intros Tb Rb HTb Hρ HC; cbn [firstn List.length rev app].
  - exists Rb; split; assumption.
  - cbn [rev] in HC; rewrite <- app_assoc in HC; cbn [app] in HC.
    destruct (sem_ctx_ass_inv (sem_ctx_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ HTb HAv) as HTb'.
    assert (Hρ' : per_env_extend A A Rb (ρ ↦ a) (ρ' ↦ a')).
    { split; [ exact Hρ |].
      destruct HA as [x x' Hx Hx' Hxx]; eapply per_head_of; [ exact Hx | exact Hx' | exact Hxx | exact Ha ]. }
    destruct (IH _ _ HTb' Hρ' HC) as (R & HR & HRρ).
    exists R; rewrite <- app_assoc; cbn [app]; split; [ exact HR | exact HRρ ].
Qed.

Lemma per_ctx_env_nil_true : EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ (fun _ _ => True).
Proof. apply per_ctx_env_nil; reflexivity. Qed.

End Fixed_GCtx.
