(** * The Rules of Variables

    The rules of variables in the PER model: a context's lookup and the
    variable rules.  The lemmas they rest on are in
    [LogicalRelation/Variables.v]. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution SystemOpt.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Contexts Universes Variables.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

Lemma sem_vlookup :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x : A ).
Proof. intros * HΓ Hx; sem_intro; [ assumption | exact (valid_exp_under_ctx_vlookup Hx HΓ) ]. Qed.

Lemma sem_exp_eq_var :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ #x : A ).
Proof. intros; eapply sem_vlookup; eassumption. Qed.

Lemma sem_exp_eq_var_delta :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ M : A ).
Proof.
  intros * HΓ Hx; sem_intro; [ assumption |].
  clear - Hx HΓ; revert HΓ.
  induction Hx as [A M Γ | A M U Γ | x A M Γ e Hx IH]; intros HΓ.
  - apply rel_exp_under_ctx_var_delta_here; assumption.
  - apply rel_exp_under_ctx_var_delta_here_dm; assumption.
  - pose proof (rel_ctx_wf_per_ctx_env HΓ) as [env_relΓe HΓeper].
    exact (rel_exp_under_ctx_shift HΓeper (IH (rel_ctx_wf_tail HΓ))).
Qed.
