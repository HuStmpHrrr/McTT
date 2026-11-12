(** * The Set Rules of Local Definitions

    A local definition's body is read at the definition's value; with the
    definition substituted it has the same value ([ζ]). *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export VariableCases.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Lets.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  Hypothesis Hmods : forall q, set_module_eq (global_module γ q) (global_module γ q).

(** The environment of a definition at its value. *)
Definition def_env (FM : set_env -> aczel_set) (ρ : set_env) : set_env := set_env_extend ρ (set_entry_term ak_relevant (FM ρ)).

Lemma set_env_in_def : forall Γ A M FM ρ, set_denotes T γ Γ M FM -> set_env_in T γ Γ ρ ->
    set_env_in T γ (ce_def A M :: Γ) (def_env FM ρ).
Proof.
  intros * HM Hρ. split; [exact Hρ |]. exists (FM ρ), (FM ρ), (FM ρ).
  constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_refl | apply set_eq_refl].
Qed.

(** A term under a definition denotes, with the definition substituted, its
    value at the definition's. *)
Lemma set_denotes_def_sub : forall Γ A M X FM FX, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_def A M :: Γ ->
    set_denotes T γ Γ M FM -> set_denotes T γ (ce_def A M :: Γ) X FX ->
    set_denotes T γ Γ (exp_sub X (sb_extend sb_id (se_exp M))) (fun ρ => FX (def_env FM ρ)).
Proof.
  intros * HΓ Hc Hσ HM HX. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  apply (set_interp_single_sub_entry T γ Γ ρ (ce_def A M) ak_relevant M (FM ρ)); [exact Hc | exact Hσ | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
  apply (set_denotes_exists _ _ _ _ _ HX). apply set_env_in_def; assumption.
Qed.

Lemma set_denotes_let_def : forall Γ A M B FM FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ ->
    set_denotes T γ Γ M FM -> set_denotes T γ (ce_def A M :: Γ) B FB ->
    set_denotes T γ Γ (a_let (b_def A M) B) (fun ρ => FB (def_env FM ρ)).
Proof.
  intros * HΓ Hc HM HB. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor.
  - intros ρ Hρ. econstructor; [exact Hc | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
    apply (set_denotes_exists _ _ _ _ _ HB). apply set_env_in_def; assumption.
  - intros ρ ρ' v Hr Hv. inversion Hv; subst.
    assert (Hρ : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    match goal with HM' : set_interp _ _ _ _ M ?v0, HB' : set_interp _ _ _ _ B _ |- _ =>
      apply (set_denotes_unique _ _ _ _ _ HB (def_env FM ρ) (set_env_extend ρ' (set_entry_term ak_relevant v0)) v); [| exact HB'];
      split; [exact Hr |]; exists (FM ρ), v0, (FM ρ);
      constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_refl
                   | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr HM')] end.
Qed.

(** [ℓ A ≔ M in B : C[M]], and [ζ] at it: [ℓ A ≔ M in B ≈ B[M]]. *)
Lemma set_rule_let_def_zeta : forall Γ A M B C FS FA FA2 FA' FM FM2 FC FB FB2, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_def A M :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_def A M :: Γ ->
    set_exp_eq_with T γ Γ FS A A FA FA2 FA2 -> set_exp_eq_with T γ Γ A M M FA' FM FM2 ->
    set_exp_eq_with T γ (ce_def A M :: Γ) C B B FC FB FB2 ->
    set_exp_eq T γ Γ (exp_sub C (sb_extend sb_id (se_exp M))) (a_let (b_def A M) B) (exp_sub B (sb_extend sb_id (se_exp M))).
Proof.
  intros * HΓ Hc Hσ _ [HA' HM _ _ HMm] [HC HB _ _ HBm].
  exists (fun ρ => FC (def_env FM ρ)), (fun ρ => FB (def_env FM ρ)), (fun ρ => FB (def_env FM ρ)).
  constructor; [apply set_denotes_def_sub with (A := A); assumption | apply set_denotes_let_def; assumption
               | apply set_denotes_def_sub with (A := A); assumption | intros; apply set_eq_refl |].
  intros ρ Hρ. apply HBm. apply set_env_in_def; assumption.
Qed.

End Lets.
