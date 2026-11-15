(** * The Set Rules of Contexts

    The rules of [⊢ Γ] in the set model: the empty context and its
    extensions.  The lemmas they rest on are in [Judgments/Contexts.v]. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Judgments Require Import Contexts.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Contexts.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_ctx_empty : set_ctx_slots Θ Ξ T γ nil.
Proof. set_open. split; exact I. Qed.

Lemma set_rule_ctx_extend : forall Γ κ A S, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ S A A ->
    set_ctx_slots Θ Ξ T γ (ce_ass κ A :: Γ).
Proof.
  intros * HΓ HA. set_open. destruct HΓ as [HΓ Hsl]. destruct HA as (FS & FA & FA' & [_ HA _ _ _]).
  split; [split; [exact HΓ | exists FA; exact HA] | exact (set_valid_slots_extend_plain T γ _ (ce_ass κ A) Hsl eq_refl)].
Qed.

Lemma set_rule_ctx_extend_def : forall Γ A M, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ A M M ->
    set_ctx_slots Θ Ξ T γ (ce_def A M :: Γ).
Proof.
  intros * HΓ HM. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; assumption | exact (set_valid_slots_extend_plain T γ _ (ce_def A M) Hsl eq_refl)].
Qed.

Lemma set_rule_ctx_extend_mod : forall Γ U, set_ctx_slots Θ Ξ T γ Γ -> set_unit_eq Θ Ξ T γ Γ U U ->
    set_ctx_slots Θ Ξ T γ (ce_mod U :: Γ).
Proof.
  intros * HΓ HU. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; [exact HΓ | exact (set_modexp_rel_of_unit_eq T γ _ _ _ HU)] | exact (set_valid_slots_extend_unit T γ _ (ce_mod U) _ Hsl eq_refl HU)].
Qed.

Lemma set_rule_ctx_extend_dm : forall Γ A M U, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ A M M ->
    set_unit_eq Θ Ξ T γ Γ U U -> set_ctx_slots Θ Ξ T γ (ce_dm A M U :: Γ).
Proof.
  intros * HΓ HM HU. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; [exact HΓ | split; [exact HM | exact (set_modexp_rel_of_unit_eq T γ _ _ _ HU)]]
         | exact (set_valid_slots_extend_unit T γ _ (ce_dm A M U) _ Hsl eq_refl HU)].
Qed.

End Contexts.
