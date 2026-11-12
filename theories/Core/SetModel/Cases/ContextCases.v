(** * The Set Rules of Contexts

    A context is valid when each entry is valid in the context before it:
    an assumption's type denotes, a definition is of its type, a module
    slot's unit is equal to itself. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Contexts.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_ctx_empty : set_ctx T γ nil.
Proof. exact I. Qed.

Lemma set_rule_ctx_extend : forall Γ κ A S FS FA FA', set_ctx T γ Γ -> set_exp_eq_with T γ Γ S A A FS FA FA' ->
    set_ctx T γ (ce_ass κ A :: Γ).
Proof. intros * HΓ [_ HA _ _ _]. split; [exact HΓ | exists FA; exact HA]. Qed.

Lemma set_rule_ctx_extend_def : forall Γ A M, set_ctx T γ Γ -> set_exp_eq T γ Γ A M M -> set_ctx T γ (ce_def A M :: Γ).
Proof. intros * HΓ HM. split; assumption. Qed.

Lemma set_rule_ctx_extend_mod : forall Γ U, set_ctx T γ Γ -> set_unit_eq T γ Γ U U -> set_ctx T γ (ce_mod U :: Γ).
Proof. intros * HΓ HU. split; assumption. Qed.

Lemma set_rule_ctx_extend_dm : forall Γ A M U, set_ctx T γ Γ -> set_exp_eq T γ Γ A M M -> set_unit_eq T γ Γ U U ->
    set_ctx T γ (ce_dm A M U :: Γ).
Proof. intros * HΓ HM HU. split; [exact HΓ | split; assumption]. Qed.

End Contexts.
