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

(** A unit equal to another denotes. *)
Lemma set_modexp_rel_of_unit_eq : forall Γ U U', set_unit_eq T γ Γ U U' -> set_modexp_rel T γ Γ (me_lit U) (me_lit U).
Proof.
  intros * (F & F' & [HF _ _ _ _]). exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_refl _ _ _ _ _ _ HF Hρ).
Qed.

Lemma set_rule_ctx_extend_mod : forall Γ U, set_ctx T γ Γ -> set_unit_eq T γ Γ U U -> set_ctx T γ (ce_mod U :: Γ).
Proof. intros * HΓ HU. split; [exact HΓ | exact (set_modexp_rel_of_unit_eq _ _ _ HU)]. Qed.

Lemma set_rule_ctx_extend_dm : forall Γ A M U, set_ctx T γ Γ -> set_exp_eq T γ Γ A M M -> set_unit_eq T γ Γ U U ->
    set_ctx T γ (ce_dm A M U :: Γ).
Proof. intros * HΓ HM HU. split; [exact HΓ | split; [exact HM | exact (set_modexp_rel_of_unit_eq _ _ _ HU)]]. Qed.

(** ** Valid Slots *)

Lemma set_rule_slots_empty : set_valid_slots T γ nil.
Proof. exact I. Qed.

(** An entry with no unit keeps the slots valid. *)
Lemma set_rule_slots_extend_plain : forall Γ ce, set_valid_slots T γ Γ -> centry_unit ce = None ->
    set_valid_slots T γ (ce :: Γ).
Proof. intros * HΓ Hn. split; [exact HΓ | intros U HU; congruence]. Qed.

Lemma set_rule_slots_extend_mod : forall Γ U, set_valid_slots T γ Γ -> set_unit_eq T γ Γ U U ->
    set_valid_slots T γ (ce_mod U :: Γ).
Proof. intros * HΓ (F & F' & [_ _ _ HU _]). split; [exact HΓ | intros U' [= <-]; exact HU]. Qed.

Lemma set_rule_slots_extend_dm : forall Γ A M U, set_valid_slots T γ Γ -> set_unit_eq T γ Γ U U ->
    set_valid_slots T γ (ce_dm A M U :: Γ).
Proof. intros * HΓ (F & F' & [_ _ _ HU _]). split; [exact HΓ | intros U' [= <-]; exact HU]. Qed.

End Contexts.
