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
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A unit equal to another denotes. *)
Lemma set_modexp_rel_of_unit_eq {GC : GCtx} : forall Γ U U', set_rel_unit_eq T γ Γ U U' ->
    set_modexp_rel T γ Γ (me_lit U) (me_lit U).
Proof.
  intros * (F & F' & [HF _ _ _ _]). exists F, F. constructor; [exact HF | exact HF |].
  intros ρ Hρ. exact (set_modexp_denotes_refl _ _ _ _ _ _ HF Hρ).
Qed.

(** An entry with no unit keeps the slots valid. *)
Lemma set_valid_slots_extend_plain {GC : GCtx} : forall Γ ce, set_valid_slots T γ Γ -> centry_unit ce = None ->
    set_valid_slots T γ (ce :: Γ).
Proof. intros * HΓ Hn. split; [exact HΓ | intros U HU; congruence]. Qed.

(** A unit equal to itself makes a slot holding it valid. *)
Lemma set_valid_slots_extend_unit {GC : GCtx} : forall Γ ce U, set_valid_slots T γ Γ -> centry_unit ce = Some U ->
    set_rel_unit_eq T γ Γ U U -> set_valid_slots T γ (ce :: Γ).
Proof. intros * HΓ Hu (F & F' & [_ _ _ HU _]). split; [exact HΓ | intros U' HU'; rewrite Hu in HU'; injection HU' as <-; exact HU]. Qed.

(** ** The Rules *)

Lemma set_rule_ctx_empty : set_ctx_slots Θ Ξ T γ nil.
Proof. set_open. split; exact I. Qed.

Lemma set_rule_ctx_extend : forall Γ κ A S, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ S A A ->
    set_ctx_slots Θ Ξ T γ (ce_ass κ A :: Γ).
Proof.
  intros * HΓ HA. set_open. destruct HΓ as [HΓ Hsl]. destruct HA as (FS & FA & FA' & [_ HA _ _ _]).
  split; [split; [exact HΓ | exists FA; exact HA] | exact (set_valid_slots_extend_plain _ (ce_ass κ A) Hsl eq_refl)].
Qed.

Lemma set_rule_ctx_extend_def : forall Γ A M, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ A M M ->
    set_ctx_slots Θ Ξ T γ (ce_def A M :: Γ).
Proof.
  intros * HΓ HM. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; assumption | exact (set_valid_slots_extend_plain _ (ce_def A M) Hsl eq_refl)].
Qed.

Lemma set_rule_ctx_extend_mod : forall Γ U, set_ctx_slots Θ Ξ T γ Γ -> set_unit_eq Θ Ξ T γ Γ U U ->
    set_ctx_slots Θ Ξ T γ (ce_mod U :: Γ).
Proof.
  intros * HΓ HU. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; [exact HΓ | exact (set_modexp_rel_of_unit_eq _ _ _ HU)] | exact (set_valid_slots_extend_unit _ (ce_mod U) _ Hsl eq_refl HU)].
Qed.

Lemma set_rule_ctx_extend_dm : forall Γ A M U, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ A M M ->
    set_unit_eq Θ Ξ T γ Γ U U -> set_ctx_slots Θ Ξ T γ (ce_dm A M U :: Γ).
Proof.
  intros * HΓ HM HU. set_open. destruct HΓ as [HΓ Hsl].
  split; [split; [exact HΓ | split; [exact HM | exact (set_modexp_rel_of_unit_eq _ _ _ HU)]]
         | exact (set_valid_slots_extend_unit _ (ce_dm A M U) _ Hsl eq_refl HU)].
Qed.

End Contexts.
