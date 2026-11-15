(** * The Set Model of Contexts

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






End Contexts.
