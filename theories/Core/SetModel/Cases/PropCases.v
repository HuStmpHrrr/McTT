(** * The Set Rules of Propositions

    The set judgments of the rules of [Prop], [⊤], [⊥] and [tt]: [Prop]
    is a relevant code of the first small universe, a proposition a
    proposition code, a proof the empty set. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export UniverseCases.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Props.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_denotes_prop : forall Γ, set_denotes T γ Γ a_prop (fun _ => prop_universe_code).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

(** [Prop : Type@0]. *)
Lemma set_rule_prop : forall Γ, set_exp_eq T γ Γ (a_univ (a_llit (0, 0))) a_prop a_prop.
Proof.
  intros. exists (fun _ => small_universe_code T (0, 0)), (fun _ => prop_universe_code).
  constructor; [apply set_denotes_univ_lit | apply set_denotes_prop .. |]. intros ρ _.
  pose proof (tower_grothendieck T (us (0, 0))) as HV. apply set_mem_small_universe_code.
  - unfold prop_universe_code. apply (grothendieck_type_code _ HV); [apply (grothendieck_empty _ HV) | apply (grothendieck_prop_codes _ HV)].
  - do 3 eexists. split; [apply set_eq_refl | discriminate].
Qed.

Lemma set_denotes_True : forall Γ, set_denotes T γ Γ a_True (fun _ => prop_code True).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_False : forall Γ, set_denotes T γ Γ a_False (fun _ => prop_code False).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_tt : forall Γ, set_denotes T γ Γ a_tt (fun _ => empty_set).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma prop_code_mem_prop_universe : forall P, set_mem (prop_code P) (code_carrier prop_universe_code).
Proof.
  intros. unfold prop_universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  exists P. apply set_eq_refl.
Qed.

(** [⊤ : Prop]. *)
Lemma set_rule_True : forall Γ, set_exp_eq T γ Γ a_prop a_True a_True.
Proof.
  intros. exists (fun _ => prop_universe_code), (fun _ => prop_code True).
  constructor; [apply set_denotes_prop | apply set_denotes_True .. | intros; apply prop_code_mem_prop_universe].
Qed.

(** [⊥ : Prop]. *)
Lemma set_rule_False : forall Γ, set_exp_eq T γ Γ a_prop a_False a_False.
Proof.
  intros. exists (fun _ => prop_universe_code), (fun _ => prop_code False).
  constructor; [apply set_denotes_prop | apply set_denotes_False .. | intros; apply prop_code_mem_prop_universe].
Qed.

(** [tt : ⊤]. *)
Lemma set_rule_tt : forall Γ, set_exp_eq T γ Γ a_True a_tt a_tt.
Proof.
  intros. exists (fun _ => prop_code True), (fun _ => empty_set).
  constructor; [apply set_denotes_True | apply set_denotes_tt .. |]. intros ρ _.
  apply (proj2 (prop_true_prop_code True)). exact I.
Qed.

End Props.
