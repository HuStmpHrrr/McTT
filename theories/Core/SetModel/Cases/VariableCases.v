(** * The Set Rules of Variables

    The variable rules in the set model.  The lemmas they rest on are in
    [Judgments/Variables.v]. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Import Variables.
From Mctt.Core.SetModel.Interpretation Require Import Weakening.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Variables.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** [Γ ∋ #x : A] gives [#x : A]. *)
Lemma set_rule_var : forall Γ x A, Γ ∋ #x : A -> set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> set_exp_eq Θ Ξ T γ Γ A (a_var x) (a_var x).
Proof.
  intros * H HΓ Hc. set_open. destruct HΓ as [HΓ _]. destruct (set_lookup_denotes T γ Hfn Hmods _ _ _ H HΓ Hc) as [FA [HA Hm]].
  exists FA, (fun ρ => set_entry_value (ρ x)), (fun ρ => set_entry_value (ρ x)).
  constructor; [exact HA | apply set_denotes_var .. | intros; apply set_eq_refl | exact Hm].
Qed.

(** δ: a defined variable is its definition's body. *)
Lemma set_rule_var_delta : forall Γ x A M, Γ ∋ #x : A -> Γ ∋ #x ≔ M : A -> set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    set_exp_eq Θ Ξ T γ Γ A (a_var x) M.
Proof.
  intros * H Hd HΓ Hc. set_open. destruct HΓ as [HΓ _]. destruct (set_lookup_denotes T γ Hfn Hmods _ _ _ H HΓ Hc) as [FA [HA Hm]].
  destruct (set_lookup_def_denotes T γ Hfn Hmods _ _ _ _ Hd HΓ Hc) as [FM [HM EM]].
  exists FA, (fun ρ => set_entry_value (ρ x)), FM.
  constructor; [exact HA | apply set_denotes_var | exact HM | exact EM | exact Hm].
Qed.

End Variables.
