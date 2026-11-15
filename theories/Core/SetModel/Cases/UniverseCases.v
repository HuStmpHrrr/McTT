(** * The Set Rules of Universes

    The rules of the universes in the set model: [Typeω@i], [Type⟨M⟩] and
    their congruences, and the tests for large and small universes.  The
    lemmas they rest on are in [Judgments/Universes.v] and
    [Judgments/Levels.v]. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Judgments Require Import Universes Levels.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

(** [Typeω@i : Typeω@(S i)]. *)
Lemma set_rule_typ : forall Θ Ξ T γ Γ i, set_exp_eq Θ Ξ T γ Γ (a_typ (S i)) (a_typ i) (a_typ i).
Proof.
  intros * Θ2 Ξ2 _.
  exists (fun _ => large_universe_code T (S i)), (fun _ => large_universe_code T i), (fun _ => large_universe_code T i).
  constructor; [apply set_denotes_typ .. | intros; apply set_eq_refl |]. intros ρ _.
  unfold large_universe_code at 1, universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  pose proof (tower_grothendieck T (ul (S i))) as HV.
  destruct (universe_code_mem (large_ordinal_set i) (tower T (ul i)) _ HV
              (grothendieck_universe_index_set _ HV (ul i)) (tower_increasing T (ul i) (ul (S i)) ltac:(cbn; lia))) as [Hm Hr].
  apply set_mem_separation; [exact is_relevant_code_resp |]. split; assumption.
Qed.

(** [M ≈ M' : Level@n] gives [Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩]. *)
Lemma set_rule_univ : forall Θ Ξ T γ Γ n M M', set_exp_eq Θ Ξ T γ Γ (a_level n) M M' ->
    set_exp_eq Θ Ξ T γ Γ (a_univ (a_succl M)) (a_univ M) (a_univ M').
Proof.
  intros * HMM' Θ2 Ξ2 Hμ. destruct (HMM' _ _ Hμ) as (FL & FM & FM' & [HL HM HM' E Hm]).
  exists (fun ρ => level_universe_code T (successor_set (FM ρ))), (fun ρ => level_universe_code T (FM ρ)),
    (fun ρ => level_universe_code T (FM' ρ)).
  constructor.
  - apply set_denotes_univ. constructor; [intros ρ Hρ; constructor; exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
    intros ρ ρ' v Hr Hv. inversion Hv; subst. apply successor_set_resp. exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)).
  - apply set_denotes_univ. exact HM.
  - apply set_denotes_univ. exact HM'.
  - intros ρ Hρ. unfold level_universe_code, universe_code. apply type_code_resp; [exact (E ρ Hρ) |].
    apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | apply small_universe_set_resp; exact (E ρ Hρ) | tauto].
  - intros ρ Hρ. pose proof (Hm ρ Hρ) as Hl.
    eapply set_mem_eq_r in Hl; [| apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HL (set_denotes_level T γ _ n) Hρ)].
    apply set_mem_level_type in Hl as [[a b] [_ Eo]].
    unfold level_universe_code at 1, universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply set_mem_separation; [exact is_relevant_code_resp |].
    assert (Hs : set_eq (small_universe_set T (successor_set (FM ρ))) (tower T (us (a, S b))))
      by (apply small_universe_set_eq; apply successor_set_resp; exact Eo).
    pose proof (tower_grothendieck T (us (a, S b))) as HV.
    destruct (universe_code_mem (FM ρ) (small_universe_set T (FM ρ)) _ HV) as [Hc Hr].
    + eapply set_mem_eq_l; [apply set_eq_sym; exact Eo |]. exact (grothendieck_universe_index_set _ HV (us (a, b))).
    + eapply set_mem_eq_l; [apply set_eq_sym; apply small_universe_set_eq; exact Eo |].
      apply tower_increasing. cbn. unfold ordinal_lt. cbn. right. split; [reflexivity | lia].
    + split; [eapply set_mem_eq_r; [apply set_eq_sym; exact Hs | exact Hc] | exact Hr].
Qed.
Section Levels.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A large universe is a universe. *)
Lemma set_rule_is_univ_large : forall Γ i, set_ctx_slots Θ Ξ T γ Γ -> set_universe Θ Ξ T γ Γ (a_typ i).
Proof.
  intros Γ i HΓ. set_open. destruct HΓ as [HΓ _]. exists (fun _ => large_universe_code T i).
  constructor; [exact HΓ | apply set_denotes_typ |].
  intros ρ _. exists (tower T (ul i)). split; [apply tower_grothendieck |]. exists (large_ordinal_set i). apply set_eq_refl.
Qed.

(** A universe at a level is a universe. *)
Lemma set_rule_is_univ_small : forall Γ n L, set_ctx_slots Θ Ξ T γ Γ -> set_exp_eq Θ Ξ T γ Γ (a_level n) L L ->
    set_universe Θ Ξ T γ Γ (a_univ L).
Proof.
  intros * HΓ HL. set_open. destruct HΓ as [HΓ _]. destruct HL as (FL & FM & FM' & HL). pose proof HL as [_ HM _ _ _].
  exists (fun ρ => level_universe_code T (FM ρ)). constructor; [exact HΓ | exact (set_denotes_univ T γ _ _ _ HM) |].
  intros ρ Hρ. destruct (level_value T γ _ _ _ _ _ _ _ HL Hρ) as (o & _ & Eo).
  exists (tower T (us o)). split; [apply tower_grothendieck |]. exists (FM ρ).
  unfold level_universe_code, universe_code. apply type_code_resp; [apply set_eq_refl |].
  apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | apply small_universe_set_eq; exact Eo | tauto].
Qed.

End Levels.
