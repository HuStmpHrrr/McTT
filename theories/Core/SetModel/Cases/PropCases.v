(** * The Set Rules of Propositions

    The rules of [Prop] and its formers in the set model: [⊤], [tt], [⊥],
    [absurd], [Σₚ] and its pairs, the injections, the proof tag, their
    congruences, and proof irrelevance.  The lemmas they rest on are in
    [Judgments/Props.v]. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Import Universes Props.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

Section Rules.
  Variables (Θ : gdeps) (Ξ : gstack) (T : universe_tower) (γ : global_valuation).

(** [Prop : Type@0]. *)
Lemma set_rule_prop : forall Γ, set_exp_eq Θ Ξ T γ Γ (a_univ (a_llit (0, 0))) a_prop a_prop.
Proof.
  intros Γ. set_open.
  exists (fun _ => small_universe_code T (0, 0)), (fun _ => prop_universe_code), (fun _ => prop_universe_code).
  constructor; [apply set_denotes_univ_lit | apply set_denotes_prop | apply set_denotes_prop | intros; apply set_eq_refl |].
  intros ρ _.
  pose proof (tower_grothendieck T (us (0, 0))) as HV. apply set_mem_small_universe_code.
  - unfold prop_universe_code. apply (grothendieck_type_code _ HV); [apply (grothendieck_empty _ HV) | apply (grothendieck_prop_codes _ HV)].
  - do 3 eexists. split; [apply set_eq_refl | discriminate].
Qed.

(** [⊤ : Prop]. *)
Lemma set_rule_True : forall Γ, set_exp_eq Θ Ξ T γ Γ a_prop a_True a_True.
Proof.
  intros Γ. set_open. exists (fun _ => prop_universe_code), (fun _ => prop_code True), (fun _ => prop_code True).
  constructor; [apply set_denotes_prop | apply set_denotes_True | apply set_denotes_True | intros; apply set_eq_refl
               | intros; apply prop_code_mem_prop_universe].
Qed.

(** [⊥ : Prop]. *)
Lemma set_rule_False : forall Γ, set_exp_eq Θ Ξ T γ Γ a_prop a_False a_False.
Proof.
  intros Γ. set_open. exists (fun _ => prop_universe_code), (fun _ => prop_code False), (fun _ => prop_code False).
  constructor; [apply set_denotes_prop | apply set_denotes_False | apply set_denotes_False | intros; apply set_eq_refl
               | intros; apply prop_code_mem_prop_universe].
Qed.

(** [tt : ⊤]. *)
Lemma set_rule_tt : forall Γ, set_exp_eq Θ Ξ T γ Γ a_True a_tt a_tt.
Proof.
  intros Γ. set_open. exists (fun _ => prop_code True), (fun _ => empty_set), (fun _ => empty_set).
  constructor; [apply set_denotes_True | apply set_denotes_tt | apply set_denotes_tt | intros; apply set_eq_refl |]. intros ρ _.
  apply (proj2 (prop_true_prop_code True)). exact I.
Qed.

(** Proof irrelevance: two proofs of a proposition are equal. *)
Lemma set_rule_irrelevant : forall Γ P M M', set_exp_eq Θ Ξ T γ Γ a_prop P P ->
    set_exp_eq Θ Ξ T γ Γ P M M -> set_exp_eq Θ Ξ T γ Γ P M' M' -> set_exp_eq Θ Ξ T γ Γ P M M'.
Proof.
  intros * HPe HMe HM'e. set_open.
  destruct HPe as (FPr & FP & FP2 & [HPr HP _ _ HPm]). destruct HMe as (FPa & FM & FM2 & [HPa HM _ _ HMm]).
  destruct HM'e as (FPb & FM' & FM'2 & [HPb HM' _ _ HM'm]). exists FPa, FM, FM'.
  constructor; [exact HPa | exact HM | exact HM' | | exact HMm]. intros ρ Hρ.
  assert (HPc : forall F, set_denotes T γ Γ P F -> is_prop_code (F ρ)).
  { intros F HF. eapply is_prop_code_resp; [exact (set_denotes_agree _ _ _ _ _ _ _ HP HF Hρ) |].
    apply is_prop_code_of_prop_universe.
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HPr (set_denotes_prop T γ _) Hρ) |].
    apply HPm. exact Hρ. }
  eapply set_eq_trans; [exact (prop_code_carrier_empty _ _ (HPc _ HPa) (HMm ρ Hρ)) |].
  apply set_eq_sym. exact (prop_code_carrier_empty _ _ (HPc _ HPb) (HM'm ρ Hρ)).
Qed.

(** Ex falso: no environment has a proof of [⊥], so anything is of any
    type there. *)
Lemma set_rule_absurd_cong : forall Γ S C C' M M', set_exp_eq Θ Ξ T γ Γ S C C' ->
    set_exp_eq Θ Ξ T γ Γ a_False M M -> set_exp_eq Θ Ξ T γ Γ a_False M' M' ->
    set_exp_eq Θ Ξ T γ Γ C (a_absurd C M) (a_absurd C' M').
Proof.
  intros * HCe HMe _. set_open.
  destruct HCe as (FS & FC & FC' & [_ HC _ _ _]). destruct HMe as (FB & FM & FM2 & [HB _ _ _ HMm]).
  exists FC, (fun _ => empty_set), (fun _ => empty_set).
  assert (HA : forall C M, set_denotes T γ Γ (a_absurd C M) (fun _ => empty_set))
    by (intros; apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]).
  constructor; [exact HC | apply HA | apply HA | intros; apply set_eq_refl |].
  intros ρ Hρ. exfalso. pose proof (HMm ρ Hρ) as Hm.
  eapply set_mem_eq_r in Hm; [| apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HB (set_denotes_False T γ _) Hρ)].
  unfold prop_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code]. apply set_mem_truth in Hm. tauto.
Qed.

Lemma set_rule_absurd : forall Γ S C M, set_exp_eq Θ Ξ T γ Γ S C C ->
    set_exp_eq Θ Ξ T γ Γ a_False M M -> set_exp_eq Θ Ξ T γ Γ C (a_absurd C M) (a_absurd C M).
Proof. intros * HC HM. exact (set_rule_absurd_cong _ _ _ _ _ _ HC HM HM). Qed.

(** [Σₚ P Q : Prop]. *)
Lemma set_rule_and : forall Γ P Q, set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P :: Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P -> set_exp_eq Θ Ξ T γ (ce_ass ak_propositional P :: Γ) a_prop Q Q ->
    set_exp_eq Θ Ξ T γ Γ a_prop (a_and P Q) (a_and P Q).
Proof.
  intros * HΓ Hc HPe HQe. set_open. destruct HΓ as [HΓ _].
  destruct HPe as (FPr & FP & FP2 & [_ HP _ _ _]). destruct HQe as (FQr & FQ & FQ2 & [_ HQ _ _ _]).
  exists (fun _ => prop_universe_code), (and_denotation FP FQ), (and_denotation FP FQ).
  constructor; [apply set_denotes_prop | exact (set_denotes_and T γ Hfn Hmods _ _ _ _ _ HΓ Hc HP HQ)
               | exact (set_denotes_and T γ Hfn Hmods _ _ _ _ _ HΓ Hc HP HQ)
               | intros; apply set_eq_refl | intros; apply prop_code_mem_prop_universe].
Qed.

(** [Σₚ P Q ≈ Σₚ P' Q']: the right one is read in its own context, which
    the identity converts from the left's. *)
Lemma set_rule_and_cong : forall Γ P P' Q Q', set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P :: Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P' :: Γ ->
    Θ ⍮ Ξ ⍮ ce_ass ak_propositional P' :: Γ ⊢ˢ sb_id : ce_ass ak_propositional P :: Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P' -> set_exp_eq Θ Ξ T γ (ce_ass ak_propositional P :: Γ) a_prop Q Q' ->
    set_exp_eq Θ Ξ T γ Γ a_prop (a_and P Q) (a_and P' Q').
Proof.
  intros * HΓ Hc Hc' Hid HPe HQe. set_open. destruct HΓ as [HΓ _].
  destruct HPe as (FPr & FP & FP' & [_ HP HP' EP _]). destruct HQe as (FQr & FQ & FQ' & [_ HQ HQ' EQ _]).
  assert (Hin : forall ρ x, set_env_in T γ Γ ρ -> set_mem x (code_carrier (FP' ρ)) ->
            set_env_in T γ (ce_ass ak_propositional P :: Γ) (set_env_extend ρ (set_entry_term ak_propositional x))).
  { intros ρ x Hρ Hx. apply (set_env_in_extend_ass T γ Γ ρ _ P (FP ρ) x Hρ (set_denotes_exists _ _ _ _ _ HP _ Hρ)).
    eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; apply EP; exact Hρ | exact Hx]. }
  exists (fun _ => prop_universe_code), (and_denotation FP FQ), (and_denotation FP' FQ').
  constructor; [apply set_denotes_prop | exact (set_denotes_and T γ Hfn Hmods _ _ _ _ _ HΓ Hc HP HQ) | | |
               intros; apply prop_code_mem_prop_universe].
  - apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
    apply (set_interp_and T γ Γ ρ P' Q' (FP' ρ) (fun x => FQ' (set_env_extend ρ (set_entry_term ak_propositional x))));
      [exact Hc' | exact (set_denotes_exists _ _ _ _ _ HP' _ Hρ) |].
    intros x Hx. apply (set_interp_ctx_conv _ _ _ _ _ _ _ Hc Hid). apply (set_denotes_exists _ _ _ _ _ HQ'). apply Hin; assumption.
  - intros ρ Hρ. unfold and_denotation. apply prop_code_eq.
    assert (Ep : set_eq (FP ρ) (FP' ρ)) by (apply EP; exact Hρ).
    assert (Eq : prop_true (FP ρ) -> set_eq (FQ (set_env_extend ρ (set_entry_term ak_propositional empty_set)))
                                            (FQ' (set_env_extend ρ (set_entry_term ak_propositional empty_set))))
      by (intros Hp; apply EQ; apply Hin; [exact Hρ | exact (prop_true_resp _ _ Ep Hp)]).
    split; intros [Hp Hq]; split.
    + exact (prop_true_resp _ _ Ep Hp).
    + exact (prop_true_resp _ _ (Eq Hp) Hq).
    + exact (prop_true_resp _ _ (set_eq_sym _ _ Ep) Hp).
    + exact (prop_true_resp _ _ (set_eq_sym _ _ (Eq (prop_true_resp _ _ (set_eq_sym _ _ Ep) Hp))) Hq).
Qed.

(** The proof of a conjunction from proofs of its components. *)
Lemma set_rule_conj : forall Γ P Q M N, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_ass ak_propositional P :: Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P -> set_exp_eq Θ Ξ T γ (ce_ass ak_propositional P :: Γ) a_prop Q Q ->
    set_exp_eq Θ Ξ T γ Γ P M M -> set_exp_eq Θ Ξ T γ Γ (exp_sub Q (sb_extend sb_id (se_exp M))) N N ->
    set_exp_eq Θ Ξ T γ Γ (a_and P Q) (a_conj P Q M N) (a_conj P Q M N).
Proof.
  intros * HΓ Hc Hσ HPe HQe HMe HNe. set_open. destruct HΓ as [HΓ _].
  destruct HPe as (FPr & FP & FP2 & HPe). destruct HQe as (FQr & FQ & FQ2 & HQe).
  destruct HMe as (FPa & FM & FM2 & [HPa HM _ _ HMm]). destruct HNe as (FQM & FN & FN2 & [HQM _ _ _ HNm]).
  pose proof HPe as [_ HP _ _ _]. pose proof HQe as [_ HQ _ _ _].
  assert (HA : set_denotes T γ Γ (a_conj P Q M N) (fun _ => empty_set))
    by (apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]).
  exists (and_denotation FP FQ), (fun _ => empty_set), (fun _ => empty_set).
  constructor; [exact (set_denotes_and T γ Hfn Hmods _ _ _ _ _ HΓ Hc HP HQ) | exact HA | exact HA | intros; apply set_eq_refl |].
  intros ρ Hρ. pose proof (set_prop_is_prop_code T γ _ _ _ _ _ _ HPe Hρ) as HPc.
  assert (Hm : set_mem (FM ρ) (code_carrier (FP ρ)))
    by (eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HPa HP Hρ) | apply HMm; exact Hρ]).
  apply (proj2 (prop_true_prop_code _)). split; [exact (prop_true_of_mem _ _ HPc Hm) |].
  pose proof (set_prop_at_proof T γ _ _ _ _ _ _ _ _ _ Hc Hσ HP HQ HM HQM Hρ HPc Hm) as E.
  assert (HQc : is_prop_code (FQ (set_env_extend ρ (set_entry_term ak_propositional empty_set)))).
  { apply (set_prop_is_prop_code T γ _ _ _ _ _ _ HQe). apply (set_env_in_extend_ass T γ Γ ρ _ P (FP ρ)); [exact Hρ | exact (set_denotes_exists _ _ _ _ _ HP _ Hρ) |].
    exact (prop_true_of_mem _ _ HPc Hm). }
  eapply prop_true_of_mem; [exact HQc |]. eapply set_mem_eq_r; [apply code_carrier_resp; exact E | apply HNm; exact Hρ].
Qed.

(** The proof of a conjunction's first component. *)
Lemma set_rule_left : forall Γ P Q M, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P :: Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P -> set_exp_eq Θ Ξ T γ (ce_ass ak_propositional P :: Γ) a_prop Q Q ->
    set_exp_eq Θ Ξ T γ Γ (a_and P Q) M M -> set_exp_eq Θ Ξ T γ Γ P (a_left M) (a_left M).
Proof.
  intros * HΓ Hc HPe HQe HMe. set_open. destruct HΓ as [HΓ _].
  destruct HPe as (FPr & FP & FP2 & [_ HP _ _ _]). destruct HQe as (FQr & FQ & FQ2 & [_ HQ _ _ _]).
  destruct HMe as (FS & FM & FM2 & [HS _ _ _ HMm]).
  assert (HA : set_denotes T γ Γ (a_left M) (fun _ => empty_set))
    by (apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]).
  exists FP, (fun _ => empty_set), (fun _ => empty_set).
  constructor; [exact HP | exact HA | exact HA | intros; apply set_eq_refl |].
  intros ρ Hρ. exact (proj1 (and_denotation_true T γ Hfn Hmods _ _ _ _ _ _ _ _ HΓ Hc HP HQ HS Hρ (HMm ρ Hρ))).
Qed.

(** The proof of the second component, at the first. *)
Lemma set_rule_right : forall Γ P Q M, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass ak_propositional P :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp (a_left M)) : ce_ass ak_propositional P :: Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P -> set_exp_eq Θ Ξ T γ (ce_ass ak_propositional P :: Γ) a_prop Q Q ->
    set_exp_eq Θ Ξ T γ Γ (a_and P Q) M M ->
    set_exp_eq Θ Ξ T γ Γ a_prop (exp_sub Q (sb_extend sb_id (se_exp (a_left M)))) (exp_sub Q (sb_extend sb_id (se_exp (a_left M)))) ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub Q (sb_extend sb_id (se_exp (a_left M)))) (a_right M) (a_right M).
Proof.
  intros * HΓ Hc Hσ HPe HQe HMe HQLe. set_open. destruct HΓ as [HΓ _].
  destruct HPe as (FPr & FP & FP2 & HPe). destruct HQe as (FQr & FQ & FQ2 & [_ HQ _ _ _]).
  destruct HMe as (FS & FM & FM2 & [HS _ _ _ HMm]). destruct HQLe as (FQLr & FQL & FQL2 & [_ HQL _ _ _]).
  pose proof HPe as [_ HP _ _ _].
  assert (HL : set_denotes T γ Γ (a_left M) (fun _ => empty_set))
    by (apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]).
  assert (HA : set_denotes T γ Γ (a_right M) (fun _ => empty_set))
    by (apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]).
  exists FQL, (fun _ => empty_set), (fun _ => empty_set).
  constructor; [exact HQL | exact HA | exact HA | intros; apply set_eq_refl |].
  intros ρ Hρ. destruct (and_denotation_true T γ Hfn Hmods _ _ _ _ _ _ _ _ HΓ Hc HP HQ HS Hρ (HMm ρ Hρ)) as [Hp Hq].
  pose proof (set_prop_is_prop_code T γ _ _ _ _ _ _ HPe Hρ) as HPc.
  pose proof (set_prop_at_proof T γ _ _ _ _ _ _ (fun _ => empty_set) _ _ Hc Hσ HP HQ HL HQL Hρ HPc Hp) as E.
  eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact E | exact Hq].
Qed.

(** A tagged proof: the proof. *)
Lemma set_rule_proof_tag : forall Γ P M, set_ctx_slots Θ Ξ T γ Γ ->
    set_exp_eq Θ Ξ T γ Γ a_prop P P -> set_exp_eq Θ Ξ T γ Γ P M M ->
    set_exp_eq Θ Ξ T γ Γ P (a_proof P M) (a_proof P M).
Proof.
  intros * HΓ _ HMe. set_open. destruct HΓ as [HΓ _]. destruct HMe as (FPa & FM & FM2 & [HPa HM _ _ HMm]).
  assert (HA : set_denotes T γ Γ (a_proof P M) FM).
  { apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
    constructor. exact (set_denotes_exists _ _ _ _ _ HM _ Hρ). }
  exists FPa, FM, FM. constructor; [exact HPa | exact HA | exact HA | intros; apply set_eq_refl | exact HMm].
Qed.

End Rules.
