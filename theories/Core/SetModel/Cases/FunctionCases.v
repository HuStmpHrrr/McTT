(** * The Set Rules of Functions

    The rules of [Π] in the set model: the type former, [λ], application,
    their congruences, [β] and [η].  The lemmas they rest on are in
    [Judgments/Functions.v]. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Import Props Functions.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Functions.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** The [Π] formation rule, into the sort of the codomain's kind over a
    universe. *)
Lemma set_rule_pi : forall Γ κd κc A B U, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> pi_kinds κd κc -> set_universe Θ Ξ T γ Γ U ->
    set_exp_eq Θ Ξ T γ Γ (abs_kind_sort κd U) A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (exp_wk (abs_kind_sort κc U) wk_shift) B B ->
    set_exp_eq Θ Ξ T γ Γ (abs_kind_sort κc U) (a_pi κd κc A B) (a_pi κd κc A B).
Proof.
  intros * HΓ Hc Hk HUe HAe HBe. set_open. destruct HΓ as [HΓ _]. destruct HUe as (FU & [_ HU Hshape]).
  destruct HAe as (FS & FA & FA2 & [HS HA _ _ HAm]). destruct HBe as (FS' & FB & FB2 & [HS' HB _ _ HBm]).
  exists (kind_sort_value T κc FU), (pi_denotation κd κc FA FB), (pi_denotation κd κc FA FB).
  constructor; [apply set_denotes_kind_sort; exact HU | apply set_denotes_pi; assumption .. | intros; apply set_eq_refl |].
  intros ρ Hρ. destruct (Hshape ρ Hρ) as [V HV].
  assert (HAk : set_mem (FA ρ) (code_carrier (kind_sort_value T κd FU ρ)))
    by (eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_kind_sort T γ _ _ _ _ HU) Hρ)
                             | apply HAm; exact Hρ]).
  assert (HBk : forall x, set_mem x (code_carrier (FA ρ)) ->
            set_mem (body_function κd FB ρ x) (code_carrier (kind_sort_value T κc FU ρ))).
  { intros x Hx. unfold body_function. eapply set_mem_eq_r; [apply code_carrier_resp; exact (kind_sort_value_shift T γ _ _ _ _ _ _ _ _ _ _ HΓ Hc HU HA HS' Hρ Hx) |].
    apply HBm. exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ (set_denotes_exists _ _ _ _ _ HA _ Hρ) Hx). }
  pose proof (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HB Hρ) as HFr.
  destruct κc; cbn [pi_denotation kind_sort_value] in HBk |- *.
  - destruct HV as [HV [l El]]. eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact El |].
    unfold universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply set_mem_separation; [exact is_relevant_code_resp |]. split; [| apply pi_code_relevant].
    apply grothendieck_pi_code; [exact HV | exact (kind_sort_value_mem T _ _ _ _ _ (conj HV (ex_intro _ l El)) HAk) | exact HFr |].
    intros x Hx. exact (kind_sort_value_mem T ak_relevant _ _ _ _ (conj HV (ex_intro _ l El)) (HBk x Hx)).
  - apply prop_code_mem_prop_universe.
  - inversion Hk; subst. cbn [kind_sort_value] in HAk.
    unfold level_sort_code in HAk |- *. eapply set_mem_eq_r in HAk; [| apply code_carrier_type_code].
    apply set_mem_separation in HAk as [_ HAl]; [| exact is_level_type_code_resp].
    assert (HBl : forall x, set_mem x (code_carrier (FA ρ)) -> is_level_type_code (body_function ak_level FB ρ x)).
    { intros x Hx. pose proof (HBk x Hx) as H. unfold level_sort_code in H. eapply set_mem_eq_r in H; [| apply code_carrier_type_code].
      apply set_mem_separation in H as [_ H]; [exact H | exact is_level_type_code_resp]. }
    assert (Hpl : is_level_type_code (pi_code (FA ρ) (body_function ak_level FB ρ))).
    { apply (is_level_type_code_pi _ (FA ρ) (restrict_fun (code_carrier (FA ρ)) (body_function ak_level FB ρ)));
        [apply restrict_fun_resp | | exact HAl |].
      - apply pi_code_resp_on; [apply set_eq_refl |]. intros x x' Hx E.
        eapply set_eq_trans; [apply HFr; [exact Hx | exact E] |]. apply set_eq_sym. apply restrict_fun_agree; [exact HFr |].
        eapply set_mem_eq_l; [exact E | exact Hx].
      - intros x Hx. eapply is_level_type_code_resp; [apply set_eq_sym; apply restrict_fun_agree; [exact HFr | exact Hx] |].
        apply HBl. exact Hx. }
    eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply set_mem_separation; [exact is_level_type_code_resp |]. split; [| exact Hpl].
    apply set_mem_union. exists (tower T (us (0, 0))). split; [exists (0, 0); apply set_eq_refl |].
    apply is_level_type_code_mem; [apply tower_grothendieck | exact Hpl].
Qed.

(** [Π A B ≈ Π A' B'], into the sort of the codomain's kind over a
    universe. *)
Lemma set_rule_pi_cong : forall Γ κd κc A A' B B' U, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ->
    Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ⊢ˢ sb_id : ce_ass κd A :: Γ -> pi_kinds κd κc -> set_universe Θ Ξ T γ Γ U ->
    set_exp_eq Θ Ξ T γ Γ (abs_kind_sort κd U) A A' ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (exp_wk (abs_kind_sort κc U) wk_shift) B B' ->
    set_exp_eq Θ Ξ T γ Γ (abs_kind_sort κc U) (a_pi κd κc A B) (a_pi κd κc A' B').
Proof.
  intros * HΓ Hc Hc' Hσ Hk HUe HAe HBe.
  pose proof (set_rule_pi _ _ _ _ _ _ HΓ Hc Hk HUe (set_exp_eq_left_refl _ _ _ _ _ _ _ _ HAe)
                (set_exp_eq_left_refl _ _ _ _ _ _ _ _ HBe)) as Hpi.
  set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS & FA & FA' & [HS HA HA' EA HAm]). destruct HBe as (FS' & FB & FB' & [HS' HB HB' EB HBm]).
  destruct Hpi as (FK & FL & _ & [HK HL _ _ HLm]).
  pose proof (set_denotes_ctx_conv_ass T γ _ _ _ _ _ _ _ _ Hfn Hmods HΓ Hc Hσ HA HA' EA HB') as HB''.
  exists FK, FL, (pi_denotation κd κc FA' FB'). constructor; [exact HK | exact HL | apply set_denotes_pi; assumption | | exact HLm].
  - intros ρ Hρ. eapply set_eq_trans; [exact (set_denotes_agree _ _ _ _ _ _ _ HL (set_denotes_pi T γ _ _ κc _ _ _ _ HΓ Hc HA HB) Hρ) |].
    pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    assert (Hacross : respects_across (code_carrier (FA ρ)) (body_function κd FB ρ) (body_function κd FB' ρ)).
    { intros x x' Hx E. unfold body_function.
      eapply set_eq_trans; [exact (EB _ (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx)) |].
      exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HB' Hρ _ _ Hx E). }
    destruct κc; cbn [pi_denotation];
      first [apply pi_code_resp_on | apply forall_code_resp_on]; first [exact (EA ρ Hρ) | exact Hacross].
Qed.

(** The λ rule: [λ A M : Π{κd,κc} A B]. *)
Lemma set_rule_fn : forall Γ κd κc i Srt A M B, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ ->
    set_exp_eq Θ Ξ T γ Γ Srt A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) B M M ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) (a_fn A M) (a_fn A M).
Proof.
  intros * HΓ HT Hc HAe HBe HMe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS & FA & FA2 & [_ HA _ _ _]). destruct HBe as (FS1 & FB & FB2 & HBe). destruct HMe as (FB' & FM & FM2 & HMe).
  pose proof HBe as [_ HB _ _ _]. pose proof HMe as [_ HM _ _ _].
  exists (pi_denotation κd κc FA FB), (fn_denotation κd κc FA FM), (fn_denotation κd κc FA FM).
  constructor; [apply set_denotes_pi; assumption | eapply set_denotes_fn; eassumption .. | intros; apply set_eq_refl
               | exact (set_fn_value_mem T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ HA HBe HMe)].
Qed.

(** [λ A M ≈ λ A' M']. *)
Lemma set_rule_fn_cong : forall Γ κd κc i A A' M M' B C' B' Srt, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B -> Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A' M' : a_pi κd κc C' B' ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ->
    Θ ⍮ Ξ ⍮ ce_ass κd A' :: Γ ⊢ˢ sb_id : ce_ass κd A :: Γ ->
    set_exp_eq Θ Ξ T γ Γ Srt A A' ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) B M M' ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) (a_fn A M) (a_fn A' M').
Proof.
  intros * HΓ HT HT' Hc Hc' Hσ HAe HBe HMe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS & FA & FA' & [HS HA HA' EA _]). destruct HBe as (FS2 & FB & FB2 & HB).
  destruct HMe as (FB3 & FM & FM' & [HB3 HM HM' EM HMm]).
  pose proof HB as [_ HBd _ _ _].
  pose proof (set_fn_value_mem T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ HA HB
                (Build_set_exp_eq_with _ _ _ _ _ _ _ _ _ HB3 HM HM (fun _ _ => set_eq_refl _) HMm)) as Hm.
  pose proof (set_denotes_pi T γ _ _ κc _ _ _ _ HΓ Hc HA HBd) as HP.
  pose proof (set_denotes_fn T γ _ _ _ _ _ _ _ _ _ Hfn HΓ HT Hc HA HM) as HL.
  pose proof (set_denotes_ctx_conv_ass T γ _ _ _ _ _ _ _ _ Hfn Hmods HΓ Hc Hσ HA HA' EA HM') as HM''.
  exists (pi_denotation κd κc FA FB), (fn_denotation κd κc FA FM), (fn_denotation κd κc FA' FM').
  constructor; [exact HP | exact HL | eapply set_denotes_fn; eassumption | | exact Hm].
  intros ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
  destruct κc; cbn [fn_denotation]; [| apply set_eq_refl |];
    (apply graph_set_resp_on; [apply code_carrier_resp; exact (EA ρ Hρ) |]; intros x x' Hx E; unfold body_function;
     eapply set_eq_trans; [exact (EM _ (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx)) |];
     exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HM' Hρ _ _ Hx E)).
Qed.

(** [M ≈ λ A (M[↑] #0) : Π A B]. *)
Lemma set_rule_fn_eta : forall Γ κd κc i Srt A B M, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A (a_app (exp_wk M wk_shift) (a_var 0)) : a_pi κd κc A B ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> set_exp_eq Θ Ξ T γ Γ Srt A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) M M ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) M (a_fn A (a_app (exp_wk M wk_shift) (a_var 0))).
Proof.
  intros * HΓ HT Hc HAe HBe HMe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS0 & FA & FA2 & [_ HA _ _ _]). destruct HBe as (FS & FB & FB2 & [HS HB _ _ HBm]).
  destruct HMe as (FP & FM & FM2 & [HP HM _ _ HMm]).
  set (Fb := fun ρ' => set_apply (FM (set_env_tail ρ')) (set_entry_value (ρ' 0))).
  assert (Hb : set_denotes T γ (ce_ass κd A :: Γ) (a_app (exp_wk M wk_shift) (a_var 0)) Fb).
  { apply set_denotes_of_exists; [exact Hfn | exact Hmods | split; [exact HΓ | exists FA; exact HA] |].
    intros ρ' [Ht _]. constructor; [| constructor].
    exact (set_interp_wk T γ _ _ _ _ (set_denotes_exists _ _ _ _ _ HM _ Ht) nil Γ _ wk_shift _ eq_refl (wf_wk_shift _ _ _ _ Hc)
             (fun y => eq_refl)). }
  exists FP, FM, (fn_denotation κd κc FA Fb).
  constructor; [exact HP | exact HM | eapply set_denotes_fn; eassumption | | exact HMm].
  intros ρ Hρ. pose proof (HMm ρ Hρ) as Hm.
  eapply set_mem_eq_r in Hm; [| apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HP (set_denotes_pi T γ _ _ κc _ _ _ _ HΓ Hc HA HB) Hρ)].
  destruct κc; cbn [pi_denotation fn_denotation] in Hm |- *.
  - unfold pi_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    eapply set_eq_trans; [eapply function_set_graph_on; [| exact Hm] | apply set_eq_refl].
    intros x y Hx E. apply code_carrier_resp. exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hx E).
  - unfold forall_code, prop_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    apply set_mem_truth in Hm as [_ Hm]. exact Hm.
  - unfold pi_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    eapply set_eq_trans; [eapply function_set_graph_on; [| exact Hm] | apply set_eq_refl].
    intros x y Hx E. apply code_carrier_resp. exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hx E).
Qed.

(** [(λ A M) N ≈ M[N] : B[N]]. *)
Lemma set_rule_pi_beta : forall Γ κd κc i Srt A M B N, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B -> ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κd A :: Γ ->
    set_exp_eq Θ Ξ T γ Γ Srt A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) B M M ->
    set_exp_eq Θ Ξ T γ Γ A N N ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub B (sb_extend sb_id (se_exp N))) (a_app (a_fn A M) N) (exp_sub M (sb_extend sb_id (se_exp N))).
Proof.
  intros * HΓ HT Hc Hσ HAe HBe HMe HNe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS0 & FA & FA2 & [_ HA _ _ _]). destruct HBe as (FS & FB & FB2 & [HS HB _ _ HBm]).
  destruct HMe as (FB' & FM & FM2 & [HB' HM _ _ HMm]). destruct HNe as (FA' & FN & FN2 & [HA' HN _ _ HNm]).
  assert (HNa : forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA ρ)))
    by (intros ρ Hρ; eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA' HA Hρ) | apply HNm; exact Hρ]).
  exists (fun ρ => body_function κd FB ρ (FN ρ)), (fun ρ => set_apply (fn_denotation κd κc FA FM ρ) (FN ρ)),
    (fun ρ => body_function κd FM ρ (FN ρ)).
  assert (Hx : forall ρ, set_env_in T γ Γ ρ -> set_env_in T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd (FN ρ))))
    by (intros ρ Hρ; exact (set_env_in_extend_ass T γ Γ ρ κd A _ _ Hρ (set_denotes_exists _ _ _ _ _ HA _ Hρ) (HNa ρ Hρ))).
  assert (Heq : forall ρ, set_env_in T γ Γ ρ -> set_eq (set_apply (fn_denotation κd κc FA FM ρ) (FN ρ)) (body_function κd FM ρ (FN ρ))).
  { intros ρ Hρ. destruct κc; cbn [fn_denotation].
    - apply set_apply_graph_on; [exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact (HNa ρ Hρ)].
    - eapply set_eq_trans; [apply set_apply_empty |]. apply set_eq_sym.
      assert (HP : is_prop_code (FB' (set_env_extend ρ (set_entry_term κd (FN ρ))))).
      { apply is_prop_code_of_prop_universe. cbn [abs_kind_sort] in HS.
        eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_prop T γ _) (Hx ρ Hρ)) |].
        eapply set_mem_eq_l; [exact (set_denotes_agree _ _ _ _ _ _ _ HB HB' (Hx ρ Hρ)) |]. apply HBm. exact (Hx ρ Hρ). }
      exact (prop_code_carrier_empty _ _ HP (HMm _ (Hx ρ Hρ))).
    - apply set_apply_graph_on; [exact (body_function_respects T γ _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact (HNa ρ Hρ)]. }
  constructor.
  - apply (set_denotes_single_sub T γ Γ κd A N _ FA); assumption.
  - apply set_denotes_app; [eapply set_denotes_fn; eassumption | exact HN].
  - apply (set_denotes_single_sub T γ Γ κd A N _ FA); assumption.
  - exact Heq.
  - intros ρ Hρ. eapply set_mem_eq_l; [apply set_eq_sym; exact (Heq ρ Hρ) |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HB' HB (Hx ρ Hρ)) |].
    apply HMm. exact (Hx ρ Hρ).
Qed.

(** The application rule: [M N : B[N]]. *)
Lemma set_rule_app : forall Γ κd κc i Srt A B M N, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κd A :: Γ ->
    set_exp_eq Θ Ξ T γ Γ Srt A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) M M -> set_exp_eq Θ Ξ T γ Γ A N N ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub B (sb_extend sb_id (se_exp N))) (a_app M N) (a_app M N).
Proof.
  intros * HΓ Hc Hσ HAe HBe HMe HNe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS0 & FA & FA2 & [_ HA _ _ _]). destruct HBe as (FS & FB & FB2 & HBe).
  destruct HMe as (FP & FM & FM2 & HMe). destruct HNe as (FA' & FN & FN2 & HNe).
  pose proof HBe as [_ HB _ _ _]. pose proof HNe as [HA' HN _ _ HNm].
  assert (HNa : forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA ρ)))
    by (intros ρ Hρ; eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA' HA Hρ) | apply HNm; exact Hρ]).
  pose proof HMe as [_ HM _ _ _].
  exists (fun ρ => body_function κd FB ρ (FN ρ)), (fun ρ => set_apply (FM ρ) (FN ρ)), (fun ρ => set_apply (FM ρ) (FN ρ)).
  constructor; [exact (set_denotes_single_sub T γ _ _ _ _ _ _ _ _ Hfn Hmods HΓ Hc Hσ HA HN HNa HB)
               | apply set_denotes_app; assumption .. | intros; apply set_eq_refl
               | exact (set_apply_value_mem T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ Hc HA HBe HMe HNe)].
Qed.

(** [M ≈ M'] and [N ≈ N'] give [M N ≈ M' N' : B[N]]. *)
Lemma set_rule_app_cong : forall Γ κd κc i Srt A B M M' N N', set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_ass κd A :: Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κd A :: Γ ->
    set_exp_eq Θ Ξ T γ Γ Srt A A ->
    set_exp_eq Θ Ξ T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B ->
    set_exp_eq Θ Ξ T γ Γ (a_pi κd κc A B) M M' -> set_exp_eq Θ Ξ T γ Γ A N N' ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub B (sb_extend sb_id (se_exp N))) (a_app M N) (a_app M' N').
Proof.
  intros * HΓ Hc Hσ HAe HBe HMe HNe. set_open. destruct HΓ as [HΓ _].
  destruct HAe as (FS0 & FA & FA2 & [_ HA _ _ _]). destruct HBe as (FS & FB & FB2 & HBe).
  destruct HMe as (FP & FM & FM' & HMe). destruct HNe as (FA' & FN & FN' & HNe).
  pose proof HBe as [_ HB _ _ _]. pose proof HNe as [HA' HN _ _ HNm].
  assert (HNa : forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA ρ)))
    by (intros ρ Hρ; eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA' HA Hρ) | apply HNm; exact Hρ]).
  pose proof HMe as [_ HM HM' EM _]. pose proof HNe as [_ _ HN' EN _].
  exists (fun ρ => body_function κd FB ρ (FN ρ)), (fun ρ => set_apply (FM ρ) (FN ρ)), (fun ρ => set_apply (FM' ρ) (FN' ρ)).
  constructor; [exact (set_denotes_single_sub T γ _ _ _ _ _ _ _ _ Hfn Hmods HΓ Hc Hσ HA HN HNa HB)
               | apply set_denotes_app; assumption .. | intros ρ Hρ; apply set_apply_resp; [exact (EM ρ Hρ) | exact (EN ρ Hρ)]
               | exact (set_apply_value_mem T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ Hc HA HBe HMe HNe)].
Qed.

End Functions.
