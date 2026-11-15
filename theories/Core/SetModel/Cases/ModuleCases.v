(** * The Set Rules of Module Expressions

    The rules of [⊢ᵐ] and of members in the set model.  The lemmas they
    rest on are in [Modules/ModuleLemmas.v] and [Modules/Sel.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution.
From Mctt.Core.SetModel.Modules Require Import ValidUnit MemberTypes ModuleLemmas Unit Canon App Sel.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Mem App.
From Mctt.Core.Completeness.Modules Require Sel.
Import ListNotations.

Section ModuleCases.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_me_var : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    set_modexp_eq Θ Ξ T γ Γ (me_var x) (me_var x).
Proof.
  intros * Hl HΓ Hc. set_open. destruct HΓ as [HC Hsl]. destruct (set_valid_modexp_var T γ Hfn Hmods Hgw _ _ _ Hl HC Hsl Hc) as [Hv _].
  exact (set_modexp_eq_of_rel T γ _ _ _ (set_modexp_rel_refl_left T γ _ _ _ (set_slot_rel T γ Hfn Hmods _ _ _ Hl HC Hc)) Hv Hv
           (fun _ _ _ _ => eq_refl)).
Qed.

Lemma set_rule_me_delta_slot : forall Γ x U, Γ ∋ #x ≔ₘ U -> set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    set_modexp_eq Θ Ξ T γ Γ (me_var x) (me_lit U).
Proof.
  intros * Hl HΓ Hc. set_open. destruct HΓ as [HC Hsl]. destruct (set_valid_modexp_var T γ Hfn Hmods Hgw _ _ _ Hl HC Hsl Hc) as [Hv HK].
  exact (set_modexp_eq_of_rel T γ _ _ _ (set_slot_rel T γ Hfn Hmods _ _ _ Hl HC Hc) Hv (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK)
           (fun κs Hκ ys z => set_slots_coherent_lookup γ _ _ _ Hl _ Hκ ys z)).
Qed.

Lemma set_rule_me_unit : forall Γ fp TΦ, ⊢ Θ ⍮ Ξ ⍮ Γ -> set_ctx_slots Θ Ξ T γ Γ -> gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
    set_modexp_eq Θ Ξ T γ Γ (me_unit fp) (me_unit fp).
Proof.
  intros * Hc HΓ Hu. set_open. destruct HΓ as [HC _]. destruct TΦ as [T0 Φs]. destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hls).
  destruct (gc_loc_grow _ _ _ _ Hgw (set_source_sub T γ Θ Ξ Hμ) _ _ _
              (gc_loc_of_loc _ _ (set_source_wf T γ Θ Ξ Hμ) _ _ _ Hls)) as (Φ0 & _ & _ & Hl).
  pose proof (mod_qname_inv _ _ Hq) as Heq. rewrite Heq.
  assert (HK : set_valid_unit T γ Γ (me_apps (qname_mod mp) nil)).
  { apply (set_valid_unit_filed T γ Γ mp T0 Φ0 T0 nil nil); [exact (loc_modexp_wf _ _ _ Hc _ _ _ Hl) | exact (gc_loc_of_loc _ _ Hgw _ _ _ Hl)
                                                            | exact HC |].
    constructor; [rewrite List.app_nil_r; reflexivity | reflexivity | constructor | exact I
                 | intros [| k] N A HN; discriminate | intros [| k] A HA; discriminate]. }
  pose proof (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as Hv.
  exact (set_modexp_eq_of_rel T γ _ _ _ (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) Hv Hv (fun _ _ _ _ => eq_refl)).
Qed.

Lemma set_rule_me_sym : forall Γ H H', set_modexp_eq Θ Ξ T γ Γ H H' -> set_modexp_eq Θ Ξ T γ Γ H' H.
Proof.
  intros * HH. set_open. destruct HH as (F & F' & [HF HF' E Hv Hv' Hpr]).
  exists F', F. constructor; [exact HF' | exact HF | | exact Hv' | exact Hv |].
  - intros ρ Hρ. apply set_module_eq_sym. exact (E _ Hρ).
  - intros κs Hκ ys x. exact (eq_sym (Hpr κs Hκ ys x)).
Qed.

Lemma set_rule_me_trans : forall Γ H H' H'', set_modexp_eq Θ Ξ T γ Γ H H' -> set_modexp_eq Θ Ξ T γ Γ H' H'' ->
    set_modexp_eq Θ Ξ T γ Γ H H''.
Proof.
  intros * H1 H2. set_open. destruct H1 as (F & F' & [HF HF' E Hv _ Hpr]). destruct H2 as (G & G' & [HG HG' E' _ Hv'' Hpr']).
  exists F, G'.
  constructor; [exact HF | exact HG' | | exact Hv | exact Hv'' |].
  - intros ρ Hρ. eapply set_module_eq_trans; [exact (E _ Hρ) |]. eapply set_module_eq_trans; [| exact (E' _ Hρ)].
    exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
  - intros κs Hκ ys x. exact (eq_trans (Hpr κs Hκ ys x) (Hpr' κs Hκ ys x)).
Qed.

Lemma set_rule_me_lit : forall Γ U U', set_unit_eq Θ Ξ T γ Γ U U' -> set_modexp_eq Θ Ξ T γ Γ (me_lit U) (me_lit U').
Proof.
  intros * HU0. set_open. destruct HU0 as (F & F' & [HF HF' E HU HU' Hpr]). exists F, F'.
  constructor; [exact HF | exact HF' | exact E | exact (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HU)
               | exact (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HU') | exact Hpr].
Qed.

(** An alias of no parameter is its target. *)
Lemma set_rule_me_beta_alias0 : forall Γ E, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ me_lit (gu_mk nil (md_alias E)) ->
    set_modexp_eq Θ Ξ T γ Γ E E -> set_modexp_eq Θ Ξ T γ Γ (me_lit (gu_mk nil (md_alias E))) E.
Proof.
  intros * HΓ Hw HEe. set_open. destruct HΓ as [HΓ _]. destruct HEe as (FE & FE' & [HFE HFE' EE HvE _]).
  assert (HEE : set_modexp_rel T γ Γ E E).
  { exists FE, FE. constructor; [exact HFE | exact HFE |].
    intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HFE _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HFE _ Hρ)). }
  pose proof (set_alias0_rel T γ Hfn Hmods _ _ HΓ HEE) as HrelE.
  pose proof (set_modexp_rel_refl_left T γ _ _ _ HrelE) as Hrel.
  assert (HK : set_valid_unit T γ Γ (me_lit (gu_mk nil (md_alias E)))).
  { apply set_valid_unit_alias; [constructor | exact HvE].
    - exact Hw.
    - constructor.
    - exists 0. apply set_params_evaluated_nil.
    - exact HΓ.
    - exact HΓ.
    - exact Hrel.
    - exact HEE. }
  exact (set_modexp_eq_of_rel T γ _ _ _ HrelE (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) HvE (fun _ _ _ _ => eq_refl)).
Qed.

(** A term member of a valid module expression is of its type. *)
Lemma set_rule_mem : forall Γ H x R1 A, set_ctx_slots Θ Ξ T γ Γ -> set_modexp_eq Θ Ξ T γ Γ H H ->
    mdenote Θ Ξ Γ (me_mem H x) R1 -> mdesc_type R1 = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A ->
    set_exp_eq Θ Ξ T γ Γ A (a_mem H x) (a_mem H x).
Proof.
  intros * HΓ HH Hm1 Ht1 HT. set_open. destruct HΓ as [HΓ _]. destruct HH as (F & F' & [HF _ _ Hv _]).
  destruct (set_member_here T γ Hgw Θ Ξ Hμ _ _ _ _ _ Hm1 Ht1) as (R & Hm & Ht & _ & Hkn).
  destruct (proj1 (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ Hv _ _ _ Hkn Hm Ht)) as (FA & HA).
  assert (HM : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) | exact HT ]. }
  exists FA, (fun ρ => select_term γ (F ρ) x), (fun ρ => select_term γ (F ρ) x).
  constructor; [exact HA | exact HM | exact HM | intros; apply set_eq_refl |].
  intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ Hv HF _ _ _ _ Hkn Hm Ht HA _ Hρ)).
Qed.

(** Members of equal module expressions are equal. *)
Lemma set_rule_mem_cong : forall Γ H H' x R1 A, set_ctx_slots Θ Ξ T γ Γ -> set_modexp_eq Θ Ξ T γ Γ H H' ->
    mdenote Θ Ξ Γ (me_mem H x) R1 -> mdesc_type R1 = Some A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H' x : A ->
    set_exp_eq Θ Ξ T γ Γ A (a_mem H x) (a_mem H' x).
Proof.
  intros * HΓ HH Hm1 Ht1 HT HT'. set_open. destruct HΓ as [HΓ _]. destruct HH as (F & F' & [HF HF' E Hv _]).
  destruct (set_member_here T γ Hgw Θ Ξ Hμ _ _ _ _ _ Hm1 Ht1) as (R & Hm & Ht & _ & Hkn).
  destruct (proj1 (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ Hv _ _ _ Hkn Hm Ht)) as (FA & HA).
  assert (HM : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) | exact HT ]. }
  assert (HM' : set_denotes T γ Γ (a_mem H' x) (fun ρ => select_term γ (F' ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) | exact HT' ]. }
  exists FA, (fun ρ => select_term γ (F ρ) x), (fun ρ => select_term γ (F' ρ) x).
  constructor; [exact HA | exact HM | exact HM' | |].
  - intros ρ Hρ. exact (select_term_resp γ _ _ (E _ Hρ) x).
  - intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ Hv HF _ _ _ _ Hkn Hm Ht HA _ Hρ)).
Qed.

(** [δ] for members: a term member of a valid module expression is its
    reduct. *)
Lemma set_rule_mem_delta : forall Γ H x R1 A M, set_ctx_slots Θ Ξ T γ Γ -> set_modexp_eq Θ Ξ T γ Γ H H ->
    mdenote Θ Ξ Γ (me_mem H x) R1 -> mdesc_type R1 = Some A -> mdesc_reduct R1 = Some M ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A -> set_exp_eq Θ Ξ T γ Γ A (a_mem H x) M.
Proof.
  intros * HΓ HH Hm1 Ht1 HM1 HT. set_open. destruct HΓ as [HΓ _]. destruct HH as (F & F' & [HF _ _ Hv _]).
  destruct (set_member_here T γ Hgw Θ Ξ Hμ _ _ _ _ _ Hm1 Ht1) as (R & Hm & Ht & HRr & Hkn).
  assert (HM : mdesc_reduct R = Some M) by (rewrite HRr; exact HM1).
  destruct (set_valid_modexp_members_denote T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ Hv _ _ _ Hkn Hm Ht) as [(FA & HA) HMd].
  destruct (HMd _ HM) as (FM & HFM).
  assert (HMem : set_denotes T γ Γ (a_mem H x) (fun ρ => select_term γ (F ρ) x)).
  { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    econstructor; [ exact (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) | exact HT ]. }
  exists FA, (fun ρ => select_term γ (F ρ) x), FM.
  constructor; [exact HA | exact HMem | exact HFM | |].
  - intros ρ Hρ.
    exact (proj2 (set_valid_modexp_members T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ Hv HF _ _ _ _ Hkn Hm Ht HA _ Hρ) _ _ HM HFM).
  - intros ρ Hρ. exact (proj1 (set_valid_modexp_members T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ Hv HF _ _ _ _ Hkn Hm Ht HA _ Hρ)).
Qed.

(** A literal body or alias given its outermost parameter is the literal
    instantiated. *)
Lemma set_rule_me_beta : forall Γ Δ κ X D N, set_ctx_slots Θ Ξ T γ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N ≈ me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N))) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    set_unit_eq Θ Ξ T γ Γ (gu_mk (Δ ++ [ce_ass κ X]) D) (gu_mk (Δ ++ [ce_ass κ X]) D) -> set_exp_eq Θ Ξ T γ Γ X N N ->
    set_modexp_eq Θ Ξ T γ Γ (me_app (me_lit (gu_mk (Δ ++ [ce_ass κ X]) D)) N) (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N)))).
Proof.
  intros * _ Hβ HNw HUe HN. set_open. destruct HUe as (FU & _ & [_ _ _ HKU _]).
  destruct (me_denotes _ _ _ _ _ (set_valid_unit_wf T γ _ _ HKU)) as (R0 & _ & HR0 & _).
  destruct (set_unit_beta_reduct T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ _ _ _ HKU HR0 HNw HN) as (R' & [Hat Hrel HK' HmK HR' Hpr]).
  apply set_modexp_eq_of_rel; [exact Hrel | | exact (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK') | exact Hpr].
  apply (set_valid_modexp_intro T γ _ _ (me_lit (gunit_sub (gu_mk Δ D) (sb_extend sb_id (se_exp N)))) R' R' R'); [| exact HK'].
  constructor; [exact (wf_modexp_eq_refl_left Hβ) | eapply mdenote_app; [exact HR0 | exact Hat] | exact HR' | exact Hrel | exact HmK | exact HR' |].
  exact Hpr.
Qed.

(** Equal module expressions given equal arguments are equal. *)
Lemma set_rule_me_app : forall Γ H H' N N' R Tl B T1 Srt R' Tl' B' T1' Srt', set_ctx_slots Θ Ξ T γ Γ ->
    set_modexp_eq Θ Ξ T γ Γ H H' ->
    mdenote Θ Ξ Γ H R -> mdesc_mod_tele R = Some Tl -> tele_view Tl = Some (B, T1) ->
    evaluated_sort Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt -> set_exp_eq Θ Ξ T γ Γ Srt B B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : B -> set_exp_eq Θ Ξ T γ Γ B N N -> set_exp_eq Θ Ξ T γ Γ B N N' ->
    mdenote Θ Ξ Γ H' R' -> mdesc_mod_tele R' = Some Tl' -> tele_view Tl' = Some (B', T1') ->
    evaluated_sort Srt' -> Θ ⍮ Ξ ⍮ Γ ⊢ B' : Srt' -> set_exp_eq Θ Ξ T γ Γ Srt' B' B' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' -> set_exp_eq Θ Ξ T γ Γ B' N' N' ->
    set_modexp_eq Θ Ξ T γ Γ (me_app H N) (me_app H' N').
Proof.
  intros * HΓ HH Hms Hts HV HS HBw HB HNw HN HNN Hms' Hts' HV' HS' HBw' HB' HNw' HN'. set_open. destruct HΓ as [HΓ _].
  destruct HH as (F & F' & [HF HF' E Hv Hv' Hpr]). destruct HNN as (FB & FN & FN' & [_ HFN HFN' EN _]).
  pose proof (proj1 (mdenote_grow_all _ _ _ _ (set_source_wf T γ Θ Ξ Hμ) Hgw (set_source_sub T γ Θ Ξ Hμ))) as Hgrow.
  destruct (Hgrow _ _ _ Hms) as (R2 & Hm & HR). pose proof (mdesc_grows_mtele _ _ _ _ _ _ _ HR Hts) as Ht.
  destruct (Hgrow _ _ _ Hms') as (R2' & Hm' & HR'). pose proof (mdesc_grows_mtele _ _ _ _ _ _ _ HR' Hts') as Ht'.
  exists (fun ρ => apply_module (F ρ) (FN ρ)), (fun ρ => apply_module (F' ρ) (FN' ρ)). constructor.
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) (set_denotes_exists _ _ _ _ _ HFN _ Hρ)).
  - apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    exact (set_interp_me_app T γ _ _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) (set_denotes_exists _ _ _ _ _ HFN' _ Hρ)).
  - intros ρ Hρ. exact (apply_module_resp _ _ (E _ Hρ) _ _ (EN _ Hρ)).
  - exact (proj2 (set_valid_unit_app_all T γ Hfn Hmods Hgw Θ Ξ Hμ) _ _ Hv _ _ _ _ _ _ Hm Ht HV HS HBw (ex_intro _ _ (conj HS HB)) HNw HN).
  - exact (proj2 (set_valid_unit_app_all T γ Hfn Hmods Hgw Θ Ξ Hμ) _ _ Hv' _ _ _ _ _ _ Hm' Ht' HV' HS' HBw' (ex_intro _ _ (conj HS' HB')) HNw' HN').
  - exact Hpr.
Qed.

End ModuleCases.
Section Sel.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** Submodules of equal module expressions are equal. *)
Lemma set_rule_me_mem : forall Γ H H' y R1 Tl R1' Tl', set_ctx_slots Θ Ξ T γ Γ -> set_modexp_eq Θ Ξ T γ Γ H H' ->
    mdenote Θ Ξ Γ (me_mem H y) R1 -> mdesc_mod_tele R1 = Some Tl ->
    mdenote Θ Ξ Γ (me_mem H' y) R1' -> mdesc_mod_tele R1' = Some Tl' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H' y ≈ me_mem H' y ->
    set_modexp_eq Θ Ξ T γ Γ (me_mem H y) (me_mem H' y).
Proof.
  intros * HΓ HH Hm1 Ht1 Hm1' Ht1' HwY HwY'. set_open. destruct HΓ as [HΓ _].
  destruct HH as (F & F' & [HF HF' E Hv Hv' Hpr]).
  destruct (set_submodule_here T γ Hgw Θ Ξ Hμ _ _ _ _ _ Hm1 Ht1) as (R & Hm & Ht & Hkn).
  destruct (set_submodule_here T γ Hgw Θ Ξ Hμ _ _ _ _ _ Hm1' Ht1') as (R' & Hm' & Ht' & Hkn').
  destruct (mdesc_mod_tele_mod _ _ Ht) as (Rm & Hmd). destruct (mdesc_mod_tele_mod _ _ Ht') as (Rm' & Hmd').
  apply set_modexp_eq_of_rel; [| exact (proj2 (set_valid_modexp_sel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ _ Hv Hkn Hm Hmd))
                              | exact (proj2 (set_valid_modexp_sel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ _ Hv' Hkn' Hm' Hmd'))
                              | intros κs Hκ ys x; exact (Hpr κs Hκ (y :: ys) x)].
  apply set_modexp_rel_mem; [exact Hfn | exact Hmods | exact HΓ | | exact HwY | exact HwY']. exists F, F'. constructor; assumption.
Qed.

(** [δ] for submodules: a submodule is the unit its module part stands
    for. *)
Lemma set_rule_me_delta_sel : forall Γ H y R Rm, set_modexp_eq Θ Ξ T γ Γ (me_mem H y) (me_mem H y) ->
    mdenote Θ Ξ Γ (me_mem H y) R -> mdesc_mod R = Some Rm ->
    set_modexp_eq Θ Ξ T γ Γ (me_mem H y) (mdesc_unit Rm).
Proof.
  intros * HH Hms Hmds. set_open. destruct HH as (F & F' & [_ _ _ Hv _]).
  destruct (proj1 (mdenote_grow_all _ _ _ _ (set_source_wf T γ Θ Ξ Hμ) Hgw (set_source_sub T γ Θ Ξ Hμ)) _ _ _ Hms)
    as (R2 & Hm & HR).
  destruct (mdesc_grows_mod _ _ _ _ _ _ _ HR Hmds) as (Rm2 & Hmd & HRm). rewrite (mdesc_grows_unit _ _ _ _ _ _ HRm).
  destruct (set_valid_modexp_canon T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ _ _ Hv Hm Hmd) as [Hr HK Hpr].
  exact (set_modexp_eq_of_rel T γ _ _ _ Hr Hv (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) Hpr).
Qed.

End Sel.
