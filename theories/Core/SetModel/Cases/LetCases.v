(** * The Set Rules of Lets

    The rules of the three lets in the set model: of a term, of a module
    and of a definition with a module part, their congruences and their
    [ζ]-rules.  The lemmas they rest on are in [Judgments/Lets.v]. *)

From Stdlib Require Import String List Lia.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Import Variables Lets.
From Mctt.Core.SetModel.Interpretation Require Import Substitution ContextRelation.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Lets.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** [ℓ A ≔ M in B : C[M]], and [ζ] at it: [ℓ A ≔ M in B ≈ B[M]]. *)
Lemma set_rule_let_def_zeta : forall Γ A M B C, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_def A M :: Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_def A M :: Γ ->
    set_exp_eq Θ Ξ T γ Γ A M M -> set_exp_eq Θ Ξ T γ (ce_def A M :: Γ) C B B ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_exp M))) (a_let (b_def A M) B) (exp_sub B (sb_extend sb_id (se_exp M))).
Proof.
  intros * HΓ Hc Hσ HMe HBe. set_open. destruct HΓ as [HΓ _].
  destruct HMe as (FA' & FM & FM2 & [HA' HM _ _ HMm]). destruct HBe as (FC & FB & FB2 & [HC HB _ _ HBm]).
  exists (fun ρ => FC (def_env FM ρ)), (fun ρ => FB (def_env FM ρ)), (fun ρ => FB (def_env FM ρ)).
  constructor; [apply set_denotes_def_sub with (A := A); assumption | apply set_denotes_let_def; assumption
               | apply set_denotes_def_sub with (A := A); assumption | intros; apply set_eq_refl |].
  intros ρ Hρ. apply HBm. apply set_env_in_def; assumption.
Qed.

(** [ℓₘ U in B : C[U]], and [ζ] at it: [ℓₘ U in B ≈ B[U]]. *)
Lemma set_rule_let_mod_zeta : forall Γ U B C, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_mod U :: Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_mod (me_lit U)) : ce_mod U :: Γ ->
    set_unit_eq Θ Ξ T γ Γ U U ->
    set_exp_eq Θ Ξ T γ (ce_mod U :: Γ) C B B ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_mod (me_lit U)))) (a_let (b_mod U) B)
      (exp_sub B (sb_extend sb_id (se_mod (me_lit U)))).
Proof.
  intros * HΓ Hc Hσ HUe HBe. set_open. destruct HΓ as [HΓ _].
  destruct HUe as (FU & FU' & [HU _ _ _ _]). destruct HBe as (FC & FB & FB2 & [HC HB _ _ HBm]).
  exists (fun ρ => FC (mod_env FU ρ)), (fun ρ => FB (mod_env FU ρ)), (fun ρ => FB (mod_env FU ρ)).
  constructor; [apply set_denotes_mod_sub; assumption | apply set_denotes_let_mod; assumption
               | apply set_denotes_mod_sub; assumption | intros; apply set_eq_refl |].
  intros ρ Hρ. apply HBm. apply set_env_in_mod; assumption.
Qed.

(** [ℓᵈ A ≔ M ‖ U in B : C[M ‖ U]], and [ζ] at it:
    [ℓᵈ A ≔ M ‖ U in B ≈ B[M ‖ U]]. *)
Lemma set_rule_let_dm_zeta : forall Γ A M U B C, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_dm A M U :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_dm M (me_lit U)) : ce_dm A M U :: Γ ->
    set_exp_eq Θ Ξ T γ Γ A M M -> set_unit_eq Θ Ξ T γ Γ U U ->
    set_exp_eq Θ Ξ T γ (ce_dm A M U :: Γ) C B B ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_dm M (me_lit U)))) (a_let (b_def_mod A M U) B)
      (exp_sub B (sb_extend sb_id (se_dm M (me_lit U)))).
Proof.
  intros * HΓ Hc Hσ HMe HUe HBe. set_open. destruct HΓ as [HΓ _].
  destruct HMe as (FA' & FM & FM2 & [_ HM _ _ _]). destruct HUe as (FU & FU' & [HU _ _ _ _]).
  destruct HBe as (FC & FB & FB2 & [HC HB _ _ HBm]).
  exists (fun ρ => FC (dm_env FM FU ρ)), (fun ρ => FB (dm_env FM FU ρ)), (fun ρ => FB (dm_env FM FU ρ)).
  constructor; [apply set_denotes_dm_sub with (A := A); assumption | apply set_denotes_let_dm; assumption
               | apply set_denotes_dm_sub with (A := A); assumption | intros; apply set_eq_refl |].
  intros ρ Hρ. apply HBm. apply set_env_in_dm; assumption.
Qed.

Lemma set_rule_let_def_cong : forall Γ A A' M M' B B' C, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_def A M :: Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_def A' M' :: Γ ->
    Θ ⍮ Ξ ⍮ ce_def A' M' :: Γ ⊢ˢ sb_id : ce_def A M :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp M) : ce_def A M :: Γ ->
    set_exp_eq Θ Ξ T γ Γ A M M' -> set_exp_eq Θ Ξ T γ (ce_def A M :: Γ) C B B' ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_exp M))) (a_let (b_def A M) B) (a_let (b_def A' M') B').
Proof.
  intros * HΓ Hc Hc' Hid Hσ HMe HBe. set_open. destruct HΓ as [HΓ _].
  destruct HMe as (FA & FM & FM' & [_ HM HM' EM _]). destruct HBe as (FC & FB & FB' & [HC HB HB' EB HBm]).
  assert (Hin' : forall ρ, set_env_in T γ Γ ρ -> set_env_in T γ (ce_def A M :: Γ) (def_env FM' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists ak_relevant, (FM' ρ), (FM' ρ), (FM ρ).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_sym; apply EM; exact Hρ ..]. }
  assert (Hrel : forall ρ, set_env_in T γ Γ ρ -> set_env_rel T γ (ce_def A M :: Γ) (def_env FM ρ) (def_env FM' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists ak_relevant, (FM ρ), (FM' ρ), (FM ρ).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) | apply set_eq_refl | apply set_eq_sym; apply EM; exact Hρ]. }
  exists (fun ρ => FC (def_env FM ρ)), (fun ρ => FB (def_env FM ρ)), (fun ρ => FB' (def_env FM' ρ)).
  constructor; [apply set_denotes_def_sub with (A := A); assumption | apply set_denotes_let_def; assumption | | |].
  - apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
    econstructor; [exact Hc' | exact (set_denotes_exists _ _ _ _ _ HM' _ Hρ) |].
    apply (set_interp_ctx_conv _ _ _ _ _ _ _ Hc Hid). apply (set_denotes_exists _ _ _ _ _ HB'). apply Hin'; exact Hρ.
  - intros ρ Hρ. eapply set_eq_trans; [apply EB; apply set_env_in_def; assumption |].
    apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HB' _ _ _ (Hrel ρ Hρ) (set_denotes_exists _ _ _ _ _ HB' _ (Hin' ρ Hρ))).
  - intros ρ Hρ. apply HBm. apply set_env_in_def; assumption.
Qed.

Lemma set_rule_let_mod_cong : forall Γ U U' B B' C, set_ctx_slots Θ Ξ T γ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ ce_mod U :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ ce_mod U :: nil ≈ ce_mod U' :: nil ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_mod (me_lit U)) : ce_mod U :: Γ ->
    set_unit_eq Θ Ξ T γ Γ U U' -> set_exp_eq Θ Ξ T γ (ce_mod U :: Γ) C B B' ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_mod (me_lit U)))) (a_let (b_mod U') B') (a_let (b_mod U') B') ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_mod (me_lit U)))) (a_let (b_mod U) B) (a_let (b_mod U') B').
Proof.
  intros * HΓ Hc Hx Hσ HUe HBe HLe. set_open. destruct HΓ as [HΓ _].
  destruct HUe as (FU & FU' & [HU HU' EU _ _]). destruct HBe as (FC & FB & FB' & [HC HB HB' EB HBm]).
  destruct HLe as (FS & FL & FL' & [_ HL _ _ _]).
  assert (Hin' : forall ρ, set_env_in T γ Γ ρ -> set_env_in T γ (ce_mod U :: Γ) (mod_env FU' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists (FU' ρ), (FU' ρ), (FU ρ).
    constructor; [reflexivity | reflexivity | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
                 | apply set_module_eq_sym; apply EU; exact Hρ ..]. }
  assert (Hrel : forall ρ, set_env_in T γ Γ ρ -> set_env_rel T γ (ce_mod U :: Γ) (mod_env FU ρ) (mod_env FU' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists (FU ρ), (FU' ρ), (FU ρ).
    constructor; [reflexivity | reflexivity | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
                 | exact (set_modexp_denotes_refl _ _ _ _ _ _ HU Hρ) | apply set_module_eq_sym; apply EU; exact Hρ]. }
  exists (fun ρ => FC (mod_env FU ρ)), (fun ρ => FB (mod_env FU ρ)), FL.
  constructor; [apply set_denotes_mod_sub; assumption | apply set_denotes_let_mod; assumption | exact HL | |].
  - intros ρ Hρ. eapply set_eq_trans; [apply EB; apply set_env_in_mod; assumption |].
    eapply set_eq_trans;
      [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HB' _ _ _ (Hrel ρ Hρ) (set_denotes_exists _ _ _ _ _ HB' _ (Hin' ρ Hρ))) |].
    pose proof (set_denotes_exists _ _ _ _ _ HL _ Hρ) as HLρ. inversion HLρ; subst.
    unfold mod_env in *.
    match goal with Hm : set_interp_gunit _ _ _ _ U' ?m, Hw : set_interp _ _ (ce_mod U' :: Γ) _ B' _ |- _ =>
      eapply (set_interp_body_across T γ Hmods _ _ _ _ _ _ _ _ _ Hfnx Hx Hρ); [| exact (set_denotes_exists _ _ _ _ _ HB' _ (Hin' ρ Hρ)) | exact Hw];
      constructor; apply set_module_eq_sym;
      exact (set_modexp_denotes_unique _ _ _ _ _ HU' _ _ _ Hρ (set_interp_me_lit T γ _ _ _ _ Hm)) end.
  - intros ρ Hρ. apply HBm. apply set_env_in_mod; assumption.
Qed.

Lemma set_rule_let_dm_cong : forall Γ A A' M M' U U' B B' C,
    set_ctx_slots Θ Ξ T γ Γ -> ⊢ Θ ⍮ Ξ ⍮ ce_dm A M U :: Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ ce_dm A M U :: nil ≈ ce_dm A' M' U' :: nil ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend sb_id (se_dm M (me_lit U)) : ce_dm A M U :: Γ ->
    set_exp_eq Θ Ξ T γ Γ A M M' -> set_unit_eq Θ Ξ T γ Γ U U' ->
    set_exp_eq Θ Ξ T γ (ce_dm A M U :: Γ) C B B' ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_dm M (me_lit U)))) (a_let (b_def_mod A' M' U') B')
      (a_let (b_def_mod A' M' U') B') ->
    set_exp_eq Θ Ξ T γ Γ (exp_sub C (sb_extend sb_id (se_dm M (me_lit U)))) (a_let (b_def_mod A M U) B)
      (a_let (b_def_mod A' M' U') B').
Proof.
  intros * HΓ Hc Hx Hσ HMe HUe HBe HLe. set_open. destruct HΓ as [HΓ _].
  destruct HMe as (FA & FM & FM' & [_ HM HM' EM _]). destruct HUe as (FU & FU' & [HU HU' EU _ _]).
  destruct HBe as (FC & FB & FB' & [HC HB HB' EB HBm]). destruct HLe as (FS & FL & FL' & [_ HL _ _ _]).
  assert (Hin' : forall ρ, set_env_in T γ Γ ρ -> set_env_in T γ (ce_dm A M U :: Γ) (dm_env FM' FU' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists (FM' ρ), (FM' ρ), (FM ρ), (FU' ρ), (FU' ρ), (FU ρ).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ)
                 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
                 | apply set_eq_sym; apply EM; exact Hρ | apply set_eq_sym; apply EM; exact Hρ
                 | apply set_module_eq_sym; apply EU; exact Hρ | apply set_module_eq_sym; apply EU; exact Hρ]. }
  assert (Hrel : forall ρ, set_env_in T γ Γ ρ -> set_env_rel T γ (ce_dm A M U :: Γ) (dm_env FM FU ρ) (dm_env FM' FU' ρ)).
  { intros ρ Hρ. split; [exact Hρ |]. exists (FM ρ), (FM' ρ), (FM ρ), (FU ρ), (FU' ρ), (FU ρ).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ Hρ)
                 | apply set_interp_me_lit_iff; exact (set_modexp_denotes_exists _ _ _ _ _ HU _ Hρ)
                 | apply set_eq_refl | apply set_eq_sym; apply EM; exact Hρ
                 | exact (set_modexp_denotes_refl _ _ _ _ _ _ HU Hρ) | apply set_module_eq_sym; apply EU; exact Hρ]. }
  exists (fun ρ => FC (dm_env FM FU ρ)), (fun ρ => FB (dm_env FM FU ρ)), FL.
  constructor; [apply set_denotes_dm_sub with (A := A); assumption | apply set_denotes_let_dm; assumption | exact HL | |].
  - intros ρ Hρ. eapply set_eq_trans; [apply EB; apply set_env_in_dm; assumption |].
    eapply set_eq_trans;
      [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HB' _ _ _ (Hrel ρ Hρ) (set_denotes_exists _ _ _ _ _ HB' _ (Hin' ρ Hρ))) |].
    pose proof (set_denotes_exists _ _ _ _ _ HL _ Hρ) as HLρ. inversion HLρ; subst. unfold dm_env in *.
    match goal with Hv : set_interp _ _ Γ ρ M' ?v, Hm : set_interp_gunit _ _ _ _ U' ?m,
                    Hw : set_interp _ _ (ce_dm A' M' U' :: Γ) _ B' _ |- _ =>
      eapply (set_interp_body_across T γ Hmods _ _ _ _ _ _ _ _ _ Hfnx Hx Hρ); [| exact (set_denotes_exists _ _ _ _ _ HB' _ (Hin' ρ Hρ)) | exact Hw];
      constructor; [exact (set_eq_sym _ _ (set_denotes_unique _ _ _ _ _ HM' _ _ _ Hρ Hv)) |];
      apply set_module_eq_sym;
      exact (set_modexp_denotes_unique _ _ _ _ _ HU' _ _ _ Hρ (set_interp_me_lit T γ _ _ _ _ Hm)) end.
  - intros ρ Hρ. apply HBm. apply set_env_in_dm; assumption.
Qed.

End Lets.
