(** * The Set Rules of Extensions and Units

    The rules of [⊢ˣ] (equal extensions) and of [⊢ᵘ] (equal units) in the
    set model.  The lemmas they rest on are in [Modules/Slots.v] and
    [Modules/Unit.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects ContextRelation Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution Contexts Subtyping.
From Mctt.Core.SetModel.Modules Require Import ValidUnit MemberTypes ModuleLemmas Unit Sel Slots.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound Presup.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body.
Import ListNotations.

Section Units.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_ext_eq_nil : forall Γ, set_ctx_slots Θ Ξ T γ Γ -> set_ext_eq_suffixes Θ Ξ T γ Γ nil nil.
Proof.
  intros Γ HΓ. set_open. destruct HΓ as [HΓ Hsl]. constructor; [| exact Hsl | exact Hsl].
  intros [| ? ?] Ψ [| ? ?] Ψ' E E' _; try discriminate. cbn in E, E'. subst. exact (set_ext_eq_with_nil T γ _ HΓ).
Qed.

Lemma set_rule_ext_eq_ass : forall Γ Ψ Ψ' κ A A' S S', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) S A A -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) S' A' A' ->
    set_subtyp Θ Ξ T γ (Ψ ++ Γ) A A' -> set_subtyp Θ Ξ T γ (Ψ ++ Γ) A' A ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_ass κ A :: Ψ) (ce_ass κ A' :: Ψ').
Proof.
  intros * HΨw HΨ HAe HA'e Hs Hs'. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HAe as (FS & FA & FA2 & HA). destruct HA'e as (FS' & FA' & FA'2 & HA').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons T γ _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_ass; eassumption.
  - exact (set_valid_slots_extend_plain T γ _ (ce_ass κ A) Hsl eq_refl).
  - exact (set_valid_slots_extend_plain T γ _ (ce_ass κ A') Hsl' eq_refl).
Qed.

Lemma set_rule_ext_eq_def : forall Γ Ψ Ψ' A A' M M', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) A M M' -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) A' M' M' ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_def A M :: Ψ) (ce_def A' M' :: Ψ').
Proof.
  intros * HΨw HΨ HMe HM'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HMe as (FA & FM & FM' & HM). destruct HM'e as (FA' & FM2 & FM2' & HM').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons T γ _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_def; eassumption.
  - exact (set_valid_slots_extend_plain T γ _ (ce_def A M) Hsl eq_refl).
  - exact (set_valid_slots_extend_plain T γ _ (ce_def A' M') Hsl' eq_refl).
Qed.

Lemma set_rule_ext_eq_mod : forall Γ Ψ Ψ' U U', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_unit_eq Θ Ξ T γ (Ψ ++ Γ) U U' -> set_unit_eq Θ Ξ T γ (Ψ' ++ Γ) U' U' ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_mod U :: Ψ) (ce_mod U' :: Ψ').
Proof.
  intros * HΨw HΨ HUe HU'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HUe as (FU & FU' & HU). destruct HU'e as (FU2 & FU2' & HU').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons T γ _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_mod; eassumption.
  - split; [exact Hsl | intros U0 HU0; injection HU0 as <-; destruct HU as [_ _ _ Hv _ _]; exact Hv].
  - split; [exact Hsl' | intros U0 HU0; injection HU0 as <-; destruct HU' as [_ _ _ Hv _ _]; exact Hv].
Qed.

Lemma set_rule_ext_eq_dm : forall Γ Ψ Ψ' A A' M M' E E', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Ψ Ψ' ->
    set_exp_eq Θ Ξ T γ (Ψ ++ Γ) A M M' -> set_exp_eq Θ Ξ T γ (Ψ' ++ Γ) A' M' M' ->
    set_unit_eq Θ Ξ T γ (Ψ ++ Γ) (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E')) ->
    set_unit_eq Θ Ξ T γ (Ψ' ++ Γ) (gu_mk nil (md_alias E')) (gu_mk nil (md_alias E')) ->
    set_ext_eq_suffixes Θ Ξ T γ Γ (ce_dm A M (gu_mk nil (md_alias E)) :: Ψ) (ce_dm A' M' (gu_mk nil (md_alias E')) :: Ψ').
Proof.
  intros * HΨw HΨ HMe HM'e HUe HU'e. set_open. pose proof (ext_eq_length _ _ _ _ _ HΨw) as Hlen.
  destruct HΨ as [Hsuf Hsl Hsl']. destruct HMe as (FA & FM & FM' & HM). destruct HM'e as (FA' & FM2 & FM2' & HM').
  destruct HUe as (FU & FU' & HU). destruct HU'e as (FU2 & FU2' & HU').
  constructor.
  - apply (set_ext_eq_suffixes_eq_cons T γ _ _ _ _ _ Hsuf Hlen).
    pose proof (Hsuf nil Ψ nil Ψ' eq_refl eq_refl Hlen) as Hwh. eapply set_ext_eq_with_dm; eassumption.
  - split; [exact Hsl | intros U0 HU0; injection HU0 as <-; destruct HU as [_ _ _ Hv _ _]; exact Hv].
  - split; [exact Hsl' | intros U0 HU0; injection HU0 as <-; destruct HU' as [_ _ _ Hv _ _]; exact Hv].
Qed.

Lemma set_rule_unit_eq_alias : forall Γ Δ Δ' E E' l ps,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Δ Δ' ->
    all_assumptions Δ -> all_assumptions Δ' -> (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    (forall Δ1 κ A Δ2, Δ' = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    set_modexp_eq Θ Ξ T γ (Δ ++ Γ) E E' -> set_modexp_eq Θ Ξ T γ (Δ' ++ Γ) E' E' ->
    set_unit_eq Θ Ξ T γ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ' (md_alias E')).
Proof.
  intros * HUU HΔw HΔs HΔ HΔ' Hps HAs HAs' HEe HE'e. set_open.
  pose proof (set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs Δ1 κ A Δ2 E0 _ _ Hμ)) as Hl.
  pose proof (set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs' Δ1 κ A Δ2 E0 _ _ Hμ)) as Hl'.
  pose proof (set_ext_eq_suffixes_eq T γ _ _ _ HΔs) as Hext.
  pose proof HEe as (G & G' & [_ _ _ HvE _ _]). pose proof HE'e as (G2 & _ & [_ _ _ HvE2 _ _]).
  pose proof (set_valid_unit_alias_of T γ Hfnx Hmods _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) HΔ Hl HvE) as HK.
  pose proof (set_valid_unit_alias_of T γ Hfnx Hmods _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) HΔ' Hl' HvE2) as HK'.
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as (F & _ & [HF _ _]).
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK') as (F' & _ & [HF' _ _]).
  exists F, F'. constructor; [exact HF | exact HF' | | exact HK | exact HK' |].
  - exact (set_unit_alias_eq_values T γ Hfnx Hmods _ _ _ _ _ _ _ HΔw Hext HΔ HΔ' HEe HE'e HF HF').
  - exact (set_unit_alias_eq_proofs T γ _ _ _ _ _ HΔw HΔ HΔ' HEe).
Qed.

Lemma set_rule_unit_eq_body : forall Γ Δ Δ' Φ Φ' Φx Φx' l ps (entry_sort : string -> exp),
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ Δ Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ -> set_ext_eq_suffixes Θ Ξ T γ Γ (body_ctx Φx ++ Δ) (body_ctx Φx ++ Δ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' -> set_ext_eq_suffixes Θ Ξ T γ Γ (body_ctx Φx' ++ Δ') (body_ctx Φx' ++ Δ') ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       exists i, entry_sort y = abs_kind_sort (entry_kind E) (a_typ i)) ->
    (forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       exists i, entry_sort y = abs_kind_sort (entry_kind E') (a_typ i)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ ++ Γ) (entry_sort y) (exp_sub A σ) (exp_sub A' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ' ++ Γ) (entry_sort y) (exp_sub A' σ') (exp_sub A' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ ++ Γ) (exp_sub A σ) (exp_sub M σ) (exp_sub M' σ')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_exp_eq Θ Ξ T γ (Δ' ++ Γ) (exp_sub A' σ') (exp_sub M' σ') (exp_sub M' σ')) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_unit_eq Θ Ξ T γ (Δ ++ Γ) (gunit_sub U σ) (gunit_sub U' σ')) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       set_unit_eq Θ Ξ T γ (Δ' ++ Γ) (gunit_sub U' σ') (gunit_sub U' σ')) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> set_modexp_eq Θ Ξ T γ (Ψ ++ Δ ++ Γ) H H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> set_modexp_eq Θ Ξ T γ (Ψ' ++ Δ' ++ Γ) H' H') ->
    all_assumptions Δ -> all_assumptions Δ' -> (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    (forall Δ1 κ A Δ2, Δ' = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    set_unit_eq Θ Ξ T γ Γ (gu_open Δ Φ) (gu_open Δ' Φ').
Proof.
  intros * HUU Hx Hx' HΔw HΔs Hxb Hb Hxb' Hb' Htag Htag' HA0 HA0' HM0 HM0' HU0 HU0' Ho0 Ho0' HΔ HΔ' Hps HAs HAs' Hs Hsxx Hnd.
  set_open.
  pose proof (proj1 (set_ext_eq_suffixes_whole T γ _ _ _ Hb eq_refl)) as HC.
  pose proof (proj1 (set_ext_eq_suffixes_whole T γ _ _ _ Hb' eq_refl)) as HC'.
  pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb) as Hsl. pose proof (set_ext_eq_suffixes_slots T γ _ _ _ Hb') as Hsl'.
  pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb) as Hcx. pose proof (ext_eq_ctx_left _ _ _ _ _ Hxb') as Hcx'.
  rewrite <- List.app_assoc in HC, HC', Hsl, Hsl', Hcx, Hcx'.
  assert (Hset : set_body_eq_setting T γ Γ Δ Δ' Φ Φ' Φx Φx' l entry_sort).
  { refine {| set_body_eq_wf := HUU; set_body_eq_xp := Hx; set_body_eq_xp' := Hx'; set_body_eq_tele_wf := HΔw;
              set_body_eq_ctx_wf := Hcx; set_body_eq_ctx_wf' := Hcx'; set_body_eq_tele := set_ext_eq_suffixes_eq T γ _ _ _ HΔs;
              set_body_eq_ctx := HC; set_body_eq_ctx' := HC'; set_body_eq_slots := Hsl; set_body_eq_slots' := Hsl';
              set_body_eq_sorts := Htag; set_body_eq_sorts' := Htag';
              set_body_eq_assumptions := HΔ; set_body_eq_assumptions' := HΔ';
              set_body_eq_params := set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs Δ1 κ A Δ2 E0 _ _ Hμ);
              set_body_eq_params' := set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E0 => HAs' Δ1 κ A Δ2 E0 _ _ Hμ);
              set_body_eq_shape := Hs; set_body_eq_shape_xp := Hsxx; set_body_eq_names := Hnd |}.
    - intros; eapply HA0; eassumption. - intros; eapply HA0'; eassumption.
    - intros; eapply HM0; eassumption. - intros; eapply HM0'; eassumption.
    - intros; eapply HU0; eassumption. - intros; eapply HU0'; eassumption.
    - intros; eapply Ho0; eassumption. - intros; eapply Ho0'; eassumption. }
  destruct (set_body_eq_valid T γ Hfnx Hmods _ _ _ _ _ _ _ _ _ Hset) as [HK HK'].
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as (F & _ & [HF _ _]).
  destruct (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK') as (F' & _ & [HF' _ _]).
  exists F, F'. constructor; [exact HF | exact HF' | | exact HK | exact HK' |].
  - exact (set_body_eq_values T γ Hfnx Hmods _ _ _ _ _ _ _ _ _ _ _ Hset HF HF').
  - exact (set_body_eq_proofs T γ _ _ _ _ _ _ _ _ _ Hset).
Qed.

End Units.
Section Unit.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma set_rule_unit_eq_sym : forall Γ U U', set_unit_eq Θ Ξ T γ Γ U U' -> set_unit_eq Θ Ξ T γ Γ U' U.
Proof.
  intros * HU0. set_open. destruct HU0 as (F & F' & [HF HF' E HU HU' Hpr]).
  exists F', F. constructor; [exact HF' | exact HF | | exact HU' | exact HU |].
  - intros ρ Hρ. apply set_module_eq_sym. exact (E _ Hρ).
  - intros κs Hκ ys x. exact (eq_sym (Hpr κs Hκ ys x)).
Qed.

Lemma set_rule_unit_eq_trans : forall Γ U U' U'', set_unit_eq Θ Ξ T γ Γ U U' -> set_unit_eq Θ Ξ T γ Γ U' U'' ->
    set_unit_eq Θ Ξ T γ Γ U U''.
Proof.
  intros * H1 H2. set_open. destruct H1 as (F & F' & [HF HF' E HU _ Hpr]). destruct H2 as (G & G' & [HG HG' E' _ HU'' Hpr']).
  exists F, G'.
  constructor; [exact HF | exact HG' | | exact HU | exact HU'' |].
  - intros ρ Hρ. eapply set_module_eq_trans; [exact (E _ Hρ) |]. eapply set_module_eq_trans; [| exact (E' _ Hρ)].
    exact (set_modexp_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
  - intros κs Hκ ys x. exact (eq_trans (Hpr κs Hκ ys x) (Hpr' κs Hκ ys x)).
Qed.

(** An alias over assumptions of a literal is the literal over both
    telescopes. *)
Lemma set_rule_unit_eq_flatten : forall Γ Δ Δ' D l ps, all_assumptions Δ -> (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> set_exp_eq Θ Ξ T γ (Δ2 ++ Γ) (ps (List.length Δ2)) A A) ->
    set_unit_eq Θ Ξ T γ (Δ ++ Γ) (gu_mk Δ' D) (gu_mk Δ' D) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D ->
    set_unit_eq Θ Ξ T γ Γ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) (gu_mk (Δ' ++ Δ) D).
Proof.
  intros * HΔ Hps HAs HUe HUU. set_open.
  pose proof (set_params_evaluated_of_sorts T γ _ _ _ _ Hps (fun Δ1 κ A Δ2 E => HAs Δ1 κ A Δ2 E _ _ Hμ)) as Hl.
  destruct HUe as (FU & _ & [HFU _ _ HK _]).
  pose proof (set_valid_unit_ctx T γ _ _ HK) as HΔΓ. pose proof (set_ctx_app_r T γ _ _ HΔΓ) as HΓ.
  pose proof (presup_modexp_eq_ctx (set_valid_unit_wf T γ _ _ HK)) as HcΔΓ.
  pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left HUU)) as HwA. pose proof (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) as HwF.
  pose proof (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK) as HrU.
  assert (HrA : set_modexp_rel T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))))).
  { exact (set_unit_rel_abs T γ Hfn Hmods Δ Γ nil _ HΔ HΔΓ HcΔΓ
             (set_modexp_rel_refl_left T γ _ _ _ (set_alias0_rel T γ Hfn Hmods _ _ HΔΓ HrU))). }
  assert (HKA : set_valid_unit T γ Γ (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))))).
  { apply set_valid_unit_alias; [| exact (set_valid_modexp_of_unit T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HK)].
    constructor; [exact HwA | exact HΔ | exists l; exact Hl | exact HΓ | exact HΔΓ | exact HrA | exact HrU]. }
  pose proof (set_valid_unit_abs T γ Hfn Hmods _ _ _ _ _ HK HΔ Hl HwF) as HKF.
  destruct (set_unit_rel_flatten T γ Hfn Hmods _ _ _ _ HΔ HrA (set_valid_unit_rel T γ Hfn Hmods Hgw Θ Ξ Hμ _ _ HKF)) as (F1 & F2 & [HF1 HF2 E12]).
  exists F1, F2. constructor; [exact HF1 | exact HF2 | exact E12 | exact HKA | exact HKF |].
  intros κs _ ys x. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs modexp_member_proofs].
  rewrite unit_member_proofs_tele_out, List.rev_app_distr, tele_out_proofs_app. reflexivity.
Qed.

(** A body unit is its expansion. *)
Lemma set_rule_unit_eq_expand : forall Γ Δ Φ, set_unit_eq Θ Ξ T γ Γ (gu_open Δ Φ) (gu_open Δ Φ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ (gm_expand Φ) ->
    set_unit_eq Θ Ξ T γ Γ (gu_open Δ Φ) (gu_open Δ (gm_expand Φ)).
Proof.
  intros * HUe HUU. set_open. destruct HUe as (F & _ & [HF _ _ HK _]).
  pose proof (gm_noopen_expand Φ) as Hno. pose proof (gm_expand_noopen _ Hno) as Hee.
  assert (HD : forall Γ' ρ' n, set_interp_moddef T γ Γ' ρ' (md_body sm_open Φ) n -> set_interp_moddef T γ Γ' ρ' (md_body sm_open (gm_expand Φ)) n)
    by (intros * Hn; inversion Hn; subst; eapply set_interp_md_body; rewrite Hee; eassumption).
  assert (HPκ : forall κs ys x, unit_member_proofs γ κs (gu_open Δ Φ) ys x = unit_member_proofs γ κs (gu_open Δ (gm_expand Φ)) ys x).
  { intros κs ys x. rewrite !unit_member_proofs_tele_out. cbn [moddef_member_proofs].
    rewrite (proj2 (body_member_proofs_expand γ Φ _)). reflexivity. }
  assert (HP : forall ρ ys x, unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ Φ) ys x =
                             unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ)) ys x)
    by (intros; apply HPκ).
  pose proof (set_valid_unit_ctx T γ _ _ HK) as HΓ.
  set (F' := fun ρ => params_with_proofs (List.rev Δ) (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ))) (F ρ)).
  assert (HF' : set_modexp_denotes T γ Γ (me_lit (gu_open Δ (gm_expand Φ))) F').
  { apply (set_modexp_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ. constructor.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm. apply set_interp_me_lit_iff in Hm.
    inversion Hm as [? ? ? ? P m HPm HL]; subst.
    apply (set_interp_gunit_mk T γ _ _ _ _ (unit_member_proofs γ (env_slot_proofs γ ρ) (gu_open Δ (gm_expand Φ)))); [intros; reflexivity |].
    exact (set_interp_unit_params_moddef T γ _ _ _ _ _ _ (set_interp_unit_params_with_proofs T γ _ _ _ _ _ _ HL _) _ HD). }
  assert (E : forall ρ, set_env_in T γ Γ ρ -> set_module_eq γ (F ρ) (F' ρ)).
  { intros ρ Hρ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as Hm1. apply set_interp_me_lit_iff in Hm1.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ) as Hm2. apply set_interp_me_lit_iff in Hm2.
    inversion Hm1 as [? ? ? ? P1 m1 HP1 HL1]; subst. inversion Hm2 as [? ? ? ? P2 m2 HP2 HL2]; subst.
    pose proof HK as HK0. inversion HK0 as [| ? ? ? Φx [_ _ HΔ _ _ _ _ _ _ _ _] _ _ |]; subst;
      try (exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end).
    rewrite <- (List.app_nil_r (List.rev Δ)) in HL2.
    apply (set_unit_params_eq_app T γ Hfn Hmods (List.rev Δ) Γ ρ P1 P2 _ nil _ _ _ (List.Forall_rev HΔ) Hρ HL1 HL2).
    - intros ys x. rewrite HP1, HP2. apply HP.
    - intros ρ' n1 n2 Hρ' _ Hn1 Hn2. inversion Hn2; subst.
      match goal with Hd : set_interp_moddef _ _ _ _ _ n2 |- _ => inversion Hd; subst end. inversion Hn1; subst.
      rewrite Hee in *. constructor.
      match goal with Ha : set_interp_gmod _ _ _ _ (gm_expand Φ) ?ms1 _, Hb : set_interp_gmod _ _ _ _ (gm_expand Φ) ?ms2 _ |-
                      set_members_eq _ ?ms1 ?ms2 =>
        exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods))))))))
                _ _ _ _ _ Ha _ _ _ (set_env_rel_eq T γ _ _ _ Hρ') Hb)) end. }
  (* the expansion is a valid body *)
  assert (HK' : set_valid_unit T γ Γ (me_lit (gu_open Δ (gm_expand Φ)))).
  { inversion HK as [| ? ? ? Φx Hb Hsub Hop |]; subst;
      try (exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_not_lit _ _ _ Hq) end).
    destruct Hb as [_ Hx HΔ Hl HΓ' HC Hs Hsh Hshx _ _].
    pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. subst Φx.
    apply set_valid_unit_body with (Φx := gm_expand Φ); [| exact Hsub |].
    - constructor; [exact (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_right HUU)) | exact (body_xp_noopen _ _ _ _ Hno) | exact HΔ | exact Hl
                   | exact HΓ' | exact HC | exact Hs | exact Hshx | exact Hshx | | ].
      + exists F', F'. constructor; [exact HF' | exact HF' |].
        intros ρ Hρ. exact (set_modexp_denotes_unique _ _ _ _ _ HF' _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF' _ Hρ)).
      + intros k Ψ H Hk. rewrite (body_opens_noopen _ Hno) in Hk. destruct k; discriminate.
    - intros k Ψ H Hk. rewrite (body_opens_noopen _ Hno) in Hk. destruct k; discriminate. }
  exists F, F'. constructor; [exact HF | exact HF' | exact E | exact HK | exact HK' | intros κs _; exact (HPκ κs)].
Qed.

End Unit.
