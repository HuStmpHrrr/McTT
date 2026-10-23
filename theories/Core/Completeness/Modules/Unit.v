(** * Valid Units: Validity, Substitution, Instantiation, Abstraction

    A valid unit is valid in the PER model ([valid_unit_rel]) and moved along
    substitutions as the PER model asks ([valid_unit_links]).  Valid units and
    module expressions valid in what they denote stay so along
    substitutions built from valid parts ([valid_unit_modexp_gsub]); a valid literal
    with an outermost parameter, given an argument for it, is the valid
    literal instantiated ([valid_unit_beta]); a valid unit of a context extended by
    parameters, abstracted over them, is valid ([valid_unit_abs]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values UnitSubst ModexpRel.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.
  Hypothesis Hgf : valid_filed_mods Θm Ξm.

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

Lemma body_xp_target : forall Γ Φ Φx, body_xp Θm Ξm Γ Φ Φx -> body_xp gc_deps gc_stack Γ Φ Φx.
Proof. exact (proj1 (proj2 (proj2 (proj2 (mdenote_grow_all _ _ _ _ Hgm Hgw Hsub))))). Qed.

(** ** Valid Units Are Valid *)

Lemma valid_unit_lit_unit : forall Γ U, valid_unit Γ (me_lit U) -> Γ ⊨ᵘ U ≈ U.
Proof.
  intros * HK; inversion HK as [| ? Δ Φ Φx Hw Hx HΔ HΓ HC Hsl Hsh Hsx HU Hov Hos | ? Δ E Hw HΔ HΓ HΔΓ HU HE Hsm];
    subst; [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_lit _ _ _ Hq) end | |].
  - assert (Hsu : rel_unit_wf Γ (gu_open Δ Φ))
      by (eapply rel_unit_wf_body; [ exact HΔ | exact (body_xp_target _ _ _ Hx) | exact Hsh | exact Hsx | exact HC | exact Hov ]).
    constructor; [ exact HU | exact Hsu | exact Hsu ].
  - assert (Hsu : rel_unit_wf Γ (gu_mk Δ (md_alias E))) by (apply rel_unit_wf_alias; assumption).
    constructor; [ exact HU | exact Hsu | exact Hsu ].
Qed.

Lemma valid_unit_rel : forall Γ K, valid_unit Γ K -> Γ ⊨ᵐ K ≈ K.
Proof.
  intros * HK; destruct HK as [Γ p T Φ Ns _ Hgl HΓ Hs | | ]; try assumption.
  eapply filed_valid; eassumption.
Qed.

(** Member typing moves along related module expressions. *)
Lemma valid_mem_transport : forall Γ H K x A om, Γ ⊨ᵐ H ≈ K -> valid_mem Γ K x A om -> valid_mem Γ H x A om.
Proof.
  intros * HHK [HA HM HS]; constructor; [ exact HA | exact HM |].
  intros R HR ρ Hρ.
  destruct (HS _ HR _ Hρ) as [k a i RA Hk Ha HRA Hm Hred].
  destruct (rel_modexp_at _ _ _ _ _ HHK HR _ _ Hρ) as (h & k' & Hh & Hk' & Hhk).
  pose proof (functional_eval_modexp _ _ _ _ Hk' Hk) as ->.
  assert (HPA : PER RA) by (eapply per_elem_PER; exact HRA).
  apply mk_valid_mem_at with (vma_mod := h) (vma_typ := a) (vma_lvl := i) (vma_rel := RA); try assumption;
    [ eapply dmod_has_mem_resp; [ exact HPA | exact Hhk | exact Hm ] |].
  intros M HM0; destruct (Hred _ HM0) as [m r Hm0 Hr Hmr].
  destruct (Hm _ Hhk) as [r1 r2 Hr1 Hr2 Hrr].
  pose proof (functional_eval_sel _ _ _ _ Hr2 Hr) as ->.
  apply (mk_rel_mem_reduct _ _ _ _ _ m r1); [ exact Hm0 | exact Hr1 | etransitivity; [ exact Hmr | symmetry; exact Hrr ] ].
Qed.

(** ** Valid Units along Substitutions, in the PER Model *)

Lemma valid_unit_links : forall Γ U, valid_unit Γ (me_lit U) -> modexp_sub_rel Γ (me_lit U).
Proof.
  intros * HK; inversion HK as [| ? Δ Φ Φx Hw Hx HΔ HΓ HC Hsl Hsh Hsx HU Hov Hos | ? Δ E Hw HΔ HΓ HΔΓ HU HE Hsm];
    subst; [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_lit _ _ _ Hq) end | |];
    intros Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
  - eapply unit_sub_link_body; try eassumption.
    intros k Ψ H Hk; split; [ exact (Hov _ _ _ Hk) | exact (valid_modexp_kinds _ _ Hgm Hgf _ _ (Hos _ _ _ Hk)) ].
  - eapply unit_sub_link_alias; eassumption.
Qed.

(** The same under one parameter fewer. *)
Lemma valid_unit_links_unabs1 : forall Γ Δ X D, valid_unit Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) ->
    modexp_sub_rel (Γ ▹ X) (me_lit (gu_mk Δ D)).
Proof.
  intros * HK; inversion HK as [| ? Δ0 Φ Φx Hw Hx HΔ HΓ HC Hsl Hsh Hsx HU Hov Hos | ? Δ0 E Hw HΔ HΓ HΔΓ HU HE Hsm];
    subst; [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_lit _ _ _ Hq) end | |];
    intros Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
  - rewrite <- app_assoc in Hx, HC, Hov, Hos; cbn [List.app] in Hx, HC, Hov, Hos.
    eapply unit_sub_link_body; try eassumption.
    + exact (proj1 (tele_ass_app_inv _ _ HΔ)).
    + intros k Ψ H Hk; split; [ exact (Hov _ _ _ Hk) | exact (valid_modexp_kinds _ _ Hgm Hgf _ _ (Hos _ _ _ Hk)) ].
  - rewrite <- app_assoc in HΔΓ, HE; cbn [List.app] in HΔΓ, HE.
    eapply unit_sub_link_alias; [ exact (proj1 (tele_ass_app_inv _ _ HΔ)) | exact HΔΓ | exact HE | eassumption .. ].
Qed.

(** ** Valid Units along Substitutions Built from Valid Parts *)

Lemma ext_gsub : forall Ψ Δ Γ τ, ⊨ Ψ ++ Δ -> ⊢ Θm ⍮ Ξm ⍮ Ψ ++ Δ -> gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ ->
    ⊨ tele_sub Ψ τ ++ Γ /\ gsub (tele_sub Ψ τ ++ Γ) (sb_qn (length Ψ) τ) (Ψ ++ Δ) /\
    ⊢ Θm ⍮ Ξm ⍮ tele_sub Ψ τ ++ Γ /\ Θm ⍮ Ξm ⍮ tele_sub Ψ τ ++ Γ ⊢ˢ sb_qn (length Ψ) τ : Ψ ++ Δ.
Proof.
  intros * HC HwC Hg Hτ.
  destruct (rel_ctx_wf_gsub Θm Ξm Hgw Hgm Hsub _ _ _ _ HC HwC Hg (wf_sub_mod_compat _ _ _ _ _ Hτ)) as [H1 H2].
  pose proof (ctx_sub_wf_gen _ _ _ _ _ _ Hτ HwC) as Hw'.
  split; [ exact H1 |]; split; [ exact H2 |]; split; [ exact Hw' | apply wf_sub_ext; assumption ].
Qed.

(** The parts of a body, along a substitution built from valid parts, make
    a valid unit, once its literal is valid there. *)
Lemma valid_unit_body_sub : forall Δ Δu Φ Φx Γ τ,
    Θm ⍮ Ξm ⍮ Δ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu Φ ->
    body_xp Θm Ξm (Δu ++ Δ) Φ Φx -> tele_ass Δu -> ⊨ body_ctx Φx ++ Δu ++ Δ ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    (forall y Φ0 pv U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
       forall Γ0 τ0, gsub Γ0 τ0 (body_ctx Φ0 ++ Δu ++ Δ) -> Θm ⍮ Ξm ⍮ Γ0 ⊢ˢ τ0 : body_ctx Φ0 ++ Δu ++ Δ ->
       valid_unit Γ0 (me_lit U)[τ0]ᵐ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δu ++ Δ ⊨ᵐ H ≈ H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       forall Γ0 τ0, gsub Γ0 τ0 (Ψ ++ Δu ++ Δ) -> Θm ⍮ Ξm ⍮ Γ0 ⊢ˢ τ0 : Ψ ++ Δu ++ Δ -> valid_modexp Γ0 H[τ0]ᵐ) ->
    gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ (me_lit (gu_open Δu Φ))[τ]ᵐ ≈ (me_lit (gu_open Δu Φ))[τ]ᵐ ->
    Γ ⊨ᵐ (me_lit (gu_open Δu Φ))[τ]ᵐ ≈ (me_lit (gu_open Δu Φ))[τ]ᵐ ->
    valid_unit Γ (me_lit (gu_open Δu Φ))[τ]ᵐ.
Proof.
  intros Δ Δu Φ Φx Γ τ HU Hx HΔu HC Hs Hsx IHmods Hopv IHops Hg Hτ Hw' HK'.
  pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf; cbn [unit_full] in Hf.
  destruct Hf as (Φx0 & lv & Hx0 & HwCx & _).
  pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx0) as <-.
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΔs & HUs & _).
  rewrite gunit_scoped_mk in HUs; destruct HUs as [_ HDs]; cbn in HDs.
  pose proof (wf_ctx_scoped _ _ _ HwCx) as HCxs.
  assert (HΔCs : ctx_scoped 0 (Δu ++ Δ)) by exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HCxs)).
  pose proof (wf_sub_mod_compat _ _ _ _ _ Hτ) as Hc.
  pose proof (body_xp_sub _ _ (wf_gstack_closed _ _ Hgm) _ _ _ Hx HΔCs
                ltac:(rewrite length_app; exact (proj2 HDs)) _ _ (sub_mod_compat_ext Δu _ _ _ Hc)) as Hxσ.
  pose proof (ctx_app_wf_tail _ _ _ _ HwCx) as HwΔ.
  destruct (ext_gsub Δu Δ Γ τ (rel_ctx_wf_app_r _ _ HC) HwΔ Hg Hτ) as (HΔσ & HgΔ & HwΔσ & HτΔ).
  cbn [modexp_sub] in Hw', HK' |- *; rewrite gunit_sub_mk in Hw', HK' |- *; cbn [moddef_sub] in Hw', HK' |- *.
  apply (valid_unit_body _ _ _ _ _ (gmod_sub Φx (sb_qn (length Δu) τ))).
  1: exact Hw'.
  1: exact Hxσ.
  1: apply tele_ass_sub; exact HΔu.
  1: exact (proj1 (gsub_sem Hg)).
  1: { rewrite app_assoc in HC, HwCx.
       destruct (ext_gsub _ _ Γ τ HC HwCx Hg Hτ) as (HCσ & _).
       rewrite body_ctx_sub, app_assoc, <- tele_sub_app; exact HCσ. }
  1: { (* the modules, each in the body before it, then substituted *)
    intros y Φ0w pv Uw Hp.
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E & Hp0 & -> & HE).
    destruct E as [| pv0 U | | |]; cbn in HE; try discriminate; injection HE as -> ->.
    destruct (prefix_body_ctx _ _ _ (body_xp_nopens _ _ _ _ _ Hx) Hp0) as (X & HX); cbn [body_ctx] in HX.
    rewrite HX, <- !app_assoc in HC, HwCx; cbn [List.app] in HC, HwCx.
    pose proof (rel_ctx_wf_tail (rel_ctx_wf_app_r _ _ HC)) as HC0.
    pose proof (ctx_app_wf_tail _ _ (_ :: nil) _ (ctx_app_wf_tail _ _ _ _ HwCx)) as HwC0.
    rewrite app_assoc in HC0, HwC0.
    destruct (ext_gsub _ _ Γ τ HC0 HwC0 Hg Hτ) as (_ & Hg0 & _ & Hτ0).
    rewrite <- app_assoc in Hg0, Hτ0.
    pose proof (IHmods _ _ _ _ Hp0 _ _ Hg0 Hτ0) as HK0.
    rewrite body_ctx_sub, app_assoc, <- tele_sub_app.
    cbn [modexp_sub] in HK0.
    rewrite (gunit_sub_sb_eq U _ _ (sb_qn_add _ _ _)), <- length_body_ctx, <- length_app.
    exact HK0. }
  1, 2: apply body_shape_sub; assumption.
  1: exact HK'.
  all: intros k Ψw Hw0 Hk;
    rewrite (body_opens_sub _ _ _ _ _ Hx), List.nth_error_map in Hk;
    destruct (List.nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Ek; try discriminate;
    cbn in Hk; injection Hk as <- <-;
    destruct (body_opens_prefix _ _ _ _ _ Hx _ _ _ Ek) as [Ψr HΨr];
    rewrite HΨr, <- !app_assoc in HC, HwCx;
    rewrite (app_assoc Ψ Δu Δ) in HC, HwCx;
    destruct (ext_gsub (Ψ ++ Δu) Δ Γ τ (rel_ctx_wf_app_r _ _ HC) (ctx_app_wf_tail _ _ _ _ HwCx) Hg Hτ) as (_ & Hgo & _ & Hτo);
    rewrite <- app_assoc in Hgo, Hτo;
    rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)), tele_sub_app, <- app_assoc, length_app in *.
  + exact (rel_modexp_under_ctx_gsub Hgo (Hopv _ _ _ Ek)).
  + exact (IHops _ _ _ Ek _ _ Hgo Hτo).
Qed.

Lemma valid_unit_alias_sub : forall Δ Δu E Γ τ,
    Θm ⍮ Ξm ⍮ Δ ⊢ᵘ gu_mk Δu (md_alias E) ≈ gu_mk Δu (md_alias E) ->
    tele_ass Δu -> ⊨ Δu ++ Δ -> Δu ++ Δ ⊨ᵐ E ≈ E ->
    (forall Γ0 τ0, gsub Γ0 τ0 (Δu ++ Δ) -> Θm ⍮ Ξm ⍮ Γ0 ⊢ˢ τ0 : Δu ++ Δ -> valid_modexp Γ0 E[τ0]ᵐ) ->
    gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ ->
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ (me_lit (gu_mk Δu (md_alias E)))[τ]ᵐ ≈ (me_lit (gu_mk Δu (md_alias E)))[τ]ᵐ ->
    Γ ⊨ᵐ (me_lit (gu_mk Δu (md_alias E)))[τ]ᵐ ≈ (me_lit (gu_mk Δu (md_alias E)))[τ]ᵐ ->
    valid_unit Γ (me_lit (gu_mk Δu (md_alias E)))[τ]ᵐ.
Proof.
  intros Δ Δu E Γ τ HU HΔu HΔΔ HE IHE Hg Hτ Hw' HK'.
  pose proof (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as Hf; cbn [unit_full] in Hf.
  destruct Hf as (HwΔ & _ & _).
  destruct (ext_gsub Δu Δ Γ τ HΔΔ HwΔ Hg Hτ) as (HΔσ & HgΔ & HwΔσ & HτΔ).
  cbn [modexp_sub] in Hw', HK' |- *; rewrite gunit_sub_mk in Hw', HK' |- *; cbn [moddef_sub] in Hw', HK' |- *.
  apply valid_unit_alias; [ exact Hw' | apply tele_ass_sub; exact HΔu | exact (proj1 (gsub_sem Hg)) | exact HΔσ | exact HK'
                  | exact (rel_modexp_under_ctx_gsub HgΔ HE) | exact (IHE _ _ HgΔ HτΔ) ].
Qed.

Lemma valid_unit_modexp_gsub :
  (forall Δ K, valid_unit Δ K -> forall Γ τ, gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ -> valid_unit Γ K[τ]ᵐ) /\
  (forall Δ H, valid_modexp Δ H -> forall Γ τ, gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ -> valid_modexp Γ H[τ]ᵐ).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Δ p T Φ Ns Hw Hgl HΔ Hs Γ τ Hg Hτ.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hτ) as Hw'.
    rewrite me_apps_sub, qname_mod_sub in Hw' |- *.
    eapply valid_unit_filed; [ exact Hw' | exact Hgl | exact (proj1 (gsub_sem Hg)) |].
    destruct Hs as [T1 T2 -> Hl Ha Hsc HN].
    apply (mk_valid_args _ _ _ T1 T2); [ reflexivity | rewrite length_map; exact Hl | exact Ha | exact Hsc |].
    intros k N A HNk HAk.
    rewrite List.nth_error_map in HNk; destruct (nth_error Ns k) as [N0 |] eqn:HN0; [| discriminate ]; injection HNk as <-.
    rewrite <- (tele_insts_sub T2 0 Id Id τ Ns Ha Hsc ltac:(intros; lia)), List.nth_error_map in HAk.
    destruct (nth_error (tele_insts T2 Id Ns) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HAk as <-.
    exact (rel_exp_under_ctx_gsub Hg (HN _ _ _ HN0 HA0)).
  - (* a body *)
    intros Δ Δu Φ Φx Hw Hx HΔu HΔ HC Hsl IHsl Hs Hsx HK Hopv Hops IHops Γ τ Hg Hτ.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
    exact (valid_unit_body_sub _ _ _ _ _ _ (unit_eq_of_full _ _ _ _ Hf) Hx HΔu HC Hs Hsx IHsl Hopv IHops Hg Hτ
             (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hτ) (rel_modexp_under_ctx_gsub Hg HK)).
  - (* an alias *)
    intros Δ Δu E Hw HΔu HΔ HΔΔ HK HE Hsmt IHE Γ τ Hg Hτ.
    pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
    exact (valid_unit_alias_sub _ _ _ _ _ (unit_eq_of_full _ _ _ _ Hf) HΔu HΔΔ HE IHE Hg Hτ
             (sub_preserves_modexp _ _ _ _ _ _ _ Hw Hτ) (rel_modexp_under_ctx_gsub Hg HK)).
  - (* a module expression equal to a valid unit *)
    intros Δ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK Γ τ Hg Hτ.
    pose proof (valid_unit_wf _ _ _ _ HK) as HwK.
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HwH) as (HΔs & HHs & _).
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HwK) as (_ & HKs & _).
    pose proof (wf_sub_mod_compat _ _ _ _ _ Hτ) as Hc.
    pose proof (wf_gstack_closed _ _ Hgm) as Hcl.
    eapply (valid_modexp_intro _ _ _ _ (ds_sub R τ) (ds_sub Rm τ) K[τ]ᵐ (ds_sub RK τ)).
    + exact (sub_preserves_modexp _ _ _ _ _ _ _ HwH Hτ).
    + exact (mdenote_sub _ _ Hcl _ _ _ HmH HΔs HHs _ _ Hc).
    + apply ds_mod_sub; exact HmodH.
    + exact (rel_modexp_under_ctx_gsub Hg HHK).
    + exact (IHK _ _ Hg Hτ).
    + exact (mdenote_sub _ _ Hcl _ _ _ HmK HΔs HKs _ _ Hc).
    + apply ds_mod_sub; exact HmodK.
Qed.

Corollary valid_unit_gsub : forall Δ K Γ τ, valid_unit Δ K -> gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ -> valid_unit Γ K[τ]ᵐ.
Proof. intros * HK Hg Hτ; exact (proj1 valid_unit_modexp_gsub _ _ HK _ _ Hg Hτ). Qed.

Corollary valid_modexp_gsub : forall Δ H Γ τ, valid_modexp Δ H -> gsub Γ τ Δ -> Θm ⍮ Ξm ⍮ Γ ⊢ˢ τ : Δ -> valid_modexp Γ H[τ]ᵐ.
Proof. intros * HH Hg Hτ; exact (proj2 valid_unit_modexp_gsub _ _ HH _ _ Hg Hτ). Qed.

(** ** Valid Units Given an Argument *)

Lemma valid_unit_beta : forall Γ T1 X D N i, valid_unit Γ (me_lit (gu_mk (T1 ++ ce_ass X :: nil) D)) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ X : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    valid_unit Γ (me_lit (gu_mk T1 D)[Id,,N]ᵘ).
Proof.
  intros * HK HXw HNw HN.
  pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HΓ.
  pose proof (valid_unit_wf _ _ _ _ HK) as Hw.
  pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
  pose proof (unit_full_unabs _ _ _ (ce_ass X :: nil) T1 D Hf) as Hf1; cbn [List.app] in Hf1.
  pose proof (unit_eq_of_full _ _ _ _ Hf1) as HU1.
  pose proof (unit_full_beta _ _ _ _ _ _ _ Hf HNw) as HUNw.
  pose proof (wf_sub_single _ _ _ _ _ _ HXw HNw) as Hτ.
  destruct (presup_rel_exp_under_ctx HN) as [j HX].
  assert (Hg : gsub Γ (Id,,N) (Γ ▹ X)) by (eapply gsub_ass; [ constructor; exact HΓ | exact HX | rewrite exp_sub_id; exact HN ]).
  pose proof (rel_lit_beta Γ T1 X D N j HΓ (valid_unit_rel _ _ HK) (valid_unit_links_unabs1 _ _ _ _ HK) HX HN) as HKN.
  pose proof (wf_me_lit _ _ _ _ _ HUNw) as HwN.
  inversion HK as [| ? Δ Φ Φx Hw0 Hx HΔ HΓ0 HC Hsl Hsh Hsx HU Hov Hos | ? Δ E Hw0 HΔ HΓ0 HΔΓ HU HE Hsm];
    subst; [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_lit _ _ _ Hq) end | |].
  - (* a body *)
    change (valid_unit Γ (me_lit (gu_open T1 Φ))[Id,,N]ᵐ).
    rewrite <- app_assoc in Hx, HC, Hsl, Hov, Hos; cbn [List.app] in Hx, HC, Hsl, Hov, Hos.
    eapply (valid_unit_body_sub (Γ ▹ X)); [ exact HU1 | exact Hx | exact (proj1 (tele_ass_app_inv _ _ HΔ)) | exact HC | exact Hsh
                                   | exact Hsx | | exact Hov | | exact Hg | exact Hτ | exact HwN | exact HKN ].
    + intros * Hp * Hg0 Hτ0; exact (valid_unit_gsub _ _ _ _ (Hsl _ _ _ _ Hp) Hg0 Hτ0).
    + intros * Hk * Hg0 Hτ0; exact (valid_modexp_gsub _ _ _ _ (Hos _ _ _ Hk) Hg0 Hτ0).
  - (* an alias *)
    change (valid_unit Γ (me_lit (gu_mk T1 (md_alias E)))[Id,,N]ᵐ).
    rewrite <- app_assoc in HΔΓ, HE, Hsm; cbn [List.app] in HΔΓ, HE, Hsm.
    eapply (valid_unit_alias_sub (Γ ▹ X)); [ exact HU1 | exact (proj1 (tele_ass_app_inv _ _ HΔ)) | exact HΔΓ | exact HE
                                    | | exact Hg | exact Hτ | exact HwN | exact HKN ].
    intros * Hg0 Hτ0; exact (valid_modexp_gsub _ _ _ _ Hsm Hg0 Hτ0).
Qed.

(** ** Valid Units Abstracted over Parameters *)

Lemma closure_walk : forall Δ Γ Δy D RΓ, tele_ass Δ -> ⊨ Δ ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    Δ ++ Γ ⊨ᵐ me_lit (gu_mk Δy D) ≈ me_lit (gu_mk Δy D) ->
    forall ρ ρ', RΓ ρ ρ' -> rel_mexp (me_lit (gu_mk (Δy ++ Δ) D)) ρ (me_lit (gu_mk (Δy ++ Δ) D)) ρ'.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HC HΓ HU ρ ρ' Hρ; cbn [List.app] in *.
  - rewrite app_nil_r; exact (unit_chain_at HU HΓ _ _ Hρ).
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [A ->] _]; subst.
    rewrite <- app_assoc in HC, HU; cbn [List.app] in HC, HU.
    destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [i HA].
    pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
    destruct (rel_exp_of_typ_inversion_simple_at HΓ HA _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    rewrite app_assoc.
    apply (mk_rel_mexp _ _ _ _ (dm_local ((Δy ++ Δ0) ++ ce_ass A :: nil) D ρ) (dm_local ((Δy ++ Δ0) ++ ce_ass A :: nil) D ρ'));
      [ apply lit_params_val | apply lit_params_val |].
    assert (Hstep : forall c c', Ra c c' -> rel_mexp (me_lit (gu_mk (Δy ++ Δ0) D)) (ρ ↦ c) (me_lit (gu_mk (Δy ++ Δ0) D)) (ρ' ↦ c')).
    { intros c c' Hc; apply (IH (Γ ▹ A) _ _ _ HΔ0 HC HΓA HU).
      split; [ exact Hρ | eapply per_head_of; [ exact Ha | exact Ha' | exact HRa | exact Hc ] ]. }
    eapply (per_dmod_fun Ra); [ constructor; exact Ha | constructor; exact Ha' | exact HRa | | |].
    + intros c c' Hc; destruct (Hstep _ _ Hc) as [hc _ Hhc _ _]; exists hc; apply eval_appm_local, eval_me_lit_iff; exact Hhc.
    + intros c c' Hc; destruct (Hstep _ _ Hc) as [_ hc' _ Hhc' _]; exists hc'; apply eval_appm_local, eval_me_lit_iff; exact Hhc'.
    + intros c c' hc hc' Hc Hhc Hhc'.
      destruct (Hstep _ _ Hc) as [g g' Hg Hg' Hgg].
      inversion Hhc; subst; inversion Hhc'; subst.
      repeat match goal with Hl : _ ++ _ = _ ++ _ |- _ => apply app_inj_tail in Hl as [-> [= ->]] end.
      apply eval_me_lit_iff in Hg, Hg'.
      rewrite (functional_eval_close _ _ _ _ _ Hg ltac:(eassumption)), (functional_eval_close _ _ _ _ _ Hg' ltac:(eassumption)) in Hgg.
      exact Hgg.
Qed.

Lemma valid_unit_abs : forall Δ Γ U, valid_unit (Δ ++ Γ) (me_lit U) -> tele_ass Δ -> valid_unit Γ (me_lit (gunit_abs Δ U)).
Proof.
  intros * HK HΔ.
  pose proof (valid_unit_rel _ _ HK) as HU.
  pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HΓ.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  pose proof (valid_unit_wf _ _ _ _ HK) as Hw.
  pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
  pose proof (wf_me_lit _ _ _ _ _ (unit_eq_of_full _ _ _ _ (unit_full_abs _ _ _ _ _ Hf HΔ))) as Hw'.
  assert (Hat : forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ ρ', R ρ ρ' ->
             rel_mexp (me_lit (gunit_abs Δ U)) ρ (me_lit (gunit_abs Δ U)) ρ').
  { intros R HR ρ ρ' Hρ.
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct U as [Δy D]; cbn [gunit_abs].
    exact (closure_walk _ _ _ _ _ HΔ HC HRΓ HU _ _ (proj1 (E _ _) Hρ)). }
  inversion HK as [| ? Δy Φ Φx Hw0 Hx HΔy HΓ0 HCx Hsl Hsh Hsx HU0 Hov Hos | ? Δy E Hw0 HΔy HΓ0 HΔΓ HU0 HE Hsm];
    subst; [ exfalso; match goal with Hq : me_apps _ _ = me_lit _ |- _ => exact (me_apps_qname_lit _ _ _ Hq) end | |];
    cbn [gunit_abs] in *.
  - assert (HL : modexp_sub_rel Γ (me_lit (gu_open (Δy ++ Δ) Φ))).
    { intros Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
      eapply unit_sub_link_body; [ apply List.Forall_app; split; assumption | rewrite <- app_assoc; exact Hx | exact Hsh | exact Hsx
                                 | rewrite <- app_assoc; exact HCx | | eassumption .. ].
      intros k Ψ H Hk; rewrite <- app_assoc.
      split; [ exact (Hov _ _ _ Hk) | exact (valid_modexp_kinds _ _ Hgm Hgf _ _ (Hos _ _ _ Hk)) ]. }
    eapply valid_unit_body; [ exact Hw' | rewrite <- app_assoc; exact Hx | apply List.Forall_app; split; assumption | exact HΓ
                    | rewrite <- app_assoc; exact HCx | rewrite <- app_assoc; exact Hsl | exact Hsh | exact Hsx
                    | exact (rel_modexp_of_links _ _ _ HΓ HL HL Hat)
                    | intros * Hk; rewrite <- app_assoc; exact (Hov _ _ _ Hk)
                    | intros * Hk; rewrite <- app_assoc; exact (Hos _ _ _ Hk) ].
  - assert (HL : modexp_sub_rel Γ (me_lit (gu_mk (Δy ++ Δ) (md_alias E)))).
    { intros Γ' R' σ σ' ρ ρσ HΓ' Hσ Hρ Hev.
      eapply unit_sub_link_alias; [ apply List.Forall_app; split; assumption | rewrite <- app_assoc; exact HΔΓ
                                  | rewrite <- app_assoc; exact HE | eassumption .. ]. }
    eapply valid_unit_alias; [ exact Hw' | apply List.Forall_app; split; assumption | exact HΓ | rewrite <- app_assoc; exact HΔΓ
                     | exact (rel_modexp_of_links _ _ _ HΓ HL HL Hat) | rewrite <- app_assoc; exact HE | rewrite <- app_assoc; exact Hsm ].
Qed.

End Fixed_GCtx.
