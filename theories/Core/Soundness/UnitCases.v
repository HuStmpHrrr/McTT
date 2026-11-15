(** * The Rules of Extensions and Units

    The rules of [⊢ˣ] (equal extensions) and of [⊢ᵘ] (equal units) in the
    gluing model.  The lemmas they rest on are in [Modules/Extensions.v]
    and [Modules/UnitEq.v]. *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Instance Modules.Extensions Modules.UnitEq.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma glu_ext_eq_nil :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ ⋅ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ ⋅ ).
Proof. intros * HΓ; split; intros Θ2 Ξ2 Hμ; exact (HΓ _ _ Hμ). Qed.

(** An assumption: its type at a sort of its kind, on each side. *)
Lemma glu_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Srt' ->
     sort_kind Srt' κ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▹{κ} A) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▹{κ} A') ).
Proof.
  intros * [HΨ HΨ'] HA HS HA' HS'; split; intros Θ2 Ξ2 Hμ.
  - destruct (HΨ _ _ Hμ) as [He Hd]; split; [ split; [ exact He | exists Srt; split; [ exact HS | exact (proj1 (HA _ _ Hμ)) ] ] |].
    apply glu_ctx_deep_cons_term; [ reflexivity | exact Hd ].
  - destruct (HΨ' _ _ Hμ) as [He Hd]; split; [ split; [ exact He | exists Srt'; split; [ exact HS' | exact (proj1 (HA' _ _ Hμ)) ] ] |].
    apply glu_ctx_deep_cons_term; [ reflexivity | exact Hd ].
Qed.

(** A definition: its type at a sort of types and its body at the type, on
    each side. *)
Lemma glu_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Srt' ->
     type_sort Srt' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▸ A ≔ M) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▸ A' ≔ M') ).
Proof.
  intros * [HΨ HΨ'] HA HS HA' HS' HM HM'; split; intros Θ2 Ξ2 Hμ.
  - destruct (HΨ _ _ Hμ) as [He Hd]; split; [ split; [ exact He |] |].
    + exists Srt; constructor; [ exact HS | exact (proj1 (HA _ _ Hμ)) | exact (proj1 (HM _ _ Hμ)) ].
    + apply glu_ctx_deep_cons_term; [ reflexivity | exact Hd ].
  - destruct (HΨ' _ _ Hμ) as [He Hd]; split; [ split; [ exact He |] |].
    + exists Srt'; constructor; [ exact HS' | exact (proj1 (HA' _ _ Hμ)) | exact (proj1 (HM' _ _ Hμ)) ].
    + apply glu_ctx_deep_cons_term; [ reflexivity | exact Hd ].
Qed.

(** A body unit: each side's expansion's context over its parameters is an
    extension the rule glues. *)
Lemma glu_unit_eq_body :
  `( body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx ++ Δ) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx ++ Δ) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx' ++ Δ') /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (body_ctx Φx' ++ Δ') ->
     glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ' Φ') ).
Proof.
  intros * HΦx HΦx' [HΔ _] [HB _] [HB' _].
  apply body_xp_expand in HΦx, HΦx'; subst Φx Φx'.
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - destruct (HB _ _ Hμ) as [HBg HBd]; rewrite <- app_assoc in HBd.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_body_inst _ _ _ _ HBg _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; split; [ exact HBg | exact (glu_gmod_units_deep_of_ctx _ _ HBd) ].
  - destruct (HB' _ _ Hμ) as [HBg HBd]; rewrite <- app_assoc in HBd.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_body_inst _ _ _ _ HBg _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; split; [ exact HBg | exact (glu_gmod_units_deep_of_ctx _ _ HBd) ].
Qed.

(** An alias: each side's parameters are an extension the rule glues, and
    each side's target over them a module expression it glues. *)
Lemma glu_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ' ->
     glu_modexp Θ Ξ (Δ ++ Γ) E /\ glu_modexp Θ Ξ (Δ ++ Γ) E' ->
     glu_modexp Θ Ξ (Δ' ++ Γ) E' /\ glu_modexp Θ Ξ (Δ' ++ Γ) E' ->
     glu_unit_eq Θ Ξ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ' (md_alias E')) ).
Proof.
  intros * [HΔ HΔ'] [HE _] [HE' _].
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - destruct (HE _ _ Hμ) as [HEi HEp _].
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg HEi _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg | exact HEi | exact HEp ].
  - destruct (HΔ' _ _ Hμ) as [HΔg' _]; destruct (HE' _ _ Hμ) as [HEi HEp _].
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg' HEi _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg' | exact HEi | exact HEp ].
Qed.

(** An alias of a literal: the alias by its parameters and its target, the
    literal, glued at the instances by the construction
    ([glu_rel_modexp_under_sub_lit]); the literal over both telescopes by
    the literal, glued at the instance lifted through the alias's
    parameters. *)
Lemma glu_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     glu_unit_eq Θ Ξ (Δ ++ Γ) (gu_mk Δ' D) (gu_mk Δ' D) ->
     glu_unit_eq Θ Ξ Γ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) (gu_mk (Δ' ++ Δ) D) ).
Proof.
  intros * [HΔ _] HUt [HUc HU _].
  constructor; intros Θ2 Ξ2 Hμ; destruct (HΔ _ _ Hμ) as [HΔg HΔd].
  - split; [ exact (glu_rel_ext_under_sub_ctx HΔg) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
  - glu_gctx_embedding_wf.
    destruct (HUc _ _ Hμ) as [HUcg _]; destruct (HU _ _ Hμ) as [HUi HUd _].
    pose proof (glu_rel_modexp_under_sub_lit HUcg (Hwu _ _ _ HUt) HUi) as HL.
    constructor; [ intros Γ' τ Hτ; exact (glu_unit_at_alias_inst _ _ _ HΔg HL _ _ Hτ) | | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    cbn [glu_unit_deep]; constructor; [ exact HΔg | exact HL | cbn [glu_modexp_parts_deep]; exact HUd ].
  - destruct (HU _ _ Hμ) as [HUi HUd _].
    constructor; [ intros Γ' τ Hτ | exact (glu_unit_deep_params_join _ _ _ _ HΔg HUd) | exact (glu_ctx_deep_suffix _ _ HΔd) ].
    pose proof (glu_rel_ext_under_sub_inst HΔg _ _ Hτ) as Hτ'.
    pose proof (HUi _ _ Hτ') as H.
    rewrite gunit_sub_mk in H |- *.
    rewrite tele_sub_app, List.length_app, <- (moddef_sub_sb_eq _ _ _ (sb_qn_add _ _ _)).
    apply glu_unit_at_flatten; [| exact (glu_rel_ext_under_renaming_of_inst HΔg Hτ) | exact H ].
    destruct (glu_rel_sub_inst_ctx _ _ _ Hτ') as [Sb HSb]; exact (glu_ctx_env_wf_ctx HSb).
Qed.

(** A body and its expansion: the expansion's context is the body's, and
    its module entries are the body's and those of its opens' fragments. *)
Lemma glu_unit_eq_expand :
  `( glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ Φ) ->
     glu_unit_eq Θ Ξ Γ (gu_open Δ Φ) (gu_open Δ (gm_expand Φ)) ).
Proof.
  intros * [HΓ HU _]; constructor; [ exact HΓ | exact HU |].
  intros Θ2 Ξ2 Hμ; destruct (HU _ _ Hμ) as [HUi HUd HUcd]; constructor; [ intros Γ' τ Hτ | | exact HUcd ].
  - pose proof (HUi _ _ Hτ) as H.
    rewrite gunit_sub_mk in H |- *; cbn [moddef_sub glu_unit_at] in H |- *.
    destruct H as [H1 H2]; split.
    + rewrite !gm_expand_sub in *; rewrite (gm_expand_noopen _ (gm_noopen_expand _)); exact H1.
    + rewrite <- gm_expand_sub; exact (glu_gmod_units_expand _ _ H2).
  - cbn [glu_unit_deep] in HUd |- *; destruct HUd as [H1 H2]; split.
    + rewrite (gm_expand_noopen _ (gm_noopen_expand _)); exact H1.
    + exact (glu_gmod_units_deep_expand _ _ H2).
Qed.

Lemma glu_unit_eq_sym :
  `( glu_unit_eq Θ Ξ Γ U U' ->
     glu_unit_eq Θ Ξ Γ U' U ).
Proof. intros * [HΓ HU HU']; constructor; assumption. Qed.

Lemma glu_unit_eq_trans :
  `( glu_unit_eq Θ Ξ Γ U U' ->
     glu_unit_eq Θ Ξ Γ U' U'' ->
     glu_unit_eq Θ Ξ Γ U U'' ).
Proof. intros * [HΓ HU _] [_ _ HU'']; constructor; assumption. Qed.

Lemma glu_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     glu_unit_eq Θ Ξ (Ψ ++ Γ) U U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     glu_unit_eq Θ Ξ (Ψ' ++ Γ) U' U' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▹ₘ U) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▹ₘ U') ).
Proof.
  intros * [HΨ HΨ'] HUU [_ HU _] HU' [_ HU'g _].
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HUw.
  split; intros Θ2 Ξ2 Hμ; glu_gctx_embedding_wf.
  - destruct (HΨ _ _ Hμ) as [HΨg HΨd]; destruct (HU _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg | split; [ exact (Hwu _ _ _ HUw) | exact HUi ] ] |].
    exact (glu_ctx_deep_cons_unit (ce_mod U) _ U eq_refl HUd HΨd).
  - destruct (HΨ' _ _ Hμ) as [HΨg HΨd]; destruct (HU'g _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg | split; [ exact (Hwu _ _ _ HU') | exact HUi ] ] |].
    exact (glu_ctx_deep_cons_unit (ce_mod U') _ U' eq_refl HUd HΨd).
Qed.

Lemma glu_ext_eq_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E') ->
     glu_unit_eq Θ Ξ (Ψ ++ Γ) (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E')) ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ gu_mk nil (md_alias E') ≈ gu_mk nil (md_alias E') ->
     glu_unit_eq Θ Ξ (Ψ' ++ Γ) (gu_mk nil (md_alias E')) (gu_mk nil (md_alias E')) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▸ₘ A' ≔ M' ‖ gu_mk nil (md_alias E')) ).
Proof.
  intros * [HΨ HΨ'] HA HM HA' HM' HUU [_ HU _] HU' [_ HU'g _].
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HUw.
  split; intros Θ2 Ξ2 Hμ; glu_gctx_embedding_wf.
  - destruct (HΨ _ _ Hμ) as [HΨg HΨd]; destruct (HU _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg |] |].
    + do 2 eexists; constructor; [ reflexivity | exact (proj1 (HA _ _ Hμ)) | exact (proj1 (HM _ _ Hμ)) | exact (Hwu _ _ _ HUw) | exact HUi ].
    + exact (glu_ctx_deep_cons_unit (ce_dm A M (gu_mk nil (md_alias E))) _ _ eq_refl HUd HΨd).
  - destruct (HΨ' _ _ Hμ) as [HΨg HΨd]; destruct (HU'g _ _ Hμ) as [HUi HUd _].
    split; [ cbn; split; [ exact HΨg |] |].
    + do 2 eexists; constructor; [ reflexivity | exact (proj1 (HA' _ _ Hμ)) | exact (proj1 (HM' _ _ Hμ)) | exact (Hwu _ _ _ HU') | exact HUi ].
    + exact (glu_ctx_deep_cons_unit (ce_dm A' M' (gu_mk nil (md_alias E'))) _ _ eq_refl HUd HΨd).
Qed.
