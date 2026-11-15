(** * The Rules of Module Expressions

    The rules of [⊢ᵐ] and of members in the gluing model.  The lemmas they
    rest on are in [Modules/ModuleLemmas.v] and the other files of
    [Modules/]. *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup Paths DescTyping LookupSound.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Variables
  Modules.ModuleValues LogicalRelation.Instance Modules.ModexpInstances Modules.UnitEq Modules.UnitDeep Modules.Sel
  Modules.Mem Modules.DescDeep Modules.ModuleLemmas.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma glu_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A) ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊩ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_mem H x : A ).
Proof.
  intros * HH [HHg _] Hm Ht HA HAg HS HMt HMg Θ2 Ξ2 Hμ.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hgs.
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  destruct (HHg _ _ Hμ) as [HHi _ HHd]; split; [| exact HHd ].
  exact (@glu_rel_exp_member_under_sub _ _ _ _ Hgs Hg2 Hμ _ _ _ _ _ _ HH Hm Ht HA HS
           ltac:(eapply wf_mem; eassumption) HHi (proj1 (HAg _ _ Hμ)) (fun M HM => proj1 (HMg M HM _ _ Hμ))).
Qed.

Lemma glu_exp_eq_mem_cong :
  `( glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. intros * [HH _]; exact (glu_ctx_of_modexp _ _ _ _ HH). Qed.

Lemma glu_exp_eq_mem_delta :
  `( glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. intros * [HH _]; exact (glu_ctx_of_modexp _ _ _ _ HH). Qed.

Lemma glu_me_unit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     glu_modexp Θ Ξ Γ (me_unit fp) /\ glu_modexp Θ Ξ Γ (me_unit fp) ).
Proof.
  intros * HΓ HΓg Hu.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgs.
  assert (G : glu_modexp Θ Ξ Γ (me_unit fp)); [| exact (conj G G) ].
  intros Θ2 Ξ2 Hμ; destruct (HΓg _ _ Hμ) as [HΓt HΓd].
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  destruct TΦ as [T Φ].
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & HlΦ).
  constructor; [| exact I | exact HΓd ].
  apply (@glu_rel_modexp_under_sub_path_mod_of_source _ _ _ _ Hgs Hg2 Hμ _ _ mp T Φ (wf_me_unit _ _ _ _ _ HΓ Hu) Hq);
    [| | exact HΓt ].
  - apply (gc_loc_of_loc _ _ Hgs); destruct HlΦ as [Hl | (_ & _ & Hb & _)]; [ left | right ]; assumption.
  - intros Γ1; eexists; split; [ eapply mdenote_unit; eassumption | reflexivity ].
Qed.

Lemma glu_me_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     glu_modexp Θ Ξ Γ (me_var x) /\ glu_modexp Θ Ξ Γ (me_var x) ).
Proof.
  intros * HΓg Hx.
  assert (G : glu_modexp Θ Ξ Γ (me_var x)); [| exact (conj G G) ].
  intros Θ2 Ξ2 Hμ; destruct (HΓg _ _ Hμ) as [HΓt HΓd].
  constructor; [ exact (glu_rel_modexp_under_sub_var HΓt Hx) | exact I | exact HΓd ].
Qed.

Lemma glu_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     glu_unit_eq Θ Ξ Γ U U' ->
     glu_modexp Θ Ξ Γ (me_lit U) /\ glu_modexp Θ Ξ Γ (me_lit U') ).
Proof.
  intros * HU [HΓg HUg HU'g].
  pose proof (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU)) as Hgs.
  split; intros Θ2 Ξ2 Hμ; destruct (HΓg _ _ Hμ) as [HΓt HΓd];
    pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  - destruct (HUg _ _ Hμ) as [_ HUd _].
    exact (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ (wf_unit_eq_refl_left HU) HΓt HΓd HUd).
  - destruct (HU'g _ _ Hμ) as [_ HUd _].
    exact (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ (wf_unit_eq_refl_right HU) HΓt HΓd HUd).
Qed.

Lemma glu_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H' ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     mdesc_mod_tele R' = Some T' ->
     glu_modexp Θ Ξ Γ (me_mem H y) /\ glu_modexp Θ Ξ Γ (me_mem H' y) ).
Proof.
  intros * HH [HHg HH'g] Hm HT Hm' HT'.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hgs.
  pose proof (wf_modexp_eq_refl_left HH) as HHl; pose proof (wf_modexp_eq_refl_right HH) as HHr.
  split; intros Θ2 Ξ2 Hμ;
    pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  - destruct (HHg _ _ Hμ) as [HHi HHp HHd]; constructor; [| exact HHp | exact HHd ].
    exact (@glu_rel_modexp_under_sub_mem_of_source _ _ _ _ Hgs Hg2 Hμ _ _ _ _
             ltac:(eapply wf_me_mem; [ exact HHl | exact Hm | exact HT | exact Hm | exact HT ]) HHl Hm HHi).
  - destruct (HH'g _ _ Hμ) as [HHi HHp HHd]; constructor; [| exact HHp | exact HHd ].
    exact (@glu_rel_modexp_under_sub_mem_of_source _ _ _ _ Hgs Hg2 Hμ _ _ _ _
             ltac:(eapply wf_me_mem; [ exact HHr | exact Hm' | exact HT' | exact Hm' | exact HT' ]) HHr Hm' HHi).
Qed.

Lemma glu_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H' ->
     mdenote Θ Ξ Γ H R ->
     mdesc_mod_tele R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
     evaluated_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : B ->
     mdenote Θ Ξ Γ H' R' ->
     mdesc_mod_tele R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Srt' ->
     evaluated_sort Srt' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N' : B' ->
     glu_modexp Θ Ξ Γ (me_app H N) /\ glu_modexp Θ Ξ Γ (me_app H' N') ).
Proof.
  intros * HH [HHg HH'g] Hm HT Hv HB HS HN HNg Hm' HT' Hv' HB' HS' HN' HN'g.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hgs.
  split; intros Θ2 Ξ2 Hμ;
    pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  - exact (glu_modexp_at_target_app _ _ _ _ Hgs Hg2 Hμ _ _ _ _ _ _ _ _ (wf_modexp_eq_refl_left HH) (HHg _ _ Hμ)
             Hm HT Hv HB HS HN (proj1 (HNg _ _ Hμ))).
  - exact (glu_modexp_at_target_app _ _ _ _ Hgs Hg2 Hμ _ _ _ _ _ _ _ _ (wf_modexp_eq_refl_right HH) (HH'g _ _ Hμ)
             Hm' HT' Hv' HB' HS' HN' (proj1 (HN'g _ _ Hμ))).
Qed.

Lemma glu_me_delta_slot :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     glu_modexp Θ Ξ Γ (me_var x) /\ glu_modexp Θ Ξ Γ (me_lit U) ).
Proof.
  intros * HΓ HΓg Hx.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgs.
  assert (Hv : glu_modexp Θ Ξ Γ (me_var x) /\ glu_modexp Θ Ξ Γ (me_var x)) by (eapply glu_me_var; eassumption).
  split; [ exact (proj1 Hv) |].
  intros Θ2 Ξ2 Hμ; destruct (HΓg _ _ Hμ) as [HΓt HΓd].
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  exact (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hx) HΓt HΓd
           (glu_ctx_deep_lookup _ _ _ Hx HΓt HΓd)).
Qed.

Lemma glu_me_delta_sel :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y ->
     glu_modexp Θ Ξ Γ (me_mem H y) /\ glu_modexp Θ Ξ Γ (me_mem H y) ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod R = Some Rm ->
     glu_modexp Θ Ξ Γ (me_mem H y) /\ glu_modexp Θ Ξ Γ (mdesc_unit Rm) ).
Proof.
  intros * HHy [HHg _] Hm Hmd.
  pose proof (presup_modexp_eq_ctx HHy) as HΓs.
  pose proof (ctx_wf_gctx _ _ _ HΓs) as Hgs.
  split; [ exact HHg |]; intros Θ2 Ξ2 Hμ.
  pose proof (gctx_embedding_wf _ _ _ _ (glu_gctx_embedding_embedding _ _ _ _ Hμ)) as Hg2.
  destruct (HHg _ _ Hμ) as [HHi HHp HHd].
  pose proof (glu_rel_modexp_under_sub_ctx _ _ HHi) as HΓt.
  (** The selection's description is deep, so is its module part *)
  pose proof (@glu_desc_deep_of_source _ _ _ _ Hgs Hg2 Hμ _ _ _ Hm HHy HΓt HHd HHp) as HR.
  pose proof (proj1 (glu_desc_deep_mod _ _ _ Hmd) HR) as HRm.
  pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgs Hm) Hmd) as Hc.
  pose proof (mdesc_mod_is_mod _ _ Hmd) as Him.
  pose proof (proj1 (mdesc_unit_wf _ _ _ _ HΓs (desc_ok_mod _ _ Hgs _ _ _ (me_desc_ok _ _ _ _ _ _ HHy Hm) Hmd) Hc Him
                       (wf_mdenote_mod_xp _ _ _ _ _ _ _ HHy Hm Hmd))) as HU.
  destruct (@glu_mdesc_unit_of_deep _ _ _ _ Hgs Hg2 Hμ _ _ HRm Him Hc HU HΓt) as [HUi HUp].
  constructor; [ exact HUi | exact HUp | exact HHd ].
Qed.

Lemma glu_me_beta_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ) ->
     glu_unit_eq Θ Ξ Γ (gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ)) (gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     glu_modexp Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_body sm_open Φ))) N) /\
     glu_modexp Θ Ξ Γ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_body sm_open (gmod_sub Φ (sb_qn (length Δ) (Id,,N)))))) ).
Proof. intros; eapply glu_me_beta; eassumption. Qed.

Lemma glu_me_beta_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E) ->
     glu_unit_eq Θ Ξ Γ (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E)) (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : X ->
     glu_modexp Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) (md_alias E))) N) /\
     glu_modexp Θ Ξ Γ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (length Δ) (Id,,N)]ᵐ))) ).
Proof. intros; eapply glu_me_beta; eassumption. Qed.

Lemma glu_me_beta_alias0 :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E ->
     glu_modexp Θ Ξ Γ E /\ glu_modexp Θ Ξ Γ E ->
     frame_free_target Θ Ξ Γ E ->
     glu_modexp Θ Ξ Γ (me_lit (gu_mk nil (md_alias E))) /\ glu_modexp Θ Ξ Γ E ).
Proof.
  intros * HE [HEg _] Hff.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hgs.
  split; [| exact HEg ]; intros Θ2 Ξ2 Hμ.
  destruct (HEg _ _ Hμ) as [HEi HEp HEd].
  pose proof (glu_rel_modexp_under_sub_ctx _ _ HEi) as HΓt.
  pose proof (wf_modexp_eq_refl_left (wf_me_beta_alias0 _ _ _ _ HE Hff)) as HL.
  apply (glu_modexp_at_target_lit _ _ _ _ Hμ _ _ (unit_eq_of_full _ _ _ _ (proj1 (modexp_gen _ _ _ _ _ HL))) HΓt HEd).
  constructor; [ exact HΓt | exact HEi | exact HEp ].
Qed.

Lemma glu_me_sym :
  `( glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H' ->
     glu_modexp Θ Ξ Γ H' /\ glu_modexp Θ Ξ Γ H ).
Proof. intros * [H1 H2]; exact (conj H2 H1). Qed.

Lemma glu_me_trans :
  `( glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H' ->
     glu_modexp Θ Ξ Γ H' /\ glu_modexp Θ Ξ Γ H'' ->
     glu_modexp Θ Ξ Γ H /\ glu_modexp Θ Ξ Γ H'' ).
Proof. intros * [H1 _] [_ H3]; exact (conj H1 H3). Qed.
