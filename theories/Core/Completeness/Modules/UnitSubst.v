(** * Semantic Contexts and Units along Substitutions Built from Valid Parts

    A semantically well-formed extension of a context, read along a
    substitution built from valid parts ([gsub]), is semantically well
    formed over the substitution's domain, and the substitution lifted past
    it is again built from valid parts; a unit valid in its parts is so
    along such a substitution.  The extension is read syntactically too, for
    its scoping: the expansion of a body is moved along the substitution as
    the syntax does ([body_xp_sub]). *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
  Hypothesis Hsub : gc_sub Θm Ξm gc_deps gc_stack.

Scheme rel_ctx_wf_mut_ind := Induction for rel_ctx_wf Sort Prop
with rel_unit_wf_mut_ind := Induction for rel_unit_wf Sort Prop.
Combined Scheme rel_ctx_wf_unit_ind from rel_ctx_wf_mut_ind, rel_unit_wf_mut_ind.

(** The expansion of a valid body, read at the source, is the one at the
    target. *)
Lemma body_xp_src_tgt : forall Γ Φ Φx Φx', body_xp Θm Ξm Γ Φ Φx -> body_xp gc_deps gc_stack Γ Φ Φx' -> Φx = Φx'.
Proof.
  intros * H1 H2.
  pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_grow_all _ _ _ _ Hgm Hgw Hsub)))) _ _ _ H1) as H1'.
  exact (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgw)))) _ _ _ H1' _ H2).
Qed.

Lemma tele_sub_cons : forall e Ψ σ, tele_sub (e :: Ψ) σ = centry_sub e (sb_qn (length Ψ) σ) :: tele_sub Ψ σ.
Proof. reflexivity. Qed.

Lemma rel_ctx_wf_unit_gsub_all :
  (forall C, ⊨ C -> forall Ψ2 Ψ Δ, C = Ψ2 ++ Ψ ++ Δ -> ⊢ Θm ⍮ Ξm ⍮ C ->
     forall Γ τ, gsub Γ τ Δ -> sub_mod_compat τ Γ Δ ->
     ⊨ tele_sub Ψ τ ++ Γ /\ gsub (tele_sub Ψ τ ++ Γ) (sb_qn (length Ψ) τ) (Ψ ++ Δ)) /\
  (forall C U, rel_unit_wf C U -> ⊢ Θm ⍮ Ξm ⍮ C ▹ₘ U ->
     forall Γ τ, gsub Γ τ C -> sub_mod_compat τ Γ C -> rel_unit_wf Γ U[τ]ᵘ).
Proof.
  apply rel_ctx_wf_unit_ind.
  - (* the empty context *)
    intros Ψ2 Ψ Δ Heq _ Γ τ Hg _.
    destruct Ψ2, Ψ, Δ; try discriminate; cbn; split; [ exact (proj1 (gsub_sem Hg)) | exact Hg ].
  - (* an assumption *)
    intros C A i R HC IHC HR HA Ψ2 Ψ Δ Heq HwC Γ τ Hg Hc.
    destruct Ψ2 as [| e Ψ2]; cbn [List.app] in Heq.
    + destruct Ψ as [| e Ψ]; cbn [List.app] in Heq |- *.
      * subst Δ; split; [ exact (proj1 (gsub_sem Hg)) | exact Hg ].
      * injection Heq as <- ->.
        destruct (IHC nil Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc) as [HΓ' Hg'].
        pose proof (rel_exp_under_ctx_gsub Hg' HA) as HA'; cbn in HA'.
        rewrite tele_sub_cons; cbn [centry_sub List.app].
        split; [ eapply rel_ctx_wf_extend; eassumption | eapply gsub_q; eassumption ].
    + injection Heq as <- ->.
      exact (IHC Ψ2 Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc).
  - (* a definition *)
    intros C A M i R HC IHC HR HA HM Ψ2 Ψ Δ Heq HwC Γ τ Hg Hc.
    destruct Ψ2 as [| e Ψ2]; cbn [List.app] in Heq.
    + destruct Ψ as [| e Ψ]; cbn [List.app] in Heq |- *.
      * subst Δ; split; [ exact (proj1 (gsub_sem Hg)) | exact Hg ].
      * injection Heq as <- ->.
        destruct (IHC nil Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc) as [HΓ' Hg'].
        pose proof (rel_exp_under_ctx_gsub Hg' HA) as HA'; cbn in HA'.
        pose proof (rel_exp_under_ctx_gsub Hg' HM) as HM'.
        rewrite tele_sub_cons; cbn [centry_sub List.app].
        split; [ eapply rel_ctx_wf_extend_def; eassumption | eapply gsub_q_def; eassumption ].
    + injection Heq as <- ->.
      exact (IHC Ψ2 Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc).
  - (* a module slot *)
    intros C U R HC IHC HR HU HsU IHU Ψ2 Ψ Δ Heq HwC Γ τ Hg Hc.
    destruct Ψ2 as [| e Ψ2]; cbn [List.app] in Heq.
    + destruct Ψ as [| e Ψ]; cbn [List.app] in Heq |- *.
      * subst Δ; split; [ exact (proj1 (gsub_sem Hg)) | exact Hg ].
      * injection Heq as <- ->.
        destruct (IHC nil Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc) as [HΓ' Hg'].
        pose proof (rel_modexp_under_ctx_gsub Hg' HU) as HU'; cbn [modexp_sub] in HU'.
        pose proof (IHU HwC _ _ Hg' (sub_mod_compat_ext Ψ _ _ _ Hc)) as HsU'.
        assert (HUU : tele_sub Ψ τ ++ Γ ⊨ᵘ U[sb_qn (length Ψ) τ]ᵘ ≈ U[sb_qn (length Ψ) τ]ᵘ)
          by (constructor; [ exact HU' | exact HsU' | exact HsU' ]).
        rewrite tele_sub_cons; cbn [centry_sub List.app].
        split; [ eapply rel_ctx_wf_extend_mod; eassumption
               | eapply gsub_q_mod; [ exact Hg' | constructor; [ exact HU | exact HsU | exact HsU ] | exact HUU ] ].
    + injection Heq as <- ->.
      exact (IHC Ψ2 Ψ Δ eq_refl (ctx_decomp_tail HwC) _ _ Hg Hc).
  - (* a body unit *)
    intros C Δu Φ Φx HΔu Hx Hs Hsx HCx IHCx Ho HwU Γ τ Hg Hc.
    destruct (ctx_decomp_mod HwU) as [HwC HUU].
    destruct (proj1 (unit_full_of_eq _ _ _ _ _ HUU)) as (Φx0 & lv & Hx0 & HwCx & _).
    pose proof (body_xp_src_tgt _ _ _ _ Hx0 Hx) as ->.
    destruct (wf_unit_eq_scoped _ _ _ _ _ HUU) as (_ & HUs & _).
    rewrite gunit_scoped_mk in HUs; destruct HUs as [HΔs HDs]; cbn in HDs.
    pose proof (wf_ctx_scoped _ _ _ HwCx) as HCxs.
    assert (HΔCs : ctx_scoped 0 (Δu ++ C))
      by exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HCxs)).
    rewrite gunit_sub_mk; cbn [moddef_sub].
    assert (Hcx : sub_mod_compat (sb_qn (length Δu) τ) (tele_sub Δu τ ++ Γ) (Δu ++ C)) by (apply sub_mod_compat_ext; exact Hc).
    pose proof (body_xp_sub _ _ (wf_gstack_closed _ _ Hgw) _ _ _ Hx HΔCs
                  ltac:(rewrite length_app; exact (proj2 HDs)) _ _ Hcx) as Hxσ.
    destruct (IHCx nil (body_ctx Φx ++ Δu) C ltac:(rewrite <- app_assoc; reflexivity) HwCx _ _ Hg Hc) as [HCxσ Hgx].
    apply (rel_unit_wf_body _ _ _ (gmod_sub Φx (sb_qn (length Δu) τ))).
    + apply tele_ass_sub; exact HΔu.
    + exact Hxσ.
    + apply body_shape_sub; exact Hs.
    + apply body_shape_sub; exact Hsx.
    + rewrite body_ctx_sub, app_assoc, <- tele_sub_app; exact HCxσ.
    + intros k Ψw Hw Hk.
      rewrite (body_opens_sub _ _ _ _ _ Hx), List.nth_error_map in Hk.
      destruct (List.nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Ek; [| discriminate ].
      cbn in Hk; injection Hk as <- <-.
      destruct (body_opens_prefix _ _ _ _ _ Hx _ _ _ Ek) as [Ψr HΨr].
      destruct (IHCx Ψr (Ψ ++ Δu) C ltac:(rewrite HΨr, <- !app_assoc; reflexivity) HwCx _ _ Hg Hc) as [_ Hgo].
      rewrite <- app_assoc in Hgo.
      pose proof (rel_modexp_under_ctx_gsub Hgo (Ho _ _ _ Ek)) as HH.
      rewrite tele_sub_app, <- app_assoc, length_app in HH.
      rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)); exact HH.
  - (* an alias unit *)
    intros C Δu E HΔu HC IHC HE HwU Γ τ Hg Hc.
    destruct (ctx_decomp_mod HwU) as [HwC HUU].
    destruct (proj1 (unit_full_of_eq _ _ _ _ _ HUU)) as (HwΔ & _ & _).
    destruct (IHC nil Δu C eq_refl HwΔ _ _ Hg Hc) as [HΔσ Hgx].
    rewrite gunit_sub_mk; cbn [moddef_sub].
    apply rel_unit_wf_alias; [ apply tele_ass_sub; exact HΔu | exact HΔσ |].
    exact (rel_modexp_under_ctx_gsub Hgx HE).
Qed.

Corollary rel_ctx_wf_gsub : forall Ψ Δ Γ τ, ⊨ Ψ ++ Δ -> ⊢ Θm ⍮ Ξm ⍮ Ψ ++ Δ ->
    gsub Γ τ Δ -> sub_mod_compat τ Γ Δ ->
    ⊨ tele_sub Ψ τ ++ Γ /\ gsub (tele_sub Ψ τ ++ Γ) (sb_qn (length Ψ) τ) (Ψ ++ Δ).
Proof. intros * HC HwC Hg Hc; exact (proj1 rel_ctx_wf_unit_gsub_all _ HC nil Ψ Δ eq_refl HwC _ _ Hg Hc). Qed.

Corollary rel_unit_wf_gsub : forall C U Γ τ, rel_unit_wf C U -> ⊢ Θm ⍮ Ξm ⍮ C ▹ₘ U ->
    gsub Γ τ C -> sub_mod_compat τ Γ C -> rel_unit_wf Γ U[τ]ᵘ.
Proof. intros * HU HwU Hg Hc; exact (proj2 rel_ctx_wf_unit_gsub_all _ _ HU HwU _ _ Hg Hc). Qed.

End Fixed_GCtx.
