(** * Valid Module Expressions Given Arguments

    A module expression valid in what it denotes, given arguments for the
    outermost parameters of an abstraction its description is, is valid
    ([set_valid_modexp_apps_up]): one argument at a time, by
    [set_valid_unit_app_all]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Cases Require Import ValidUnit MemberTypes ModuleCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas MemberWf DescTyping LookupSound Presup.
Import ListNotations.

Section App.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The context the derivations were checked at *)
  Variable Θs : gdeps.
  Variable Ξs : gstack.
  (** The valuation models, here, everything that context resolves *)
  Hypothesis Hemb : set_gctx_embedding Θs Ξs gc_deps gc_stack T γ.

(** A module expression valid in what it denotes, given arguments for the
    outermost parameters of an abstraction its description is. *)
Lemma set_valid_modexp_apps_up : forall Ns Γ Δa R H l, set_valid_modexp T γ Γ H ->
    mdenote gc_deps gc_stack Γ H (mdesc_up Δa R) -> mdesc_is_mod R ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Δa ++ Γ -> all_assumptions Δa -> List.length Ns <= List.length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa sb_id Ns) k = Some A -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : A) ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa sb_id Ns) k = Some A -> set_rel_exp_eq T γ Γ A N N) ->
    (forall k A, nth_error (tele_insts Δa sb_id Ns) k = Some A -> exists Srt, evaluated_sort Srt /\ set_rel_exp_eq T γ Γ Srt A A) ->
    params_evaluated gc_deps gc_stack Γ Δa l ->
    desc_ok gc_deps gc_stack (Δa ++ Γ) R ->
    set_valid_modexp T γ Γ (me_apps H Ns).
Proof.
  induction Ns as [| N Ns IH]; intros * Hs Hm Hmod HΔ Ha Hl HNs HNv HNr HΔr HR; [exact Hs |].
  destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [intros ->; cbn in Hl; lia |].
  unfold all_assumptions in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? (κ & C & ->) _]; subst.
  rewrite tele_insts_snoc in HNs, HNv, HNr.
  pose proof (HNs 0 N (exp_sub C sb_id) eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
  pose proof (HNv 0 N (exp_sub C sb_id) eq_refl eq_refl) as HNsem; rewrite exp_sub_id in HNsem.
  destruct (HNr 0 (exp_sub C sb_id) eq_refl) as (Sr & HSr & HCr); rewrite exp_sub_id in HCr.
  pose proof (HΔr Δ1 κ C nil eq_refl) as HC0; cbn [List.app] in HC0.
  assert (HCw : exists SC, evaluated_sort SC /\ gc_deps ⍮ gc_stack ⍮ Γ ⊢ C : SC)
    by (destruct HC0 as [HC | HC]; eexists; (split; [constructor | exact HC])).
  destruct HCw as (SC & HSC & HC).
  pose proof (proj1 (params_evaluated_app_inv _ _ _ _ _ _ HΔr)) as HΔ1r.
  rewrite <- List.app_assoc in HΔ, HR; cbn [List.app] in HΔ, HR.
  destruct (ctx_decomp_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as (SCk & HSCk & HCk).
  pose proof (wf_sub_single _ _ _ _ _ _ _ HCk HSCk HN) as Hs1.
  assert (HΔN : ⊢ gc_deps ⍮ gc_stack ⍮ tele_sub Δ1 (sb_extend sb_id (se_exp N)) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
  assert (Hσ : gc_deps ⍮ gc_stack ⍮ tele_sub Δ1 (sb_extend sb_id (se_exp N)) ++ Γ
                 ⊢ˢ sb_qn (List.length Δ1) (sb_extend sb_id (se_exp N)) : Δ1 ++ ce_ass κ C :: Γ)
    by (apply wf_sub_ext; assumption).
  destruct (desc_ok_tele _ _ _ _ HR Hmod) as (T0 & Ht0).
  assert (Hmt : mdesc_mod_tele (mdesc_up (Δ1 ++ ce_ass κ C :: nil) R) = Some ((T0 ++ Δ1) ++ ce_ass κ C :: nil))
    by (unfold mdesc_mod_tele; rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Hmod)), (mdesc_tele_up _ _ _ Ht0), List.app_assoc;
        reflexivity).
  pose proof (proj2 (set_valid_unit_app_all T γ Hfn Hmods Hgw Θs Ξs Hemb) _ _ Hs _ _ _ _ _ _ Hm Hmt (tele_view_last _ _ _) HSC HC
                (ex_intro _ Sr (conj HSr HCr)) HN HNsem) as HsN.
  cbn [me_apps].
  eapply (IH Γ (tele_sub Δ1 (sb_extend sb_id (se_exp N))) (mdesc_sub R (sb_qn (List.length Δ1) (sb_extend sb_id (se_exp N)))) _ l).
  - exact HsN.
  - eapply mdenote_app; [exact Hm | apply mdesc_at_up].
  - apply mdesc_is_mod_sub; exact Hmod.
  - exact HΔN.
  - apply all_assumptions_sub; exact Ha1.
  - rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
  - intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_extend sb_id (se_exp N))) in HA by apply sb_compose_id_right.
    exact (HNs (S k) N1 A HN1 HA).
  - intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_extend sb_id (se_exp N))) in HA by apply sb_compose_id_right.
    exact (HNv (S k) N1 A HN1 HA).
  - intros k A HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_extend sb_id (se_exp N))) in HA by apply sb_compose_id_right.
    exact (HNr (S k) A HA).
  - exact (params_evaluated_sub _ _ _ _ _ _ _ HΔ1r Hs1 HΔ HΔN).
  - exact (desc_ok_sub _ _ Hgw _ _ HR _ _ Hσ).
Qed.

End App.
