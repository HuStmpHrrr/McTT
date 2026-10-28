(** * Applications of Valid Units

    A valid unit, or a module expression valid in what it denotes, lacks
    the parameter its description says it takes next, and applied to an
    argument of that parameter's type it is valid in what it denotes
    ([valid_unit_app_all]): a filed module records the argument, a literal is
    instantiated ([valid_unit_lit_app]), an alias with no parameter is its target
    applied. *)

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
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit Canon.
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

Lemma mdesc_tele_up_tele : forall Δ R T, mdesc_is_mod R -> mdesc_tele (mdesc_up Δ R) = Some T ->
    exists T0, mdesc_tele R = Some T0 /\ T = T0 ++ Δ.
Proof.
  intros * Hm Ht; destruct R as [| Δ' Φ | Θ0 p T' Φ Ns |]; cbn in Hm, Ht |- *; try contradiction.
  - injection Ht as <-; eauto.
  - destruct (Nat.leb _ _); [ injection Ht as <-; rewrite app_assoc; eauto | discriminate ].
Qed.

(** The unit a valid literal with an outermost parameter is, given an
    argument for it: the literal instantiated, with the description at the
    argument. *)
Lemma valid_unit_lit_app : forall Γ Δ X D N R i, valid_unit Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) ->
    udenote Θm Ξm Γ None (gu_mk (Δ ++ ce_ass X :: nil) D) R ->
    Θm ⍮ Ξm ⍮ Γ ⊢ X : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : X -> Γ ⊨ N : X ->
    modexp_next_param Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) X /\
    exists R', mdesc_at R N = Some R' /\
      Γ ⊨ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ /\
      valid_unit Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ) /\
      mdenote Θm Ξm Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ) R' /\ mdesc_mod R' = Some R'.
Proof.
  intros * HK Hu HXw HNw HN.
  pose proof (valid_unit_beta Hgw _ _ Hgm Hsub Hgf _ _ _ _ _ _ HK HXw HNw HN) as HK'.
  pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HΓ.
  destruct (presup_rel_exp_under_ctx HN) as [j HX].
  pose proof (valid_unit_wf _ _ _ _ HK) as Hw.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ Hw) as (HΓs & HUs & _).
  destruct (udenote_beta _ _ (wf_gstack_closed _ _ Hgm) _ _ _ _ N _ HΓs HUs Hu) as (R1 & Ha1 & Hu1).
  split; [ eapply lit_params_lacks; exact HX |].
  exists R1; split; [ exact Ha1 |]; split; [| split; [ exact HK' | split; [ apply mdenote_lit; exact Hu1 | apply mdesc_is_mod_mod; eapply udenote_is_mod; exact Hu1 ] ] ].
  exact (rel_modexp_under_ctx_beta _ _ _ _ _ _ HΓ (valid_unit_rel _ _ Hgf _ _ HK) (valid_unit_links_unabs1 Hgw _ _ Hgm Hsub Hgf _ _ _ _ HK) HX HN).
Qed.

Lemma app_wf : forall Γ H R T B T1 i N, Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θm Ξm Γ H R ->
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θm ⍮ Ξm ⍮ Γ ⊢ B : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : B -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N.
Proof.
  intros * Hw Hm Ht Hv HBw HNw.
  eapply wf_me_app; [ exact Hw | exact Hm | exact Ht | exact Hv | exact HBw | exact HNw | mauto 3
                    | exact Hm | exact Ht | exact Hv | exact HBw | exact HNw ].
Qed.

Lemma valid_unit_app_all :
  (forall Γ K, valid_unit Γ K -> forall RK Rm T B T1 i N, mdenote Θm Ξm Γ K RK -> mdesc_mod RK = Some Rm ->
     mdesc_tele Rm = Some T -> tele_view T = Some (B, T1) ->
     Θm ⍮ Ξm ⍮ Γ ⊢ B : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : B -> Γ ⊨ N : B ->
     modexp_next_param Γ K B /\ exists K' RK' Rm', mdesc_at Rm N = Some Rm' /\ Γ ⊨ᵐ me_app K N ≈ K' /\ valid_unit Γ K' /\
       mdenote Θm Ξm Γ K' RK' /\ mdesc_mod RK' = Some Rm') /\
  (forall Γ H, valid_modexp Γ H -> forall R T B T1 i N, mdenote Θm Ξm Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
     Θm ⍮ Ξm ⍮ Γ ⊢ B : Typeω@i -> Θm ⍮ Ξm ⍮ Γ ⊢ N : B -> Γ ⊨ N : B ->
     modexp_next_param Γ H B /\ valid_modexp Γ (me_app H N)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments: the argument recorded *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs RK Rm T' B T1 i N Hm Hmod Ht Hv HBw HNw HN.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmod; injection Hmod as <-.
    assert (HmtK : mdesc_mod_tele R1 = Some T') by (unfold mdesc_mod_tele; rewrite Hmod1; exact Ht).
    assert (HwN : Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_app (me_apps (qname_mod p) Ns) N ≈ me_app (me_apps (qname_mod p) Ns) N)
      by exact (app_wf _ _ _ _ _ _ _ _ Hw Hm1 HmtK Hv HBw HNw).
    pose proof Hs as [T1s T2s -> Hlen HTa2 HTs2 HNs].
    cbn [mdesc_tele] in Ht.
    rewrite length_app in Ht.
    destruct (Nat.leb_spec (List.length Ns) (List.length T1s + List.length T2s)) as [_ | Hgt]; [| lia ].
    injection Ht as <-.
    replace (List.length T1s + List.length T2s - List.length Ns) with (List.length T1s) in Hv by lia.
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag in Hv; cbn [List.firstn] in Hv; rewrite !app_nil_r in Hv.
    destruct (Hgf _ _ _ Hgl) as [_ _ _ HTa _ _ _ _ _ _ _].
    destruct (tele_ass_app_inv _ _ HTa) as [HTa1 _].
    destruct (List.exists_last (l := T1s)) as (L & e & ->); [ intros ->; cbn in Hv; discriminate |].
    destruct (tele_ass_app_inv _ _ HTa1) as [_ He]; inversion He as [| ? ? [A ->] _]; subst.
    rewrite tele_sub_app in Hv; cbn [tele_sub List.length sb_qn centry_sub] in Hv.
    rewrite tele_view_last in Hv; injection Hv as <- <-.
    assert (HT : L ++ ce_ass A :: T2s = (L ++ ce_ass A :: nil) ++ T2s) by (rewrite <- app_assoc; reflexivity).
    rewrite <- HT in Hgl |- *.
    pose proof (filed_lacks _ _ Hgf _ _ _ _ _ _ _ _ Hgl HΓ eq_refl (eq_sym Hlen) HNs) as Hl.
    split; [ exact Hl |].
    assert (Hs' : valid_args Γ (L ++ ce_ass A :: T2s) (Ns ++ N :: nil)).
    { apply (mk_valid_args _ _ _ L (ce_ass A :: T2s));
        [ reflexivity | cbn; rewrite length_app; cbn; lia | constructor; [ eexists; reflexivity | exact HTa2 ]
        | destruct (Hgf _ _ _ Hgl) as [_ _ _ _ HTs _ _ _ _ _ _]; exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HTs)) |].
      assert (Hti : tele_insts (ce_ass A :: T2s) Id (Ns ++ N :: nil) = tele_insts T2s Id Ns ++ A[sb_of_list Id Ns] :: nil).
      { change (ce_ass A :: T2s) with ((ce_ass A :: nil) ++ T2s).
        rewrite tele_insts_app by (try exact HTa2; lia); reflexivity. }
      assert (HlT : List.length (tele_insts T2s Id Ns) = List.length Ns) by (rewrite length_tele_insts by exact HTa2; lia).
      intros k N0 B0 HN0 HB0; rewrite Hti in HB0.
      destruct (Nat.lt_ge_cases k (List.length Ns)) as [Hk | Hk].
      + rewrite nth_error_app1 in HN0, HB0 by lia; exact (HNs _ _ _ HN0 HB0).
      + rewrite nth_error_app2 in HN0, HB0 by lia; rewrite HlT in HB0.
        destruct (k - List.length Ns) as [| k']; cbn in HN0, HB0; [ injection HN0 as <-; injection HB0 as <-; exact HN |].
        destruct k'; discriminate. }
    destruct (filed_denote _ _ Hgm _ _ _ Γ (Ns ++ N :: nil) Hgl) as (R2 & Hm2 & Hmod2).
    exists (me_apps (qname_mod p) (Ns ++ N :: nil)), R2, (mdesc_closed nil p (L ++ ce_ass A :: T2s) Φ (Ns ++ N :: nil)).
    split; [ cbn; rewrite (List.map_ext _ (fun M => M) exp_sub_id), List.map_id; reflexivity |].
    split; [ pose proof (filed_valid _ _ Hgf _ _ _ _ _ Hgl HΓ Hs') as HV'; rewrite ?me_apps_snoc in HV' |- *; exact HV' |].
    split; [ eapply valid_unit_filed; [ rewrite me_apps_snoc; exact HwN | exact Hgl | exact HΓ | exact Hs' ] |].
    split; assumption.
  - (* a body: β *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hsl IHsl Hs Hsx HU Hopv Hops IHops RK Rm T B T1 i N Hm Hmod Ht Hv HBw HNw HN.
    pose proof (valid_unit_body _ _ _ _ _ _ Hw Hx HΔ HΓ HC Hsl Hs Hsx HU Hopv Hops) as HK0.
    apply mdenote_lit_inv in Hm.
    rewrite (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ Hm)) in Hmod; injection Hmod as <-.
    inversion Hm; subst.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn in Ht; injection Ht as <-.
    pose proof (tele_view_ass _ _ _ HΔ Hv) as ->.
    destruct (valid_unit_lit_app _ _ _ _ _ _ _ HK0 Hm HBw HNw HN) as (Hl & R' & Ha & HKN & HK' & Hm' & Hmod').
    split; [ exact Hl |].
    exists (me_lit (gu_mk T1 (md_body sm_open Φ))[Id,,N]ᵘ), R', R'; repeat split; assumption.
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HU HE Hsmt IHE RK Rm T B T1 i N Hm Hmod Ht Hv HBw HNw HN.
    pose proof (valid_unit_alias _ _ _ _ _ Hw HΔ HΓ HΔΓ HU HE Hsmt) as HK0.
    apply mdenote_lit_inv in Hm.
    rewrite (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ Hm)) in Hmod; injection Hmod as <-.
    pose proof Hm as Hu.
    inversion Hm as [| ? ? ? E0 RE Rem HmE HmodE]; subst.
    destruct (mdesc_tele_up_tele _ _ _ (mdesc_mod_is_mod _ _ HmodE) Ht) as (T0 & Ht0 & ->).
    destruct Δ as [| e Δ'] using List.rev_ind.
    + (* with no parameter: its target given the argument *)
      cbn [List.app] in *; rewrite List.app_nil_r in Hv; rewrite mdesc_up_nil.
      assert (HmtE : mdesc_mod_tele RE = Some T0) by (unfold mdesc_mod_tele; rewrite HmodE; exact Ht0).
      destruct (IHE _ _ _ _ _ _ HmE HmtE Hv HBw HNw HN) as (HlE & HsN).
      pose proof (rel_modexp_under_ctx_beta_alias0 _ _ HE) as Hβ.
      pose proof (modexp_next_param_resp _ _ _ _ Hβ HlE) as Hl.
      split; [ exact Hl |].
      inversion HsN as [? ? RN RNm KN RKN HwN HmN HmodN HNK HKN HmKN HmodKN]; subst.
      inversion HmN; subst; try (match goal with Hq : mod_qname (me_app _ _) = Some _ |- _ => cbn in Hq; discriminate end).
      match goal with Hm0 : mdenote _ _ _ E ?R0, Ha0 : mdesc_at ?R0 N = Some RN |- _ =>
        pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm0 _ HmE) as ->; rename Ha0 into HaN end.
      destruct (mdesc_mod_at _ _ _ _ HmodE HaN) as (Rm' & HaRm & HmodRN).
      rewrite HmodRN in HmodN; injection HmodN as <-.
      exists KN, RKN, Rm'; split; [ exact HaRm |]; split; [| split; [ exact HKN | split; assumption ] ].
      eapply rel_modexp_under_ctx_trans; [| exact HNK ].
      eapply rel_modexp_under_ctx_app; [ exact Hβ | exact HN | exact Hl ].
    + (* β *)
      destruct (tele_ass_app_inv _ _ HΔ) as [HΔ' He]; inversion He as [| ? ? [X ->] _]; subst.
      rewrite app_assoc, tele_view_last in Hv; injection Hv as <- <-.
      destruct (valid_unit_lit_app _ _ _ _ _ _ _ HK0 Hu HBw HNw HN) as (Hl & R' & Ha & HKN & HK' & Hm' & Hmod').
      split; [ exact Hl |].
      exists (me_lit (gu_mk Δ' (md_alias E))[Id,,N]ᵘ), R', R'; repeat split; assumption.
  - (* a module expression equal to a valid unit: as the unit does *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK R0 T B T1 i N Hm Ht Hv HBw HNw HN.
    pose proof (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH) as ->.
    unfold mdesc_mod_tele in Ht; rewrite HmodH in Ht.
    destruct (IHK _ _ _ _ _ _ _ HmK HmodK Ht Hv HBw HNw HN) as (HlK & K' & RK' & Rm' & Ha & HKN & HK' & HmK' & HmodK').
    pose proof (modexp_next_param_resp _ _ _ _ HHK HlK) as Hl.
    split; [ exact Hl |].
    destruct (mdesc_mod_at_inv _ _ _ _ HmodH Ha) as (R' & HaR & HmodR').
    eapply (valid_modexp_intro _ _ _ _ R' Rm' K' RK'); [ | eapply mdenote_app; eassumption | exact HmodR' | | exact HK' | exact HmK' | exact HmodK' ].
    + assert (HmtR : mdesc_mod_tele R = Some T) by (unfold mdesc_mod_tele; rewrite HmodH; exact Ht).
      exact (app_wf _ _ _ _ _ _ _ _ HwH Hm HmtR Hv HBw HNw).
    + eapply rel_modexp_under_ctx_trans; [| exact HKN ].
      eapply rel_modexp_under_ctx_app; [ exact HHK | exact HN | exact Hl ].
Qed.

(** A module expression valid in what it denotes, given arguments for the
    outermost parameters of an abstraction its description is. *)
Lemma valid_modexp_apps_up : forall Ns Γ Δa R H, valid_modexp Γ H -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H -> mdenote Θm Ξm Γ H (mdesc_up Δa R) -> mdesc_is_mod R ->
    ⊢ Θm ⍮ Ξm ⍮ Δa ++ Γ -> tele_ass Δa -> List.length Ns <= List.length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θm ⍮ Ξm ⍮ Γ ⊢ N : A) ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Γ ⊨ N : A) ->
    desc_ok Θm Ξm (Δa ++ Γ) R ->
    valid_modexp Γ (me_apps H Ns).
Proof.
  induction Ns as [| N Ns IH]; intros * Hs HH Hm Hmod HΔ Ha Hl HNs HNv HR; [ exact Hs |].
  destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
  unfold tele_ass in Ha; apply List.Forall_app in Ha as [Ha1 He]; inversion He as [| ? ? [C ->] _]; subst.
  rewrite tele_insts_snoc in HNs, HNv.
  pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
  pose proof (HNv 0 N C[Id] eq_refl eq_refl) as HNsem; rewrite exp_sub_id in HNsem.
  rewrite <- List.app_assoc in HΔ, HR; cbn [List.app] in HΔ, HR.
  destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ [j HC]].
  pose proof (wf_sub_single _ _ _ _ _ _ HC HN) as Hs1.
  assert (HΔN : ⊢ Θm ⍮ Ξm ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
  assert (Hσ : Θm ⍮ Ξm ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (List.length Δ1) (Id,,N) : Δ1 ++ ce_ass C :: Γ)
    by (apply wf_sub_ext; assumption).
  destruct (desc_ok_tele _ _ _ _ HR Hmod) as (T0 & Ht0).
  assert (Hmt : mdesc_mod_tele (mdesc_up (Δ1 ++ ce_ass C :: nil) R) = Some ((T0 ++ Δ1) ++ ce_ass C :: nil))
    by (unfold mdesc_mod_tele; rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Hmod)), (mdesc_tele_up _ _ _ Ht0), app_assoc; reflexivity).
  pose proof (app_wf _ _ _ _ _ _ _ _ HH Hm Hmt (tele_view_last _ _) HC HN) as HHN.
  destruct (proj2 valid_unit_app_all _ _ Hs _ _ _ _ _ _ Hm Hmt (tele_view_last _ _) HC HN HNsem) as [_ HsN].
  cbn [me_apps].
  eapply (IH Γ (tele_sub Δ1 (Id,,N)) (mdesc_sub R (sb_qn (List.length Δ1) (Id,,N)))).
  - exact HsN.
  - exact HHN.
  - eapply mdenote_app; [ exact Hm | apply mdesc_at_up ].
  - apply mdesc_is_mod_sub; exact Hmod.
  - exact HΔN.
  - apply tele_ass_sub; exact Ha1.
  - rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
  - intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
    exact (HNs (S k) N1 A HN1 HA).
  - intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
    exact (HNv (S k) N1 A HN1 HA).
  - exact (desc_ok_sub _ _ Hgm _ _ HR _ _ Hσ).
Qed.

End Fixed_GCtx.
