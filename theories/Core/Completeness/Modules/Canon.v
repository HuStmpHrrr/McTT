(** * Valid Units Are Their Canonical Units

    An alias of a literal is the literal over both telescopes in the PER
    model ([rel_lit_flatten]), and an alias over parameters of the unit of a
    module part is the unit of that module part abstracted over them
    ([rel_alias_unit_up]).  So a valid unit, and a module expression valid
    in what it denotes, is equal in the PER model to the unit its module
    part stands for, [⌜R⌝], which is valid ([valid_unit_canon_all]): the semantic
    counterpart of lookup soundness. *)

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
From Mctt.Core.Completeness.Modules Require Import ValidUnit Body Filed Unit.
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

(** ** Aliases of Literals *)

Lemma flat_walk : forall Δ Γ Δ' D RΓ, tele_ass Δ -> ⊨ Δ ++ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    Δ ++ Γ ⊨ᵐ me_lit (gu_mk Δ' D) ≈ me_lit (gu_mk Δ' D) ->
    forall ρ ρ', RΓ ρ ρ' ->
      rel_mexp (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) ρ (me_lit (gu_mk (Δ' ++ Δ) D)) ρ'.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HC HΓ HU ρ ρ' Hρ; cbn [List.app] in *.
  - rewrite app_nil_r.
    destruct (unit_chain_at HU HΓ _ _ Hρ) as [h h' Hh Hh' Hhh].
    apply (mk_rel_mexp _ _ _ _ h h'); [ apply eval_me_lit, eval_close_alias0; exact Hh | exact Hh' | exact Hhh ].
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [A ->] _]; subst.
    rewrite <- app_assoc in HC, HU; cbn [List.app] in HC, HU.
    destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as [i HA].
    pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
    destruct (rel_exp_of_typ_inversion_simple_at HΓ HA _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    rewrite app_assoc.
    econstructor; [ apply eval_me_lit, close_unsat; rewrite length_app; cbn; lia
                  | apply eval_me_lit, close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa |].
    intros c c' Hc.
    destruct (IH (Γ ▹ A) _ _ _ HΔ0 HC HΓA HU (ρ ↦ c) (ρ' ↦ c')) as [h h' Hh Hh' Hhh].
    { split; [ exact Hρ | eapply per_head_of; [ exact Ha | exact Ha' | exact HRa | exact Hc ] ]. }
    apply eval_me_lit_iff in Hh, Hh'; exists h, h'; repeat split; assumption.
Qed.

Lemma ext_refl : forall Γ Δ, ⊨ Δ ++ Γ -> Γ ⊨ˣ Δ ≈ Δ.
Proof. intros * HC; constructor; [ exact HC | exact HC | exact (rel_ctx_wf_per_ctx HC) ]. Qed.

(** An alias of a literal is the literal over both telescopes. *)
Lemma rel_lit_flatten : forall Γ Δ Δ' D, tele_ass Δ -> valid_unit (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) ≈ me_lit (gu_mk (Δ' ++ Δ) D).
Proof.
  intros * HΔ HK.
  pose proof (valid_unit_rel _ _ Hgf _ _ HK) as HU.
  pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HΓ.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  apply rel_modexp_of_at.
  - exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HC) HΔ HΔ eq_refl HU HU).
  - exact (valid_unit_rel _ _ Hgf _ _ (valid_unit_abs _ _ Hgm Hgf _ _ _ HK HΔ)).
  - intros R HR ρ ρ' Hρ.
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (flat_walk _ _ _ _ _ HΔ HC HRΓ HU _ _ (proj1 (E _ _) Hρ)) as [h h' Hh Hh' Hhh].
    exists h, h'; auto.
Qed.

(** ** Aliases of Canonical Units *)

Lemma rel_alias_unit_up : forall Γ Δ X, Δ <> nil -> tele_ass Δ -> ds_is_mod X -> valid_unit (Δ ++ Γ) (ds_unit X) ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias (ds_unit X))) ≈ ds_unit (ds_up Δ X) /\ valid_unit Γ (ds_unit (ds_up Δ X)).
Proof.
  intros * Hne HΔ Hm HK.
  destruct X as [A om | Δe Φ Φx | [| e Θ'] p T Φ Ns | Θ0 p Ns | Θ0 p Ns]; cbn in Hm; try contradiction; cbn [ds_up ds_unit] in HK |- *.
  - (* a local body *)
    split; [ exact (rel_lit_flatten _ _ _ _ HΔ HK) | exact (valid_unit_abs _ _ Hgm Hgf _ _ _ HK HΔ) ].
  - (* a filed module at arguments: the alias is the unit *)
    rewrite app_nil_l; destruct Δ as [| e Δ0]; [ contradiction |].
    pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HC.
    pose proof (valid_unit_rel _ _ Hgf _ _ HK) as HE.
    pose proof (valid_unit_wf _ _ _ _ HK) as HwE.
    pose proof (presup_modexp_eq_ctx HwE) as HwC.
    assert (HL : Γ ⊨ᵐ me_lit (gu_mk (e :: Δ0) (md_alias (me_apps (qname_mod p) Ns))) ≈ me_lit (gu_mk (e :: Δ0) (md_alias (me_apps (qname_mod p) Ns))))
      by exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HC) HΔ HΔ eq_refl HE HE).
    split; [ exact HL |].
    apply valid_unit_alias; [ apply wf_me_lit, wf_unit_eq_alias; [ exact (ext_of_ctx' _ _ _ _ HwC) | exact HΔ | exact HΔ | exact HwE | exact HwE ]
                    | exact HΔ | exact (rel_ctx_wf_app_r _ _ HC) | exact HC | exact HL | exact HE | ].
    destruct (me_denotes _ _ _ _ _ HwE) as (R & Rm & HmR & HmdR).
    exact (valid_modexp_intro _ _ _ _ _ _ _ _ HwE HmR HmdR HE HK HmR HmdR).
  - (* an alias of a filed module at arguments *)
    split; [ exact (rel_lit_flatten _ _ _ _ HΔ HK) | exact (valid_unit_abs _ _ Hgm Hgf _ _ _ HK HΔ) ].
Qed.

(** ** Canonical Units *)

Lemma valid_unit_canon_all :
  (forall Γ K, valid_unit Γ K -> forall RK Rm, mdenote Θm Ξm Γ K RK -> ds_mod Θm Ξm RK = Some Rm ->
     Γ ⊨ᵐ K ≈ ds_unit Rm /\ valid_unit Γ (ds_unit Rm)) /\
  (forall Γ H, valid_modexp Γ H -> forall R Rm, mdenote Θm Ξm Γ H R -> ds_mod Θm Ξm R = Some Rm ->
     Γ ⊨ᵐ H ≈ ds_unit Rm /\ valid_unit Γ (ds_unit Rm)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs RK Rm Hm Hmd.
    pose proof (valid_unit_filed _ _ _ _ _ _ _ Hw Hgl HΓ Hs) as HK.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmd; injection Hmd as <-.
    cbn [ds_unit]; split; [ exact (valid_unit_rel _ _ Hgf _ _ HK) | exact HK ].
  - (* a body: its own literal *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hsl IHsl Hs Hsx HU Hopv Hops IHops RK Rm Hm Hmd.
    pose proof (valid_unit_body _ _ _ _ _ _ Hw Hx HΔ HΓ HC Hsl Hs Hsx HU Hopv Hops) as HK.
    apply mdenote_lit_inv in Hm; inversion Hm; subst.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn in Hmd; injection Hmd as <-; cbn [ds_unit]; split; [ exact HU | exact HK ].
  - (* an alias: its target's unit, abstracted *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HU HE Hsmt IHE RK Rm Hm Hmd.
    apply mdenote_lit_inv in Hm; inversion Hm as [| ? ? ? ? RE REm HmE HmdE]; subst.
    pose proof (ds_mod_is_mod _ _ _ _ HmdE) as Him.
    rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ Him)) in Hmd; injection Hmd as <-.
    destruct (IHE _ _ HmE HmdE) as [HEu HKu].
    destruct Δ as [| e Δ0].
    + rewrite ds_up_nil; cbn [List.app] in *.
      split; [ exact (rel_modexp_under_ctx_trans (rel_modexp_under_ctx_beta_alias0 _ _ HE) HEu) | exact HKu ].
    + destruct (rel_alias_unit_up Γ (e :: Δ0) REm ltac:(discriminate) HΔ Him HKu) as [Hup HKup].
      split; [| exact HKup ].
      eapply rel_modexp_under_ctx_trans; [| exact Hup ].
      exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HΔΓ) HΔ HΔ eq_refl HEu (rel_modexp_refl_right HEu)).
  - (* a module expression equal to a valid unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK R' Rm' Hm Hmd.
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH), HmodH in Hmd; injection Hmd as <-.
    destruct (IHK _ _ HmK HmodK) as [HKu HKK]; split; [ exact (rel_modexp_under_ctx_trans HHK HKu) | exact HKK ].
Qed.

Corollary valid_modexp_canon : forall Γ H R Rm, valid_modexp Γ H -> mdenote Θm Ξm Γ H R -> ds_mod Θm Ξm R = Some Rm ->
    Γ ⊨ᵐ H ≈ ds_unit Rm /\ valid_unit Γ (ds_unit Rm).
Proof. intros * HH Hm Hmd; exact (proj2 valid_unit_canon_all _ _ HH _ _ Hm Hmd). Qed.

Lemma valid_modexp_of_valid_unit : forall Γ K, valid_unit Γ K -> valid_modexp Γ K.
Proof.
  intros * HK.
  pose proof (valid_unit_wf _ _ _ _ HK) as HwK.
  destruct (me_denotes _ _ _ _ _ HwK) as (R & Rm & HmR & HmdR).
  exact (valid_modexp_intro _ _ _ _ _ _ _ _ HwK HmR HmdR (valid_unit_rel _ _ Hgf _ _ HK) HK HmR HmdR).
Qed.

End Fixed_GCtx.
