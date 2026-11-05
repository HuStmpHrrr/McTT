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
      rel_modexp_evals (me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))) ρ (me_lit (gu_mk (Δ' ++ Δ) D)) ρ'.
Proof.
  induction Δ as [| e Δ0 IH] using rev_ind; intros * HΔ HC HΓ HU ρ ρ' Hρ; cbn [List.app] in *.
  - rewrite app_nil_r.
    destruct (unit_chain_at HU HΓ _ _ Hρ) as [h h' Hh Hh' Hhh].
    apply (mk_rel_modexp_evals _ _ _ _ h h'); [ apply eval_me_lit, eval_close_alias0; exact Hh | exact Hh' | exact Hhh ].
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? (κ & A & ->) _]; subst.
    rewrite <- app_assoc in HC, HU; cbn [List.app] in HC, HU.
    destruct (rel_ctx_wf_ass_inv (rel_ctx_wf_app_r _ _ HC)) as (Srt & HS & HA0).
    destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA0) as [i HA].
    pose proof (per_ctx_env_of_typ (κ := κ) HΓ HA) as HΓA.
    destruct (rel_type_inversion_simple_at HΓ HA _ _ Hρ) as (a & a' & Ha & Ha' & [Ra HRa]).
    (** The parameter's type is of its tag, at both sides. *)
    destruct (rel_type_kind_of_sort_kind HS HA0 _ HΓ _ _ Hρ) as (a0 & Ea0 & Ka).
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ha) as ->.
    assert (Ka' : domain_kind a' = κ) by (rewrite <- (per_univ_elem_kind _ _ _ _ HRa); exact Ka).
    rewrite app_assoc.
    econstructor; [ apply eval_me_lit, close_unsat; rewrite length_app; cbn; lia
                  | apply eval_me_lit, close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa | exact Ka | exact Ka' |].
    intros c c' Hc.
    pose proof (entry_readable_of_elem_closure Ha Ha' HRa Hc) as [Rc Rc'].
    destruct (IH (Γ ▹{κ} A) _ _ _ HΔ0 HC HΓA HU (ρ ↦ c ⦂ entry_type_closure A ρ) (ρ' ↦ c' ⦂ entry_type_closure A ρ'))
      as [h h' Hh Hh' Hhh].
    { apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ ↦ c ⦂ entry_type_closure A ρ) (ρ' ↦ c' ⦂ entry_type_closure A ρ') Hρ);
        [ eapply per_head_of; [ exact Ha | exact Ha' | exact HRa | exact Hc ] | intros _; eexists; reflexivity
        | intros _; eexists; reflexivity | split; [ exact Rc | cbn; lia ] | split; [ exact Rc' | cbn; lia ] ]. }
    apply eval_me_lit_iff in Hh, Hh'; exists h, h'; rewrite !eval_close_expand_iff; repeat split; assumption.
Qed.

Lemma ext_refl : forall Γ Δ, ⊨ Δ ++ Γ -> Γ ⊨ˣ Δ ≈ Δ.
Proof. intros * HC; constructor; [ exact HC | exact HC | exact (rel_ctx_wf_per_ctx HC) ]. Qed.

(** An alias of a literal is the literal over both telescopes. *)
Lemma rel_lit_flatten : forall Γ Δ Δ' D l, tele_ass Δ -> params_evaluated Θm Ξm Γ Δ l -> rel_params_evaluated Γ Δ l ->
    (forall R, mdenote Θm Ξm (Δ ++ Γ) (me_lit (gu_mk Δ' D)) R -> desc_levels_abstractable Θm Ξm Γ Δ R) ->
    valid_unit (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D)))) ≈ me_lit (gu_mk (Δ' ++ Δ) D).
Proof.
  intros * HΔ HΔw HΔr HΔa HK.
  pose proof (valid_unit_rel _ _ Hgf _ _ HK) as HU.
  pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HC.
  pose proof (rel_ctx_wf_app_r _ _ HC) as HΓ.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  apply rel_modexp_of_at.
  - exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HC) HΔ HΔ eq_refl HU HU).
  - exact (valid_unit_rel _ _ Hgf _ _ (valid_unit_abs _ _ Hgm Hgf _ _ _ _ HK HΔ HΔw HΔr
                                         (fun R HR => HΔa R (mdenote_lit _ _ _ _ _ HR)))).
  - intros R HR ρ ρ' Hρ.
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (flat_walk _ _ _ _ _ HΔ HC HRΓ HU _ _ (proj1 (E _ _) Hρ)) as [h h' Hh Hh' Hhh].
    exists h, h'; auto.
Qed.

(** ** Aliases of Canonical Units *)


Lemma rel_alias_unit_up : forall Γ Δ X l, Δ <> nil -> tele_ass Δ -> params_evaluated Θm Ξm Γ Δ l -> rel_params_evaluated Γ Δ l ->
    mdesc_is_mod X ->
    (forall R, mdenote Θm Ξm (Δ ++ Γ) (mdesc_unit X) R -> desc_levels_abstractable Θm Ξm Γ Δ R) ->
    valid_unit (Δ ++ Γ) (mdesc_unit X) ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias (mdesc_unit X))) ≈ mdesc_unit (mdesc_up Δ X) /\ valid_unit Γ (mdesc_unit (mdesc_up Δ X)).
Proof.
  intros * Hne HΔ HΔw HΔr Hm HΔa HK.
  destruct X as [A om | Δe Φ Φx | [| e Θ'] p T Φ Ns | Θd Ad Md Rm]; cbn in Hm; try contradiction;
    cbn [mdesc_up mdesc_unit] in HK, HΔa |- *.
  - (* a local body *)
    split; [ exact (rel_lit_flatten _ _ _ _ _ HΔ HΔw HΔr HΔa HK)
           | exact (valid_unit_abs _ _ Hgm Hgf _ _ _ _ HK HΔ HΔw HΔr (fun R HR => HΔa R (mdenote_lit _ _ _ _ _ HR))) ].
  - (* a filed module at arguments: the alias is the unit *)
    rewrite app_nil_l; destruct Δ as [| e Δ0]; [ contradiction |].
    pose proof (valid_unit_ctx_wf _ _ _ _ HK) as HC.
    pose proof (valid_unit_rel _ _ Hgf _ _ HK) as HE.
    pose proof (valid_unit_wf _ _ _ _ HK) as HwE.
    pose proof (presup_modexp_eq_ctx HwE) as HwC.
    assert (HL : Γ ⊨ᵐ me_lit (gu_mk (e :: Δ0) (md_alias (me_apps (qname_mod p) Ns))) ≈ me_lit (gu_mk (e :: Δ0) (md_alias (me_apps (qname_mod p) Ns))))
      by exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HC) HΔ HΔ eq_refl HE HE).
    split; [ exact HL |].
    destruct (params_evaluated_sorts _ _ _ _ _ HΔw) as (ps & Hps & HpΔ).
    assert (HF : exists lv Rt, levels_flag Θm Ξm Γ (e :: Δ0) (me_apps (qname_mod p) Ns) lv Rt).
    { destruct (me_denotes _ _ _ _ _ HwE) as (RE & _ & HmE & _).
      destruct (HΔa _ HmE) as [HLs | HN];
        [ exists true, RE; constructor; [ intros _; exact HLs | discriminate | discriminate ]
        | exists false, RE; constructor; [ discriminate | intros _; exact HmE | intros _; exact HN ] ]. }
    destruct HF as (lv & Rt & HF).
    apply valid_unit_alias;
      [ apply wf_me_lit; eapply wf_unit_eq_alias with (param_level := l) (param_sorts := ps) (lv := lv) (Rt := Rt) (lv' := lv) (Rt' := Rt);
        [ exact (ext_of_ctx' _ _ _ _ HwC) | exact HΔ | exact HΔ | exact HwE | exact HwE | exact Hps | exact HpΔ | exact HpΔ
        | exact (levels_flag_sorted _ _ _ _ _ _ _ HF) | exact (levels_flag_denotes _ _ _ _ _ _ _ HF)
        | exact (levels_flag_no_level _ _ _ _ _ _ _ HF)
        | exact (levels_flag_sorted _ _ _ _ _ _ _ HF) | exact (levels_flag_denotes _ _ _ _ _ _ _ HF)
        | exact (levels_flag_no_level _ _ _ _ _ _ _ HF) ]
                    | exact HΔ | exists l; exact HΔr | exact (rel_ctx_wf_app_r _ _ HC) | exact HC | exact HL | exact HE | ].
    destruct (me_denotes _ _ _ _ _ HwE) as (R & Rm & HmR & HmdR).
    exact (valid_modexp_intro _ _ _ _ _ _ _ _ HwE HmR HmdR HE HK HmR HmdR).
  - (* an alias of a filed module at arguments *)
    split; [ exact (rel_lit_flatten _ _ _ _ _ HΔ HΔw HΔr HΔa HK)
           | exact (valid_unit_abs _ _ Hgm Hgf _ _ _ _ HK HΔ HΔw HΔr (fun R HR => HΔa R (mdenote_lit _ _ _ _ _ HR))) ].
Qed.

(** ** Canonical Units *)

Lemma valid_unit_canon_all :
  (forall Γ K, valid_unit Γ K -> forall RK Rm, mdenote Θm Ξm Γ K RK -> mdesc_mod RK = Some Rm ->
     Γ ⊨ᵐ K ≈ mdesc_unit Rm /\ valid_unit Γ (mdesc_unit Rm)) /\
  (forall Γ H, valid_modexp Γ H -> forall R Rm, mdenote Θm Ξm Γ H R -> mdesc_mod R = Some Rm ->
     Γ ⊨ᵐ H ≈ mdesc_unit Rm /\ valid_unit Γ (mdesc_unit Rm)).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs RK Rm Hm Hmd.
    pose proof (valid_unit_filed _ _ _ _ _ _ _ Hw Hgl HΓ Hs) as HK.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmd; injection Hmd as <-.
    cbn [mdesc_unit]; split; [ exact (valid_unit_rel _ _ Hgf _ _ HK) | exact HK ].
  - (* a body: its own literal *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΔr HΓ HC Hsv Hsl IHsl Hs Hsx HU Hopv Hops IHops RK Rm Hm Hmd.
    pose proof (valid_unit_body _ _ _ _ _ _ Hw Hx HΔ HΔr HΓ HC Hsv Hsl Hs Hsx HU Hopv Hops) as HK.
    apply mdenote_lit_inv in Hm; inversion Hm; subst.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    cbn in Hmd; injection Hmd as <-; cbn [mdesc_unit]; split; [ exact HU | exact HK ].
  - (* an alias: its target's unit, abstracted *)
    intros Γ Δ E Hw HΔ HΔr HΓ HΔΓ HU HE Hsmt IHE RK Rm Hm Hmd.
    apply mdenote_lit_inv in Hm; inversion Hm as [| ? ? ? ? RE REm HmE HmdE]; subst.
    pose proof (mdesc_mod_is_mod _ _ HmdE) as Him.
    rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ Him)) in Hmd; injection Hmd as <-.
    destruct (IHE _ _ HmE HmdE) as [HEu HKu].
    destruct Δ as [| e Δ0].
    + rewrite mdesc_up_nil; cbn [List.app] in *.
      split; [ exact (rel_modexp_under_ctx_trans (rel_modexp_under_ctx_beta_alias0 _ _ HE) HEu) | exact HKu ].
    + pose proof (proj1 (modexp_gen _ _ _ _ _ Hw)) as Hf; cbn [gen_m] in Hf.
      destruct (proj1 (unit_eq_params_evaluated _ _ _ _ _ (unit_eq_of_full _ _ _ _ Hf))) as [lw HΔw]; cbn [gu_params] in HΔw.
      destruct HΔr as [lr HΔr].
      (* the alias's flag: what the unit of the target's module part
         denotes has the module part the target's has *)
      assert (HΔa : forall R, mdenote Θm Ξm ((e :: Δ0) ++ Γ) (mdesc_unit REm) R -> desc_levels_abstractable Θm Ξm Γ (e :: Δ0) R).
      { destruct Hf as [_ _ _ _ _ HEE _ lv Rt [Hf1 Hf2 Hf3]]; intros R HR; destruct lv; [ left; exact (Hf1 eq_refl) | right ].
        pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgm HmE) HmdE) as Hcan.
        destruct (mdesc_unit_denote _ _ _ Hgm Hcan Him _ (wf_mdenote_mod_xp _ _ _ _ _ _ _ HEE HmE HmdE)) as (Ru & Hmu & Hmdu).
        rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ HR _ Hmu).
        rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ HmE _ (Hf2 eq_refl)) in HmdE.
        exact (no_level_of_mod _ _ _ _ _ Hmdu (no_level_mod _ _ _ _ _ (Hf3 eq_refl) HmdE)). }
      destruct (rel_alias_unit_up Γ (e :: Δ0) REm (max lw lr) ltac:(discriminate) HΔ (params_evaluated_max _ _ _ _ _ _ HΔw)
                  (rel_params_evaluated_ge _ _ lr (max lw lr) ltac:(lia) HΔr) Him HΔa HKu) as [Hup HKup].
      split; [| exact HKup ].
      eapply rel_modexp_under_ctx_trans; [| exact Hup ].
      exact (rel_lit_alias _ _ _ _ _ (ext_refl _ _ HΔΓ) HΔ HΔ eq_refl HEu (rel_modexp_refl_right HEu)).
  - (* a module expression equal to a valid unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK R' Rm' Hm Hmd.
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH), HmodH in Hmd; injection Hmd as <-.
    destruct (IHK _ _ HmK HmodK) as [HKu HKK]; split; [ exact (rel_modexp_under_ctx_trans HHK HKu) | exact HKK ].
Qed.

Corollary valid_modexp_canon : forall Γ H R Rm, valid_modexp Γ H -> mdenote Θm Ξm Γ H R -> mdesc_mod R = Some Rm ->
    Γ ⊨ᵐ H ≈ mdesc_unit Rm /\ valid_unit Γ (mdesc_unit Rm).
Proof. intros * HH Hm Hmd; exact (proj2 valid_unit_canon_all _ _ HH _ _ Hm Hmd). Qed.

Lemma valid_modexp_of_valid_unit : forall Γ K, valid_unit Γ K -> valid_modexp Γ K.
Proof.
  intros * HK.
  pose proof (valid_unit_wf _ _ _ _ HK) as HwK.
  destruct (me_denotes _ _ _ _ _ HwK) as (R & Rm & HmR & HmdR).
  exact (valid_modexp_intro _ _ _ _ _ _ _ _ HwK HmR HmdR (valid_unit_rel _ _ Hgf _ _ HK) HK HmR HmdR).
Qed.

End Fixed_GCtx.
