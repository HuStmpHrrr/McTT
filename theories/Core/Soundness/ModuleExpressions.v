(** * Module Expressions at the Instances

    A module expression is glued at the instances of its context
    ([glu_rel_modexp_under_sub]) when, at each instance, its value at
    every glued environment is glued as it ([glu_modexp_at]).  A slot moves
    to its instance's module component: the literal of the slot's unit
    moved, glued by the construction ([glu_unit_modexp_at]), or a slot,
    glued by the context gluing ([glu_slot_modexp_at]).  A literal is the
    construction at each instance ([glu_rel_modexp_under_sub_lit]).  An
    application is glued by the clauses of the value lacking a parameter
    ([glu_modexp_at_app]). *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness Require ContextCases UnitCases.
From Mctt.Core.Completeness.Modules Require Import ModexpRel Values.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases ModuleValues Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A module slot of a context glued with its variables' types is glued at
    the instances: its instance is its unit's literal moved, glued by the
    construction from the instance's gluing of the unit, or a slot of the
    instance's context. *)
Lemma glu_rel_modexp_under_sub_var : forall {Γ x U},
    glu_rel_ctx_types Γ ->
    Γ ∋ #x ≔ₘ U ->
    glu_rel_modexp_under_sub Γ (me_var x).
Proof.
  intros * HΓ Hx; constructor; [ exact HΓ |].
  intros Γ' τ Hτ.
  pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
  pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
  destruct (wf_sub_mod_compat _ _ _ _ _ Hτt _ _ Hx) as [E | (z & Ez & Hz)]; cbn [modexp_sub]; [ rewrite E | rewrite Ez ].
  - (** The literal of the unit moved *)
    assert (HwΓ : ⊢ Γ) by exact (wf_sub_cod _ _ _ _ _ Hτt).
    assert (HwΓ' : ⊢ Γ') by exact (wf_sub_dom _ _ _ _ _ Hτt).
    pose proof (sub_preserves_unit _ _ _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ HwΓ Hx) Hτt) as HUτ.
    pose proof (glu_rel_sub_inst_mods _ _ _ Hτ _ _ Hx _ _ (wf_wk_id _ _ _ HwΓ') HΓ') as Hg; rewrite gunit_wk_id in Hg.
    exact (glu_unit_modexp_at _ _ HUτ HΓ' Hg).
  - (** A slot of the instance's context *)
    exact (glu_slot_modexp_at _ _ _ Hz).
Qed.

(** An application of a glued module expression to a glued argument of
    its next parameter's type is glued: the value lacks the parameter
    ([modexp_next_param], the parameter's value related to the type's),
    so it is glued as a value lacking a parameter, at the argument glued
    at the parameter's value ([glu_univ_elem_exp_conv]); the application
    to the variable read through [Id,,N] is the application to [N]. *)
Lemma glu_modexp_at_app : forall Γ H N R T B T1 Srt,
    glu_modexp_at Γ H ->
    Γ ⊩ N : B ->
    mdenote gc_deps gc_stack Γ H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Γ ⊢ B : Srt -> evaluated_sort Srt -> Γ ⊢ N : B ->
    modexp_next_param Γ H B ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N ->
    glu_modexp_at Γ (me_app H N).
Proof.
  intros * HH HN Hm HT Hv HB HS HNt Hnp HHN Sb HSb Δ σ ρ Hσ.
  destruct (HH _ HSb _ _ _ Hσ) as (h & Eh & Hg).
  pose proof (glu_ctx_env_sub_escape HSb _ _ _ Hσ) as Hσt.
  destruct HN as [SbN HSbN kN HNb].
  assert (EN : Sb <∙> SbN) by (eapply functional_glu_ctx_env; eassumption).
  destruct (HNb _ _ _ (proj1 (EN _ _ _) Hσ)) as [aB n PB ElB EaB En HgB HNσ].
  destruct (glu_ctx_env_per_ctx_env HSb) as [RΓ HRΓ].
  pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
  destruct (Hnp _ HRΓ _ Hρ) as [h' a aB' i RB Eh' Hn EaB' HR].
  pose proof (functional_eval_modexp _ _ _ _ Eh' Eh) as ->.
  pose proof (functional_eval_exp _ _ _ _ EaB' EaB) as ->.
  (** The value lacks a parameter: it is glued as such *)
  inversion Hg; subst;
    [ exfalso; eapply next_param_global_sat; eassumption
    | exfalso; inversion Hn; subst; match goal with Hl : _ ++ _ :: nil = nil |- _ => destruct Δ0; discriminate end |].
  match goal with Hn' : next_param h ?a0 |- _ => pose proof (next_param_functional _ _ Hn _ Hn') as <- end.
  rename H4 into Hpar, H5 into Happ.
  pose proof (glu_sub_through_id _ _ _ Hσt) as Hst.
  rewrite <- (modexp_sub_id H) in Hm.
  pose proof (evaluated_sort_type_sort _ HS) as HTS.
  destruct (Hpar _ _ _ _ _ _ _ _ _ _ Hst Hm HT Hv HTS HB) as (j & Pa & Ela & [Hga HBPa]).
  (** The parameter's type is of the kind of its sort, an evaluated one *)
  pose proof (completeness_fundamental_exp _ _ _ HB) as HBc.
  assert (Hks : exists κs, sort_kind Srt κs /\ evaluated_kind κs /\ Completeness.ContextCases.rel_type_kind Γ B κs).
  { destruct HS as [l |];
      [ exists ak_relevant; split; [ constructor | split; [ constructor | exact (Completeness.ContextCases.rel_type_kind_of_typ HBc) ] ]
      | exists ak_level; split; [ constructor | split; [ constructor | exact (Completeness.ContextCases.rel_type_kind_of_level_sort HBc) ] ] ]. }
  destruct Hks as (κs & Hsk & Hκs & HBk).
  destruct (HBk _ HRΓ _ _ Hρ) as (aB0 & EaB0 & HkB).
  pose proof (functional_eval_exp _ _ _ _ EaB0 EaB) as ->.
  pose proof (per_univ_elem_kind _ _ _ _ HR) as Hka; rewrite HkB in Hka.
  (** So the argument's value is its evaluation *)
  assert (En' : ⟦ N ⟧ ρ ↘ n) by (unfold glu_term_value in En; rewrite HkB in En; destruct Hκs; exact En).
  (** The argument at the parameter's value *)
  assert (HNa : Δ ⊢ N[σ] : B[σ] ® n ∈ Ela)
    by (eapply glu_univ_elem_exp_conv_universe_index;
        [ exists RB; apply per_univ_elem_sym; exact HR | exact HgB | exact Hga | exact HNσ | exact HBPa ]).
  (** The value at the argument: the application evaluates at [ρ]
      (completeness) *)
  destruct (Completeness.UnitCases.rel_modexp_at _ _ _ _ _ (proj2 (proj2 completeness_fundamental_modules) _ _ _ HHN) HRΓ _ _ Hρ)
    as (hN & _ & EhN & _ & _).
  assert (Ehc : $ᵐ| h & n | gc_deps ⍮ gc_stack ↘ hN).
  { inversion EhN; subst.
    match goal with
    | Eh1 : ⟦ H ⟧ᵐ _ ⍮ _ ⍮ ρ ↘ ?h1, En1 : ⟦ N ⟧ ρ ↘ ?n1 |- _ =>
        pose proof (functional_eval_modexp _ _ _ _ Eh1 Eh) as ->;
        pose proof (functional_eval_exp _ _ _ _ En1 En') as ->
    end.
    assumption. }
  exists hN; split; [ exact EhN |].
  (** Glued as the application to the variable over the context extended
      by the parameter, read through [Id,,N] *)
  pose proof (Happ _ _ _ _ _ _ _ _ _ _ Hst Hm HT Hv HTS HB _ _ _ _ _ _ Hga HBPa HNa Ehc) as Hg1.
  rewrite Hka in Hg1.
  assert (HNσt : Δ ⊢ N[σ] : B[σ]) by exact (glu_univ_elem_trm_escape _ _ _ _ Hga _ _ _ _ HNa).
  assert (HId : Γ ⊢ˢ Id,,N : Γ ▹{κs} B)
    by (eapply wf_sub_extend; [ exact (wf_sub_id _ _ _ (wf_sub_cod _ _ _ _ _ Hσt)) | exact HB | exact Hsk | rewrite exp_sub_id; exact HNt ]).
  assert (Hsb : sb_eq ((Id,,N) ⨟ σ) (σ,,N[σ])) by (intros [| k]; reflexivity).
  assert (Heq : Δ ⊢ˢ σ,,N[σ] ≈ (Id,,N) ⨟ σ : Γ ▹{κs} B).
  { apply wf_sub_eq_of_sb_eq; [ eapply wf_sub_extend; [ exact Hσt | exact HB | exact Hsk | exact HNσt ] | symmetry; exact Hsb ]. }
  pose proof (proj1 glu_dmod_through _ _ _ _ _ Hg1 _ _ _ HId Hσt Heq) as Hg2.
  assert (EH : (me_app H[Id]ᵐ[Wk]ᵐ #0)[Id,,N]ᵐ = me_app H N).
  { cbn [modexp_sub]; rewrite !modexp_sub_sub; f_equal.
    rewrite <- (modexp_sub_id H) at 2; apply modexp_sub_sb_eq; intros [| k]; reflexivity. }
  rewrite EH in Hg2; exact Hg2.
Qed.

End Fixed_GCtx.
