(** * The Rules for Module Expressions and Members

    A member read through the spine of a module expression is the member
    selected from the expression's value ([eval_mem_of_sel]): arguments
    commute with selection.  With this, the module PER relates the values of
    equivalent module expressions, and the members of related values are
    related at their canonical types. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases SubtypingCases
  VariableCases LetCases TrueFalseCases UnitCases InstanceCases MemberCases MemberTyping MemberReps MemberSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Arguments Commute with Selection *)

Lemma selc_local_le : forall ρ U args ch r,
    eval_selc gc_deps gc_stack (dm_local ρ U args) ch r -> List.length args <= List.length (gu_params U).
Proof.
  intros * H; inversion H; subst;
    match goal with Hs : eval_sel _ _ _ _ _ |- _ => inversion Hs | Hs : eval_selm _ _ _ _ _ |- _ => inversion Hs end;
    subst; cbn; lia.
Qed.

Lemma sel_app_local : forall ρ U args n ch r,
    List.length args < List.length (gu_params U) -> ch <> nil ->
    eval_selc gc_deps gc_stack (dm_local ρ U (args ++ n :: nil)) ch r ->
    exists f, eval_selc gc_deps gc_stack (dm_local ρ U args) ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  intros * Hl Hch Hs.
  exists (d_member (dm_local ρ U args) ch); split; [ apply selc_unsat_ex; assumption |].
  econstructor; [| exact Hs ].
  destruct U as [Δ [Φ | E]]; cbn in Hl; [ apply eval_appm_body | apply eval_appm_alias_unsat ]; exact Hl.
Qed.

Lemma sel_app_global : forall ch p args n r, ch <> nil ->
    eval_selc gc_deps gc_stack (dm_global p (args ++ n :: nil)) ch r ->
    exists f, eval_selc gc_deps gc_stack (dm_global p args) ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  induction ch as [| y ch IH]; intros * Hch Hs; [ congruence |].
  inversion Hs; subst.
  - match goal with Hs1 : eval_sel _ _ _ _ _ |- _ => inversion Hs1; subst end.
    match goal with Ha : eval_apps _ _ _ (args ++ _) r |- _ =>
      apply (eval_apps_app gc_deps gc_stack) in Ha as (g & Hg & Ha2) end.
    inversion Ha2; subst.
    match goal with Hn : eval_apps _ _ _ nil r |- _ => inversion Hn; subst end.
    eexists; split; [ constructor; econstructor; eassumption | eassumption ].
  - match goal with Hc : eval_selc _ _ _ ch r |- _ => assert (Hch' : ch <> nil) by (intros ->; inversion Hc) end.
    match goal with Hs1 : eval_selm _ _ _ _ _ |- _ => inversion Hs1; subst end.
    + destruct (IH _ _ _ _ Hch' ltac:(eassumption)) as (f & Hf & Ha).
      exists f; split; [ econstructor; [ apply eval_selm_global; assumption | exact Hf ] | exact Ha ].
    + match goal with H1 : eval_selmc _ _ (dm_local nil ?U _) ?ch1 ?h1, H2 : eval_selc _ _ ?h1 ch r |- _ =>
        assert (Hc : eval_selc gc_deps gc_stack (dm_local nil U (args ++ n :: nil)) (ch1 ++ ch) r)
          by (apply (eval_selc_app gc_deps gc_stack); [ exact Hch' | eexists; split; eassumption ]);
        pose proof (selc_local_le _ _ _ _ _ Hc) as Hle; rewrite length_app in Hle; cbn in Hle;
        assert (Hlt : List.length args < List.length (gu_params U)) by lia;
        assert (Hne : ch1 ++ ch <> nil) by (destruct ch; [ congruence | intros Hx; apply app_eq_nil in Hx as [_ Hx]; discriminate ]);
        destruct (sel_app_local _ _ _ _ _ _ Hlt Hne Hc) as (f & Hf & Ha);
        apply (eval_selc_app gc_deps gc_stack) in Hf as (h1' & Hh1' & Hf); [| exact Hch' ];
        exists f; split; [ econstructor; [ eapply eval_selm_global_alias; eassumption | exact Hf ] | exact Ha ] end.
Qed.

(** Selecting from an applied module value is applying the selected member. *)
Lemma sel_appm : forall h0 n h, eval_appm gc_deps gc_stack h0 n h ->
    forall ch r, ch <> nil -> eval_selc gc_deps gc_stack h ch r ->
    exists f, eval_selc gc_deps gc_stack h0 ch f /\ eval_app gc_deps gc_stack f n r.
Proof.
  induction 1 as [p args n | ρ Δ Φ args n Hl | ρ Δ E args n Hl | ρ Δ E args n h1 r1 Hl HE Hap IH
                 | hm n hm' ch0 r1 Hap Hs ]; intros ch r Hch Hc.
  - exact (sel_app_global _ _ _ _ _ Hch Hc).
  - eapply sel_app_local; [ cbn; exact Hl | exact Hch | exact Hc ].
  - eapply sel_app_local; [ cbn; exact Hl | exact Hch | exact Hc ].
  - destruct (IH _ _ Hch Hc) as (f & Hf & Ha).
    exists f; split; [ apply (selc_alias _ _ _ _ _ _ _ Hl HE); exact Hf | exact Ha ].
  - exists (d_member hm (ch0 ++ ch)); split; [ apply selc_member_ex; exact Hch |].
    econstructor; [ exact Hap |].
    apply (eval_selc_app gc_deps gc_stack); [ exact Hch | eexists; split; eassumption ].
Qed.

Lemma eval_spine_of_selc : forall H ρ h, eval_modexp gc_deps gc_stack H ρ h ->
    forall R args pre, modexp_spine H = (R, args, pre) ->
    forall ch r, ch <> nil -> eval_selc gc_deps gc_stack h ch r ->
    exists hr f ns, eval_modexp gc_deps gc_stack R ρ hr /\ eval_selc gc_deps gc_stack hr (pre ++ ch) f /\
      eval_exps gc_deps gc_stack args ρ ns /\ eval_apps gc_deps gc_stack f ns r.
Proof.
  induction H as [p | x | H IH y | H IH N | U]; intros ρ h He R args pre Hs ch r Hch Hc;
    cbn in Hs.
  1,2,5: injection Hs as <- <- <-; exists h, r, nil; repeat split; [ exact He | exact Hc | constructor | constructor ].
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    match goal with H1 : eval_modexp _ _ H ρ ?h0, H2 : eval_selm _ _ ?h0 y h |- _ =>
      destruct (IH _ _ H1 _ _ _ eq_refl (y :: ch) r ltac:(discriminate) ltac:(econstructor; eassumption))
        as (hr & f & ns & Hr & Hf & Hns & Ha) end.
    exists hr, f, ns; repeat split; [ exact Hr | rewrite <- app_assoc; exact Hf | exact Hns | exact Ha ].
  - destruct (modexp_spine H) as [[R0 a0] p0] eqn:E; injection Hs as <- <- <-.
    inversion He; subst.
    match goal with H1 : eval_modexp _ _ H ρ ?h0, H2 : eval_exp _ _ N ρ ?n, H3 : eval_appm _ _ ?h0 ?n h |- _ =>
      destruct (sel_appm _ _ _ H3 _ _ Hch Hc) as (f0 & Hf0 & Ha0);
      destruct (IH _ _ H1 _ _ _ eq_refl _ _ Hch Hf0) as (hr & f & ns & Hr & Hf & Hns & Ha);
      exists hr, f, (ns ++ n :: nil); repeat split; [ exact Hr | exact Hf | |];
        [ apply eval_exps_app; [ exact Hns | econstructor; [ exact H2 | constructor ] ]
        | apply (eval_apps_app gc_deps gc_stack); exists f0; split; [ exact Ha | econstructor; [ exact Ha0 | constructor ] ] ] end.
Qed.

Lemma eval_mem_of_sel : forall H ρ h x r,
    eval_modexp gc_deps gc_stack H ρ h -> eval_sel gc_deps gc_stack h x r -> ⟦ a_mem H x ⟧ ρ ↘ r.
Proof.
  intros * He Hs.
  destruct (modexp_spine H) as [[R args] pre] eqn:E.
  destruct (eval_spine_of_selc _ _ _ He _ _ _ E (x :: nil) r ltac:(discriminate) ltac:(constructor; exact Hs))
    as (hr & f & ns & Hr & Hf & Hns & Ha).
  apply (eval_mem_spine gc_deps gc_stack _ _ _ _ _ _ _ E); do 3 eexists; eauto.
Qed.

End Fixed_GCtx.
