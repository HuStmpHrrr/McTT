(** * Telescopes over a Context in the PER Model

    The eliminator's motive and branches live under telescopes over the
    context of the elimination, whose types are those of a closed
    declaration instantiated by terms of the context.  This file gives the
    generic tools the eliminator's case of the fundamental theorem uses:

    - a closed context is a context over any other: its relation is weaker
      than that of the extension ([closed_app_sem]), so its judgments hold
      there ([closed_app_valid]);
    - its instance at terms of a context is a substitution built from valid
      parts ([gsub_closed_inst]);
    - the [q^n] of a semantic substitution into a context extended by a
      telescope ([rel_sub_qn]), and its value ([eval_sub_qn_args]);
    - related arguments of a telescope at the value of a substitution are
      related arguments of its instance ([tele_stage_rel]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import FunctionCases.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Closed Context over Another *)

Lemma closed_app_sem : forall C Γ, all_assumptions C -> ⊨ C -> ⊨ Γ ->
    ⊨ C ++ Γ /\
    (forall RC RCΓ, EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C ++ Γ ≈ C ++ Γ ∈ per_ctx_env ↘ RCΓ ->
       forall ρ ρ', RCΓ ρ ρ' -> RC ρ ρ').
Proof.
  induction C as [| e C IH]; intros Γ HCa HC HΓ; cbn [List.app].
  - split; [ exact HΓ |].
    intros * HR _ ρ ρ' _.
    assert (E : RC <~> (fun _ _ => True)) by (eapply per_ctx_env_right_irrel; [ exact HR | exact per_ctx_env_nil_true ]).
    apply E; exact I.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HCa' : all_assumptions C) by (inversion HCa; assumption).
    destruct (rel_ctx_wf_ass_inv HC) as (Srt & HS & HA).
    pose proof (rel_ctx_wf_tail HC) as HC'.
    destruct (IH Γ HCa' HC' HΓ) as [HCΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HC') as [RC' HRC'].
    destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ' HRCΓ'].
    assert (HA' : C ++ Γ ⊨ A ≈ A : Srt)
      by (eapply rel_exp_under_ctx_restrict; [ exact HRCΓ' | exact HRC' | apply Hres; assumption
                                              | rewrite List.length_app; lia
                                              | exact (ctx_props_agree_app _ _ _ _ HRCΓ' HRC' (Hres _ _ HRC' HRCΓ')) | exact HA ]).
    destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA) as [i HAt].
    destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA') as [i' HAt'].
    pose proof (per_ctx_env_of_typ (κ := κ) HRC' HAt) as HRCA.
    pose proof (per_ctx_env_of_typ (κ := κ) HRCΓ' HAt') as HRCΓA.
    split; [ econstructor; [ exact HCΓ | exact HRCΓA | exact HS | exact HA' ] |].
    intros * HR HRΓ ρ ρ' Hρ.
    assert (E1 : RC <~> per_env_extend A A RC') by (eapply per_ctx_env_right_irrel; eassumption).
    assert (E2 : RCΓ <~> per_env_extend A A RCΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    apply E1; apply E2 in Hρ; destruct Hρ as [Ht Hh Hl Hr Hrl Hrr].
    exact (mk_per_ctx_env_cons_rel _ _ _ _ _ _ (Hres _ _ HRC' HRCΓ' _ _ Ht) Hh Hl Hr Hrl Hrr).
Qed.

Lemma closed_app_valid : forall C Γ T M M', all_assumptions C -> ⊨ C -> ⊨ Γ ->
    C ⊨ M ≈ M' : T -> C ++ Γ ⊨ M ≈ M' : T.
Proof.
  intros * HCa HC HΓ HM.
  destruct (closed_app_sem C Γ HCa HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  eapply rel_exp_under_ctx_restrict; [ exact HRCΓ | exact HRC | apply Hres; assumption
                                     | rewrite List.length_app; lia
                                     | exact (ctx_props_agree_app _ _ _ _ HRCΓ HRC (Hres _ _ HRC HRCΓ)) | exact HM ].
Qed.

(** ** The Instance of a Closed Context *)

Lemma gsub_closed_inst : forall C Γ Ms, all_assumptions C -> ⊨ C -> ⊨ Γ ->
    List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    gsub Γ (sb_of_list Id Ms) (C ++ Γ).
Proof.
  induction C as [| e C IH]; intros Γ Ms HCa HC HΓ Hl HMs HMss.
  - destruct Ms; cbn in Hl; [| discriminate ]; cbn; constructor; exact HΓ.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HCa' : all_assumptions C) by (inversion HCa; assumption).
    destruct (rel_ctx_wf_ass_inv HC) as (Srt & HS & HA).
    pose proof (rel_ctx_wf_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length C) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass κ A :: C) Id (Ms' ++ M :: nil) = tele_insts C Id Ms' ++ A[sb_of_list Id Ms'] :: nil).
    { change (ce_ass κ A :: C) with ((ce_ass κ A :: nil) ++ C).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts C Id Ms') = List.length C) by (rewrite length_tele_insts by exact HCa'; lia).
    pose proof (IH Γ Ms' HCa' HC' HΓ ltac:(lia)) as Hg.
    apply List.Forall_app in HMss as [HMss' HMs1]; inversion HMs1 as [| ? ? HMsc _]; subst.
    rewrite sb_of_list_app; cbn [sb_of_list List.app].
    eapply gsub_ass; [ apply Hg | exact HS | exact (closed_app_valid _ _ _ _ _ HCa' HC' HΓ HA) | | exact HMsc ].
    + intros k N T HN HT.
      assert (Hk : k < List.length C) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    + exact HMss'.
    + apply (HMs (List.length C)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity.
Qed.

(** ** Relations along a Chain of Types *)

Lemma per_univ_elem_chain_iff : forall i j R S a b c,
    DF a ≈ b ∈ per_univ_elem i ↘ R -> DF b ≈ c ∈ per_univ_elem j ↘ S -> (R <~> S).
Proof.
  intros * H1 H2.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 H2) as (R' & H3 & E).
  etransitivity; [ exact E | eapply per_univ_elem_left_irrel; [ exact H3 | exact H2 ] ].
Qed.

(** ** Environments of a Context Extended by a Telescope *)

Lemma tele_args_env_rel_gen : forall Δ Γ RΓ R ρ ρ' xs xs',
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R -> ⊨ Δ ++ Γ ->
    RΓ ρ ρ' -> List.length xs = List.length Δ ->
    per_tele_args (List.rev Δ) ρ ρ' xs xs' -> R (env_tele ρ (List.rev Δ) xs) (env_tele ρ' (List.rev Δ) xs').
Proof.
  intros * HΓ HR HC Hρ Hl Hg.
  assert (HC' : ⊨ List.rev (List.rev Δ) ++ Γ) by (rewrite List.rev_involutive; exact HC).
  destruct (tele_args_rel _ _ _ _ _ Hg _ _ HΓ Hρ HC') as (R' & HR' & Hρ').
  rewrite List.firstn_all2 in HR' by (rewrite List.length_rev; lia).
  rewrite List.rev_involutive in HR'.
  assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; exact Hρ'.
Qed.

(** Arguments related at a telescope read back at the closures of its
    types, as the telescope's entries store them. *)
Lemma per_tele_args_entries_readable : forall ts ρ ρ' xs xs', per_tele_args ts ρ ρ' xs xs' ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (tele_entries ρ ts xs) /\
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) (tele_entries ρ' ts xs').
Proof.
  induction 1 as [ts ρ ρ' | i A ρ ρ' a a' ts args args' κ R HA Ha Hg IH]; [ split; constructor |].
  destruct HA as [b b' Eb Eb' HR].
  pose proof (entry_readable_of_elem_closure Eb Eb' HR Ha) as [Ra Ra'].
  destruct IH as [IH1 IH2]; split; constructor; assumption.
Qed.

(** Arguments related at a telescope make related extensions of the bases,
    whatever readable types the extensions store them at: a context PER
    reads the types only through their readability. *)
Lemma tele_args_env_rel_typed : forall ts Tb RTb R, EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> all_assumptions ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' vts vts', RTb ρ ρ' -> List.length vts = List.length ts -> List.length vts' = List.length ts ->
      per_tele_args ts ρ ρ' (List.map fst vts) (List.map fst vts') ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts' ->
      R (env_extend_typed ρ vts) (env_extend_typed ρ' vts').
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts HR * Hρ Hl Hl' Hg Hr Hr'.
  - destruct vts, vts'; cbn in Hl, Hl'; try discriminate.
    assert (E : R <~> RTb) by (eapply per_ctx_env_right_irrel; eassumption). apply E; exact Hρ.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
    destruct vts as [| [x t] vts], vts' as [| [x' t'] vts']; cbn in Hl, Hl'; try discriminate.
    cbn [List.map fst] in Hg.
    inversion Hg as [| ? A0 ? ? ? ? ? ys ys' ? R0 HA Hx Hg']; subst.
    inversion Hr as [| ? ? Rt Hr0]; inversion Hr' as [| ? ? Rt' Hr0']; subst; cbn [fst snd] in Rt, Rt'.
    cbn [List.rev] in HC, HR; rewrite <- List.app_assoc in HC, HR; cbn [List.app] in HC, HR.
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ (κ := κ) HTb HAv) as HTb'.
    assert (HP : PER RTb) by (eapply per_env_PER; exact HTb).
    destruct HA as [a a' Ea Ea' HR0].
    pose proof (entry_readable_of_elem_closure Ea Ea' HR0 Hx) as [Rx Rx'].
    assert (HP0 : PER R0) by (eapply per_elem_PER; exact HR0).
    assert (Hρρ : RTb ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    assert (Hρ'ρ' : RTb ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρρ) as (b & b0 & Eb & Eb0 & [R1 HR1]).
    destruct (rel_type_inversion_simple_at HTb HAv _ _ Hρ'ρ') as (b' & b0' & Eb' & Eb0' & [R2 HR2]).
    assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b' = a') as -> by (eapply functional_eval_exp; eassumption).
    assert (b0' = a') as -> by (eapply functional_eval_exp; eassumption).
    assert (E1 : R1 <~> R0) by (eapply per_univ_elem_right_irrel; [ exact HR1 | exact HR0 ]).
    assert (E2 : R2 <~> R0) by (eapply per_univ_elem_left_irrel; [ exact HR2 | exact HR0 ]).
    assert (Hxx : R1 x x) by (apply E1; etransitivity; [ exact Hx | symmetry; exact Hx ]).
    assert (Hx'x' : R2 x' x') by (apply E2; etransitivity; [ symmetry; exact Hx | exact Hx ]).
    (** The rest are related over the bases at the given types, which are
        related to those at the closures of the parameter's type. *)
    assert (Hb : per_env_extend A A RTb (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t'))
      by (apply per_env_extend_intro'; [ exact Hρ | exact (per_head_of Ea Ea' HR0 Hx) | exact Rt | exact Rt' ]).
    assert (Hg2 : per_tele_args ts (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t') (List.map fst vts) (List.map fst vts')).
    { eapply (per_tele_args_base _ _ _ HTb' HC Hts' (ρ ↦ x ⦂ entry_type_closure A ρ) (ρ' ↦ x' ⦂ entry_type_closure A ρ'));
        [ | | | exact Hg' ].
      - apply per_env_extend_intro'; [ exact Hρ | exact (per_head_of Ea Ea' HR0 Hx) | exact Rx | exact Rx' ].
      - apply per_env_extend_intro'; [ exact Hρρ | exact (per_head_of Ea Ea HR1 Hxx) | exact Rx | exact Rt ].
      - apply per_env_extend_intro'; [ exact Hρ'ρ' | exact (per_head_of Ea' Ea' HR2 Hx'x') | exact Rx' | exact Rt' ]. }
    exact (IH _ _ _ HTb' HC Hts' HR _ _ vts vts' Hb ltac:(lia) ltac:(lia) Hg2 Hr0 Hr0').
Qed.

(** And conversely: extensions related at the telescope store their values
    at readable types. *)
Lemma per_tele_args_of_env_extend_readable : forall ts Tb RTb R, EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> all_assumptions ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' vts vts', List.length vts = List.length ts -> List.length vts' = List.length ts ->
      R (env_extend_typed ρ vts) (env_extend_typed ρ' vts') ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts /\
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts'.
Proof.
  induction ts as [| e ts IH]; intros * HTb HC Hts HR * Hl Hl' Hρ.
  - destruct vts, vts'; cbn in Hl, Hl'; try discriminate; split; constructor.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion Hts as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (Hts' : all_assumptions ts) by (inversion Hts; assumption).
    destruct vts as [| [x t] vts], vts' as [| [x' t'] vts']; cbn in Hl, Hl'; try discriminate.
    cbn [List.rev] in HC, HR; rewrite <- List.app_assoc in HC, HR; cbn [List.app] in HC, HR.
    destruct (rel_ctx_wf_ass_typ (rel_ctx_wf_app_r _ _ HC)) as [j HAv].
    pose proof (per_ctx_env_of_typ (κ := κ) HTb HAv) as HTb'.
    destruct (IH _ _ _ HTb' HC Hts' HR (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t') vts vts' ltac:(lia) ltac:(lia) Hρ) as [H1 H2].
    destruct (per_tele_args_of_env_extend _ _ _ _ HTb' HC Hts' HR (ρ ↦ x ⦂ t) (ρ' ↦ x' ⦂ t') vts vts' ltac:(lia) ltac:(lia) Hρ)
      as [[_ _ _ _ [Rt _] [Rt' _]] _].
    split; constructor; cbn [fst snd]; assumption.
Qed.

(** Extensions related at the telescope stay related when one side's
    values are stored at other readable types. *)
Lemma per_ctx_env_retype_right : forall ts Tb RTb R, EF Tb ≈ Tb ∈ per_ctx_env ↘ RTb -> ⊨ List.rev ts ++ Tb -> all_assumptions ts ->
    EF List.rev ts ++ Tb ≈ List.rev ts ++ Tb ∈ per_ctx_env ↘ R ->
    forall ρ ρ' vts vts' wts', List.length vts = List.length ts -> List.length vts' = List.length ts ->
      R (env_extend_typed ρ vts) (env_extend_typed ρ' vts') ->
      List.map fst wts' = List.map fst vts' ->
      List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts' ->
      R (env_extend_typed ρ vts) (env_extend_typed ρ' wts').
Proof.
  intros * HTb HC Hts HR * Hl Hl' H Hw Rw.
  destruct (per_tele_args_of_env_extend _ _ _ _ HTb HC Hts HR _ _ _ _ Hl Hl' H) as [Hρ Hg].
  destruct (per_tele_args_of_env_extend_readable _ _ _ _ HTb HC Hts HR _ _ _ _ Hl Hl' H) as [Rv _].
  assert (Hlw : List.length wts' = List.length ts) by (rewrite <- (List.length_map fst), Hw, List.length_map; exact Hl').
  rewrite <- Hw in Hg.
  exact (tele_args_env_rel_typed _ _ _ _ HTb HC Hts HR _ _ _ _ Hρ Hl Hlw Hg Rv Rw).
Qed.

(** ** [q^n] of a Semantic Substitution *)

Lemma rel_sub_qn : forall Δ Γ Γ' σ σ', all_assumptions Δ -> ⊨ Δ ++ Γ -> Γ' ⊨ˢ σ ≈ σ' : Γ ->
    tele_sub Δ σ ++ Γ' ⊨ˢ sb_qn (List.length Δ) σ ≈ sb_qn (List.length Δ) σ' : Δ ++ Γ.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ Hσ; cbn [List.app tele_sub List.length sb_qn]; [ exact Hσ |].
  assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
  destruct He as (κ & A & ->).
  assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
  destruct (rel_ctx_wf_ass_typ HΔ) as [i HA].
  cbn [centry_sub].
  exact (rel_sub_under_ctx_q (IH _ _ _ _ HΔa' (rel_ctx_wf_tail HΔ) Hσ) HA).
Qed.

Lemma env_entry_typed_lt : forall ρ ρ' vts x, x < List.length vts ->
    env_entry (env_extend_typed ρ vts) x = env_entry (env_extend_typed ρ' vts) x.
Proof.
  intros; rewrite !env_extend_typed_rev, !env_entry_nth, !List.app_nth1 by (rewrite List.length_rev, List.length_map; lia).
  reflexivity.
Qed.

(** The heads of an environment of [K ++ Γ] read back at [K], a telescope
    of assumptions: their room does not depend on the context. *)
Lemma env_heads_readable_app_tele : forall K Γ ρ, all_assumptions K -> env_heads_readable (K ++ Γ) ρ -> env_heads_readable K ρ.
Proof.
  intros * HK H x e Hx.
  pose proof (List.nth_error_In _ _ Hx) as Hin.
  unfold all_assumptions in HK; rewrite List.Forall_forall in HK; destruct (HK _ Hin) as (κ & A & ->).
  exact (H x (ce_ass κ A) ltac:(rewrite List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact Hx)).
Qed.

(** An environment the PER of a telescope [K] relates is related as its
    retagging at an extension [K ++ Γ], when the retagging is an
    environment of [K ++ Γ]'s PER: the PER of [K] reads only its first
    entries, up to retagging. *)
Lemma per_ctx_env_retag_app_left : forall K Γ RK RF X F, all_assumptions K ->
    EF K ≈ K ∈ per_ctx_env ↘ RK -> EF K ++ Γ ≈ K ++ Γ ∈ per_ctx_env ↘ RF ->
    RF (ctx_retag (K ++ Γ) X) (ctx_retag (K ++ Γ) X) -> RK X F -> RK (ctx_retag (K ++ Γ) X) F.
Proof.
  intros * HK HRK HRF HT HXF.
  pose proof (proj1 (per_ctx_env_heads_readable HRF _ _ HT)) as Hr.
  exact (per_ctx_env_resp_retagged_left HRK _ _ _ (env_agree_retagged_ctx_retag _ _ _)
           (env_heads_readable_app_tele _ _ _ HK Hr) HXF).
Qed.

(** The retagging of an environment at [Δ ++ Γ], past [Δ]: its tail
    retagged at [Γ]. *)
Lemma skipn_ctx_retag_app : forall Δ Γ X, List.skipn (List.length Δ) (ctx_retag (Δ ++ Γ) X) = ctx_retag Γ (List.skipn (List.length Δ) X).
Proof.
  induction Δ as [| e Δ IH]; intros; [ reflexivity |].
  cbn [List.length List.app ctx_retag List.skipn]; rewrite IH.
  destruct X; cbn [List.tl List.skipn]; [ rewrite !List.skipn_nil |]; reflexivity.
Qed.

(** [q^n σ] at the arguments [vts] of a telescope [Δ] over [Γ]: the
    arguments, then the value of [σ] past them, all retagged at [Δ ++ Γ]
    ([ctx_retag]): a variable keeps its entry, retagged; past the
    telescope, the value of [σ] retagged at [Γ], whose propositional
    entries are those of the value itself, at an environment of [Γ]'s
    PER. *)
#[local] Transparent eval_sub.
Lemma eval_sub_qn_args : forall Δ Γ σ ρ vts Y RΓ, List.length vts = List.length Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ Y Y ->
    ⟦ sb_wk σ (wk_shiftn (List.length Δ)) : Γ ⟧s env_extend_typed ρ vts ↘ Y ->
    ⟦ sb_qn (List.length Δ) σ : Δ ++ Γ ⟧s env_extend_typed ρ vts ↘ ctx_retag (Δ ++ Γ) (env_extend_typed Y vts).
Proof.
  intros * Hl HΓ HY H x Hx; rewrite (env_entry_ctx_retag _ _ _ Hx); rewrite List.length_app in Hx.
  destruct (Nat.lt_ge_cases x (List.length Δ)) as [Hlt | Hge].
  - (** A variable of the telescope: its entry, retagged. *)
    assert (Ee : env_entry (env_extend_typed Y vts) x = env_entry (env_extend_typed ρ vts) x)
      by (apply env_entry_typed_lt; lia).
    rewrite sb_qn_lt by exact Hlt; cbn; rewrite Ee; split; intros _; reflexivity.
  - destruct (Nat.le_exists_sub (List.length Δ) x Hge) as (k & -> & _).
    rewrite (Nat.add_comm k) in *.
    pose proof (H k ltac:(lia)) as [Hp1 Hn1].
    assert (Hs : List.skipn (List.length Δ) (ctx_retag (Δ ++ Γ) (env_extend_typed Y vts)) = ctx_retag Γ Y)
      by (rewrite skipn_ctx_retag_app, <- Hl, skipn_env_extend_typed; reflexivity).
    assert (Ee : env_entry (env_extend_typed Y vts) (List.length Δ + k) = env_entry Y k)
      by (rewrite <- Hl; apply env_entry_extend_typed_app).
    rewrite Ee, sb_qn_ge by lia.
    replace (List.length Δ + k - List.length Δ) with k by lia.
    split.
    + intros Hpx; apply eval_sentry_proof_retag with (t := ctx_entry_tag Γ k Y) (U := ctx_entry_unit Γ k); apply Hp1.
      pose proof (entry_propositional_shiftn _ _ _ _ Hpx) as Hpx'; rewrite Hs in Hpx'.
      exact (proj1 (entry_propositional_ctx_retag _ _ _ _ k HΓ HY) Hpx').
    + intros Hnx; apply eval_sentry_retag with (t := ctx_entry_tag Γ k Y) (U := ctx_entry_unit Γ k); apply Hn1.
      intros Hp'; apply Hnx.
      apply entry_propositional_shiftn_intro; rewrite Hs.
      exact (proj2 (entry_propositional_ctx_retag _ _ _ _ k HΓ HY) Hp').
Qed.
#[local] Opaque eval_sub.

(** The tail of [q^n] at a stage: the value of the substitution past the
    telescope's values, related to its value at the stage's own tail. *)
Lemma stage_base : forall Ψ Γ' Γ σ RΓ RS ρ ρσ vts,
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Ψ ++ Γ' ≈ Ψ ++ Γ' ∈ per_ctx_env ↘ RS ->
    Γ' ⊨ˢ σ ≈ σ : Γ -> RS (env_extend_typed ρ vts) (env_extend_typed ρ vts) -> List.length vts = List.length Ψ ->
    ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    exists Y, ⟦ sb_wk σ (wk_shiftn (List.length Ψ)) : Γ ⟧s env_extend_typed ρ vts ↘ Y /\ RΓ Y ρσ.
Proof.
  intros * HΓ HS Hσ HE Hl Hev.
  destruct Hσ as [R1 H1 R2 H2 Hσ _].
  pose proof (rel_wk_shiftn _ _ _ _ HS H1) as Hwk.
  destruct (Hσ _ _ HS _ Hwk ltac:(intros x Hx; cbn [wk_shiftn]; rewrite List.length_app; lia) _ _ HE)
    as [y1 y2 y3 y4 Hy1 Hy2 Hy3 Hy4 Hc].
  rewrite <- Hl, eval_wk_shiftn_extend_typed in Hy2.
  assert (Heq : env_agree_upto (List.length Γ) y2 ρσ) by (eapply functional_eval_sub; eassumption).
  assert (E : R2 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  exists y1; split; [ exact Hy1 |].
  apply E; eapply (per_ctx_env_resp_agree H2); [ reflexivity | exact Heq |].
  destruct Hc as (Hc & _); exact Hc.
Qed.

(** ** Instances along a Semantic Substitution *)

Lemma typ_inst_link : forall Δ0 Γ0 A A' (i : nat) τ RΓ0 E Eτ,
    Δ0 ⊨ᵗ A ≈ A' at i -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ : Δ0 ⟧s E ↘ Eτ ->
    exists a b, ⟦ A[τ] ⟧ E ↘ a /\ ⟦ A ⟧ Eτ ↘ b /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HA HΓ0 Hτ HE Hev.
  destruct (rel_type_inversion HA) as (R & HR & Hgen).
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as [a b c d Ha Hb Hc Hd Hch].
  exists a, b; split; [ exact Ha | split; [ exact Hb | destruct Hch as (H & _); exact H ] ].
Qed.

Lemma exp_inst_link : forall Δ0 Γ0 T M M' τ RΓ0 E Eτ,
    Δ0 ⊨ M ≈ M' : T -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 -> Γ0 ⊨ˢ τ ≈ τ : Δ0 ->
    RΓ0 E E -> ⟦ τ : Δ0 ⟧s E ↘ Eτ -> rel_typ_evaluated T Eτ ->
    exists m n, ⟦ M[τ] ⟧ E ↘ m /\ ⟦ M ⟧ Eτ ↘ n /\ Dom m ≈ n ∈ per_head T T Eτ Eτ.
Proof.
  intros * HM HΓ0 Hτ HE Hev Hr.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  destruct HMl as [R HR i Hgen].
  destruct (Hgen _ _ HΓ0 _ _ Hτ _ _ _ _ HE Hev Hev) as (R0 & Htyp & Hexp).
  apply (rel_exp_or_prop_evaluated Htyp Hr) in Hexp.
  destruct Htyp as [a b c d Ha Hb Hc Hd Hch]; destruct Hexp as [m n n' m' Hm Hn Hn' Hm' Hmc].
  exists m, n; split; [ exact Hm | split; [ exact Hn |] ].
  destruct Hch as (_ & Hbc & _); destruct Hmc as (Hmn & _).
  eapply per_head_of; [ exact Hb | exact Hc | exact Hbc | exact Hmn ].
Qed.

(** ** The Instance of a Telescope at the Value of a Substitution

    Arguments related at a telescope over the value of [σ] at [ρ] are, over
    [ρ], related at its instance by [σ], at any readable types the
    extensions store them at. *)
Lemma tele_stage_rel : forall Δ Γ Γ' σ RΓ' ρ ρσ, all_assumptions Δ -> ⊨ Δ ++ Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    forall vts, per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts) -> List.length vts = List.length Δ ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
    forall RS, EF tele_sub Δ σ ++ Γ' ≈ tele_sub Δ σ ++ Γ' ∈ per_ctx_env ↘ RS ->
      RS (env_extend_typed ρ vts) (env_extend_typed ρ vts).
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HΓ' Hσ Hρ Hev vts Hg Hl Hr RS HS.
  - destruct vts; cbn in Hl; [| discriminate ].
    cbn in HS; assert (E : RS <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
    apply E; exact Hρ.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
    destruct He as (κ & B & ->).
    assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
    destruct (rel_ctx_wf_ass_typ HΔ) as [i HB].
    pose proof (rel_ctx_wf_tail HΔ) as HΔ'.
    destruct (List.exists_last (l := vts) ltac:(intros ->; cbn in Hl; discriminate)) as (vts' & [x t] & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length vts' = List.length Δ) by lia; clear Hl.
    rewrite List.map_app in Hg; cbn [List.map fst] in Hg.
    apply List.Forall_app in Hr as [Hr' Hrx]; inversion Hrx as [| ? ? Rt _]; subst; cbn [fst snd] in Rt.
    cbn [List.rev] in Hg.
    assert (Hlr : List.length (List.map fst vts') = List.length (List.rev Δ))
      by (rewrite List.length_map, List.length_rev; exact Hl').
    destruct (per_tele_args_app (List.rev Δ) (ce_ass κ B :: nil) ρσ ρσ _ _ (x :: nil) (x :: nil) Hlr Hg Hlr)
      as [Hg' Hgx].
    inversion Hgx as [| ? ? ? ? ? ? ? ? ? ? R0 HB0 Hx _]; subst.
    pose proof (rel_ctx_wf_app_r _ _ HΔ') as HΓ.
    destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env HΔ') as [RΔ HRΔ].
    pose proof (rel_sub_qn _ _ _ _ _ HΔa' HΔ' Hσ) as Hq.
    destruct (rel_sub_under_ctx_simple Hq) as (RS' & HS' & _).
    pose proof (IH _ _ _ _ _ _ HΔa' HΔ' HΓ' Hσ Hρ Hev vts' Hg' Hl' Hr' RS' HS') as IHx.
    cbn [tele_sub List.app centry_sub] in HS.
    pose proof (per_ctx_env_of_typ_sub (κ := κ) HS' Hq HB) as HS2.
    assert (E : RS <~> per_env_extend B[sb_qn (List.length Δ) σ] B[sb_qn (List.length Δ) σ] RS')
      by (eapply per_ctx_env_right_irrel; eassumption).
    apply E; rewrite env_extend_typed_app; cbn [env_extend_typed List.fold_left fst snd].
    (** The head: the instance's value at the stage, against the type's at
        the value of [q^n σ] and then at [ρσ]. *)
    destruct (stage_base (tele_sub Δ σ) Γ' Γ σ RΓ RS' ρ ρσ vts' HRΓ HS' Hσ IHx ltac:(rewrite length_tele_sub; exact Hl') Hev)
      as (Y & HY & HYρ).
    rewrite length_tele_sub in HY.
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (Hρσ : RΓ ρσ ρσ) by (etransitivity; [ symmetry; exact HYρ | exact HYρ ]).
    assert (HCr : ⊨ List.rev (List.rev Δ) ++ Γ) by (rewrite List.rev_involutive; exact HΔ').
    assert (HRr : EF List.rev (List.rev Δ) ++ Γ ≈ List.rev (List.rev Δ) ++ Γ ∈ per_ctx_env ↘ RΔ)
      by (rewrite List.rev_involutive; exact HRΔ).
    assert (Har : all_assumptions (List.rev Δ)) by (apply List.Forall_rev; exact HΔa').
    assert (HgY : per_tele_args (List.rev Δ) Y ρσ (List.map fst vts') (List.map fst vts')).
    { eapply (per_tele_args_base _ _ _ HRΓ HCr Har ρσ ρσ); [ exact Hρσ | symmetry; exact HYρ | exact Hρσ | exact Hg' ]. }
    (** The image of the stage along [q^n σ], against the extension of
        [ρσ] at the same types and at the telescope's closures. *)
    assert (Hlr' : List.length vts' = List.length (List.rev Δ)) by (rewrite List.length_rev; exact Hl').
    pose proof (tele_args_env_rel_typed _ _ _ _ HRΓ HCr Har HRr _ _ vts' vts' HYρ Hlr' Hlr' HgY Hr' Hr') as HYE.
    pose proof (per_tele_args_entries_readable _ _ _ _ _ Hg') as [_ Hte].
    assert (Hlt : List.length (tele_entries ρσ (List.rev Δ) (List.map fst vts')) = List.length (List.rev Δ))
      by (rewrite tele_entries_length; exact Hlr).
    assert (HYT : RΔ (env_extend_typed ρσ vts') (env_tele ρσ (List.rev Δ) (List.map fst vts'))).
    { unfold env_tele; apply (tele_args_env_rel_typed _ _ _ _ HRΓ HCr Har HRr _ _ vts' _ Hρσ Hlr' Hlt);
        [ rewrite tele_entries_values; exact Hg' | exact Hr' | exact Hte ]. }
    assert (HYY : RΓ Y Y) by (etransitivity; [ exact HYρ | symmetry; exact HYρ ]).
    pose proof (eval_sub_qn_args _ _ _ _ _ _ _ Hl' HRΓ HYY HY) as Hqev.
    destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HB HS' (rel_sub_under_ctx_refl_left Hq) IHx Hqev) as (a & b & Ea & Eb & Hab).
    destruct (rel_type_inversion_simple_at HRΔ HB _ _ (per_ctx_env_retag_left HRΔ _ _ HYE)) as (b' & c & Eb' & Ec & Hbc).
    assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (rel_type_inversion_simple_at HRΔ HB _ _ HYT) as (c' & c0' & Ec' & Ec0' & Hcc0).
    assert (c' = c) as -> by (eapply functional_eval_exp; eassumption).
    destruct HB0 as [c0 c1 Ec0 Ec1 HR0].
    assert (c0' = c0) as -> by (eapply functional_eval_exp; eassumption).
    destruct Hab as [R1 HR1]; destruct Hbc as [R2 HR2]; destruct Hcc0 as [R3 HR3].
    assert (Hhead : Dom x ≈ x ∈ per_head B[sb_qn (List.length Δ) σ] B[sb_qn (List.length Δ) σ]
                                  (env_extend_typed ρ vts') (env_extend_typed ρ vts')).
    { intros j R a1 a2 Ea1 Ea2 HR.
      assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (E1 : R <~> R1) by (eapply per_univ_elem_right_irrel; [ exact HR | exact HR1 ]).
      assert (E2 : R1 <~> R2) by (eapply per_univ_elem_chain_iff; [ exact HR1 | exact HR2 ]).
      assert (E3 : R2 <~> R3) by (eapply per_univ_elem_chain_iff; [ exact HR2 | exact HR3 ]).
      assert (E4 : R3 <~> R0) by (eapply per_univ_elem_chain_iff; [ exact HR3 | exact HR0 ]).
      apply E1, E2, E3, E4; exact Hx. }
    apply per_env_extend_intro'; [ exact IHx | exact Hhead | exact Rt | exact Rt ].
Qed.

(** ** Base Change for a Closed Context *)

Lemma closed_env_base : forall C RC vts vts' wts wts' B1 B2 B3 B4, all_assumptions C -> ⊨ C ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> List.length vts = List.length C -> List.length vts' = List.length C ->
    List.map fst wts = List.map fst vts -> List.map fst wts' = List.map fst vts' ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) wts' ->
    RC (env_extend_typed B1 vts) (env_extend_typed B2 vts') -> RC (env_extend_typed B3 wts) (env_extend_typed B4 wts').
Proof.
  intros * HCa HC HRC Hl Hl' Hw Hw' Hr Hr' H.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  assert (HCr : all_assumptions (List.rev C)) by (apply List.Forall_rev; exact HCa).
  destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HC' HCr HRC' B1 B2 vts vts'
              ltac:(rewrite List.length_rev; exact Hl) ltac:(rewrite List.length_rev; exact Hl') H) as [_ Hg].
  pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HC' HCr B1 B2 B3 B4 _ _ I I I Hg) as Hg'.
  rewrite <- Hw, <- Hw' in Hg'.
  assert (Hlw : List.length wts = List.length (List.rev C))
    by (rewrite <- (List.length_map fst), Hw, List.length_map, List.length_rev; exact Hl).
  assert (Hlw' : List.length wts' = List.length (List.rev C))
    by (rewrite <- (List.length_map fst), Hw', List.length_map, List.length_rev; exact Hl').
  exact (tele_args_env_rel_typed _ _ _ _ per_ctx_env_nil_true HC' HCr HRC' _ _ _ _ I Hlw Hlw' Hg' Hr Hr').
Qed.

(** The same into the telescope's own extensions, at the closures of its
    types: those read back by the relation itself. *)
Corollary closed_env_tele : forall C RC vts vts' B1 B2 B3 B4, all_assumptions C -> ⊨ C ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> List.length vts = List.length C -> List.length vts' = List.length C ->
    RC (env_extend_typed B1 vts) (env_extend_typed B2 vts') ->
    RC (env_tele B3 (List.rev C) (List.map fst vts)) (env_tele B4 (List.rev C) (List.map fst vts')).
Proof.
  intros * HCa HC HRC Hl Hl' H.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  assert (HCr : all_assumptions (List.rev C)) by (apply List.Forall_rev; exact HCa).
  destruct (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HC' HCr HRC' B1 B2 vts vts'
              ltac:(rewrite List.length_rev; exact Hl) ltac:(rewrite List.length_rev; exact Hl') H) as [_ Hg].
  pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HC' HCr B1 B2 B3 B4 _ _ I I I Hg) as Hg'.
  pose proof (per_tele_args_entries_readable _ _ _ _ _ Hg') as [Hr Hr'].
  unfold env_tele; eapply closed_env_base; [ exact HCa | exact HC | exact HRC | exact Hl | exact Hl'
                                            | rewrite tele_entries_values; reflexivity | rewrite tele_entries_values; reflexivity
                                            | exact Hr | exact Hr' | exact H ].
Qed.

(** ** Instances of a Closed Type

    A type [X] of some sort of a closed context [Pre ++ C0], instantiated
    past [Pre] by a substitution [τ] of [C0], is related at an environment
    of the instance of [Pre] to [X] at any environment related to the
    values there. *)
Lemma closed_typ_inst : forall Pre C0 Γ X S τ RΓ RK RS B vts Bτ F,
    all_assumptions (Pre ++ C0) -> ⊨ Pre ++ C0 -> all_assumptions C0 -> ⊨ C0 -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Pre ++ C0 ≈ Pre ++ C0 ∈ per_ctx_env ↘ RK ->
    EF tele_sub Pre τ ++ Γ ≈ tele_sub Pre τ ++ Γ ∈ per_ctx_env ↘ RS ->
    type_sort S -> Pre ++ C0 ⊨ X : S -> Γ ⊨ˢ τ ≈ τ : C0 ++ Γ ->
    RS (env_extend_typed B vts) (env_extend_typed B vts) -> List.length vts = List.length Pre ->
    ⟦ τ : C0 ++ Γ ⟧s B ↘ Bτ -> RK (env_extend_typed Bτ vts) F ->
    exists (j : nat) a b, ⟦ X[sb_qn (List.length Pre) τ] ⟧ env_extend_typed B vts ↘ a /\ ⟦ X ⟧ F ↘ b /\
      Dom a ≈ b ∈ per_univ j.
Proof.
  intros * HKa HK HC0a HC0 HΓ HRΓ HRK HRS HS HX Hτ HE Hl Hev HF.
  destruct (rel_type_of_sort_at HS) as [j Hj]; exists j.
  destruct (closed_app_sem _ _ HKa HK HΓ) as [HKΓ HresK].
  destruct (closed_app_sem _ _ HC0a HC0 HΓ) as [HC0Γ Hres0].
  destruct (rel_ctx_wf_per_ctx_env HC0Γ) as [R0Γ HR0Γ].
  destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
  assert (HPK : PER RK) by (eapply per_env_PER; exact HRK).
  assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
  assert (HPa : all_assumptions Pre) by (apply List.Forall_app in HKa as [H _]; exact H).
  (** The value of [q^n τ]. *)
  destruct (stage_base (tele_sub Pre τ) Γ (C0 ++ Γ) τ R0Γ RS B Bτ vts HR0Γ HRS Hτ HE
              ltac:(rewrite length_tele_sub; exact Hl) Hev) as (Y & HY & HYτ).
  rewrite length_tele_sub in HY.
  pose proof (rel_sub_qn Pre (C0 ++ Γ) Γ τ τ HPa ltac:(rewrite List.app_assoc; exact HKΓ) Hτ) as Hq.
  assert (HXΓ : Pre ++ C0 ++ Γ ⊨ X : S) by (rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ HKa HK HΓ HX)).
  (** The value at the instance's tail, against the given one. *)
  assert (HYτ0 : R0 Y Bτ) by (exact (Hres0 _ _ HR0 HR0Γ _ _ HYτ)).
  assert (HPre : ⊨ List.rev (List.rev Pre) ++ C0) by (rewrite List.rev_involutive; exact HK).
  assert (HRK' : EF List.rev (List.rev Pre) ++ C0 ≈ List.rev (List.rev Pre) ++ C0 ∈ per_ctx_env ↘ RK)
    by (rewrite List.rev_involutive; exact HRK).
  assert (HBB : RK (env_extend_typed Bτ vts) (env_extend_typed Bτ vts)) by (etransitivity; [ exact HF | symmetry; exact HF ]).
  assert (Hlr : List.length vts = List.length (List.rev Pre)) by (rewrite List.length_rev; exact Hl).
  destruct (per_tele_args_of_env_extend _ _ _ _ HR0 HPre (List.Forall_rev HPa) HRK' Bτ Bτ vts vts Hlr Hlr HBB) as [HBτ Hg].
  destruct (per_tele_args_of_env_extend_readable _ _ _ _ HR0 HPre (List.Forall_rev HPa) HRK' Bτ Bτ vts vts Hlr Hlr HBB) as [Hr _].
  pose proof (per_tele_args_base _ _ _ HR0 HPre (List.Forall_rev HPa) Bτ Bτ Y Bτ _ _ HBτ (symmetry HYτ0) HBτ Hg) as Hg'.
  pose proof (tele_args_env_rel_typed _ _ _ _ HR0 HPre (List.Forall_rev HPa) HRK' _ _ vts vts HYτ0 Hlr Hlr Hg' Hr Hr) as HYB.
  (** The value of [q^n τ]. *)
  assert (HP0Γ : PER R0Γ) by (eapply per_env_PER; exact HR0Γ).
  assert (HYY : R0Γ Y Y) by (etransitivity; [ exact HYτ | symmetry; exact HYτ ]).
  pose proof (eval_sub_qn_args _ _ _ _ _ _ _ Hl HR0Γ HYY HY) as Hqev.
  destruct (typ_inst_link _ _ _ _ _ _ _ _ _ (Hj _ _ _ HXΓ) HRS (rel_sub_under_ctx_refl_left Hq) HE Hqev)
    as (a & b0 & Ea & Eb0 & Hab).
  assert (HYF : RK (env_extend_typed Y vts) F) by (etransitivity; [ exact HYB | exact HF ]).
  (** The value of [q^n τ] is the retagging of [env_extend_typed Y vts],
      which the PER of [Pre ++ C0] relates as it does the environment. *)
  destruct (rel_ctx_wf_per_ctx_env HKΓ) as [RF HRF].
  rewrite <- List.app_assoc in HRF.
  assert (HT : RF (ctx_retag (Pre ++ C0 ++ Γ) (env_extend_typed Y vts)) (ctx_retag (Pre ++ C0 ++ Γ) (env_extend_typed Y vts)))
    by (eapply (rel_sub_under_ctx_at' Hq HRS HRF); eassumption).
  rewrite List.app_assoc in HRF, HT, Eb0.
  pose proof (per_ctx_env_retag_app_left _ _ _ _ _ _ HKa HRK HRF HT HYF) as HYF'.
  destruct (rel_type_inversion_simple_at HRK (Hj _ _ _ HX) _ _ HYF') as (b1 & b & Eb1 & Eb & Hbb).
  assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
  exists a, b; split; [ exact Ea | split; [ exact Eb | etransitivity; [ exact Hab | exact Hbb ] ] ].
Qed.

(** ** Substitutions Built from Valid Parts, over Telescopes *)

Lemma gsub_of_list : forall Δ Γ Γ1 σ0 Ms, gsub Γ σ0 Γ1 -> all_assumptions Δ -> ⊨ Δ ++ Γ1 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ0 Ms) k = Some T -> Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    gsub Γ (sb_of_list σ0 Ms) (Δ ++ Γ1).
Proof.
  induction Δ as [| e Δ IH]; intros Γ Γ1 σ0 Ms Hg0 HCa HC Hl HMs HMss.
  - destruct Ms; cbn in Hl; [| discriminate ]; cbn; exact Hg0.
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HCa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HCa' : all_assumptions Δ) by (inversion HCa; assumption).
    destruct (rel_ctx_wf_ass_inv HC) as (Srt & HS & HA).
    pose proof (rel_ctx_wf_tail HC) as HC'.
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl' : List.length Ms' = List.length Δ) by lia; clear Hl.
    assert (Hti : tele_insts (ce_ass κ A :: Δ) σ0 (Ms' ++ M :: nil) = tele_insts Δ σ0 Ms' ++ A[sb_of_list σ0 Ms'] :: nil).
    { change (ce_ass κ A :: Δ) with ((ce_ass κ A :: nil) ++ Δ).
      rewrite tele_insts_app by (try exact HCa'; lia); reflexivity. }
    assert (HlT : List.length (tele_insts Δ σ0 Ms') = List.length Δ) by (rewrite length_tele_insts by exact HCa'; lia).
    apply List.Forall_app in HMss as [HMss' HMs1]; inversion HMs1 as [| ? ? HMsc _]; subst.
    rewrite sb_of_list_app; cbn [sb_of_list List.app].
    eapply gsub_ass; [ apply (IH _ _ _ _ Hg0 HCa' HC' Hl') | exact HS | exact HA | | exact HMsc ].
    + intros k N T HN HT.
      assert (Hk : k < List.length Δ) by (rewrite <- HlT; apply List.nth_error_Some; congruence).
      apply (HMs k); [ rewrite List.nth_error_app1 by lia; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HT ].
    + exact HMss'.
    + apply (HMs (List.length Δ)); [ rewrite List.nth_error_app2, Hl', Nat.sub_diag by lia; reflexivity |].
      rewrite Hti, List.nth_error_app2, HlT, Nat.sub_diag by lia; reflexivity.
Qed.

(** An extension by a type of a universe, an assumption of its kind
    [ak_relevant]. *)
Lemma rel_ctx_wf_ext_typ : forall Γ A (i : nat), ⊨ Γ -> Γ ⊨ A : Typeω@i -> ⊨ Γ ▹{ak_relevant} A.
Proof. intros * HΓ HA; exact (rel_ctx_wf_extend HΓ HA). Qed.

(** The same, for a type of any sort, at the sort's kind. *)
Lemma rel_ctx_wf_ext_sort : forall Γ κ A S, ⊨ Γ -> sort_kind S κ -> Γ ⊨ A : S -> ⊨ Γ ▹{κ} A.
Proof. intros * HΓ HS HA; exact (rel_ctx_wf_extend_sort HΓ HS HA). Qed.

Lemma gsub_rel_ctx_wf : forall Γ τ Δ, gsub Γ τ Δ -> ⊨ Γ.
Proof. intros * Hg; exact (proj1 (gsub_sem Hg)). Qed.

Lemma gsub_qn : forall Pre Γ0 τ Δ0, gsub Γ0 τ Δ0 -> all_assumptions Pre -> ⊨ Pre ++ Δ0 ->
    gsub (tele_sub Pre τ ++ Γ0) (sb_qn (List.length Pre) τ) (Pre ++ Δ0).
Proof.
  induction Pre as [| e Pre IH]; intros * Hg HPa HP; cbn [tele_sub List.app List.length sb_qn]; [ exact Hg |].
  assert (He : exists κ A, e = ce_ass κ A) by (inversion HPa as [| ? ? He _]; exact He).
  destruct He as (κ & B & ->).
  assert (HPa' : all_assumptions Pre) by (inversion HPa; assumption).
  destruct (rel_ctx_wf_ass_inv HP) as (Srt & HS & HB).
  cbn [centry_sub].
  exact (gsub_q _ _ _ _ _ _ (IH _ _ _ Hg HPa' (rel_ctx_wf_tail HP)) HS HB).
Qed.

Lemma gsub_wk : forall Γ φ Δ, Γ ⊨ʷ φ : Δ -> ⊨ Γ -> ⊨ Δ -> gsub Γ (sb_of_wk φ) Δ.
Proof.
  intros * Hφ HΓ HΔ.
  eapply gsub_eq; [ eapply gsub_comp; [ constructor; exact HΔ | exact HΓ | exact (rel_sub_of_wk Hφ) | exact (sub_link_wk Hφ) ] |].
  intros x; reflexivity.
Qed.

(** ** Telescopes of [Π] *)

Lemma rel_exp_ctx_pi : forall Δ Γ B (i : nat), all_assumptions Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ B : Typeω@i ->
    exists j : nat, Γ ⊨ ctx_pi Δ B : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HB; [ exists i; exact HB |].
  assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
  destruct He as (κ & A & ->).
  assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
  destruct (rel_ctx_wf_ass_typ HΔ) as [k HA].
  cbn [ctx_pi_at].
  apply (IH _ _ (max k i) HΔa' (rel_ctx_wf_tail HΔ)).
  assert (HA' : Δ ++ Γ ⊨ᵗ A ≈ A at max k i) by (eapply rel_type_cumu_ge; [| exact HA ]; lia).
  apply rel_exp_under_ctx_pi_cong;
    [ exact HA' | exact HA' | exact (rel_ctx_wf_ass_kind HΔ) | eapply rel_exp_cumu_ge; [| exact HB ]; lia ].
Qed.

(** A type of an evaluated kind [r] generalized over relevant parameters
    ([rel_params_evaluated]) whose kinds a [Π] into [r] takes
    ([pi_kinds]): a type of an index, of the kind [r] ([ctx_pi_at]).  For
    example, the member [v : Level] of [module M (l : Level) ≔ …] is read
    at [Πₗ (l : Level) Level]. *)
Lemma rel_type_ctx_pi : forall Δ Γ B r l k, all_assumptions Δ -> ⊨ Δ ++ Γ -> rel_params_evaluated Γ Δ l ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ r) -> evaluated_kind r ->
    Δ ++ Γ ⊨ᵗ B ≈ B at k -> rel_type_kind (Δ ++ Γ) B r ->
    Γ ⊨ᵗ ctx_pi_at r Δ B ≈ ctx_pi_at r Δ B at max l k /\ rel_type_kind Γ (ctx_pi_at r Δ B) r.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HΔr HΔk Hev HB HBr.
  - split; [ eapply rel_type_cumu_ge; [| exact HB ]; lia | exact HBr ].
  - assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
    destruct He as (κ & A & ->).
    assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
    apply rel_params_evaluated_cons_iff in HΔr as [Hh HΔr'].
    pose proof (rel_type_cumu_ge (i := l) (j := max l k) ltac:(lia) (rel_param_typed_type _ _ _ (Hh κ A eq_refl))) as HA.
    pose proof (HΔk nil κ A Δ eq_refl) as Hk.
    cbn [ctx_pi_at List.app] in *.
    destruct (IH _ _ _ l (max l k) HΔa' (rel_ctx_wf_tail HΔ) HΔr'
                (fun Δ1 κ1 A1 Δ2 E => HΔk (ce_ass κ A :: Δ1) κ1 A1 Δ2 ltac:(rewrite E; reflexivity)) Hev
                (rel_type_under_ctx_pi HA (rel_ctx_wf_ass_kind HΔ) (rel_type_cumu_ge (i := k) (j := max l k) ltac:(lia) HB) HBr Hk Hev)
                (rel_type_kind_pi HA)) as [H1 H2].
    split; [ eapply rel_type_cumu_ge; [| exact H1 ]; lia | exact H2 ].
Qed.

(** A term of a type of an evaluated kind generalized over relevant
    parameters: the λ over them, at the [Π] over them ([rel_type_ctx_pi]). *)
Lemma rel_exp_ctx_fn : forall Δ Γ B M r l k, all_assumptions Δ -> ⊨ Δ ++ Γ -> rel_params_evaluated Γ Δ l ->
    (forall Δ1 κ A Δ2, Δ = Δ1 ++ ce_ass κ A :: Δ2 -> pi_kinds κ r) -> evaluated_kind r ->
    Δ ++ Γ ⊨ᵗ B ≈ B at k -> rel_type_kind (Δ ++ Γ) B r -> Δ ++ Γ ⊨ M : B ->
    Γ ⊨ ctx_fn Δ M : ctx_pi_at r Δ B.
Proof.
  induction Δ as [| e Δ IH]; intros * HΔa HΔ HΔr HΔk Hev HB HBr HM; [ exact HM |].
  assert (He : exists κ A, e = ce_ass κ A) by (inversion HΔa as [| ? ? He _]; exact He).
  destruct He as (κ & A & ->).
  assert (HΔa' : all_assumptions Δ) by (inversion HΔa; assumption).
  apply rel_params_evaluated_cons_iff in HΔr as [Hh HΔr'].
  pose proof (rel_type_cumu_ge (i := l) (j := max l k) ltac:(lia) (rel_param_typed_type _ _ _ (Hh κ A eq_refl))) as HA.
  pose proof (rel_type_cumu_ge (i := k) (j := max l k) ltac:(lia) HB) as HB'.
  pose proof (HΔk nil κ A Δ eq_refl) as Hk.
  pose proof (rel_ctx_wf_ass_kind HΔ) as HAk.
  cbn [ctx_fn ctx_pi_at List.app] in *.
  exact (IH _ _ _ _ l (max l k) HΔa' (rel_ctx_wf_tail HΔ) HΔr'
           (fun Δ1 κ1 A1 Δ2 E => HΔk (ce_ass κ A :: Δ1) κ1 A1 Δ2 ltac:(rewrite E; reflexivity)) Hev
           (rel_type_under_ctx_pi HA HAk HB' HBr Hk Hev) (rel_type_kind_pi HA)
           (rel_exp_under_ctx_fn_cong_evaluated HA HA HAk HB' HBr Hk Hev HM)).
Qed.

Lemma rel_exp_apps_ctx_pi_n : forall n Δ Γ B (i : nat) M Ms,
    List.length Δ = n -> all_assumptions Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ B : Typeω@i ->
    Γ ⊨ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    Γ ⊨ apps M Ms : B[sb_of_list Id Ms].
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HM Hl HMs HMss.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    pose proof (rel_ctx_wf_app_r _ _ HΔ) as HΓA.
    destruct (rel_ctx_wf_ass_inv HΓA) as (Srt & HS & HA0).
    pose proof (rel_ctx_wf_tail HΓA) as HΓ.
    destruct (rel_exp_ctx_pi _ _ _ _ Hass HΔ HB) as [j HPi].
    assert (HM0 : Γ ⊨ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    inversion HMss as [| ? ? HM0s HMss']; subst.
    (** The application, at a domain of any kind. *)
    assert (Happ : Γ ⊨ M $ M0 : (ctx_pi Δ B)[Id,,M0]).
    { destruct HS as [k | |].
      - exact (rel_exp_under_ctx_app_cong (rel_type_of_typ HA0) (rel_type_kind_of_typ HA0) evaluated_kind_relevant
                 evaluated_kind_relevant (rel_type_of_typ HPi) HM HM0 HM0s).
      - exact (rel_exp_under_ctx_app_cong_prop HA0 HPi HM HM0 HM0s HM0s).
      - exact (rel_exp_under_ctx_app_cong (rel_type_of_level_sort 0 HA0) (rel_type_kind_of_level_sort HA0) evaluated_kind_level
                 evaluated_kind_relevant (rel_type_of_typ HPi) HM HM0 HM0s). }
    rewrite ctx_pi_sub in Happ.
    assert (Hg0 : gsub Γ (Id,,M0) (Γ ▹{κ0} A0)).
    { eapply gsub_ass; [ constructor; exact HΓ | exact HS | exact HA0 | rewrite exp_sub_id; exact HM0 | exact HM0s ]. }
    pose proof (gsub_qn _ _ _ _ Hg0 Hass HΔ) as Hgq.
    pose proof (gsub_rel_ctx_wf _ _ _ Hgq) as HΔ'.
    pose proof (rel_exp_under_ctx_gsub Hgq HB) as HB'; cbn [exp_sub] in HB'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH (tele_sub Δ (Id,,M0)) Γ (B[sb_qn (List.length Δ) (Id,,M0)]) i (M $ M0) Ms); [ rewrite length_tele_sub; lia | apply all_assumptions_sub; exact Hass | exact HΔ' | exact HB' | exact Happ
               | rewrite length_tele_sub; lia | | exact HMss' ].
    intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
    rewrite tele_insts_snoc; cbn [List.nth_error].
    rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
    apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.


(** A judgment about closed terms at [⋅] holds in every context. *)
Lemma closed_weaken_valid : forall Γ T N N', ⊨ Γ -> ⋅ ⊨ N ≈ N' : T -> Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ H.
  rewrite <- (exp_wk_id_ext T wk_id), <- (exp_wk_id_ext N wk_id), <- (exp_wk_id_ext N' wk_id) by (intros x; reflexivity).
  eapply rel_exp_under_ctx_wk; [| exact H ].
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
  eapply (rel_wk_under_ctx_intro (R' := fun _ _ => True)); [ exact HR | | | intros x Hx; cbn in Hx; lia
                                                          | intros ? ? _ x Hx; cbn in Hx; lia ].
  - apply per_ctx_env_nil; reflexivity.
  - constructor; [ apply wk_mono_id | intros; exact I ].
Qed.

(** ** The Outer Links of a Judgment over a Telescope

    The instance of a judgment over [Δ ++ Γ] along [q^n σ], at an
    environment of the instance of [Δ] over [ρ], against the judgment at
    the value of [σ] at [ρ] extended by the same arguments. *)
Lemma outer_base : forall Δ Γ Γ' RΓ' σ ρ ρσ, all_assumptions Δ -> ⊨ Δ ++ Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    forall vts, per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts) -> List.length vts = List.length Δ ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
    exists RS RΔ Y, EF tele_sub Δ σ ++ Γ' ≈ tele_sub Δ σ ++ Γ' ∈ per_ctx_env ↘ RS /\
      RS (env_extend_typed ρ vts) (env_extend_typed ρ vts) /\
      EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ RΔ /\
      ⟦ sb_qn (List.length Δ) σ : Δ ++ Γ ⟧s env_extend_typed ρ vts ↘ ctx_retag (Δ ++ Γ) (env_extend_typed Y vts) /\
      RΔ (ctx_retag (Δ ++ Γ) (env_extend_typed Y vts)) (env_extend_typed ρσ vts) /\
      tele_sub Δ σ ++ Γ' ⊨ˢ sb_qn (List.length Δ) σ ≈ sb_qn (List.length Δ) σ : Δ ++ Γ.
Proof.
  intros * HΔa HΔ HΓ' Hσ Hρ Hev vts Hg Hl Hr.
  pose proof (rel_sub_qn _ _ _ _ _ HΔa HΔ Hσ) as Hq.
  destruct (rel_sub_under_ctx_simple Hq) as (RS & HRS & _).
  pose proof (tele_stage_rel _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl Hr _ HRS) as HE.
  pose proof (rel_ctx_wf_app_r _ _ HΔ) as HΓ.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env HΔ) as [RΔ HRΔ].
  destruct (stage_base (tele_sub Δ σ) Γ' Γ σ RΓ RS ρ ρσ vts HRΓ HRS Hσ HE ltac:(rewrite length_tele_sub; exact Hl) Hev)
    as (Y & HY & HYρ).
  rewrite length_tele_sub in HY.
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
  assert (Hρσ : RΓ ρσ ρσ) by (etransitivity; [ symmetry; exact HYρ | exact HYρ ]).
  assert (HCr : ⊨ List.rev (List.rev Δ) ++ Γ) by (rewrite List.rev_involutive; exact HΔ).
  assert (HRr : EF List.rev (List.rev Δ) ++ Γ ≈ List.rev (List.rev Δ) ++ Γ ∈ per_ctx_env ↘ RΔ)
    by (rewrite List.rev_involutive; exact HRΔ).
  assert (Har : all_assumptions (List.rev Δ)) by (apply List.Forall_rev; exact HΔa).
  assert (HgY : per_tele_args (List.rev Δ) Y ρσ (List.map fst vts) (List.map fst vts)).
  { eapply (per_tele_args_base _ _ _ HRΓ HCr Har ρσ ρσ); [ exact Hρσ | symmetry; exact HYρ | exact Hρσ | exact Hg ]. }
  assert (Hlr : List.length vts = List.length (List.rev Δ)) by (rewrite List.length_rev; exact Hl).
  pose proof (tele_args_env_rel_typed _ _ _ _ HRΓ HCr Har HRr _ _ vts vts HYρ Hlr Hlr HgY Hr Hr) as HYE.
  pose proof (eval_sub_qn_args _ _ _ _ _ _ _ Hl HRΓ (ltac:(etransitivity; [ exact HYρ | symmetry; exact HYρ ]) : RΓ Y Y) HY) as Hqev.
  pose proof (per_ctx_env_retag_left HRΔ _ _ HYE) as HYE'.
  exists RS, RΔ, Y; repeat split; assumption.
Qed.

Lemma outer_type_link : forall Δ Γ Γ' RΓ' σ ρ ρσ A (i : nat), all_assumptions Δ -> ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ᵗ A ≈ A at i ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    forall vts, per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts) -> List.length vts = List.length Δ ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
    exists a b, ⟦ A[sb_qn (List.length Δ) σ] ⟧ env_extend_typed ρ vts ↘ a /\ ⟦ A ⟧ env_extend_typed ρσ vts ↘ b /\
      Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HΔa HΔ HA HΓ' Hσ Hρ Hev vts Hg Hl Hr.
  destruct (outer_base _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl Hr) as (RS & RΔ & Y & HRS & HE & HRΔ & Hqev & HYE & Hq).
  destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HA HRS Hq HE Hqev) as (a & b0 & Ea & Eb0 & Hab).
  destruct (rel_type_inversion_simple_at HRΔ HA _ _ HYE) as (b1 & b & Eb1 & Eb & Hbb).
  assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
  exists a, b; split; [ exact Ea | split; [ exact Eb | etransitivity; [ exact Hab | exact Hbb ] ] ].
Qed.

(** The same for a type of a universe. *)
Lemma outer_universe_type_link : forall Δ Γ Γ' RΓ' σ ρ ρσ A A' (i : nat), all_assumptions Δ -> ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ A ≈ A' : Typeω@i ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    forall vts, per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts) -> List.length vts = List.length Δ ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
    exists a b, ⟦ A[sb_qn (List.length Δ) σ] ⟧ env_extend_typed ρ vts ↘ a /\ ⟦ A ⟧ env_extend_typed ρσ vts ↘ b /\
      Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HΔa HΔ HA; exact (outer_type_link _ _ _ _ _ _ _ _ _ HΔa HΔ (rel_type_of_typ (rel_exp_under_ctx_refl_left HA))).
Qed.

Lemma outer_exp_link : forall Δ Γ Γ' RΓ' σ ρ ρσ T M M', all_assumptions Δ -> ⊨ Δ ++ Γ ->
    Δ ++ Γ ⊨ M ≈ M' : T ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ -> RΓ' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    forall vts, per_tele_args (List.rev Δ) ρσ ρσ (List.map fst vts) (List.map fst vts) -> List.length vts = List.length Δ ->
    List.Forall (fun vt => entry_readable (de_term (fst vt) (snd vt))) vts ->
    rel_typ_evaluated T (env_extend_typed ρσ vts) ->
    exists RΔ F m n, EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ RΔ /\ RΔ F (env_extend_typed ρσ vts) /\
      ⟦ M[sb_qn (List.length Δ) σ] ⟧ env_extend_typed ρ vts ↘ m /\ ⟦ M ⟧ env_extend_typed ρσ vts ↘ n /\
      Dom m ≈ n ∈ per_head T T F (env_extend_typed ρσ vts).
Proof.
  intros * HΔa HΔ HM HΓ' Hσ Hρ Hev vts Hg Hl Hr [t [Et Hrt]].
  destruct (outer_base _ _ _ _ _ _ _ HΔa HΔ HΓ' Hσ Hρ Hev _ Hg Hl Hr) as (RS & RΔ & Y & HRS & HE & HRΔ & Hqev & HYE & Hq).
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  destruct (rel_exp_under_ctx_simple_full_at HRΔ HMl) as [k Hs].
  destruct (Hs _ _ HYE) as (t1 & t2 & Rt & Et1 & Et2 & HRt & Hd).
  assert (t2 = t) as -> by (eapply functional_eval_exp; eassumption).
  pose proof (per_univ_elem_kind _ _ _ _ HRt) as Er.
  destruct Hd as [Hd | (n1 & n & En1 & En & Hnn)]; [ exfalso; rewrite Hd in Er; rewrite <- Er in Hrt; inversion Hrt |].
  (** The type is of an evaluated kind at the stage's environment too. *)
  assert (Er1 : evaluated_kind (domain_kind t1)) by (rewrite Er; exact Hrt).
  destruct (exp_inst_link _ _ _ _ _ _ _ _ _ HMl HRS Hq HE Hqev (ex_intro _ t1 (conj Et1 Er1)))
    as (m & n0 & Em & En0 & Hmn).
  assert (n1 = n0) as -> by (eapply functional_eval_exp; eassumption).
  exists RΔ, (ctx_retag (Δ ++ Γ) (env_extend_typed Y vts)), m, n; split; [ assumption | split; [ assumption | split; [ assumption | split; [ assumption |] ] ] ].
  (** Both relations are those of the type at the left environment. *)
  pose proof (per_univ_elem_sym _ _ _ _ HRt) as [HRts _].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRt HRts) as (R11 & HR11 & E11).
  assert (HPt : PER Rt) by (eapply per_elem_PER; exact HRt).
  apply (per_head_iff Et1 Et1 HR11) in Hmn.
  eapply per_head_of; [ exact Et1 | exact Et2 | exact HRt |].
  etransitivity; [ apply E11; exact Hmn | exact Hnn ].
Qed.

End Fixed_GCtx.
