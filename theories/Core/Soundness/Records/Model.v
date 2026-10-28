(** * Record Types in the Gluing Model

    A record found in a well-formed global context is typed there, so
    valid in the PER model ([record_model_at]); [Core/Completeness/Records/Model.v]
    then gives the values of its type former, its fields' types and its
    projections.  On top of them: a projection of a glued element is glued
    at its field's type ([glu_rel_exp_proj]), a tuple of glued fields is
    glued at its record type ([glu_rel_exp_tuple]), and the type former,
    at a declaration whose judgments are glued ([glu_record_decl]), is
    glued at its type ([glu_rel_exp_record0]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Completeness.Records Require Import Model.
From Mctt.Core.Completeness Require Import RecordCases.
From Mctt.Core.Semantic Require Import Realizability RecordPER Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Syntactic Require Import Substitution Records.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args ViewCon.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Record of a Well-Formed Global Context *)

(** A record found in a well-formed global context is valid there in the
    PER model: it is typed where it is found, and the identity embedding
    is sound. *)
Lemma record_model_at : forall p R, ⊢ᵍ gc_deps ⍮ gc_stack -> record_lookup gc_deps gc_stack p = Some R ->
    record_model p R.
Proof.
  intros * Hg Hl.
  pose proof (record_model_of_embedding _ _ _ _ _ _ (valid_gctx_embedding_refl _ _ Hg) Hl) as H.
  destruct GC; exact H.
Qed.

(** Arguments glued along a closed telescope are glued to their values by
    their readback. *)
Lemma glu_args_params_glu_top : forall C Δ Ms vs, tele_ass C -> ctx_scoped 0 C ->
    glu_args Δ C Id nil Ms vs -> params_glu_top C Δ Ms vs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  constructor; [ exact L1 | |].
  - intros k M T HM HT.
    assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (H _ _ _ _ _ HM HT Hv He) as [i a P El _ Hglu _ HMg].
    eapply glu_univ_elem_trm_escape; eassumption.
  - intros Δ' φ Rs Hφ HRs.
    destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
    split; [ rewrite List.length_map, HRl; congruence |].
    intros k X Y T HX HY HT.
    rewrite List.nth_error_map in HX.
    destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
    rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
    destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
    assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (HRn _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
    rewrite HY' in HY; injection HY as <-.
    destruct (H _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
    exact (Hrb _ _ _ Hφ HV).
Qed.

(** ** A Record at its Model *)

Section RecordAt.
  Variables (p : qname) (R : record_decl).
  Hypothesis (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) (Hl : record_lookup gc_deps gc_stack p = Some R).

  (** What the model asks of the record, and its parts. *)
  Let Hmodel := record_model_at p R Hg Hl.
  Let Hc := model_closed _ _ Hmodel.
  Let Hass := model_params_ass _ _ Hmodel.
  Let Hnd := model_fields_distinct _ _ Hmodel.
  Let Hsu := model_sort _ _ Hmodel.
  Let HPv := params_valid _ (model_valid _ _ Hmodel).
  Let HSv := sort_valid _ (model_valid _ _ Hmodel).
  Let HFv := field_ctx_valid _ (model_valid _ _ Hmodel).
  Let HTv := fields_valid _ (model_valid _ _ Hmodel).

  (** Parameters glued at their telescope, along a glued substitution: glued
      arguments of it. *)
  Lemma record_params_glu_args_at : forall Γ Sb Ns Δ σ ρ ns, EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊢ N : A) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊩ N : A) ->
      ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns ->
      glu_args Δ (record_params R) Id nil (List.map (fun N => N[σ]) Ns) ns.
  Proof.
    intros * HSb Hσ Hn HNt HNg Ens.
    assert (HΓ : ⊢ Γ) by exact (glu_ctx_env_wf_ctx HSb).
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    eapply params_glu_args; [ exact Hass | exact (closed_params _ Hc) | eapply record_params_sem; exact HFv
                            | exact HΓs | exact HRΓ | exact HSb | exact Hσ | exact Hn | | exact HNg | exact Ens ].
    intros * HN HA; exact (completeness_fundamental_exp _ _ _ (HNt _ _ _ HN HA)).
  Qed.

  (** So they are glued to their values by their readback. *)
  Lemma record_params_glu_at : forall Γ Sb Ns Δ σ ρ ns, EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊢ N : A) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊩ N : A) ->
      ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns ->
      params_glu_top (record_params R) Δ (List.map (fun N => N[σ]) Ns) ns.
  Proof.
    intros * HSb Hσ Hn HNt HNg Ens.
    apply glu_args_params_glu_top; [ exact Hass | exact (closed_params _ Hc) |].
    eapply record_params_glu_args_at; eassumption.
  Qed.

  (** Two types of a value related to one glued at [i] are glued at [i]. *)
  Lemma glu_univ_elem_resp_per_univ_at : forall (i j : universe_index) t u P El, DG u ∈ glu_univ_elem i ↘ P ↘ El ->
      Dom t ≈ u ∈ per_univ j -> DG t ∈ glu_univ_elem i ↘ P ↘ El.
  Proof.
    intros * Hu Htu.
    pose proof (glu_univ_elem_per_univ _ _ _ _ Hu) as Huu.
    pose proof (per_univ_trans' _ _ _ _ _ Huu (per_univ_sym' _ _ _ Htu)) as Hut.
    exact (glu_univ_elem_resp_per_univ _ _ _ _ _ Hut Hu).
  Qed.

  (** ** Projections *)

  (** The projection of an element glued at the record type at parameters
      is glued at its field's type: it is the projection the element's
      gluing glues, at the parameters, which are the element's type's. *)
  Lemma glu_rel_exp_proj : forall Γ M Ns k f U,
      Γ ⊩ M : apps_exp (a_record p) Ns ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊢ N : A) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊩ N : A) ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      Γ ⊩ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HM Hn HNt HNg Hfk.
    pose proof HM as [Sb HSb j Hbody].
    assert (HΓ : ⊢ Γ) by exact (glu_ctx_env_wf_ctx HSb).
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := j); [ exact HSb |]; intros Δ σ ρ Hσ.
    destruct (Hbody _ _ _ Hσ) as [a m P El Ea Em Hglu HMg].
    destruct (eval_record_apps_inv _ _ Hl _ _ _ Ea Hn) as (ns & Ens & ->).
    invert_glu_univ_elem Hglu.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p ns) (d_record p ns) |- _ => rename H0 into Hper end.
    match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl in HMg end.
    destruct HMg as [HMs Hm Ns0 HNs0 vs Hvs Hk].
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ HE].
    pose proof (proj1 (HE _ _) Hm) as HrelM.
    pose proof (List.Forall2_length Hvs) as Hlv.
    destruct (nth_error_lt_some' vs k ltac:(lia)) as [r Hr].
    pose proof (record_projs_prefix_diag _ _ _ _ k HrelM Hvs ltac:(lia)) as Hpre.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HSb _ _ _ Hσ)).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as Ht.
    assert (HCw : ⊢ record_params R ++ Δ).
    { pose proof (record_fctx_app_wf _ _ R 0 Δ ltac:(lia) Hc Hass (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) HΔ) as H.
      change (record_fctx R 0) with (@nil centry) in H; exact H. }
    (* the parameters of the element's type are the substituted ones *)
    pose proof (record_params_glu_at _ _ _ _ _ _ _ HSb Hσ Hn HNt HNg Ens) as HNσ.
    destruct HNs0 as [_ Hwk0]; destruct (Hwk0 Δ wk_id Hid) as [Htop0 _ _].
    rewrite map_wk_id in Htop0.
    assert (HEq : exps_eq_at Δ (record_params R) Ns0 (List.map (fun N => N[σ]) Ns)).
    { eapply record_params_glu_eq; [ exact Hass | exact HCw | | exact Htop0 | exact HNσ ].
      destruct (Htop (length Δ)) as (Cs & HCs & _); exists Cs; exact HCs. }
    pose proof (Hk Δ wk_id (List.map (fun N => N[σ]) Ns) Hid ltac:(rewrite map_wk_id; exact HEq) k f U r Hfk Hr) as HPk.
    rewrite exp_wk_id in HPk.
    (* the field's type at the parameters and the projections before *)
    assert (Ems : ⟦ Ns ++ record_pre R k M ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns ++ List.firstn k vs)
      by (apply eval_exps_app; [ exact Ens | exact (eval_record_pre _ _ _ _ _ Em Hvs k ltac:(lia)) ]).
    assert (HMv : Γ ⊨ M : apps_exp (a_record p) Ns) by exact (completeness_fundamental_exp _ _ _ HMt).
    assert (HNv : forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
                    Γ ⊨ N : A)
      by (intros * HN HA; exact (completeness_fundamental_exp _ _ _ (HNt _ _ _ HN HA))).
    destruct (field_inst_link R Hass Hsu HFv HTv Γ k f U (Ns ++ record_pre R k M) RΓ ρ (ns ++ List.firstn k vs)
                Hfk HΓs HRΓ ltac:(rewrite List.length_app, length_record_pre by lia; lia)
                ltac:(apply record_pre_insts; try assumption; [ lia |];
                      intros j0 g U0 Hj0 Hg0; eapply valid_exp_under_ctx_proj; eassumption)
                (glu_ctx_env_per_env HSb HRΓ Hσ) Ems) as (j0 & t & u & Et & Eu & Htu).
    pose proof (HgF0 k f U (List.firstn k vs) u Hfk Hpre Eu) as Hgu.
    pose proof (glu_univ_elem_resp_per_univ_at _ _ _ _ _ _ Hgu Htu) as Hgt.
    econstructor; [ exact Et | econstructor; [ exact Em | exact (Forall2_nth_both _ _ _ _ _ _ Hvs Hfk Hr) ] | exact Hgt |].
    cbn [exp_sub].
    rewrite (record_field_sub R k f U Ns (record_pre R k M) σ Hc Hfk Hn ltac:(apply length_record_pre; lia)), record_pre_sub.
    exact HPk.
  Qed.

  (** ** Tuples *)

  (** A tuple of glued fields at a glued record type at glued parameters
      is glued at that type: the type is the record type at the
      parameters, and each field's projection is the field (field-β),
      glued at its type, by induction on the position, since the field's
      type is glued after the fields before it are. *)
  Lemma glu_rel_exp_tuple : forall Γ T Ns (fs : list (String.string * exp)) (i : nat),
      Γ ⊩ T : Typeω@i ->
      Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
      Γ ⊢ a_record p : record_ty R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊢ N : A) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊩ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Γ ⊩ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      Γ ⊩ a_tuple T fs : T.
  Proof.
    intros * HT HTeq Hrt Hn HNt HNg Hfs HMt HMg.
    pose proof HT as [Sb HSb _ _].
    assert (HΓ : ⊢ Γ) by exact (glu_ctx_env_wf_ctx HSb).
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    assert (Ht : Γ ⊢ a_tuple T fs : T)
      by (eapply wf_tuple; [ exact (glu_rel_exp_to_wf_exp HT) | exact HTeq | exact Hrt | exact Hl | exact Hn | exact HNt
                           | exact Hfs | exact HMt ]).
    destruct (rel_exp_of_typ_inversion_simple (completeness_fundamental_exp_eq _ _ _ _ HTeq)) as (RΓ1 & HRΓ1 & HTrel).
    destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Ht)) as (RΓ2 & HRΓ2 & j2 & Htrel).
    pose proof (per_ctx_env_right_irrel _ _ _ _ _ HRΓ HRΓ1) as ER1.
    pose proof (per_ctx_env_right_irrel _ _ _ _ _ HRΓ HRΓ2) as ER2.
    assert (HNv : forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
                    Γ ⊨ N : A)
      by (intros * HN HA; exact (completeness_fundamental_exp _ _ _ (HNt _ _ _ HN HA))).
    assert (HMv : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
                    Γ ⊨ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))])
      by (intros * HM HU; exact (completeness_fundamental_exp _ _ _ (HMt _ _ _ _ HM HU))).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [ exact HSb |]; intros Δ σ ρ Hσ.
    pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
    assert (Hσt : Δ ⊢ˢ σ : Γ) by exact (glu_ctx_env_sub_escape HSb _ _ _ Hσ).
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσt).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    destruct (glu_rel_exp_of_univ_inversion (u := ul i) HSb HT _ _ _ Hσ) as (HTσ & a & Ea & Hpa & HPa & _).
    destruct (HTrel ρ ρ (proj1 (ER1 _ _) Hρ)) as (a1 & a2 & Ea1 & Ea2 & Ha12).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (eval_record_apps_inv _ _ Hl _ _ _ Ea2 Hn) as (ns & Ens & ->).
    assert (Hdd : Dom d_record p ns ≈ d_record p ns ∈ per_univ i)
      by exact (per_univ_trans' _ _ _ _ _ (per_univ_sym' _ _ _ Ha12) Ha12).
    destruct (per_univ_glu_univ_elem _ _ Hdd) as (P & El & Hglu).
    pose proof (glu_univ_elem_resp_per_univ_at _ _ _ _ _ _ Hglu Ha12) as Hga.
    destruct (Htrel ρ ρ (proj1 (ER2 _ _) Hρ)) as (b & b' & Rb & Eb & _ & HRb & mt & mt' & Emt & Emt' & Hmt).
    assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (mt' = mt) as -> by (eapply functional_eval_exp; eassumption).
    pose proof Emt as Emt0; inversion Emt0; subst.
    match goal with H : ⟦ List.map snd fs ⟧* _ ⍮ _ ⍮ ρ ↘ ?vs |- _ => rename vs into ms; rename H into Ems end.
    econstructor; [ exact Ea | exact Emt | exact Hga |].
    pose proof Hglu as Hglu'; invert_glu_univ_elem Hglu'.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p ns) (d_record p ns) |- _ => rename H0 into Hper end.
    match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
    match goal with HeT : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename HeT into HeT0 end.
    match goal with HP : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename HP into HPP end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl end.
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ HE].
    assert (Hm : elem_rel (d_tuple (List.combine (List.map fst fs) ms)) (d_tuple (List.combine (List.map fst fs) ms))).
    { destruct Ha12 as [R12 HR12].
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR12 HRb) as E1.
      pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR12 Hper) as E2.
      exact (proj1 (E2 _ _) (proj2 (E1 _ _) Hmt)). }
    pose proof (proj1 (HE _ _) Hm) as HrelM.
    assert (Hlms : List.length ms = List.length (record_fields R))
      by (rewrite (Completeness.Inductives.Model.eval_exps_length _ _ _ Ems), List.length_map; exact Hlf).
    pose proof (tuple_projs R Hnd fs ms Hfs Hlms) as Hvs.
    pose proof (record_params_glu_args_at _ _ _ _ _ _ _ HSb Hσ Hn HNt HNg Ens) as HNσ.
    (* the type is the record type at the substituted parameters *)
    assert (HTat : record_typ_at p R ns FP FEl Typeω@(large_level i) Δ T[σ] (List.map (fun N => N[σ]) Ns)).
    { destruct (proj1 (HPP _ _) (HPa _ _ Hga)) as [Ns1 HNs1].
      eapply record_typ_at_params_change; [ exact Hl | intros n0; destruct (Htop n0) as (Cs & HCs & _); exists Cs; exact HCs | | exact HNs1 ].
      intros Δ' φ Hφ; apply glu_args_params_glu_top; [ exact Hass | exact (closed_params _ Hc) |].
      eapply glu_args_wk; [ exact Hass | exact (closed_params _ Hc) | exact Hφ | exact HNσ ]. }
    destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HTat Δ wk_id Hid) as [Htop1 Hsort1 Hfg1].
    rewrite map_wk_id in Htop1, Hsort1, Hfg1.
    assert (Hfg : record_fields_glu R ns FP FEl Δ (List.map (fun N => N[σ]) Ns)).
    { apply Hfg1; split; [ reflexivity |].
      intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
      apply wf_exp_eq_refl; exact (params_glu_typ _ _ _ _ Htop1 _ _ _ HX HA). }
    set (Ms := List.map snd fs) in *.
    (* each field, glued at its family, by induction on the position *)
    assert (HG : forall n k f M U r, k < n -> List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               List.nth_error ms k = Some r ->
               Δ ⊢ M[σ] : U[sb_of_list Id (List.map (fun N => N[σ]) Ns ++ List.firstn k (List.map (fun N => N[σ]) Ms))]
                 ® r ∈ FEl k (List.firstn k ms)).
    { induction n as [| n IH]; intros k f M U r Hkn Hk Hfk Hr; [ lia |].
      destruct (Nat.lt_ge_cases k n) as [Hkn' | Hkn']; [ exact (IH _ _ _ _ _ Hkn' Hk Hfk Hr) |].
      assert (k = n) as -> by lia; clear Hkn Hkn'.
      assert (Hlt : n < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      destruct (glu_rel_exp_clean_inversion1 HSb (HMg _ _ _ _ Hk Hfk)) as [ik Hik].
      destruct (Hik _ _ _ Hσ) as [ak mk Pk Elk Eak Emk Hgk HMk].
      destruct (Completeness.Inductives.Model.eval_exps_nth _ _ _ _ _ Ems
                  ltac:(unfold Ms; rewrite List.nth_error_map, Hk; reflexivity)) as (v & Hv & Ev).
      rewrite Hr in Hv; injection Hv as <-.
      assert (mk = r) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (record_projs_prefix_diag _ _ _ _ n HrelM Hvs ltac:(lia)) as Hpre.
      destruct (field_inst_link R Hass Hsu HFv HTv Γ n f U (Ns ++ List.firstn n Ms) RΓ ρ (ns ++ List.firstn n ms)
                  Hfk HΓs HRΓ ltac:(unfold Ms; rewrite List.length_app, List.length_firstn, List.length_map; lia)
                  ltac:(eapply tuple_insts; try eassumption; lia) Hρ
                  ltac:(apply eval_exps_app; [ exact Ens | apply Completeness.Records.Model.eval_exps_firstn; exact Ems ]))
        as (j0 & t & u & Et & Eu & Htu).
      assert (t = ak) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (HgF0 n f U (List.firstn n ms) u Hfk Hpre Eu) as Hgu.
      pose proof (glu_univ_elem_resp_per_univ_at _ _ _ _ _ _ Hgu Htu) as Hgak.
      assert (HFPk : Δ ⊢ U[sb_of_list Id (List.map (fun N => N[σ]) Ns ++ List.firstn n (List.map (fun N => N[σ]) Ms))]
                       ® FP n (List.firstn n ms)).
      { apply (Hfg n f U (List.firstn n (List.map (fun N => N[σ]) Ms)) (List.firstn n ms) Hfk);
          [ unfold Ms; rewrite List.length_firstn, !List.length_map; lia | rewrite List.length_firstn; lia | | exact Hpre ].
        intros j g T' M' m Hj HM' Hm'.
        assert (Hjn : j < n) by (pose proof (nth_error_lt_length _ _ _ HM') as Hx; rewrite List.length_firstn in Hx; lia).
        rewrite nth_error_firstn_lt in HM' by exact Hjn; rewrite nth_error_firstn_lt in Hm' by exact Hjn.
        destruct (nth_error_lt_some fs j ltac:(lia)) as [[g' Mj] Hgj].
        assert (g' = g) as ->.
        { pose proof (List.map_nth_error fst _ _ Hgj) as E1; pose proof (List.map_nth_error fst _ _ Hj) as E2.
          rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
        unfold Ms in HM'; rewrite List.map_map, List.nth_error_map, Hgj in HM'; cbn in HM'; injection HM' as <-.
        rewrite !List.firstn_firstn, !Nat.min_l by lia.
        exact (IH _ _ _ _ _ Hjn Hgj Hj Hm'). }
      rewrite (record_field_sub R n f U Ns (List.firstn n Ms) σ Hc Hfk Hn ltac:(unfold Ms; rewrite List.length_firstn, List.length_map; lia)),
        <- List.firstn_map in HMk.
      eapply glu_univ_elem_exp_conv;
        [ eapply glu_univ_elem_per_univ; exact Hgk | exact Hgk | exact Hgak | exact HMk | exact HFPk ]. }
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun N => N[σ]) Ns) HTat ms Hvs _); [ mauto 3 |].
    intros Δ' φ Ns' Hφ HNs' k f U r Hfk Hr.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hk].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hk) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    pose proof (HG (S k) k f M U r ltac:(lia) Hk Hfk Hr) as HGk.
    destruct (HeT0 k f U (List.firstn k ms) Hfk (record_projs_prefix_diag _ _ _ _ k HrelM Hvs ltac:(lia))) as [u Eu].
    pose proof (HgF0 k f U (List.firstn k ms) u Hfk (record_projs_prefix_diag _ _ _ _ k HrelM Hvs ltac:(lia)) Eu) as Hgu.
    (* the projection is the field, at the field's type at the projections *)
    destruct (tuple_proj_eq _ _ _ _ _ _ _ _ _ Ht HTeq Hrt Hl Hn HNt Hfs HMt k f M U Hk Hfk) as [HUU HPM].
    assert (HUUσ : Δ ⊢ U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))][σ]
                     ≈ U[sb_of_list Id (Ns ++ List.firstn k Ms)][σ] : (record_sort R)[sb_of_list Id Ns][σ]) by mauto 3.
    assert (HPMσ : Δ ⊢ (a_proj f (a_tuple T fs))[σ] ≈ M[σ] : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))][σ])
      by mauto 3.
    change ((a_proj f (a_tuple T fs))[σ]) with (a_proj f (a_tuple T fs)[σ]) in HPMσ.
    rewrite (record_sort_sub _ _ _ Hc Hn) in HUUσ.
    rewrite (record_field_sub R k f U Ns (record_pre R k (a_tuple T fs)) σ Hc Hfk Hn ltac:(apply length_record_pre; lia)),
      record_pre_sub in HUUσ, HPMσ.
    rewrite (record_field_sub R k f U Ns (List.firstn k Ms) σ Hc Hfk Hn ltac:(unfold Ms; rewrite List.length_firstn, List.length_map; lia)),
      <- List.firstn_map in HUUσ.
    assert (HUUi := wf_exp_eq_subtyp' _ _ _ _ _ _ _ HUUσ Hsort1).
    pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgu _ _ _ _ _ HGk (symmetry HUUi)) as HG1.
    pose proof (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hgu _ _ _ _ _ HG1 (symmetry HPMσ)) as HG2.
    pose proof (glu_univ_elem_exp_monotone _ _ _ _ Hgu _ _ _ _ _ _ HG2 Hφ) as HG3.
    change ((a_proj f (a_tuple T fs)[σ])[φ]ʷ) with (a_proj f (a_tuple T fs)[σ][φ]ʷ) in HG3.
    rewrite (record_field_wk R k f U (List.map (fun N => N[σ]) Ns) (record_pre R k (a_tuple T fs)[σ]) φ Hc Hfk
               ltac:(rewrite List.length_map; exact Hn) ltac:(apply length_record_pre; lia)),
      record_pre_wk in HG3.
    eapply (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgu); [ exact HG3 |].
    destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HTat Δ' φ Hφ) as [Htop2 Hsort2 _].
    destruct HNs' as [HlN HNN].
    assert (Htσ : Δ ⊢ (a_tuple T fs)[σ] : apps_exp (a_record p) (List.map (fun N => N[σ]) Ns))
      by (eapply wf_conv'; [ mauto 3 | exact (record_typ_eq _ _ _ _ _ _ _ _ _ HTat) ]).
    assert (Htφ : Δ' ⊢ (a_tuple T fs)[σ][φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) (List.map (fun N => N[σ]) Ns)))
      by (rewrite <- wk_apps_record; mauto 3).
    assert (Hrt' : Δ' ⊢ a_record p : record_ty R) by (gen_presups; eapply wf_record_own_apps; eassumption).
    eapply record_field_params_cong;
      [ exact Htφ | exact Hrt' | exact Hl | exact (params_glu_len _ _ _ _ Htop2) | rewrite <- HlN; exact (params_glu_len _ _ _ _ Htop2)
      | exact (params_glu_typ _ _ _ _ Htop2) | exact HNN | exact Hsort2 | exact Hfk ].
  Qed.

  (** ** The Projections of a Tuple, Glued

      Fields glued along the record's fields at [Ns]: the projections of
      their tuple are glued alike (field-β). *)
  Lemma glu_args_tuple_projs : forall Δ T Ns fs (i : nat) ρ vs,
      Δ ⊢ a_tuple T fs : T -> Δ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i -> Δ ⊢ a_record p : record_ty R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Δ ⊢ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Ns) ρ (List.map snd fs) vs ->
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Ns) ρ
        (record_pre R (List.length (record_fields R)) (a_tuple T fs)) vs.
  Proof.
    intros * Ht HTeq Hrt Hn HNt Hfs HF.
    set (n := List.length (record_fields R)) in *.
    pose proof HF as [L1 L2 HFk].
    rewrite List.length_map, length_record_fctx in L1 by lia.
    rewrite length_record_fctx in L2 by lia.
    (** The fields, typed at the record's fields at [Ns]. *)
    assert (HMt : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               Δ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]).
    { intros k f M U Hk Hfk.
      assert (Hkn : k < n) by exact (nth_error_lt_length _ _ _ Hfk).
      destruct (nth_error_lt_some' (tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs)) k) as [T0 HT0].
      { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx, List.length_map by lia; lia. }
      pose proof (glu_args_typed _ _ _ _ _ _ (record_fctx_ass _ _) HF k M T0
                    ltac:(rewrite List.nth_error_map, Hk; reflexivity) HT0) as HM.
      destruct (tele_insts_nth _ _ _ _ _ HT0) as (A1 & HA1 & ->).
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA1
        by (rewrite Completeness.Records.Model.length_field_tele; lia).
      unfold Completeness.Records.Model.field_tele in HA1; rewrite List.nth_error_map, Hfk in HA1; cbn in HA1; injection HA1 as <-.
      rewrite <- sb_of_list_app in HM; exact HM. }
    constructor; [ rewrite length_record_pre, length_record_fctx by lia; reflexivity | rewrite length_record_fctx by lia; exact L2 |].
    intros k M U' v A HM HT Hv HA.
    rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA
      by (rewrite Completeness.Records.Model.length_field_tele; lia).
    destruct (Completeness.Records.Model.field_tele_nth _ _ _ HA) as [f Hf].
    assert (Hkn : k < n) by exact (nth_error_lt_length _ _ _ Hf).
    destruct (nth_error_lt_some' fs k ltac:(lia)) as [[g Mk] Hk].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hk) as E1; pose proof (List.map_nth_error fst _ _ Hf) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    unfold record_pre in HM; rewrite List.firstn_all2 in HM by lia.
    rewrite List.nth_error_map, Hf in HM; cbn in HM; injection HM as <-.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A1 & HA1 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA1
      by (rewrite Completeness.Records.Model.length_field_tele; lia).
    unfold Completeness.Records.Model.field_tele in HA1; rewrite List.nth_error_map, Hf in HA1; cbn in HA1; injection HA1 as <-.
    rewrite <- sb_of_list_app.
    replace (List.firstn k (record_pre R n (a_tuple T fs))) with (record_pre R k (a_tuple T fs))
      by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
    (** The field's own gluing. *)
    destruct (nth_error_lt_some' (tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs)) k) as [T0 HT0].
    { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx, List.length_map by lia; lia. }
    assert (HA0 : List.nth_error (List.rev (record_fctx R n)) k = Some (ce_ass A)).
    { rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2
        by (rewrite Completeness.Records.Model.length_field_tele; lia); exact HA. }
    pose proof (HFk k Mk T0 v A ltac:(rewrite List.nth_error_map, Hk; reflexivity) HT0 Hv HA0) as [lv a P El Ea Hga HP HMg].
    destruct (tele_insts_nth _ _ _ _ _ HT0) as (A1 & HA1 & ->).
    rewrite HA0 in HA1; injection HA1 as <-.
    rewrite <- sb_of_list_app in HP, HMg.
    (** Field-β, at a universe. *)
    destruct (tuple_proj_eq _ _ _ _ _ _ _ _ _ Ht HTeq Hrt Hl Hn HNt Hfs HMt k f Mk A Hk Hf) as [HUU HPM].
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) as HRt.
    pose proof (typed_sort _ _ _ HRt) as HS.
    assert (HPw : ⊢ gc_deps ⍮ gc_stack ⍮ record_params R) by (eapply presup_is_univ_ctx; eassumption).
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    assert (HSs : gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵤ (record_sort R)[sb_of_list Id Ns]).
    { eapply (proj1 (proj2 (proj2 (proj2 sub_preserves_wf)))); [ exact HS |].
      rewrite <- (List.app_nil_r (record_params R)).
      eapply wf_sub_of_list; [ exact (typed_params_ass _ _ _ HRt) | rewrite List.app_nil_r; exact HPw
                             | exact (wf_sub_to_nil _ _ _ HΔ) | exact Hn | exact HNt ]. }
    destruct (wf_exp_eq_is_univ_large HSs HUU) as [j HUUj].
    set (nn := Nat.max (large_level lv) j).
    assert (Hle : universe_index_le lv (ul nn)) by (apply universe_index_le_ul_max; unfold nn; lia).
    destruct (glu_univ_elem_cumu_ge_universe_index Hle Hga) as (Pn & Eln & Hgn).
    pose proof (glu_univ_elem_typ_cumu_ge_universe_index Hle Hga Hgn HP) as HPn.
    pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hle Hga Hgn HMg) as HMn.
    pose proof (lift_exp_eq_ge _ _ _ _ _ j nn ltac:(unfold nn; lia) HUUj) as HUUn.
    refine (mk_glu_arg _ _ _ _ _ _ (ul nn) a Pn Eln Ea Hgn _ _).
    - exact (glu_univ_elem_typ_resp_exp_eq _ _ _ _ Hgn _ _ _ HPn (wf_exp_eq_sym _ _ _ _ _ _ HUUn)).
    - pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgn _ _ _ _ _ HMn (wf_exp_eq_sym _ _ _ _ _ _ HUUn)) as H1.
      exact (glu_univ_elem_trm_resp_exp_eq _ _ _ _ Hgn _ _ _ _ _ H1 (wf_exp_eq_sym _ _ _ _ _ _ HPM)).
  Qed.

  (** ** An Element by its Projections

      A term of a glued record type at glued parameters [Ns], whose value
      is related to itself and whose projections are glued along the
      record's fields at [Ns] to the value's, is glued at the type: the
      converse of [record_elem_fields_glu].  Field by field, the field's
      type is glued at its family, given the fields before it. *)
  Lemma record_glu_of_fields : forall Δ W M Ns ns m ms (i : nat) P El,
      DG d_record p ns ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ W ® P -> Δ ⊢ M : W ->
      glu_args Δ (record_params R) Id nil Ns ns ->
      Dom m ≈ m ∈ record_rel R (canon_fields_rel R ns) -> record_projs R m ms ->
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Ns) (env_args nil ns)
        (record_pre R (List.length (record_fields R)) M) ms ->
      Δ ⊢ M : W ® m ∈ El.
  Proof.
    intros * Hglu HW HM HNs Hm Hvs HF.
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    destruct (glu_args_length _ _ _ _ _ _ HNs) as [LN _].
    invert_glu_univ_elem Hglu.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => assert_fails constr_eq R0 R; rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p ns) (d_record p ns) |- _ => rename H0 into Hper end.
    match goal with H : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename H into HgF0 end.
    match goal with H : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename H into HeT0 end.
    match goal with H : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename H into HPP end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl end.
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ HE].
    pose proof (record_projs_length _ _ _ Hvs) as Lw.
    (** The type, at the given parameters. *)
    destruct (proj1 (HPP _ _) HW) as [Ns0 HNs0].
    assert (HTat : record_typ_at p R ns FP FEl Typeω@(large_level i) Δ W Ns).
    { eapply record_typ_at_params_change;
        [ exact Hl | intros n0; destruct (Htop n0) as (Cs & HCs & _); exists Cs; exact HCs | | exact HNs0 ].
      intros Δ' φ Hφ; apply glu_args_params_glu_top; [ exact Hass | exact (closed_params _ Hc) |].
      eapply glu_args_wk; [ exact Hass | exact (closed_params _ Hc) | exact Hφ | exact HNs ]. }
    destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HTat Δ wk_id Hid) as [Htop1 Hsort1 Hfg1].
    rewrite map_wk_id in Htop1, Hsort1, Hfg1.
    assert (Hfg : record_fields_glu R ns FP FEl Δ Ns).
    { apply Hfg1; split; [ reflexivity |].
      intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
      apply wf_exp_eq_refl; exact (params_glu_typ _ _ _ _ Htop1 _ _ _ HX HA). }
    set (n := List.length (record_fields R)) in *.
    (** Each projection, glued at its family, by induction on the
        position. *)
    assert (HG : forall n0 k f U r, k < n0 -> List.nth_error (record_fields R) k = Some (f, U) -> List.nth_error ms k = Some r ->
               Δ ⊢ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] ® r ∈ FEl k (List.firstn k ms)).
    { induction n0 as [| n0 IH]; intros k f U r Hkn Hfk Hr; [ lia |].
      destruct (Nat.lt_ge_cases k n0) as [Hkn' | Hkn']; [ exact (IH _ _ _ _ Hkn' Hfk Hr) |].
      assert (k = n0) as -> by lia; clear Hkn Hkn'.
      assert (Hlt : n0 < n) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof HF as [L1 L2 HFk].
      assert (HM0 : List.nth_error (record_pre R n M) n0 = Some (a_proj f M))
        by (unfold record_pre; rewrite List.firstn_all2 by lia; rewrite List.nth_error_map, Hfk; reflexivity).
      assert (HA0 : List.nth_error (List.rev (record_fctx R n)) n0 = Some (ce_ass U)).
      { rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2
          by (rewrite Completeness.Records.Model.length_field_tele; lia).
        unfold Completeness.Records.Model.field_tele; rewrite List.nth_error_map, Hfk; reflexivity. }
      destruct (nth_error_lt_some' (tele_insts (record_fctx R n) (sb_of_list Id Ns) (record_pre R n M)) n0) as [T0 HT0].
      { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx, length_record_pre by lia; lia. }
      pose proof (HFk _ _ _ _ _ HM0 HT0 Hr HA0) as [j' a P' El' Ea Hg' HP' HM'].
      destruct (tele_insts_nth _ _ _ _ _ HT0) as (A1 & HA1 & ->).
      rewrite HA0 in HA1; injection HA1 as <-.
      rewrite <- sb_of_list_app in HP', HM'.
      replace (List.firstn n0 (record_pre R n M)) with (record_pre R n0 M) in HP', HM'
        by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
      pose proof (record_projs_prefix_diag _ _ _ _ n0 Hm Hvs ltac:(lia)) as Hpre.
      rewrite <- env_args_app in Ea.
      pose proof (HgF0 n0 f U (List.firstn n0 ms) a Hfk Hpre Ea) as Hgu.
      assert (HFPk : Δ ⊢ U[sb_of_list Id (Ns ++ record_pre R n0 M)] ® FP n0 (List.firstn n0 ms)).
      { apply (Hfg n0 f U (record_pre R n0 M) (List.firstn n0 ms) Hfk);
          [ apply length_record_pre; lia | rewrite List.length_firstn; lia | | exact Hpre ].
        intros j g T' M' m' Hj HMj Hmj.
        assert (Hjn : j < n0)
          by (pose proof (nth_error_lt_length _ _ _ HMj) as Hx; rewrite length_record_pre in Hx by lia; lia).
        unfold record_pre in HMj; rewrite List.nth_error_map, nth_error_firstn_lt, Hj in HMj by exact Hjn.
        cbn in HMj; injection HMj as <-.
        rewrite nth_error_firstn_lt in Hmj by exact Hjn.
        rewrite List.firstn_firstn, Nat.min_l by lia.
        replace (List.firstn j (record_pre R n0 M)) with (record_pre R j M)
          by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
        exact (IH _ _ _ _ Hjn Hj Hmj). }
      eapply glu_univ_elem_exp_conv_universe_index; [ eapply glu_univ_elem_per_univ; exact Hg' | exact Hg' | exact Hgu | exact HM' | exact HFPk ]. }
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ (proj2 (HE _ _) Hm) Ns HTat ms Hvs _); [ exact HM |].
    (** At a weakening and an equal instance of the parameters. *)
    intros Δ' φ Ns' Hφ HNs' k f U r Hfk Hr.
    assert (Hlt : k < n) by exact (nth_error_lt_length _ _ _ Hfk).
    pose proof (HG (S k) k f U r ltac:(lia) Hfk Hr) as HGk.
    pose proof (record_projs_prefix_diag _ _ _ _ k Hm Hvs ltac:(lia)) as Hpre.
    destruct (HeT0 k f U (List.firstn k ms) Hfk Hpre) as [u Eu].
    pose proof (HgF0 k f U (List.firstn k ms) u Hfk Hpre Eu) as Hgu.
    pose proof (glu_univ_elem_exp_monotone _ _ _ _ Hgu _ _ _ _ _ _ HGk Hφ) as HG3.
    change ((a_proj f M)[φ]ʷ) with (a_proj f M[φ]ʷ) in HG3.
    rewrite (record_field_wk R k f U Ns (record_pre R k M) φ Hc Hfk LN ltac:(apply length_record_pre; lia)), record_pre_wk in HG3.
    eapply (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgu); [ exact HG3 |].
    destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HTat Δ' φ Hφ) as [Htop2 Hsort2 _].
    destruct HNs' as [HlN HNN].
    assert (Htσ : Δ ⊢ M : apps_exp (a_record p) Ns)
      by (eapply wf_conv'; [ exact HM | exact (record_typ_eq _ _ _ _ _ _ _ _ _ HTat) ]).
    assert (Htφ : Δ' ⊢ M[φ]ʷ : apps_exp (a_record p) (List.map (fun N => N[φ]ʷ) Ns))
      by (rewrite <- wk_apps_record; mauto 3).
    assert (Hrt' : Δ' ⊢ a_record p : record_ty R) by (gen_presups; eapply wf_record_own_apps; eassumption).
    eapply record_field_params_cong;
      [ exact Htφ | exact Hrt' | exact Hl | exact (params_glu_len _ _ _ _ Htop2) | rewrite <- HlN; exact (params_glu_len _ _ _ _ Htop2)
      | exact (params_glu_typ _ _ _ _ Htop2) | exact HNN | exact Hsort2 | exact Hfk ].
  Qed.

  (** ** The Type Former

      At a declaration whose judgments are glued, and whose type former's
      type is a type, the type former applied to glued parameters is a
      type of the sort's universe, its fields glued at the families of
      the clause of [d_record] ([record_fields_glu_of_args]); so the type
      former is glued at its type. *)
  Section Former.
    Hypothesis (HG : glu_record_decl R).
    Variable (i0 : nat).
    Hypothesis (Hty : ⋅ ⊢ record_ty R : Typeω@i0).

    (** The declaration, typed where it is found. *)
    Let Ht := record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl.

    (** The type former, in every context. *)
    Lemma record_former_wf : forall Δ, ⊢ Δ -> Δ ⊢ a_record p : record_ty R.
    Proof.
      intros Δ HΔ.
      eapply wf_record; [ exact HΔ | exact Hl | exact (typed_nodup _ _ _ Ht) | exact Hass | exact Hty
                        | exact (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) | exact (typed_sort _ _ _ Ht)
                        | exact (typed_fields _ _ _ Ht) ].
    Qed.

    (** Arguments glued along the parameters: a glued substitution. *)
    Lemma record_params_glu_sub : forall Δ Ms vs Sb, ⊢ Δ -> EG record_params R ∈ glu_ctx_env ↘ Sb ->
        glu_args Δ (record_params R) Id nil Ms vs -> Δ ⊢ˢ sb_of_list Id Ms ® env_args nil vs ∈ Sb.
    Proof.
      intros * HΔ HSb Hgs.
      eapply glu_sub_of_list with (C := record_params R) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact Hass | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | exact Hg ]
        | cbn; apply wf_sub_nil'; exact HΔ | exact Hgs ].
    Qed.

    (** The sort at glued parameters is below the universe it denotes. *)
    Lemma record_sort_le : forall Δ Ms vs b, ⊢ Δ -> glu_args Δ (record_params R) Id nil Ms vs ->
        ⟦ record_sort R ⟧ env_args nil vs ↘ b ->
        Δ ⊢ (record_sort R)[sb_of_list Id Ms] ⊆ Typeω@(large_level (Completeness.Inductives.Decl.univ_idx b)).
    Proof.
      intros * HΔ Hgs Hb.
      destruct (glued_sort _ HG) as [[j Heq] | (L & n & Heq & HL)]; rewrite Heq in Hb |- *; inversion Hb; subst;
        cbn [Completeness.Inductives.Decl.univ_idx large_level exp_sub].
      - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
      - pose proof HL as [SbP HSbP _ _].
        pose proof (record_params_glu_sub _ _ _ _ HΔ HSbP Hgs) as Hσ.
        destruct (glu_rel_exp_level_elim HSbP HL _ _ _ Hσ) as (m & Hm & Hmm & Hglul).
        assert (Htl : Δ ⊢ L[sb_of_list Id Ms] : Level@n)
          by (eapply glu_lvl_escape; [ exact (per_lvl_at_lvl _ _ _ Hmm) | exact Hglul | exact HΔ ]).
        eapply wf_subtyp_small_large; eassumption.
    Qed.

    (** A type over the parameters and a prefix [Pre], at the sort shifted
        past [Pre], glued at a glued substitution: its value is glued at the
        universe the sort denotes at the parameters' values. *)
    Lemma record_sort_typ_glued : forall Pre A Sb Δ σ vs zs bu, ⊢ Pre ++ record_params R -> List.length zs = List.length Pre ->
        ⟦ record_sort R ⟧ env_args nil vs ↘ bu ->
        EG Pre ++ record_params R ∈ glu_ctx_env ↘ Sb -> Pre ++ record_params R ⊩ A : (record_sort R)[wk_shiftn (List.length Pre)]ʷ ->
        Δ ⊢ˢ σ ® env_args nil (vs ++ zs) ∈ Sb ->
        exists a, ⟦ A ⟧ env_args nil (vs ++ zs) ↘ a /\ Dom a ≈ a ∈ per_univ (Completeness.Inductives.Decl.univ_idx bu) /\
          forall P El, DG a ∈ glu_univ_elem (Completeness.Inductives.Decl.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
    Proof.
      intros * HPre Hzs Hbu HSb HA Hσ.
      destruct (wf_is_univ_typ (typed_sort _ _ _ Ht)) as [iS HS].
      destruct Hsu as [[j Heq] | [t Heq]]; rewrite Heq in HA, HS, Hbu; cbn [exp_wk] in HA.
      - destruct (glu_rel_exp_of_univ_inversion (u := ul j) HSb HA _ _ _ Hσ) as (_ & a & Ha & Hpa & HP & _).
        inversion Hbu; subst; cbn [Completeness.Inductives.Decl.univ_idx].
        exists a; split; [ exact Ha | split; [ exact Hpa | exact HP ] ].
      - destruct (glu_rel_exp_of_suniv_tm_inversion' HSb HA _ _ _ Hσ) as (l & Hlv & _ & _ & a & Ha & Hpa & HP & _).
        exists a; split; [ exact Ha |].
        assert (Hidx : Completeness.Inductives.Decl.univ_idx bu = us (dlvl_real l)).
        { assert (HCs : ⊨ Pre ++ record_params R) by (apply completeness_fundamental_ctx; exact HPre).
          assert (HSs : record_params R ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
          destruct (rel_ctx_wf_per_ctx_env HCs) as [RC HRC].
          pose proof (glu_ctx_env_per_env HSb HRC Hσ) as HE.
          assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length Pre)]ʷ ⟧ env_args nil (vs ++ zs) ↘ d_suniv l)
            by (cbn [exp_wk]; econstructor; exact Hlv).
          assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length Pre)⟫ (env_args nil (vs ++ zs)) ↘ bu)
            by (rewrite env_args_app, <- Hzs, Completeness.UnitCases.eval_wk_shiftn_args; exact Hbu).
          pose proof (Completeness.Inductives.Decl.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HRC HE Eb Ea ltac:(right; eauto)) as Hi.
          rewrite Hi; reflexivity. }
        rewrite Hidx; split; [ exact Hpa | exact HP ].
    Qed.

    (** The fields at glued parameters are glued at the families of the
        clause of [d_record] at the universe the sort denotes. *)
    Lemma record_fields_glu_of_args : forall Δ Ns vs b (u : universe_index) FP FEl, ⊢ Δ ->
        glu_args Δ (record_params R) Id nil Ns vs -> ⟦ record_sort R ⟧ env_args nil vs ↘ b ->
        universe_index_le (Completeness.Inductives.Decl.univ_idx b) u ->
        (forall k f T ws, List.nth_error (record_fields R) k = Some (f, T) ->
           tele_prefix_rel (canon_fields_rel R vs) k ws ws -> exists c, ⟦ T ⟧ env_args nil (vs ++ ws) ↘ c) ->
        (forall k f T ws c, List.nth_error (record_fields R) k = Some (f, T) ->
           tele_prefix_rel (canon_fields_rel R vs) k ws ws -> ⟦ T ⟧ env_args nil (vs ++ ws) ↘ c ->
           DG c ∈ glu_univ_elem u ↘ FP k ws ↘ FEl k ws) ->
        record_fields_glu R vs FP FEl Δ Ns.
    Proof.
      intros * HΔ HNs Hb Hub HeT HgF k f T Mfs mfs Hk HMl Hml HMs Hp.
      pose proof (glued_fields _ HG _ _ _ Hk) as HTk; pose proof HTk as [Sbk HSbk _ _].
      assert (Hlk : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
      pose proof (record_fctx_params_ass R k Hass) as HassC.
      pose proof (record_typed_fctx_wf _ _ _ Ht k ltac:(lia)) as HCk.
      pose proof (length_record_fctx R k ltac:(lia)) as HlenF.
      destruct (glu_args_length _ _ _ _ _ _ HNs) as [LN Lv].
      assert (Hσ : Δ ⊢ˢ sb_of_list Id (Ns ++ Mfs) ® env_args nil (vs ++ mfs) ∈ Sbk).
      { eapply glu_sub_of_list with (C := record_fctx R k ++ record_params R) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
          [ exact HassC | rewrite List.app_nil_r; exact HSbk | econstructor; [ reflexivity | exact Hg ]
          | cbn; apply wf_sub_nil'; exact HΔ |].
        apply glu_args_app; [ exact Hass | exact LN | exact Lv |].
        split; [ exact HNs |].
        constructor; [ lia | lia |].
        intros j M T' v A HM HT' Hv HA.
        assert (Hj : j < k) by (pose proof (nth_error_lt_length _ _ _ HM); lia).
        destruct (tele_insts_nth _ _ _ _ _ HT') as (A0 & HA0 & ->).
        rewrite HA in HA0; injection HA0 as <-.
        rewrite rev_record_fctx, nth_error_firstn_lt in HA by exact Hj.
        unfold field_tele in HA; rewrite List.nth_error_map in HA.
        destruct (List.nth_error (record_fields R) j) as [[g Tj] |] eqn:Hj'; cbn in HA; [ injection HA as <- | discriminate ].
        pose proof (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia)) as Hpj.
        destruct (HeT j g Tj (List.firstn j mfs) Hj' Hpj) as [c Ec].
        pose proof (HgF _ _ _ _ _ Hj' Hpj Ec) as Hgc.
        pose proof (HMs j g Tj M v Hj' HM Hv) as HMg.
        rewrite <- sb_of_list_app.
        apply (mk_glu_arg _ _ _ _ _ _ u c (FP j (List.firstn j mfs)) (FEl j (List.firstn j mfs)));
          [ rewrite <- env_args_app; exact Ec | exact Hgc | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ]. }
      destruct (record_sort_typ_glued (record_fctx R k) T Sbk Δ _ vs mfs b HCk ltac:(lia) Hb HSbk
                  ltac:(rewrite HlenF; exact HTk) Hσ) as (a & Ha & Hpa & HP).
      destruct (per_univ_glu_univ_elem _ _ Hpa) as (P0 & El0 & Hg0).
      exact (glu_univ_elem_typ_cumu_ge_universe_index Hub Hg0 (HgF _ _ _ _ _ Hk Hp Ha) (HP _ _ Hg0)).
    Qed.

    (** The type former applied to glued parameters is glued at the sort
        at them. *)
    Lemma record_former_base : forall Δ Ms vs (i : nat) b P El, ⊢ Δ ->
        glu_args Δ (record_params R) Id nil Ms vs ->
        ⟦ record_sort R ⟧ env_args nil vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
        (forall Rr, DF b ≈ b ∈ per_univ_elem i ↘ Rr -> Rr (d_record p vs) (d_record p vs)) ->
        Δ ⊢ apps_exp (a_record p) Ms : (record_sort R)[sb_of_list Id Ms] ® d_record p vs ∈ El.
    Proof.
      intros * HΔ HMs Hb Hglu HPER.
      pose proof (glu_args_params_glu_top _ _ _ _ Hass (closed_params _ Hc) HMs) as Htop.
      pose proof Htop as [HMl HMt HMr].
      pose proof (record_former_wf _ HΔ) as Hrt.
      assert (HAeq : Δ ⊢ apps_exp (a_record p) Ms ≈ apps_exp (a_record p) Ms : (record_sort R)[sb_of_list Id Ms]).
      { eapply wf_exp_eq_record_apps; [ exact Hrt | exact Hl | exact HMl | exact HMl |].
        intros j X Y T HX HY HT; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HMt; eassumption. }
      assert (HAt : Δ ⊢ apps_exp (a_record p) Ms : (record_sort R)[sb_of_list Id Ms]) by (gen_presups; assumption).
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
      pose proof (HPER _ HRb) as Hdrec.
      assert (Hub : Completeness.Inductives.Decl.is_univ b)
        by (destruct Hsu as [[j Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; [ left | right ]; eauto).
      destruct (Completeness.Inductives.Decl.per_univ_elem_univ _ _ _ _ HRb Hub) as [_ HRb'].
      apply HRb' in Hdrec; destruct Hdrec as [R' HR'].
      destruct (per_univ_glu_univ_elem _ _ (ex_intro _ R' HR')) as (Pd & Eld & Hglud).
      pose proof Hglud as Hglud'; invert_glu_univ_elem Hglud'.
      match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
      match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
      match goal with HeT : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename HeT into HeT0 end.
      match goal with HP : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename HP into HPd end.
      assert (Hit : record_typ_at p R vs FP FEl Typeω@(large_level (Completeness.Inductives.Decl.univ_idx b)) Δ (apps_exp (a_record p) Ms) Ms).
      { constructor; [ eapply wf_exp_eq_subtyp'; [ exact HAeq | exact (record_sort_le _ _ _ _ HΔ HMs Hb) ] |].
        intros Δ' φ Hφ.
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        pose proof (glu_args_wk _ _ _ _ _ _ _ Hass (closed_params _ Hc) Hφ HMs) as Hg'.
        constructor; [ exact (glu_args_params_glu_top _ _ _ _ Hass (closed_params _ Hc) Hg') | exact (record_sort_le _ _ _ _ HΔ' Hg' Hb) |].
        intros Ns' HNs'.
        pose proof (glu_args_resp_eq _ _ _ _ _ _ Hass (presup_is_univ_ctx (typed_sort _ _ _ Ht)) HΔ' HNs' Hg') as Hg''.
        eapply record_fields_glu_of_args; [ exact HΔ' | exact Hg'' | exact Hb | apply universe_index_le_refl | exact HeT0 | exact HgF0 ]. }
      assert (Hgd : glu_univ_typ (Completeness.Inductives.Decl.univ_idx b) (d_record p vs) Δ (apps_exp (a_record p) Ms))
        by (eapply mk_glu_typ_at; [ exact Hglud | apply HPd; exists Ms; exact Hit ]).
      clear HPER.
      destruct (glued_sort _ HG) as [[j Heq] | (L & n & Heq & HL)]; rewrite Heq in Hb, HAt |- *; cbn [exp_sub] in HAt |- *;
        inversion Hb; subst b.
      - invert_glu_univ_elem Hglu.
        apply_predicate_equivalence.
        cbn [Completeness.Inductives.Decl.univ_idx] in Hgd.
        econstructor; [ exact HAt | apply wf_exp_eq_refl; mauto 3 | exact Hgd ].
      - invert_glu_univ_elem Hglu.
        apply_predicate_equivalence.
        cbn [Completeness.Inductives.Decl.univ_idx] in Hgd.
        pose proof HL as [SbP HSbP _ _].
        pose proof (record_params_glu_sub _ _ _ _ HΔ HSbP HMs) as Hσ.
        destruct (glu_rel_exp_level_elim HSbP HL _ _ _ Hσ) as (m & Hm & Hmm & Hglul).
        assert (m = l) as -> by (eapply functional_eval_exp; eassumption).
        assert (Htl : Δ ⊢ L[sb_of_list Id Ms] : Level@n)
          by (eapply glu_lvl_escape; [ exact (per_lvl_at_lvl _ _ _ Hmm) | exact Hglul | exact HΔ ]).
        econstructor; [ exact HAt | | exact Hgd |].
        + apply (mk_suniv_glu_typ _ _ _ _ (L[sb_of_list Id Ms]) n); [ exact Hglul |].
          apply wf_exp_eq_refl; mauto 3.
        + intros Δ' φ W Hφ HW.
          inversion HW; subst.
          match goal with H : record_lookup _ _ p = Some ?R1 |- _ => rewrite Hl in H; injection H as <- end.
          match goal with HR : Rps vs at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Rs |- _ => pose proof (HMr _ _ _ Hφ HR) as [HRl HRs] end.
          assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
          assert (Hsw : (record_sort R)[sb_of_list Id Ms][φ]ʷ = (record_sort R)[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ms)]).
          { rewrite <- exp_sub_of_wk, (record_sort_sub _ _ _ Hc HMl); f_equal; f_equal.
            apply List.map_ext; intros; apply exp_sub_of_wk. }
          rewrite Heq in Hsw; cbn [exp_sub exp_wk] in Hsw.
          cbn [nf_to_exp exp_wk]; rewrite apps_exp_wk; cbn [exp_wk]; rewrite Hsw.
          assert (Hl1 : List.length (List.map (fun N => N[φ]ʷ) Ms) = List.length (record_params R))
            by (rewrite List.length_map; exact HMl).
          pose proof (wf_exp_eq_record_apps _ _ _ _ _ _ _ (record_former_wf _ HΔ') Hl Hl1 ltac:(rewrite <- HRl; exact Hl1) HRs)
            as Heqn.
          rewrite Heq in Heqn; exact Heqn.
    Qed.

    (** The type former applied to glued parameters is glued at any
        gluing of the record type at them, at a universe above the sort's
        value there. *)
    Lemma record_typ_glu : forall Δ Ms vs b (i : nat) P El, ⊢ Δ -> glu_args Δ (record_params R) Id nil Ms vs ->
        ⟦ record_sort R ⟧ env_args nil vs ↘ b -> universe_index_le (Completeness.Inductives.Decl.univ_idx b) i ->
        DG d_record p vs ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ apps_exp (a_record p) Ms ® P.
    Proof.
      intros * HΔ HMs Hb Hbi Hglu.
      pose proof (glu_args_params_glu_top _ _ _ _ Hass (closed_params _ Hc) HMs) as Htop.
      pose proof Htop as [HMl HMt HMr].
      pose proof (record_former_wf _ HΔ) as Hrt.
      assert (HAeq : Δ ⊢ apps_exp (a_record p) Ms ≈ apps_exp (a_record p) Ms : (record_sort R)[sb_of_list Id Ms]).
      { eapply wf_exp_eq_record_apps; [ exact Hrt | exact Hl | exact HMl | exact HMl |].
        intros j X Y T HX HY HT; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HMt; eassumption. }
      assert (Hsi : forall Δ' Ms', ⊢ Δ' -> glu_args Δ' (record_params R) Id nil Ms' vs ->
                 Δ' ⊢ (record_sort R)[sb_of_list Id Ms'] ⊆ Typeω@(large_level i)).
      { intros Δ' Ms' HΔ' HMs'.
        eapply wf_subtyp_trans; [ exact (record_sort_le _ _ _ _ HΔ' HMs' Hb) |].
        pose proof (universe_index_le_large_level_le _ _ Hbi) as Hle; cbn [large_level] in Hle |- *.
        destruct (Nat.eq_dec (large_level (Completeness.Inductives.Decl.univ_idx b)) i) as [-> | Hne];
          [ eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3 | apply wf_subtyp_univ; [ exact HΔ' | lia ] ]. }
      pose proof Hglu as Hglu'; invert_glu_univ_elem Hglu'.
      match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
      match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
      match goal with HeT : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename HeT into HeT0 end.
      match goal with HP : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename HP into HPd end.
      apply HPd; exists Ms.
      constructor; [ eapply wf_exp_eq_subtyp'; [ exact HAeq | exact (Hsi _ _ HΔ HMs) ] |].
      intros Δ' φ Hφ.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      pose proof (glu_args_wk _ _ _ _ _ _ _ Hass (closed_params _ Hc) Hφ HMs) as Hg'.
      constructor; [ exact (glu_args_params_glu_top _ _ _ _ Hass (closed_params _ Hc) Hg') | exact (Hsi _ _ HΔ' Hg') |].
      intros Ns' HNs'.
      pose proof (glu_args_resp_eq _ _ _ _ _ _ Hass (presup_is_univ_ctx (typed_sort _ _ _ Ht)) HΔ' HNs' Hg') as Hg''.
      eapply record_fields_glu_of_args; [ exact HΔ' | exact Hg'' | exact Hb | exact Hbi | exact HeT0 | exact HgF0 ].
    Qed.

    (** The type former is related to itself at its type, in the PER
        model. *)
    Lemma record_former_per : forall (i : nat) Rr a, ⟦ record_ty R ⟧ nil ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ Rr ->
        Rr (d_record p nil) (d_record p nil).
    Proof.
      intros * Ha HR.
      assert (Hty0 : ⋅ ⊢ a_record p : record_ty R) by (apply record_former_wf; constructor; exact Hg).
      destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hty0)) as (env_rel & Henv & j & Hsimp).
      assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
      assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
      inversion Hm1; subst; inversion Hm2; subst.
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
    Qed.

    (** The sort at an instance does not depend on the base. *)
    Lemma record_sort_base : forall Ms σ τ, List.length Ms = List.length (record_params R) ->
        (record_sort R)[sb_of_list σ Ms] = (record_sort R)[sb_of_list τ Ms].
    Proof.
      intros * HMl; eapply exp_scoped_sub_agree; [ exact (closed_sort _ Hc) |]; intros x Hx.
      rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by lia; reflexivity.
    Qed.

    (** The type former is glued at its type. *)
    Lemma glu_rel_exp_record0 : ⋅ ⊩ a_record p : record_ty R.
    Proof.
      destruct (glued_params _ HG) as [SbP HSbP].
      assert (HSbP0 : EG record_params R ++ ⋅ ∈ glu_ctx_env ↘ SbP) by (rewrite List.app_nil_r; exact HSbP).
      destruct (glu_ctx_env_entries_valid _ _ _ Hass HSbP0 i0) as (i & Hji & HAents).
      assert (Hi : ⋅ ⊢ record_ty R : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hty ]).
      eapply (glu_closed_const _ _ i (d_record p nil));
        [ reflexivity | intros; apply record_ty_sub, Hc | exact Hi | intros; constructor |].
      intros Δ σ Hσ a P El Ha Hglu.
      assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
      pose proof Hi as Hi'; unfold record_ty in Hi'.
      destruct (ctx_pi_split_typed _ _ _ _ Hass Hi') as [HCs _].
      unfold record_ty in Ha |- *.
      replace (ctx_pi (record_params R) (record_sort R)) with ((ctx_pi (record_params R) (record_sort R))[σ])
        by (change (ctx_pi (record_params R) (record_sort R)) with (record_ty R); apply record_ty_sub, Hc).
      change (a_record p) with (apps_exp (a_record p) nil).
      eapply (ctx_pi_glu_elem_by (fun xs w => w = d_record p xs) (a_record p) (record_params R ++ ⋅))
        with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbP) (xs := nil);
        [ reflexivity | | exact Hass | eapply glu_ctx_env_nil; [ reflexivity | exact Hg ] | exact HSbP0
        | exists nil; reflexivity
        | intros; eapply HAents; eassumption
        | intros; eapply HCs; eassumption
        | exact Hσ | reflexivity | reflexivity | | | | exact Ha | exact Hglu ].
      - intros Δ1 Γ' Sb' Δ' σ' xs x w HT _ _ HlΓ ->.
        exists (d_record p (xs ++ x :: nil)); split; [| reflexivity ].
        eapply eval_app_record; [ exact Hl |].
        assert (List.length Γ' <= List.length (record_params R ++ ⋅)) by (rewrite HT, List.length_app; lia).
        rewrite List.app_nil_r in *; lia.
      - cbn [apps_exp]; change (ctx_pi (record_params R) (record_sort R)) with (record_ty R).
        rewrite record_ty_sub by exact Hc; apply record_former_wf; exact HΔ.
      - intros Rr a' Ha' HR; exact (record_former_per _ _ _ Ha' HR).
      - intros Δ' φ Ms vs w' Hφ Hgs -> b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        apply (glu_args_closed_base _ _ _ Id _ _ _ Hass (closed_params _ Hc)) in Hgs.
        destruct (glu_args_length _ _ _ _ _ _ Hgs) as [HMl _].
        rewrite (record_sort_base _ _ Id HMl).
        exact (record_former_base _ _ _ _ _ _ _ HΔ' Hgs Hb Hglub HPb).
    Qed.

  End Former.

End RecordAt.

End Fixed_GCtx.
