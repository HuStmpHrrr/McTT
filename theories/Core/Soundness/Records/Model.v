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
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
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
From Mctt.Core.Soundness.Inductives Require Import Args Params.
From Mctt.Core.Soundness.Records Require Import Former.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Record at its Model *)

Section RecordAt.
  Variables (p : qname) (R : record_decl).
  Hypothesis (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) (Hl : record_lookup gc_deps gc_stack p = Some R).
  (** The record's declaration is glued *)
  Hypothesis (HG : glu_record_decl R).

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
  Let HPr := params_evaluated_valid _ (model_valid _ _ Hmodel).
  Let HFk := fields_kind_valid _ (model_valid _ _ Hmodel).

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
    destruct (glu_rel_ctx_types_ctx _ (glued_params _ HG)) as [SbP HSbP].
    eapply params_glu_args; [ exact Hass | exact (closed_params _ Hc) | eapply record_params_sem; exact HFv
                            | exact HΓs | exact HSbP | exact HRΓ | exact HSb | exact Hσ | exact Hn |
                            | exact (params_evaluated_valid _ (model_valid _ _ Hmodel))
                            | exact (typed_insts_scoped _ _ _ Hass Hn HNt) | exact HNg | exact Ens ].
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

  (** A field's type at related values of the parameters and the fields
      before it is of the field's kind. *)
  Lemma record_field_type_kind : forall ns vs n f U u,
      per_tele_args (List.rev (record_params R)) nil nil ns ns -> List.length ns = List.length (record_params R) ->
      tele_prefix_rel (canon_fields_rel R ns) n vs vs -> List.length vs = n ->
      List.nth_error (record_fields R) n = Some (f, U) -> ⟦ U ⟧ record_fields_env R ns vs ↘ u ->
      domain_kind u = record_field_kind R n.
  Proof.
    intros * Hgp Hlns Hpre Hlv Hfk Eu.
    assert (Hlt : n < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    destruct (sort_tele_value _ _ HPv HSv ns Hgp Hlns) as [a0 Ha0].
    pose proof (canon_fields_tele_args R Hsu HFv HSv HTv HFk ns ns a0 Hgp Hlns Ha0 n vs vs ltac:(lia) Hpre) as Hgf.
    assert (Hgms : per_tele_args (List.rev (record_fctx R n ++ record_params R)) nil nil (ns ++ vs) (ns ++ vs)).
    { rewrite List.rev_app_distr, rev_record_fctx.
      apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlns | exact Hgp | exact Hgf ]. }
    pose proof (record_fctx_sem R HFv n ltac:(lia)) as HC0.
    destruct (rel_ctx_wf_per_ctx_env HC0) as [RC HRC].
    assert (Hlz : List.length (ns ++ vs) = List.length (record_fctx R n ++ record_params R)).
    { rewrite !List.length_app, length_record_fctx by lia; lia. }
    pose proof (Completeness.Inductives.Model.tele_args_env_rel (record_fctx R n ++ record_params R) RC
                  (ns ++ vs) (ns ++ vs) nil nil HRC HC0 Hlz Hgms) as HE0.
    rewrite (record_fields_env_closed R ns vs Hlns), Hlv in Eu.
    rewrite <- (List.app_nil_r (record_fctx R n ++ record_params R)) in HRC.
    exact (field_type_kind R Hass Hsu HFv HTv HFk ⋅ n f U RC _ _ u Hfk ltac:(constructor) HRC HE0 Eu).
  Qed.

  (** ** Projections *)

  (** The projection of an element glued at the record type at parameters
      is glued at its field's type: it is the projection the element's
      gluing glues, at the parameters, which are the element's type's. *)
  Lemma glu_rel_exp_proj : forall Γ M Ns k f U Srt,
      Γ ⊩ M : apps_exp (a_record p) Ns ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊢ N : A) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Γ ⊩ N : A) ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      (** The field's type there is a glued type, the witness the field's
          value moves to *)
      Γ ⊩ U[sb_of_list Id (Ns ++ record_pre R k M)] : Srt -> type_sort Srt ->
      Γ ⊩ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HM Hn HNt HNg Hfk HU HSrt.
    pose proof HM as [Sb HSb j Hbody].
    assert (HSk : exists κ, sort_kind Srt κ) by (destruct HSrt; eexists; constructor).
    destruct HSk as [κU HSk].
    destruct (glu_rel_exp_sort_typ HU HSk) as (SbU & iU & HSbU & _ & HUg).
    assert (EU : Sb <∙> SbU) by (eapply functional_glu_ctx_env; eassumption).
    assert (HΓ : ⊢ Γ) by exact (glu_ctx_env_wf_ctx HSb).
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    eapply mk_glu_rel_exp with (glu_rel_exp_lvl := iU); [ exact HSb |]; intros Δ σ ρ Hσ.
    destruct (Hbody _ _ _ Hσ) as [a m P El Ea Em Hglu HMg].
    destruct (eval_record_apps_inv _ _ Hl _ _ _ Ea Hn) as (ns & Ens & ->).
    invert_glu_univ_elem Hglu.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p ns) (d_record p ns) |- _ => rename H0 into Hper end.
    match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl in HMg end.
    destruct HMg as [HMs Hm Ns0 HNs0 vs Hvs Hk].
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ _ HE].
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
      destruct (Htop (length Δ)) as [Cs ? HCs _ _]; exists Cs; exact HCs. }
    pose proof (Hk Δ wk_id (List.map (fun N => N[σ]) Ns) Hid ltac:(rewrite map_wk_id; exact HEq) k f U r Hfk Hr) as HPk.
    rewrite exp_wk_id in HPk.
    (* the field's type at the parameters and the projections before *)
    cbn [domain_kind glu_term_value] in Em.
    assert (Ems : ⟦ Ns ++ record_pre R k M ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns ++ List.firstn k vs)
      by (apply eval_exps_app; [ exact Ens | exact (eval_record_pre _ _ _ _ _ Em Hvs k ltac:(lia)) ]).
    assert (HMv : Γ ⊨ M : apps_exp (a_record p) Ns) by exact (completeness_fundamental_exp _ _ _ HMt).
    assert (HNv : forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
                    Γ ⊨ N : A)
      by (intros * HN HA; exact (completeness_fundamental_exp _ _ _ (HNt _ _ _ HN HA))).
    pose proof (typed_insts_scoped _ _ _ Hass Hn HNt) as HNss.
    pose proof (wf_exp_scoped_term _ _ _ _ _ HMt) as HMsc.
    assert (HMss : List.Forall (exp_scoped (List.length Γ)) (Ns ++ record_pre R k M))
      by (apply List.Forall_app; split; [ exact HNss | exact (record_pre_scoped _ _ k _ HMsc) ]).
    pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
    (** The parameters' values and the fields' before, related at the
        fields' telescope. *)
    assert (Hlns : List.length ns = List.length (record_params R))
      by (rewrite <- Hn; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Ens)).
    pose proof (params_inst_tele_args R Hass HFv HPr Γ Ns RΓ ρ ρ ns ns HΓs HRΓ Hn HNv HNss Hρ Ens Ens) as Hgp.
    destruct (sort_tele_value _ _ HPv HSv ns Hgp Hlns) as [a0 Ha0].
    pose proof (canon_fields_tele_args R Hsu HFv HSv HTv HFk ns ns a0 Hgp Hlns Ha0 k (List.firstn k vs) (List.firstn k vs)
                  ltac:(lia) Hpre) as Hgf.
    assert (Hgms : per_tele_args (List.rev (record_fctx R k ++ record_params R)) nil nil
                     (ns ++ List.firstn k vs) (ns ++ List.firstn k vs)).
    { rewrite List.rev_app_distr, rev_record_fctx.
      apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlns | exact Hgp | exact Hgf ]. }
    destruct (field_inst_link R Hass Hsu HFv HTv HPr HFk Γ k f U (Ns ++ record_pre R k M) RΓ ρ (ns ++ List.firstn k vs)
                Hfk HΓs HRΓ ltac:(rewrite List.length_app, length_record_pre by lia; lia)
                ltac:(apply record_pre_insts; try assumption; [ lia |];
                      intros j0 g U0 Hj0 Hg0; eapply valid_exp_under_ctx_proj; eassumption)
                HMss Hρ ltac:(rewrite !List.length_app, length_record_pre, List.length_firstn by lia; lia) Hgms
                ltac:(intros j1 N1 m1 HN1 Hm1; left;
                      destruct (Completeness.Inductives.Model.eval_exps_nth _ _ _ _ _ Ems HN1) as (m1' & Hm1' & Em1');
                      rewrite Hm1 in Hm1'; injection Hm1' as <-; exact Em1'))
      as (j0 & t & u & Et & Eu & Htu).
    pose proof (record_fields_env_closed R ns (List.firstn k vs) Hlns) as Efe.
    rewrite List.length_firstn, Nat.min_l in Efe by lia; rewrite <- Efe in Eu.
    pose proof (HgF0 k f U (List.firstn k vs) u Hfk Hpre Eu) as Hgu.
    (** The field's type at the substituted instance, glued at its own
        value [t] ([glu_rel_exp_sort_typ]) *)
    destruct (HUg _ _ _ (proj1 (EU _ _ _) Hσ)) as [t' Pt Elt Et' Hgt HPt].
    assert (t' = t) as -> by (eapply functional_eval_exp; eassumption).
    (** The projection's value: its evaluation, or the proof kept at a
        proposition. *)
    assert (HPk' : Δ ⊢ (a_proj f M)[σ] : (U[sb_of_list Id (Ns ++ record_pre R k M)])[σ] ® r ∈ FEl k (List.firstn k vs)).
    { cbn [exp_sub].
      rewrite (record_field_sub R k f U Ns (record_pre R k M) σ Hc Hfk Hn ltac:(apply length_record_pre; lia)), record_pre_sub.
      exact HPk. }
    clear HPk.
    (** The field's value moves from the field's type's value [u] to [t],
        at the witness *)
    pose proof (glu_univ_elem_exp_conv (per_univ_sym' _ _ _ Htu) Hgu Hgt HPk' HPt) as HPk.
    clear HPk'.
    assert (Hpt : Γ ⊢ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)])
      by (eapply wf_proj; [ exact HMt | exact (record_former_wf p R Hg Hl _ HΓ) | exact Hl | exact Hn | exact HNt | exact Hfk
                          | exact (glu_rel_exp_to_wf_exp HU) | exact HSrt ]).
    destruct (glu_term_value_intro Hgt HSb Hσ Hpt
                (fun _ => eval_exp_proj _ _ _ _ _ _ _ Em (Forall2_nth_both _ _ _ _ _ _ Hvs Hfk Hr)) HPk) as (m' & Hm' & HM').
    exact (mk_glu_rel_exp_with_sub _ _ _ _ _ _ t m' _ _ Et Hm' Hgt HM').
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
    (** The type's own value, glued: the type is its own witness *)
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hglu).
    pose proof (HPa _ _ Hglu) as HTa.
    destruct (Htrel ρ ρ (proj1 (ER2 _ _) Hρ)) as (b & b' & Rb & Eb & _ & HRb & [Hp | (mt & mt' & Emt & Emt' & Hmt)]);
      [ assert (b = a) as -> by (eapply functional_eval_exp; eassumption);
        destruct Ha12 as [R12 HR12]; rewrite (per_univ_elem_kind _ _ _ _ HR12) in Hp; discriminate Hp |].
    assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (mt' = mt) as -> by (eapply functional_eval_exp; eassumption).
    pose proof Emt as Emt0; inversion Emt0; subst.
    match goal with H : eval_field_vals _ _ _ (List.map snd fs) ρ ?vs |- _ => rename vs into ms; rename H into Ems end.
    match goal with H1 : ⟦ T ⟧ ρ ↘ d_record ?p0 ?nsx, H2 : record_lookup _ _ ?p0 = Some ?R0 |- _ =>
      assert (a = d_record p0 nsx) as -> by (eapply functional_eval_exp; eassumption);
      assert (p0 = p) as -> by (destruct Ha12 as [R12 HR12]; basic_invert_per_univ_elem HR12; reflexivity);
      rewrite Hl in H2; injection H2 as <-; rename nsx into ns0 end.
    econstructor; [ exact Ea | cbn [domain_kind glu_term_value]; exact Emt | exact Hglu |].
    pose proof Hglu as Hglu'; invert_glu_univ_elem Hglu'.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p _) (d_record p _) |- _ => rename H0 into Hper end.
    match goal with HgF : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename HgF into HgF0 end.
    match goal with HeT : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename HeT into HeT0 end.
    match goal with HP : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename HP into HPP end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl end.
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ Hks HE].
    assert (Hm : elem_rel (d_tuple (List.combine (List.map fst fs) ms)) (d_tuple (List.combine (List.map fst fs) ms)))
      by exact (proj2 (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hper HRb _ _) Hmt).
    pose proof (proj1 (HE _ _) Hm) as HrelM.
    assert (Hlms : List.length ms = List.length (record_fields R))
      by (rewrite (eval_field_vals_length _ _ _ _ Ems), List.length_map; exact Hlf).
    pose proof (tuple_projs R Hnd fs ms Hfs Hlms) as Hvs.
    pose proof (record_params_glu_args_at _ _ _ _ _ _ _ HSb Hσ Hn HNt HNg Ens) as HNσ.
    (** The record type at [Ns]'s values [ns], related to the type's [ns0] *)
    destruct (per_univ_sym' _ _ _ Ha12) as [R21 HR21].
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl HR21) as [_ _ _ Htop21 _ _ Hev21 _ HE21].
    (* the type is the record type at the substituted parameters *)
    assert (HTat : record_typ_at p R ns0 FP FEl Typeω@(large_level i) Δ T[σ] (List.map (fun N => N[σ]) Ns)).
    { destruct (proj1 (HPP _ _) HTa) as [Ns1 HNs1].
      eapply record_typ_at_params_change; [ exact Hl | intros n0; destruct (Htop n0) as [Cs ? HCs _ _]; exists Cs; exact HCs | | exact HNs1 ].
      intros Δ' φ Hφ.
      destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HNs1 Δ' φ Hφ) as [Htop1' _ _].
      eapply params_glu_top_resp_per_top_ps; [ exact Htop21 | | exact Htop1' ].
      apply glu_args_params_glu_top; [ exact Hass | exact (closed_params _ Hc) |].
      eapply glu_args_wk; [ exact Hass | exact (closed_params _ Hc) | exact Hφ | exact HNσ ]. }
    destruct (record_typ_wk _ _ _ _ _ _ _ _ _ HTat Δ wk_id Hid) as [Htop1 Hsort1 Hfg1].
    rewrite map_wk_id in Htop1, Hsort1, Hfg1.
    assert (Hfg : record_fields_glu R ns0 FP FEl Δ (List.map (fun N => N[σ]) Ns)).
    { apply Hfg1; split; [ reflexivity |].
      intros k X Y A HX HY HA; rewrite HX in HY; injection HY as <-.
      apply wf_exp_eq_refl; exact (params_glu_typ _ _ _ _ Htop1 _ _ _ HX HA). }
    set (Ms := List.map snd fs) in *.
    (** A field's type at the fields' values before it is of the field's
        kind. *)
    assert (Hkind : forall n f U u, List.nth_error (record_fields R) n = Some (f, U) ->
               ⟦ U ⟧ record_fields_env R ns0 (List.firstn n ms) ↘ u -> domain_kind u = record_field_kind R n).
    { intros n f U u Hfk Eu.
      assert (Hlt : n < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof (record_projs_prefix_diag _ _ _ _ n HrelM Hvs ltac:(lia)) as Hpre.
      destruct (Hks n f U _ _ Hfk Hpre) as (u' & Eu' & Hku').
      assert (u' = u) as -> by (eapply functional_eval_exp; eassumption); exact Hku'. }
    (* each field, glued at its family, by induction on the position *)
    assert (HGf : forall n k f M U r, k < n -> List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
               List.nth_error ms k = Some r ->
               Δ ⊢ M[σ] : U[sb_of_list Id (List.map (fun N => N[σ]) Ns ++ List.firstn k (List.map (fun N => N[σ]) Ms))]
                 ® r ∈ FEl k (List.firstn k ms)).
    { induction n as [| n IH]; intros k f M U r Hkn Hk Hfk Hr; [ lia |].
      destruct (Nat.lt_ge_cases k n) as [Hkn' | Hkn']; [ exact (IH _ _ _ _ _ Hkn' Hk Hfk Hr) |].
      assert (k = n) as -> by lia; clear Hkn Hkn'.
      assert (Hlt : n < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
      destruct (glu_rel_exp_clean_inversion1 HSb (HMg _ _ _ _ Hk Hfk)) as [ik Hik].
      destruct (Hik _ _ _ Hσ) as [ak mk Pk Elk Eak Emk Hgk HMk].
      destruct (eval_field_vals_nth _ _ _ _ Ems n M ltac:(unfold Ms; rewrite List.nth_error_map, Hk; reflexivity))
        as (v & Hv & Hev & Hpv).
      rewrite Hr in Hv; injection Hv as <-.
      pose proof (record_projs_prefix_diag _ _ _ _ n HrelM Hvs ltac:(lia)) as Hpre.
      (** The same prefix at [Ns]'s values *)
      pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR21 Hper) as E21.
      pose proof (record_projs_prefix_diag _ _ _ _ n (proj1 (HE21 _ _) (proj2 (E21 _ _) Hm)) Hvs ltac:(lia)) as Hpre21.
      (** The parameters' values and the fields' before, related at the
          fields' telescope. *)
      assert (Hlns : List.length ns = List.length (record_params R))
        by (rewrite <- Hn; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Ens)).
      pose proof (params_inst_tele_args R Hass HFv HPr Γ Ns RΓ ρ ρ ns ns HΓs HRΓ Hn HNv
                    (typed_insts_scoped _ _ _ Hass Hn HNt) Hρ Ens Ens) as Hgp.
      destruct (sort_tele_value _ _ HPv HSv ns Hgp Hlns) as [a0 Ha0].
      pose proof (canon_fields_tele_args R Hsu HFv HSv HTv HFk ns ns a0 Hgp Hlns Ha0 n (List.firstn n ms) (List.firstn n ms)
                    ltac:(lia) Hpre21) as Hgf.
      assert (Hgms : per_tele_args (List.rev (record_fctx R n ++ record_params R)) nil nil
                       (ns ++ List.firstn n ms) (ns ++ List.firstn n ms)).
      { rewrite List.rev_app_distr, rev_record_fctx.
        apply Decl.per_tele_args_app_intro; [ rewrite List.length_rev; exact Hlns | exact Hgp | exact Hgf ]. }
      assert (HMss : List.Forall (exp_scoped (List.length Γ)) (Ns ++ List.firstn n Ms)).
      { apply List.Forall_app; split; [ exact (typed_insts_scoped _ _ _ Hass Hn HNt) |].
        apply Forall_firstn'; unfold Ms; apply List.Forall_map, List.Forall_forall; intros [g0 M0] Hin.
        destruct (List.In_nth_error _ _ Hin) as [j0 Hj0].
        destruct (nth_error_lt_some' (record_fields R) j0) as [[g1 U1] Hj1];
          [ rewrite <- Hlf; exact (nth_error_lt_length _ _ _ Hj0) |].
        assert (g1 = g0) as ->.
        { pose proof (List.map_nth_error fst _ _ Hj0) as E1; pose proof (List.map_nth_error fst _ _ Hj1) as E2.
          rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
        exact (wf_exp_scoped_term _ _ _ _ _ (HMt _ _ _ _ Hj0 Hj1)). }
      destruct (field_inst_link R Hass Hsu HFv HTv HPr HFk Γ n f U (Ns ++ List.firstn n Ms) RΓ ρ (ns ++ List.firstn n ms)
                  Hfk HΓs HRΓ ltac:(unfold Ms; rewrite List.length_app, List.length_firstn, List.length_map; lia)
                  ltac:(eapply tuple_insts; try eassumption; lia) HMss Hρ
                  ltac:(unfold Ms; rewrite !List.length_app, !List.length_firstn, List.length_map; lia) Hgms
                  ltac:(intros j1 N1 m1 HN1 Hm1;
                        exact (tuple_prefix_vals_sorted R Ns ns Ms ρ ms n Ens Ems
                                 ltac:(unfold Ms; rewrite List.length_map; lia) j1 N1 m1 HN1 Hm1)))
        as (j0 & t & u & Et & Eu & Htu).
      assert (t = ak) as -> by (eapply functional_eval_exp; eassumption).
      (** The field's value is the term's at its kind, which is its type's. *)
      assert (Hkak : domain_kind ak = record_field_kind R n).
      { destruct Htu as [Rtu HRtu]; rewrite (per_univ_elem_kind _ _ _ _ HRtu).
        pose proof (record_fctx_sem R HFv n ltac:(lia)) as HC0.
        destruct (rel_ctx_wf_per_ctx_env HC0) as [RC HRC].
        assert (Hlz : List.length (ns ++ List.firstn n ms) = List.length (record_fctx R n ++ record_params R)).
        { rewrite !List.length_app, List.length_firstn, length_record_fctx by lia; lia. }
        pose proof (Completeness.Inductives.Model.tele_args_env_rel (record_fctx R n ++ record_params R) RC
                      (ns ++ List.firstn n ms) (ns ++ List.firstn n ms) nil nil HRC HC0 Hlz Hgms) as HE0.
        rewrite <- (List.app_nil_r (record_fctx R n ++ record_params R)) in HRC.
        exact (field_type_kind R Hass Hsu HFv HTv HFk ⋅ n f U RC _ _ u Hfk ltac:(constructor) HRC HE0 Eu). }
      assert (mk = r) as ->.
      { pose proof (HFk n) as Hfkn; unfold glu_term_value in Emk; rewrite Hkak in Emk.
        unfold record_field_kind in *.
        destruct (List.nth n (record_field_kinds R) ak_relevant) eqn:Erk; inversion Hfkn.
        - eapply functional_eval_exp; [ exact Emk | apply Hev; constructor ].
        - rewrite Emk; symmetry; apply Hpv; reflexivity. }
      pose proof (record_fields_env_closed R ns (List.firstn n ms) Hlns) as Efe.
      rewrite List.length_firstn, Nat.min_l in Efe by lia; rewrite <- Efe in Eu.
      (** The field's type at the type's parameters [ns0], related to [u],
          at [ns]: the two record types are related *)
      destruct (HeT0 n f U (List.firstn n ms) Hfk Hpre) as [u0 Eu0].
      pose proof (HgF0 n f U (List.firstn n ms) u0 Hfk Hpre Eu0) as Hgu.
      destruct (Hev21 n f U _ _ Hfk Hpre21) as [u1 u0' Eu1 Eu0' Hu10].
      assert (u1 = u) as -> by (eapply functional_eval_exp; eassumption).
      assert (u0' = u0) as -> by (eapply functional_eval_exp; eassumption).
      assert (Hak0 : Dom ak ≈ u0 ∈ per_univ (Nat.max j0 i)).
      { destruct Htu as [Rt HRt].
        pose proof (per_univ_elem_cumu_ge j0 (Nat.max j0 i) _ _ _ ltac:(lia) HRt) as Hc1.
        pose proof (per_univ_elem_cumu_ge i (Nat.max j0 i) _ _ _ ltac:(lia) Hu10) as Hc2.
        exact (per_univ_trans' _ _ _ _ _ (ex_intro _ Rt Hc1) (ex_intro _ (canon_fields_rel R ns n (List.firstn n ms)) Hc2)). }
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
        [ exact Hak0 | exact Hgk | exact Hgu | exact HMk | exact HFPk ]. }
    refine (mk_record_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ Hm (List.map (fun N => N[σ]) Ns) HTat ms Hvs _); [ mauto 3 |].
    intros Δ' φ Ns' Hφ HNs' k f U r Hfk Hr.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hk].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hk) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    pose proof (HGf (S k) k f M U r ltac:(lia) Hk Hfk Hr) as HGk.
    destruct (HeT0 k f U (List.firstn k ms) Hfk (record_projs_prefix_diag _ _ _ _ k HrelM Hvs ltac:(lia))) as [u Eu].
    pose proof (HgF0 k f U (List.firstn k ms) u Hfk (record_projs_prefix_diag _ _ _ _ k HrelM Hvs ltac:(lia)) Eu) as Hgu.
    (* the projection is the field, at the field's type at the projections *)
    destruct (tuple_proj_eq _ _ _ _ _ _ _ _ _ Ht HTeq Hrt Hl Hn HNt Hfs HMt k f M U Hk Hfk) as [HUU HPM].
    assert (HUUσ : Δ ⊢ U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))][σ]
                     ≈ U[sb_of_list Id (Ns ++ List.firstn k Ms)][σ]
                     : (abs_kind_sort (record_field_kind R k) (record_sort R)[sb_of_list Id Ns])[σ]) by mauto 3.
    rewrite abs_kind_sort_sub in HUUσ.
    assert (HPMσ : Δ ⊢ (a_proj f (a_tuple T fs))[σ] ≈ M[σ] : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))][σ])
      by mauto 3.
    change ((a_proj f (a_tuple T fs))[σ]) with (a_proj f (a_tuple T fs)[σ]) in HPMσ.
    rewrite (record_sort_sub _ _ _ Hc Hn) in HUUσ.
    rewrite (record_field_sub R k f U Ns (record_pre R k (a_tuple T fs)) σ Hc Hfk Hn ltac:(apply length_record_pre; lia)),
      record_pre_sub in HUUσ, HPMσ.
    rewrite (record_field_sub R k f U Ns (List.firstn k Ms) σ Hc Hfk Hn ltac:(unfold Ms; rewrite List.length_firstn, List.length_map; lia)),
      <- List.firstn_map in HUUσ.
    pose proof (Hkind k f U u Hfk Eu) as Hku.
    assert (HUUi : Δ ⊢ U[sb_of_list Id (List.map (fun N => N[σ]) Ns ++ record_pre R k (a_tuple T fs)[σ])]
                     ≈ U[sb_of_list Id (List.map (fun N => N[σ]) Ns ++ List.firstn k (List.map (fun N => N[σ]) Ms))]
                     : abs_kind_sort (domain_kind u) Typeω@(large_level i)).
    { rewrite Hku; pose proof (HFk k) as Hfkk; revert HUUσ.
      destruct (record_field_kind R k); inversion Hfkk; cbn [abs_kind_sort]; intros HUUσ;
        first [ exact (wf_exp_eq_subtyp' _ _ _ _ _ _ _ HUUσ Hsort1) | exact HUUσ ]. }
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
    rewrite Hku.
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
    pose proof HF as [L1 L2 HFg].
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
      destruct (tele_insts_nth _ _ _ _ _ HT0) as (κ1 & A1 & HA1 & ->).
      rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA1
        by (rewrite Completeness.Records.Model.length_field_tele; lia).
      destruct (Completeness.Records.Model.field_tele_nth _ _ _ _ HA1) as (f1 & Hf1 & _).
      rewrite Hfk in Hf1; injection Hf1 as _ <-.
      rewrite <- sb_of_list_app in HM; exact HM. }
    constructor; [ rewrite length_record_pre, length_record_fctx by lia; reflexivity | rewrite length_record_fctx by lia; exact L2 |].
    intros k M U' v κ A HM HT Hv HA.
    rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA
      by (rewrite Completeness.Records.Model.length_field_tele; lia).
    destruct (Completeness.Records.Model.field_tele_nth _ _ _ _ HA) as (f & Hf & Hκ).
    assert (Hkn : k < n) by exact (nth_error_lt_length _ _ _ Hf).
    destruct (nth_error_lt_some' fs k ltac:(lia)) as [[g Mk] Hk].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hk) as E1; pose proof (List.map_nth_error fst _ _ Hf) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    unfold record_pre in HM; rewrite List.firstn_all2 in HM by lia.
    rewrite List.nth_error_map, Hf in HM; cbn in HM; injection HM as <-.
    destruct (tele_insts_nth _ _ _ _ _ HT) as (κ1 & A1 & HA1 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2 in HA1
      by (rewrite Completeness.Records.Model.length_field_tele; lia).
    rewrite HA in HA1; injection HA1 as <- <-.
    rewrite <- sb_of_list_app.
    replace (List.firstn k (record_pre R n (a_tuple T fs))) with (record_pre R k (a_tuple T fs))
      by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
    (** The field's own gluing. *)
    destruct (nth_error_lt_some' (tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs)) k) as [T0 HT0].
    { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx, List.length_map by lia; lia. }
    assert (HA0 : List.nth_error (List.rev (record_fctx R n)) k = Some (ce_ass κ A)).
    { rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2
        by (rewrite Completeness.Records.Model.length_field_tele; lia); exact HA. }
    pose proof (HFg k Mk T0 v κ A ltac:(rewrite List.nth_error_map, Hk; reflexivity) HT0 Hv HA0) as [lv a P El Ea Hga HP HMg].
    destruct (tele_insts_nth _ _ _ _ _ HT0) as (κ1 & A1 & HA1 & ->).
    rewrite HA0 in HA1; injection HA1 as <- <-.
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
    (** The two types are equal at the field's kind, at a universe. *)
    assert (HUUj : exists j : nat, Δ ⊢ A[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))]
                     ≈ A[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : abs_kind_sort κ Typeω@j).
    { subst κ; pose proof (HFk k) as Hfkk; revert HUU.
      destruct (record_field_kind R k); inversion Hfkk; cbn [abs_kind_sort]; intros HUU;
        first [ exact (wf_exp_eq_is_univ_large HSs HUU) | exists 0; exact HUU ]. }
    destruct HUUj as [j HUUj].
    (** The field's type's value is of the field's kind. *)
    assert (Hka : domain_kind a = κ).
    { destruct (presup_exp_eq HUUj) as (_ & _ & HAr & _).
      exact (proj1 (glu_univ_elem_typ_kind _ _ _ _ _ _ _ _ Hga HP HAr)). }
    set (nn := Nat.max (large_level lv) j).
    assert (Hle : universe_index_le lv (ul nn)) by (apply universe_index_le_ul_max; unfold nn; lia).
    destruct (glu_univ_elem_cumu_ge_universe_index Hle Hga) as (Pn & Eln & Hgn).
    pose proof (glu_univ_elem_typ_cumu_ge_universe_index Hle Hga Hgn HP) as HPn.
    pose proof (glu_univ_elem_exp_cumu_ge_universe_index Hle Hga Hgn HMg) as HMn.
    assert (Hjn : j <= nn) by (unfold nn; lia).
    pose proof (lift_kind_sort_eq_ge Hjn HUUj) as HUUn.
    rewrite <- Hka in HUUn.
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
      glu_args Δ (record_fctx R (List.length (record_fields R))) (sb_of_list Id Ns) (env_tele nil (List.rev (record_params R)) ns)
        (record_pre R (List.length (record_fields R)) M) ms ->
      Δ ⊢ M : W ® m ∈ El.
  Proof.
    intros * Hglu HW HM HNs Hm Hvs HF.
    assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
    assert (Hid : Δ ⊢ᵏ wk_id : Δ) by mauto 3.
    destruct (glu_args_length _ _ _ _ _ _ HNs) as [LN LNv].
    pose proof (glu_args_per_tele_args _ _ _ _ _ _ Hass HNs) as Hgp.
    invert_glu_univ_elem Hglu.
    match goal with H : record_lookup _ _ p = Some ?R0 |- _ => assert_fails constr_eq R0 R; rewrite Hl in H; injection H as <- end.
    match goal with H0 : per_univ_elem _ _ (d_record p ns) (d_record p ns) |- _ => rename H0 into Hper end.
    match goal with H : forall k f T vs b, _ -> _ -> _ -> glu_univ_elem _ _ _ _ |- _ => rename H into HgF0 end.
    match goal with H : forall k f T vs, _ -> _ -> exists b, _ |- _ => rename H into HeT0 end.
    match goal with H : _ <∙> record_glu_typ_pred _ _ _ _ _ _ |- _ => rename H into HPP end.
    match goal with HEl : _ <∙> record_glu_exp_pred _ _ _ _ _ _ _ |- _ => apply HEl end.
    destruct (per_univ_elem_record_facts _ _ _ _ _ _ Hl Hper) as [_ _ _ Htop _ _ _ _ HE].
    pose proof (record_projs_length _ _ _ Hvs) as Lw.
    (** The type, at the given parameters. *)
    destruct (proj1 (HPP _ _) HW) as [Ns0 HNs0].
    assert (HTat : record_typ_at p R ns FP FEl Typeω@(large_level i) Δ W Ns).
    { eapply record_typ_at_params_change;
        [ exact Hl | intros n0; destruct (Htop n0) as [Cs ? HCs _ _]; exists Cs; exact HCs | | exact HNs0 ].
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
    assert (HGf : forall n0 k f U r, k < n0 -> List.nth_error (record_fields R) k = Some (f, U) -> List.nth_error ms k = Some r ->
               Δ ⊢ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] ® r ∈ FEl k (List.firstn k ms)).
    { induction n0 as [| n0 IH]; intros k f U r Hkn Hfk Hr; [ lia |].
      destruct (Nat.lt_ge_cases k n0) as [Hkn' | Hkn']; [ exact (IH _ _ _ _ Hkn' Hfk Hr) |].
      assert (k = n0) as -> by lia; clear Hkn Hkn'.
      assert (Hlt : n0 < n) by exact (nth_error_lt_length _ _ _ Hfk).
      pose proof HF as [L1 L2 HFg].
      assert (HM0 : List.nth_error (record_pre R n M) n0 = Some (a_proj f M))
        by (unfold record_pre; rewrite List.firstn_all2 by lia; rewrite List.nth_error_map, Hfk; reflexivity).
      assert (HA0 : List.nth_error (List.rev (record_fctx R n)) n0 = Some (ce_ass (record_field_kind R n0) U)).
      { rewrite Completeness.Records.Model.rev_record_fctx, List.firstn_all2
          by (rewrite Completeness.Records.Model.length_field_tele; lia).
        exact (Completeness.Records.Model.field_tele_nth_of _ _ _ _ Hfk). }
      destruct (nth_error_lt_some' (tele_insts (record_fctx R n) (sb_of_list Id Ns) (record_pre R n M)) n0) as [T0 HT0].
      { rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx, length_record_pre by lia; lia. }
      pose proof (HFg _ _ _ _ _ _ HM0 HT0 Hr HA0) as [j' a P' El' Ea Hg' HP' HM'].
      destruct (tele_insts_nth _ _ _ _ _ HT0) as (κ1 & A1 & HA1 & ->).
      rewrite HA0 in HA1; injection HA1 as <- <-.
      rewrite <- sb_of_list_app in HP', HM'.
      replace (List.firstn n0 (record_pre R n M)) with (record_pre R n0 M) in HP', HM'
        by (unfold record_pre; rewrite List.firstn_map, List.firstn_firstn, Nat.min_l by lia; reflexivity).
      pose proof (record_projs_prefix_diag _ _ _ _ n0 Hm Hvs ltac:(lia)) as Hpre.
      rewrite <- (record_fields_env_tele R ns (List.firstn n0 ms) n) in Ea by (rewrite ?List.length_firstn; lia).
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
    pose proof (HGf (S k) k f U r ltac:(lia) Hfk Hr) as HGk.
    pose proof (record_projs_prefix_diag _ _ _ _ k Hm Hvs ltac:(lia)) as Hpre.
    destruct (HeT0 k f U (List.firstn k ms) Hfk Hpre) as [u Eu].
    pose proof (HgF0 k f U (List.firstn k ms) u Hfk Hpre Eu) as Hgu.
    pose proof (record_field_type_kind ns (List.firstn k ms) k f U u Hgp ltac:(lia) Hpre
                  ltac:(rewrite List.length_firstn; lia) Hfk Eu) as Hku.
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
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    assert (Hrt' : Δ' ⊢ a_record p : record_ty R)
      by exact (record_typed_former _ _ _ _ _ (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl) Hl HΔ').
    rewrite Hku.
    eapply record_field_params_cong;
      [ exact Htφ | exact Hrt' | exact Hl | exact (params_glu_len _ _ _ _ Htop2) | rewrite <- HlN; exact (params_glu_len _ _ _ _ Htop2)
      | exact (params_glu_typ _ _ _ _ Htop2) | exact HNN | exact Hsort2 | exact Hfk ].
  Qed.

End RecordAt.

End Fixed_GCtx.
