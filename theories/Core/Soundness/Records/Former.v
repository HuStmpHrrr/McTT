(** * The Type Former of a Record in the Gluing Model

    A record found in a well-formed global context is typed there, so
    valid in the PER model ([record_model_at]); [Core/Completeness/Records/Model.v]
    then gives the values of its type former and its fields' types.  At a
    declaration whose judgments are glued ([glu_record_decl]), the type
    former at glued parameters is glued at the sort
    ([record_former_base]), and the type former is glued at its type
    ([glu_rel_exp_record0]); the fields over the parameters are a context
    glued with its types ([record_fctx_glued]).  The projections and the
    tuples are in [Records/Model.v]. *)

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
  Instances
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args.
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
Lemma glu_args_params_glu_top : forall C Δ Ms vs, all_assumptions C -> ctx_scoped 0 C ->
    glu_args Δ C Id nil Ms vs -> params_glu_top C Δ Ms vs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  constructor; [ exact L1 | |].
  - intros k M T HM HT.
    assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & He).
    destruct (H _ _ _ _ _ _ HM HT Hv He) as [i a P El _ Hglu _ HMg].
    eapply glu_univ_elem_trm_escape; eassumption.
  - intros Δ' φ Rs Hφ HRs.
    destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
    apply glu_nfs_eq_at_of_nth; [ rewrite List.length_map, HRl; congruence | |].
    + intros k X Y T HX HY HT.
      rewrite List.nth_error_map in HX.
      destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
      rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
      destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
      assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
      destruct (glu_args_ass_nth _ _ Hass Hk) as (κ & A & He).
      destruct (HRn _ _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
      rewrite HY' in HY; injection HY as <-.
      destruct (H _ _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
      exact (Hrb _ _ _ Hφ HV).
    + intros k X HX.
      apply nth_error_lt_some.
      rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.length_map, length_tele_insts by exact Hass.
      assert (HXk : k < List.length (List.map (fun P => P[φ]ʷ) Ms)) by (apply List.nth_error_Some; congruence).
      rewrite List.length_map in HXk; lia.
Qed.

(** ** The Type Former at its Model *)

Section RecordFormer.
  Variables (p : qname) (R : record_decl).
  Hypothesis (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) (Hl : record_lookup gc_deps gc_stack p = Some R).

  (** What the model asks of the record, and its parts. *)
  Let Hmodel := record_model_at p R Hg Hl.
  Let Hc := model_closed _ _ Hmodel.
  Let Hass := model_params_ass _ _ Hmodel.
  Let Hsu := model_sort _ _ Hmodel.
  Let HFk := fields_kind_valid _ (model_valid _ _ Hmodel).

  (** The fields' environment at the values of the first fields: the
      parameters' telescope, then the fields'. *)
  Lemma record_fields_env_tele : forall ns vs k, List.length ns = List.length (record_params R) ->
      List.length vs <= k -> k <= List.length (record_fields R) ->
      record_fields_env R ns vs = env_tele (env_tele nil (List.rev (record_params R)) ns) (List.rev (record_fctx R k)) vs.
  Proof.
    intros * Hlns Hlvs Hk.
    rewrite (record_fields_env_closed R ns vs Hlns), List.rev_app_distr, env_tele_app by (rewrite List.length_rev; exact Hlns).
    rewrite !rev_record_fctx, (env_tele_firstn _ (List.firstn (List.length vs) _)),
      (env_tele_firstn _ (List.firstn k _)), !List.firstn_firstn, !Nat.min_l by lia.
    reflexivity.
  Qed.

  Section Former.
    Hypothesis (HG : glu_record_decl R).
    Variable (i0 : nat).
    Hypothesis (Hty : ⋅ ⊢ record_ty R : Typeω@i0).

    (** The declaration, typed where it is found. *)
    Let Ht := record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl.

    (** The type former, in every context. *)
    Lemma record_former_wf : forall Δ, ⊢ Δ -> Δ ⊢ a_record p : record_ty R.
    Proof.
      intros Δ HΔ; exact (record_typed_former _ _ _ _ _ Ht Hl HΔ).
    Qed.

    (** Arguments glued along the parameters: a glued substitution. *)
    Lemma record_params_glu_sub : forall Δ Ms vs Sb, ⊢ Δ -> EG record_params R ∈ glu_ctx_env ↘ Sb ->
        glu_args Δ (record_params R) Id nil Ms vs -> Δ ⊢ˢ sb_of_list Id Ms ® env_tele nil (List.rev (record_params R)) vs ∈ Sb.
    Proof.
      intros * HΔ HSb Hgs.
      eapply glu_sub_of_list with (C := record_params R) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact Hass | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | exact Hg ]
        | cbn; apply wf_sub_nil'; exact HΔ | exact Hgs ].
    Qed.

    (** The sort at glued parameters is below the universe it denotes. *)
    Lemma record_sort_le : forall Δ Ms vs b, ⊢ Δ -> glu_args Δ (record_params R) Id nil Ms vs ->
        ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) vs ↘ b ->
        Δ ⊢ (record_sort R)[sb_of_list Id Ms] ⊆ Typeω@(large_level (Completeness.Inductives.Decl.univ_idx b)).
    Proof.
      intros * HΔ Hgs Hb.
      destruct (glued_sort _ HG) as [[j Heq] | (L & n & Heq & HL)]; rewrite Heq in Hb |- *; inversion Hb; subst;
        cbn [Completeness.Inductives.Decl.univ_idx large_level exp_sub].
      - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
      - apply glu_rel_exp_of_under_sub in HL.
        pose proof HL as [SbP HSbP _ _].
        pose proof (record_params_glu_sub _ _ _ _ HΔ HSbP Hgs) as Hσ.
        destruct (glu_rel_exp_level_elim HSbP HL _ _ _ Hσ) as (m & Hm & Hmm & Hglul).
        assert (Htl : Δ ⊢ L[sb_of_list Id Ms] : Level@n)
          by (eapply glu_lvl_escape; [ exact (per_lvl_at_lvl _ _ _ Hmm) | exact Hglul | exact HΔ ]).
        eapply wf_subtyp_small_large; eassumption.
    Qed.

    (** A type over the parameters and a prefix [Pre], at the sort shifted
        past [Pre], glued at a glued substitution: its value is glued at the
        universe the sort denotes at the parameters' values. *)
    Lemma record_sort_typ_glued : forall Pre A Sb Δ σ vs zs bu κ, ⊢ Pre ++ record_params R -> List.length zs = List.length Pre ->
        List.length vs = List.length (record_params R) ->
        ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) vs ↘ bu -> field_kind κ ->
        EG Pre ++ record_params R ∈ glu_ctx_env ↘ Sb ->
        Pre ++ record_params R ⊩ A : abs_kind_sort κ (record_sort R)[wk_shiftn (List.length Pre)]ʷ ->
        Δ ⊢ˢ σ ® env_tele nil (List.rev (Pre ++ record_params R)) (vs ++ zs) ∈ Sb ->
        exists a, ⟦ A ⟧ env_tele nil (List.rev (Pre ++ record_params R)) (vs ++ zs) ↘ a /\ Dom a ≈ a ∈ per_univ (Completeness.Inductives.Decl.univ_idx bu) /\
          forall P El, DG a ∈ glu_univ_elem (Completeness.Inductives.Decl.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
    Proof.
      intros * HPre Hzs Hlvs Hbu Hκ HSb HA Hσ.
      (** A proposition: a type of every index. *)
      destruct κ; inversion Hκ; cbn [abs_kind_sort] in HA.
      2:{ destruct (glu_rel_exp_prop_inversion HSb HA _ _ _ Hσ) as (a & Ha & Hpa & HP).
          exists a; split; [ exact Ha | split; [ eexists; exact (per_univ_elem_of_prop _ _ _ Hpa) |] ].
          intros P El Hglu; destruct (glu_univ_elem_prop_inv _ _ _ _ Hpa Hglu) as [HPe _]; apply HPe; exact HP. }
      destruct (wf_is_univ_typ (typed_sort _ _ _ Ht)) as [iS HS].
      destruct Hsu as [[j Heq] | [t Heq]]; rewrite Heq in HA, HS, Hbu; cbn [exp_wk] in HA.
      - destruct (glu_rel_exp_of_univ_inversion (u := ul j) HSb HA _ _ _ Hσ) as (_ & a & Ha & Hpa & HP & _).
        inversion Hbu; subst; cbn [Completeness.Inductives.Decl.univ_idx].
        exists a; split; [ exact Ha | split; [ exact Hpa | exact HP ] ].
      - destruct (glu_rel_exp_of_suniv_tm_inversion' HSb HA _ _ _ Hσ) as (l & Hlv & _ & _ & a & Ha & Hpa & HP & _).
        exists a; split; [ exact Ha |].
        assert (Hidx : Completeness.Inductives.Decl.univ_idx bu = us (domain_level_real l)).
        { assert (HCs : ⊨ Pre ++ record_params R) by (apply completeness_fundamental_ctx; exact HPre).
          assert (HSs : record_params R ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
          destruct (rel_ctx_wf_per_ctx_env HCs) as [RC HRC].
          pose proof (glu_ctx_env_per_env HSb HRC Hσ) as HE.
          assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length Pre)]ʷ ⟧ env_tele nil (List.rev (Pre ++ record_params R)) (vs ++ zs) ↘ d_suniv l)
            by (cbn [exp_wk]; econstructor; exact Hlv).
          assert (Hlvs' : List.length vs = List.length (List.rev (record_params R))) by (rewrite List.length_rev; exact Hlvs).
          assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length Pre)⟫ (env_tele nil (List.rev (Pre ++ record_params R)) (vs ++ zs)) ↘ bu)
            by (rewrite List.rev_app_distr, env_tele_app, <- Hzs, Completeness.Inductives.Decl.eval_wk_shiftn_env_tele by exact Hlvs';
                exact Hbu).
          pose proof (Completeness.Inductives.Decl.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HRC HE Eb Ea ltac:(right; eauto)) as Hi.
          rewrite Hi; reflexivity. }
        rewrite Hidx; split; [ exact Hpa | exact HP ].
    Qed.

    (** The fields at glued parameters are glued at the families of the
        clause of [d_record] at the universe the sort denotes. *)
    Lemma record_fields_glu_of_args : forall Δ Ns vs b (u : universe_index) FP FEl, ⊢ Δ ->
        glu_args Δ (record_params R) Id nil Ns vs -> ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) vs ↘ b ->
        universe_index_le (Completeness.Inductives.Decl.univ_idx b) u ->
        (forall k f T ws, List.nth_error (record_fields R) k = Some (f, T) ->
           tele_prefix_rel (canon_fields_rel R vs) k ws ws -> exists c, ⟦ T ⟧ record_fields_env R vs ws ↘ c) ->
        (forall k f T ws c, List.nth_error (record_fields R) k = Some (f, T) ->
           tele_prefix_rel (canon_fields_rel R vs) k ws ws -> ⟦ T ⟧ record_fields_env R vs ws ↘ c ->
           DG c ∈ glu_univ_elem u ↘ FP k ws ↘ FEl k ws) ->
        record_fields_glu R vs FP FEl Δ Ns.
    Proof.
      intros * HΔ HNs Hb Hub HeT HgF k f T Mfs mfs Hk HMl Hml HMs Hp.
      pose proof (glu_rel_exp_of_under_sub (glued_fields _ HG _ _ _ Hk)) as HTk; pose proof HTk as [Sbk HSbk _ _].
      assert (Hlk : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
      pose proof (record_fctx_params_ass R k Hass) as HassC.
      pose proof (record_typed_fctx_wf _ _ _ Ht k ltac:(lia)) as HCk.
      pose proof (length_record_fctx R k ltac:(lia)) as HlenF.
      destruct (glu_args_length _ _ _ _ _ _ HNs) as [LN Lv].
      assert (Hσ : Δ ⊢ˢ sb_of_list Id (Ns ++ Mfs) ® env_tele nil (List.rev (record_fctx R k ++ record_params R)) (vs ++ mfs) ∈ Sbk).
      { eapply glu_sub_of_list with (C := record_fctx R k ++ record_params R) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
          [ exact HassC | rewrite List.app_nil_r; exact HSbk | econstructor; [ reflexivity | exact Hg ]
          | cbn; apply wf_sub_nil'; exact HΔ |].
        apply glu_args_app; [ exact Hass | exact LN | exact Lv |].
        split; [ exact HNs |].
        constructor; [ lia | lia |].
        intros j M T' v κ A HM HT' Hv HA.
        assert (Hj : j < k) by (pose proof (nth_error_lt_length _ _ _ HM); lia).
        destruct (tele_insts_nth _ _ _ _ _ HT') as (κ0 & A0 & HA0 & ->).
        rewrite HA in HA0; injection HA0 as <- <-.
        rewrite rev_record_fctx, nth_error_firstn_lt in HA by exact Hj.
        destruct (field_tele_nth _ _ _ _ HA) as (g & Hj' & _).
        pose proof (tele_prefix_rel_of_pre _ _ _ _ j Hp ltac:(lia)) as Hpj.
        destruct (HeT j g A (List.firstn j mfs) Hj' Hpj) as [c Ec].
        pose proof (HgF _ _ _ _ _ Hj' Hpj Ec) as Hgc.
        pose proof (HMs j g A M v Hj' HM Hv) as HMg.
        rewrite <- sb_of_list_app.
        apply (mk_glu_arg _ _ _ _ _ _ u c (FP j (List.firstn j mfs)) (FEl j (List.firstn j mfs)));
          [ rewrite <- (record_fields_env_tele vs (List.firstn j mfs) k) by (rewrite ?List.length_firstn; lia); exact Ec
          | exact Hgc | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ]. }
      destruct (record_sort_typ_glued (record_fctx R k) T Sbk Δ _ vs mfs b _ HCk ltac:(lia) Lv Hb (HFk k) HSbk
                  ltac:(rewrite HlenF; exact HTk) Hσ) as (a & Ha & Hpa & HP).
      destruct (per_univ_glu_univ_elem _ _ Hpa) as (P0 & El0 & Hg0).
      pose proof (record_fields_env_closed R vs mfs Lv) as Efe; rewrite Hml in Efe; rewrite <- Efe in Ha.
      exact (glu_univ_elem_typ_cumu_ge_universe_index Hub Hg0 (HgF _ _ _ _ _ Hk Hp Ha) (HP _ _ Hg0)).
    Qed.

    (** The type former applied to glued parameters is glued at the sort
        at them. *)
    Lemma record_former_base : forall Δ Ms vs (i : nat) b P El, ⊢ Δ ->
        glu_args Δ (record_params R) Id nil Ms vs ->
        ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
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
      apply HRb' in Hdrec; destruct Hdrec as [[R' HR'] _].
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
        apply glu_rel_exp_of_under_sub in HL.
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
          match goal with HR : Rps vs at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Rs |- _ =>
            destruct (HMr _ _ _ Hφ HR) as [HRl HRs] end.
          unfold glu_nf_eq; cbn [nf_annotate_proofs].
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
        ⟦ record_sort R ⟧ env_tele nil (List.rev (record_params R)) vs ↘ b -> universe_index_le (Completeness.Inductives.Decl.univ_idx b) i ->
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
      destruct (Completeness.ContextCases.rel_type_kind_of_typ (completeness_fundamental_exp _ _ _ Hty) _ Henv _ _ Hnil)
        as (a0 & Ea0 & Hk0).
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & [Hp | (m1 & m2 & Hm1 & Hm2 & Hmm)]).
      { (* the type of a type former is relevant *)
        assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption); congruence. }
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

    (** The sort is a valid entry over the parameters at any index it is a
        type of: a large universe, or a small one at the glued level
        ([glued_sort]). *)
    Lemma record_sort_entry_valid : forall (i : nat), record_params R ++ ⋅ ⊢ record_sort R : Typeω@i ->
        glu_entry_valid_at i (record_params R ++ ⋅) ak_relevant (record_sort R).
    Proof.
      intros * HT.
      apply glu_entry_valid_of_rel.
      pose proof (glu_rel_ctx_types_ctx _ (glued_params _ HG)) as HΓ.
      rewrite List.app_nil_r in HT |- *.
      destruct (glued_sort _ HG) as [[j Heq] | (L & n & Heq & HL)]; rewrite Heq in HT |- *.
      - eapply glu_rel_exp_subtyp; [ exact (glu_rel_exp_typ HΓ) | exact (glu_rel_exp_typ HΓ) | constructor | exact (wf_typ_inversion HT) ].
      - apply glu_rel_exp_of_under_sub in HL.
        eapply glu_rel_exp_subtyp; [ eapply glu_rel_exp_univ_lvl; exact HL | exact (glu_rel_exp_typ HΓ) | constructor
                                   | exact (wf_univ_inversion HT) ].
    Qed.

    (** The type former is glued at its type. *)
    Lemma glu_rel_exp_record0 : ⋅ ⊩ a_record p : record_ty R.
    Proof.
      destruct (glu_rel_ctx_types_ctx _ (glued_params _ HG)) as [SbP HSbP].
      assert (HSbP0 : EG record_params R ++ ⋅ ∈ glu_ctx_env ↘ SbP) by (rewrite List.app_nil_r; exact HSbP).
      destruct (glu_ctx_env_entries_valid _ _ _ Hass HSbP0 i0) as (i & Hji & HAents).
      assert (Hi : ⋅ ⊢ record_ty R : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hty ]).
      eapply (glu_closed_const _ _ i (d_record p nil));
        [ reflexivity | intros; apply record_ty_sub, Hc | exact Hi | intros; constructor |].
      intros Δ σ Hσ ρ a P El Ha Hglu.
      assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
      pose proof Hi as Hi'; unfold record_ty in Hi'.
      destruct (ctx_pi_split_typed _ _ _ _ Hass Hi') as [HCs _].
      unfold record_ty in Ha |- *.
      replace (ctx_pi (record_params R) (record_sort R)) with ((ctx_pi (record_params R) (record_sort R))[σ])
        by (change (ctx_pi (record_params R) (record_sort R)) with (record_ty R); apply record_ty_sub, Hc).
      change (a_record p) with (apps_exp (a_record p) nil).
      eapply (ctx_pi_glu_elem_by_closed (fun xs w => w = d_record p xs) (a_record p) (record_params R ++ ⋅)) with (Sb := SbP);
        [ reflexivity | | exact Hass | exact Hg | exact HSbP0
        | exists nil; reflexivity
        | intros; eapply HAents; eassumption
        | intros; eapply HCs; eassumption
        | exact (record_sort_entry_valid i (HCs nil _ eq_refl))
        | exact Hσ | reflexivity | | | | exact Ha | exact Hglu ].
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
        rewrite List.app_nil_r in Hb.
        exact (record_former_base _ _ _ _ _ _ _ HΔ' Hgs Hb Hglub HPb).
    Qed.

  End Former.

End RecordFormer.

(** ** The Fields' Context, Glued

    At a glued declaration, the fields over the parameters are a context
    glued with its types, field by field: each is a type of the sort of
    its kind next to the record's sort glued at its instances
    ([glued_fields]).  A relevant field of a record whose sort is a small
    universe [Type⟨L⟩] is moved to [Typeω@0] at each instance, as a
    context entry is of a large universe, [Prop] or [LevelSort], the
    level being glued there. *)
Lemma record_fctx_glued : forall R, glu_record_decl R ->
    forall k, k <= List.length (record_fields R) -> glu_rel_ctx_types (record_fctx R k ++ record_params R).
Proof.
  intros R HG; induction k as [| k IH]; intros Hk.
  - change (record_fctx R 0) with (@nil centry); exact (glued_params _ HG).
  - destruct (nth_error_lt_some' (record_fields R) k ltac:(lia)) as [[f T] HfT].
    rewrite (record_fctx_succ R k f T HfT); cbn [List.app].
    pose proof (IH ltac:(lia)) as HΓ.
    pose proof (glued_fields _ HG k f T HfT) as HT.
    destruct (glued_sort _ HG) as [[i Hs] | (L & n & Hs & HL)]; rewrite Hs in HT; cbn [exp_wk] in HT.
    + exact (glu_rel_ctx_types_extend HT (sort_kind_abs_kind_sort _ _)).
    + destruct (record_field_kind R k) eqn:Hκ; cbn [abs_kind_sort] in HT.
      * (** A relevant field of a small universe: at [Typeω@0], at each
            instance. *)
        pose proof (wf_wk_shiftn_app' _ _ _ _ (presup_exp_ctx (glu_rel_exp_under_sub_wf HT))) as Hw.
        rewrite length_record_fctx in Hw by lia.
        pose proof (glu_rel_exp_under_sub_wk HL HΓ Hw) as HLw; cbn [exp_wk] in HLw.
        assert (HT0 : glu_rel_exp_under_sub (record_fctx R k ++ record_params R) T Typeω@0).
        { apply (glu_rel_exp_under_sub_conv_typ (A := Type⟨L[wk_shiftn k]ʷ⟩)); [| exact HT ].
          intros Γ' τ Hτ H; cbn [exp_sub] in *.
          pose proof (glu_rel_exp_under_sub_inst _ _ _ HLw _ _ Hτ) as HLτ; cbn [exp_sub] in HLτ.
          exact (glu_rel_exp_kind_sort_small_large (κ := ak_relevant) HLτ H). }
        exact (glu_rel_ctx_types_extend HT0 (sort_kind_universe _)).
      * exact (glu_rel_ctx_types_extend HT sort_kind_prop).
      * exact (glu_rel_ctx_types_extend HT sort_kind_level).
Qed.

End Fixed_GCtx.
