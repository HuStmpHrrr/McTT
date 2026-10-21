(** * The Telescopes and the Type Former of a Group in the Gluing Model

    The types of the telescopes of a group's members, at uniform
    parameters glued to [ups], are glued at the gluings of the clause of
    [d_ind] ([comps_of_uparams]); a declared member's type at glued
    parameters is then glued at its universe ([ind_typ_at_of_args]), and its
    type former at its type ([glu_rel_exp_ind0]).  The families of the
    clause are named by [ind_fams_glu]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model.
From Mctt.Core.Completeness.LogicalRelation Require Telescope Substitution.
From Mctt.Core.Completeness Require UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
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

(** ** The Families of a Group's Clause

    The gluings the clause of [d_ind] gives the types of the telescopes of
    the members of [D] at [ups], at the canonical relations, at the index
    [u]: the types evaluate, and their values are glued at the families. *)
Record ind_fams_glu (D : ind_decl) (ups : list domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred) : Prop :=
  mk_ind_fams_glu
  { ifg_npar_eval : forall m Mm j A vs, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b
  ; ifg_npar_glu : forall m Mm j A vs b, ind_member D m = Some Mm -> List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A) ->
      tele_prefix_rel (canon_nparams_rel D ups m) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
      DG b ∈ glu_univ_elem u ↘ NP m j vs ↘ NEl m j vs
  ; ifg_arg_eval : forall m Mm ms c gs j A vs, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
      tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b
  ; ifg_arg_glu : forall m Mm ms c gs j A vs b, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> List.nth_error (cargs_nonrec gs) j = Some A ->
      tele_prefix_rel (canon_args_rel D ups m ms c) j vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
      DG b ∈ glu_univ_elem u ↘ AP m ms c j vs ↘ AEl m ms c j vs
  ; ifg_dom_eval : forall m Mm ms c gs gs1 t gs2 ws j B ys, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) j = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
      exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b
  ; ifg_dom_glu : forall m Mm ms c gs gs1 t gs2 ws j B ys b, ind_member D m = Some Mm ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ms ms ->
      ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups m ms c) (List.length (cargs_nonrec gs1)) ws ws ->
      List.nth_error (ptyp_doms t) j = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ms ws (ptyp_doms t)) j ys ys ->
      ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
      DG b ∈ glu_univ_elem u ↘ DP m (ms ++ ws ++ ys) B ↘ DEl m (ms ++ ws ++ ys) B }.

(** ** The Components of an Inductive Type at Glued Parameters

    The types of the telescopes of a valid declaration, at uniform
    parameters glued to [ups], are glued at the gluings of the clause of
    [d_ind] at the index of the sort's universe. *)
Section Comps.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (Hass : grp_tele_ass D).
  Variable (ups : list domain) (bu : domain) (u : uidx)
    (NP : nat -> nat -> list domain -> glu_typ_pred) (NEl : nat -> nat -> list domain -> glu_exp_pred)
    (AP : nat -> list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : nat -> list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : nat -> list domain -> exp -> glu_typ_pred) (DEl : nat -> list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (Completeness.Inductives.Decl.univ_idx bu) u)
    (Hf : ind_fams_glu D ups u NP NEl AP AEl DP DEl).

  Let HeN := ifg_npar_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HNP := ifg_npar_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeA := ifg_arg_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HAP := ifg_arg_glu _ _ _ _ _ _ _ _ _ Hf.
  Let HeD := ifg_dom_eval _ _ _ _ _ _ _ _ _ Hf.
  Let HDP := ifg_dom_glu _ _ _ _ _ _ _ _ _ Hf.

  (** A type of a context ending in the uniform parameters at the sort's
      universe, glued at the sort's universe's index at uniform parameters
      [ups]. *)
  Lemma sort_typ_glued : forall Pre A Sb Δ σ zs, ⊢ Pre ++ ind_uparams D -> List.length zs = List.length Pre ->
      EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ Sb -> Pre ++ ind_uparams D ⊩ A : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      Δ ⊢ˢ σ ® env_args nil (ups ++ zs) ∈ Sb ->
      exists a, ⟦ A ⟧ env_args nil (ups ++ zs) ↘ a /\ Dom a ≈ a ∈ per_univ (Completeness.Inductives.Decl.univ_idx bu) /\
        forall P El, DG a ∈ glu_univ_elem (Completeness.Inductives.Decl.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
  Proof.
    intros * HPre Hzs HSb HA Hσ.
    pose proof (dt_sort _ _ _ Hdt) as [iS HS].
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in HA, HS, Hbu; cbn [exp_wk] in HA.
    - destruct (glu_rel_exp_of_univ_inversion (u := ul i0) HSb HA _ _ _ Hσ) as (_ & a & Ha & Hpa & HP & _).
      inversion Hbu; subst; cbn [Completeness.Inductives.Decl.univ_idx].
      exists a; split; [ exact Ha | split; [ exact Hpa | exact HP ] ].
    - destruct (glu_rel_exp_of_suniv_tm_inversion' HSb HA _ _ _ Hσ) as (l & Hlv & _ & _ & a & Ha & Hpa & HP & _).
      exists a; split; [ exact Ha |].
      assert (Hidx : Completeness.Inductives.Decl.univ_idx bu = us (dlvl_real l)).
      { assert (HCs : ⊨ Pre ++ ind_uparams D) by (apply completeness_fundamental_ctx; exact HPre).
        assert (HSs : ind_uparams D ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
        destruct (rel_ctx_wf_per_ctx_env HCs) as [R HR].
        pose proof (glu_ctx_env_per_env HSb HR Hσ) as HE.
        assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length Pre)]ʷ ⟧ env_args nil (ups ++ zs) ↘ d_suniv l) by (cbn [exp_wk]; econstructor; exact Hlv).
        assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length Pre)⟫ (env_args nil (ups ++ zs)) ↘ bu)
          by (rewrite env_args_app, <- Hzs, Completeness.UnitCases.eval_wk_shiftn_args; exact Hbu).
        pose proof (Completeness.Inductives.Decl.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HR HE Eb Ea ltac:(right; eauto)) as Hi.
        rewrite Hi; reflexivity. }
      rewrite Hidx; split; [ exact Hpa | exact HP ].
  Qed.

  Lemma nparams_prefix_ass' : forall m Mm k, ind_member D m = Some Mm -> tele_ass (nparams_prefix Mm k ++ ind_uparams D).
  Proof.
    intros * HM; destruct (nparams_prefix_suffix D Mm k) as [Δ HΔ].
    pose proof (decl_closed_params_ass D m Mm Hc HM) as H; rewrite HΔ in H.
    apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma nparams_prefix_wf : forall m Mm k, ind_member D m = Some Mm -> ⊢ nparams_prefix Mm k ++ ind_uparams D.
  Proof.
    intros * HM; destruct (nparams_prefix_suffix D Mm k) as [Δ HΔ].
    pose proof (member_params_wf _ _ _ _ _ Hdt HM) as H; rewrite HΔ in H; eapply ctx_app_wf_tail; exact H.
  Qed.

  Lemma nparams_nparams_prefix_split' : forall Mm k, exists Δ, im_nparams Mm = Δ ++ nparams_prefix Mm k.
  Proof.
    intros; exists (List.rev (List.skipn k (List.rev (im_nparams Mm)))).
    unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
  Qed.

  Lemma comps_npar : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm k Ns ns T, ind_member D m = Some Mm -> List.length ns = k -> k < im_nn Mm ->
        List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k = Some T ->
        (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
           List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T' ->
           List.nth_error ns j = Some n -> Δ ⊢ N : T' ® n ∈ NEl m j (List.firstn j ns)) ->
        tele_prefix_rel (canon_nparams_rel D ups m) k ns ns -> Δ ⊢ T ® NP m k ns.
  Proof.
    intros Δ Us HΔ HUs m Mm k Ns ns T HM Hlk Hk HT Hpre Hp.
    pose proof (dc_ass _ Hc) as HassU.
    pose proof (decl_closed_nparams_ass D Hc m Mm HM) as HassN0.
    assert (Hk' : k < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D m Mm k Hass HM Hk') as [A HA].
    pose proof (gid_npar _ HG m Mm k A HM HA) as HV.
    pose proof HV as [SbC HSbC _ _].
    pose proof (nparams_prefix_ass' m Mm k HM) as HassC.
    pose proof (length_nparams_prefix Mm k ltac:(lia)) as Hlpre.
    destruct (nparams_nparams_prefix_split' Mm k) as [Δy HΔy].
    assert (HassN : tele_ass (nparams_prefix Mm k)) by (unfold tele_ass in HassC; apply List.Forall_app in HassC as [H _]; exact H).
    assert (HlNs : k < List.length Ns).
    { assert (Hs : List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) k <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by exact HassN0; lia. }
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id (Us ++ List.firstn k Ns) ® env_args nil (ups ++ ns) ∈ SbC).
    { eapply glu_sub_of_list with (C := nparams_prefix Mm k ++ ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact HassC | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ |].
      apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs |].
      constructor; [ rewrite List.length_firstn; lia | lia |].
      intros j M T' v A' HM' HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlk; apply List.nth_error_Some; congruence).
      rewrite List.nth_error_firstn in HM'; destruct (Nat.ltb_spec j k); [| lia ].
      assert (HT'' : List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T').
      { rewrite HΔy, <- (List.firstn_skipn k Ns), tele_insts_app by (try exact HassN; rewrite List.length_firstn, Hlpre; lia).
        rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact HassN; rewrite List.length_firstn; lia); exact HT'. }
      assert (HA'' : List.nth_error (List.rev (im_nparams Mm)) j = Some (ce_ass A')).
      { unfold nparams_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn in HA'.
        destruct (Nat.ltb_spec j k); [ exact HA' | lia ]. }
      pose proof (Hpre _ _ _ _ Hj HM' HT'' Hv) as HMg.
      assert (Hpj : tele_prefix_rel (canon_nparams_rel D ups m) j (List.firstn j ns) (List.firstn j ns))
        by (eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
      destruct (HeN _ _ _ _ _ HM HA'' Hpj) as [b Hb].
      pose proof (HNP _ _ _ _ _ _ HM HA'' Hpj Hb) as Hgb.
      apply (mk_glu_arg _ _ _ _ _ _ u b (NP m j (List.firstn j ns)) (NEl m j (List.firstn j ns)));
        [ rewrite <- env_args_app; exact Hb | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ]. }
    destruct (sort_typ_glued (nparams_prefix Mm k) A SbC Δ _ ns (nparams_prefix_wf m Mm k HM) ltac:(lia) HSbC
                ltac:(rewrite Hlpre; exact HV) Hσ) as (a & Ha & Hpb & HP).
    pose proof (HNP _ _ _ _ _ _ HM HA Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A0 & HA0 & ->).
    rewrite HA in HA0; injection HA0 as <-.
    rewrite <- sb_of_list_app.
    eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  Lemma glu_args_of_nparams : forall m Mm Δ Us Ns ns, ind_member D m = Some Mm -> glu_nparams m Mm NEl Δ Us Ns ns ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      glu_args Δ (im_nparams Mm) (sb_of_list Id Us) (env_args nil ups) Ns ns.
  Proof.
    intros * HM [L1 L2 H] Hns.
    constructor; [ rewrite L1; reflexivity | rewrite L2; reflexivity |].
    intros j M T v A HM' HT Hv HA.
    pose proof (H _ _ _ _ HM' HT Hv) as HMg.
    assert (Hj : j <= List.length (List.rev (im_nparams Mm)))
      by (rewrite List.length_rev, length_im_nparams, <- L2; apply Nat.lt_le_incl, List.nth_error_Some; congruence).
    pose proof (tele_prefix_rel_of_full _ _ _ _ _ Hns Hj) as Hpj.
    destruct (HeN _ _ _ _ _ HM HA Hpj) as [b Hb].
    pose proof (HNP _ _ _ _ _ _ HM HA Hpj Hb) as Hgb.
    apply (mk_glu_arg _ _ _ _ _ _ u b (NP m j (List.firstn j ns)) (NEl m j (List.firstn j ns)));
      [ rewrite <- env_args_app; exact Hb | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ].
  Qed.

  Lemma nonrec_args_prefix_ass : forall gs k, tele_ass (nonrec_args_prefix gs k).
  Proof.
    intros; unfold nonrec_args_prefix, tele_ass; apply List.Forall_rev, Forall_firstn'.
    apply List.Forall_map, List.Forall_forall; intros; eauto.
  Qed.

  (** The substitution of the parameters and the non-recursive arguments
      before a position, glued at the context of the types there. *)
  Lemma nonrec_args_prefix_glu_sub : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 g gs2 Ns ns As vs SbC, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ g :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 -> List.length gs1 <= List.length As ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        EG nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))
          ® env_args nil ((ups ++ ns) ++ nonrec_arg_vals gs1 vs) ∈ SbC.
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 g gs2 Ns ns As vs SbC HM Hcon Heq Hnp Hns Hvl HlAs Hpre Hp HSbC.
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params_ass D m Mm Hc HM) as HassP.
    pose proof (dc_ass _ Hc) as HassU.
    pose proof (decl_closed_nparams_ass D Hc m Mm HM) as HassN.
    assert (Hkn : k <= List.length (cargs_nonrec gs)) by (unfold k; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    set (As1 := List.firstn (List.length gs1) As).
    assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_arg_vals gs1 vs).
    assert (HlNs' : List.length Ns' = k) by (unfold Ns'; apply length_nonrec_exps; exact HlAs1).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_arg_vals; exact Hvl).
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply length_nonrec_args_prefix; lia).
    eapply glu_sub_of_list with (C := nonrec_args_prefix gs k ++ im_params D Mm) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ unfold tele_ass; apply List.Forall_app; split; [ apply nonrec_args_prefix_ass | exact HassP ]
      | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ |].
    apply glu_args_app; [ exact HassP | rewrite List.length_app, LU, LN, length_im_params; unfold im_np, ind_nu in *; lia
                        | rewrite List.length_app, Hu, LNn, length_im_params; unfold im_np, ind_nu in *; lia |].
    split.
    - unfold im_params; apply glu_args_app; [ exact HassU | exact LU | exact Hu |].
      split; [ exact HUs | exact (glu_args_of_nparams _ _ _ _ _ _ HM Hnp Hns) ].
    - constructor; [ lia | lia |].
      intros j M T' v A' HM' HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlvs'; apply List.nth_error_Some; congruence).
      assert (HA1 : List.nth_error (cargs_nonrec gs1) j = Some A').
      { unfold nonrec_args_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn, List.nth_error_map in HA'.
        destruct (Nat.ltb_spec j k); [| lia ].
        rewrite Heq, cargs_nonrec_app, List.nth_error_app1 in HA' by lia.
        destruct (List.nth_error (cargs_nonrec gs1) j); cbn in HA'; [ injection HA' as ->; reflexivity | discriminate ]. }
      destruct (nonrec_nth_split _ _ _ HA1) as (hs1 & hs2 & Heq1 & Hlh).
      assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As (List.length hs1) ltac:(lia)) as [N HN].
      assert (HN1 : List.nth_error As1 (List.length hs1) = Some N)
        by (unfold As1; rewrite List.nth_error_firstn; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [ exact HN | lia ]).
      pose proof (nonrec_exps_nth_arg _ _ _ _ _ _ Heq1 HlAs1 HN1) as HN'.
      rewrite Hlh in HN'; fold Ns' in HN'; rewrite HN' in HM'; injection HM' as <-.
      destruct (nth_error_lt_some vs (List.length hs1) ltac:(lia)) as [v' Hv'].
      pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq1 Hvl Hv') as Hv''.
      rewrite Hlh in Hv''; fold vs' in Hv''; rewrite Hv'' in Hv; injection Hv as <-.
      assert (HTc : exists Tc, List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some Tc).
      { apply nth_error_lt_some; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx, Heq, List.length_app; cbn; lia. }
      destruct HTc as [Tc HTc].
      pose proof (Hpre _ _ _ _ _ _ Heq1 HN HTc Hv') as HNg.
      assert (Heqgs : gs = hs1 ++ ca_arg A' :: (hs2 ++ g :: gs2)) by (rewrite Heq, Heq1, <- List.app_assoc; reflexivity).
      pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ _ Heqgs HTc) as ETc.
      rewrite exp_wk_pat_sb_of_list in ETc by (rewrite List.length_firstn; lia).
      destruct (tele_insts_nth _ _ _ _ _ HT') as (A2 & HA2 & ET').
      rewrite HA' in HA2; injection HA2 as <-.
      assert (Efn : List.firstn j Ns' = nonrec_exps hs1 (List.firstn (List.length hs1) As)).
      { unfold Ns'; rewrite <- Hlh, (nonrec_exps_firstn _ _ _ _ _ Heq1 HlAs1); unfold As1; rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity. }
      assert (Tc = T') as <- by (rewrite ETc, ET', Efn; reflexivity).
      assert (Efv : List.firstn j vs' = nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))
        by (unfold vs'; rewrite <- Hlh; exact (nonrec_firstn _ _ _ _ _ Heq1 Hvl)).
      assert (Hpj : tele_prefix_rel (canon_args_rel D ups m ns c) j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))
                      (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))
        by (rewrite <- Efv; eapply tele_prefix_rel_of_pre; [ exact Hp | lia ]).
      assert (HAj : List.nth_error (cargs_nonrec gs) j = Some A') by (rewrite Heq, cargs_nonrec_app, List.nth_error_app1 by lia; exact HA1).
      destruct (HeA _ _ _ _ _ _ _ _ HM Hns Hcon HAj Hpj) as [b Hb].
      pose proof (HAP _ _ _ _ _ _ _ _ _ HM Hns Hcon HAj Hpj Hb) as Hgb.
      rewrite Hlh in HNg.
      apply (mk_glu_arg _ _ _ _ _ _ u b (AP m ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs)))
        (AEl m ns c j (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))));
        [ rewrite Efv, <- !env_args_app, <- List.app_assoc; exact Hb
        | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HNg ].
  Qed.

  Lemma comps_arg : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 A0 gs2 Ns ns As vs T, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_arg A0 :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        Δ ⊢ T ® AP m ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs).
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 A0 gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params_ass D m Mm Hc HM) as HassP.
    assert (HA0 : List.nth_error (cargs_nonrec gs) k = Some A0)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2 by lia; unfold k; rewrite Nat.sub_diag; reflexivity).
    pose proof (gid_arg _ HG m Mm c gs k A0 HM Hcon HA0) as HV.
    pose proof HV as [SbC HSbC _ _].
    assert (HlAs : List.length gs1 < List.length As).
    { assert (Hs : List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by apply cargs_ctx_aux_ass; lia. }
    set (As1 := List.firstn (List.length gs1) As).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_arg_vals gs1 vs).
    assert (Hkn : k <= List.length (cargs_nonrec gs)) by (apply Nat.lt_le_incl, List.nth_error_Some; congruence).
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply length_nonrec_args_prefix; lia).
    pose proof Hnp as [LN LNn _].
    pose proof (nonrec_args_prefix_glu_sub Δ Us HΔ HUs m Mm c gs gs1 (ca_arg A0) gs2 Ns ns As vs SbC HM Hcon Heq Hnp Hns Hvl
                  ltac:(lia) Hpre Hp HSbC) as Hσ.
    assert (HPre : ⊢ (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D)
      by (rewrite <- List.app_assoc; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HV).
    assert (HSbC' : EG (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D ∈ glu_ctx_env ↘ SbC)
      by (rewrite <- List.app_assoc; exact HSbC).
    assert (HV' : (nonrec_args_prefix gs k ++ im_nparams Mm) ++ ind_uparams D
                  ⊩ A0 : (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k ++ im_nparams Mm))]ʷ)
      by (rewrite <- List.app_assoc, List.length_app, Hlast, length_im_nparams; exact HV).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_arg_vals; exact Hvl).
    rewrite <- List.app_assoc, <- List.app_assoc in Hσ.
    destruct (sort_typ_glued _ A0 SbC Δ _ (ns ++ vs') HPre ltac:(rewrite !List.length_app, Hlast, length_im_nparams; lia) HSbC' HV' Hσ)
      as (a & Ha & Hpb & HP).
    pose proof (HAP _ _ _ _ _ _ _ _ _ HM Hns Hcon HA0 Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ _ Heq HT) as ET.
    rewrite exp_wk_pat_sb_of_list in ET by (rewrite List.length_firstn; lia).
    fold As1 in ET; fold Ns' in ET.
    rewrite ET, <- !sb_of_list_app, <- List.app_assoc.
    eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  (** Glued arguments of the non-uniform parameters' telescope are glued
      at the gluings of the clause, given the components. *)
  Lemma nparams_of_glu_args : forall m Mm Δ Us Ns ns, ind_member D m = Some Mm -> ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us ->
      glu_args Δ (im_nparams Mm) (sb_of_list Id Us) (env_args nil ups) Ns ns ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      glu_nparams m Mm NEl Δ Us Ns ns.
  Proof.
    intros * HM Hc0 Hg Hns.
    pose proof Hc0 as [HCN _ _].
    pose proof Hg as [L1 L2 H].
    rewrite length_im_nparams in L1, L2.
    constructor; [ exact L1 | exact L2 |].
    enough (forall n, n <= im_nn Mm -> forall j N T v, j < n -> List.nth_error Ns j = Some N ->
              List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T ->
              List.nth_error ns j = Some v -> Δ ⊢ N : T ® v ∈ NEl m j (List.firstn j ns)) as Hm.
    { intros j N T v HN HT Hv.
      assert (Hj : j < im_nn Mm) by (rewrite <- L2; apply List.nth_error_Some; congruence).
      exact (Hm (im_nn Mm) ltac:(lia) _ _ _ _ Hj HN HT Hv). }
    induction n as [| n IH]; intros Hn j N T v Hj HN HT Hv; [ lia |].
    destruct (Nat.eq_dec j n) as [-> | Hne]; [| eapply IH; eauto; lia ].
    assert (Hk' : n < List.length (List.rev (im_nparams Mm))) by (rewrite List.length_rev, length_im_nparams; lia).
    destruct (nparams_lt_ass D m Mm n Hass HM Hk') as [A HA].
    destruct (H _ _ _ _ _ HN HT Hv HA) as [i' a P' El' Ha Hglu' HP' HM'].
    assert (Hpm : tele_prefix_rel (canon_nparams_rel D ups m) n (List.firstn n ns) (List.firstn n ns))
      by (eapply tele_prefix_rel_of_full; [ exact Hns | rewrite List.length_rev, length_im_nparams; lia ]).
    rewrite <- env_args_app in Ha.
    pose proof (HNP _ _ _ _ _ _ HM HA Hpm Ha) as Hgu.
    assert (HTP : Δ ⊢ T ® NP m n (List.firstn n ns)).
    { eapply (HCN m Mm n Ns (List.firstn n ns) T HM); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' v' Hj' HN' HT' Hv'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' n); [| discriminate ].
      eapply IH; eauto; lia. }
    eapply glu_univ_elem_exp_conv_uidx; [ eapply glu_univ_elem_per_univ; exact Hglu' | exact Hglu' | exact Hgu | exact HM' | exact HTP ].
  Qed.

  (** A glued instance of a shape's context after [k] domains, weakened and
      extended by an argument glued at the next domain's gluing. *)
  Lemma shape_sub_step : forall m Mm c gs gs1 t gs2 k B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c',
      ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) k = Some B ->
      EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
        ∈ glu_ctx_env ↘ SbC ->
      EG doms_ctx (List.firstn (S k) (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
        ∈ glu_ctx_env ↘ SbC' ->
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC -> Δ' ⊢ᵏ φ : Δ ->
      ⟦ B ⟧ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b0 ->
      DG b0 ∈ glu_univ_elem u ↘ DP m (ns ++ nv ++ ys) B ↘ DEl m (ns ++ nv ++ ys) B ->
      Δ' ⊢ B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® DP m (ns ++ nv ++ ys) B ->
      Δ' ⊢ b : B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® c' ∈ DEl m (ns ++ nv ++ ys) B ->
      Δ' ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))
        ® env_args nil (ups ++ ns ++ nv ++ ys ++ c' :: nil) ∈ SbC'.
  Proof.
    intros * HM Hcon Heq HB HSbC HSbC' Hσ Hφ Hb0 Hgb0 HTy Hb.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    pose proof HSbC' as HSbC''.
    rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc in HSbC''; cbn [List.app] in HSbC''.
    assert (Hσ' : Δ' ⊢ˢ (sb_wk σ φ),,b ® env_args nil (ups ++ ns ++ nv ++ ys) ↦ c' ∈ SbC').
    { eapply glu_sub_snoc; [ exact HSbC | exact HSbC'' | eapply glu_ctx_env_sub_monotone; eassumption |].
      rewrite <- exp_wk_sub.
      exact (mk_glu_arg _ _ _ _ _ _ u b0 (DP m (ns ++ nv ++ ys) B) (DEl m (ns ++ nv ++ ys) B) Hb0 Hgb0 HTy Hb). }
    assert (Esb : sb_eq ((sb_wk σ φ),,b) (sb_of_list (sb_wk τ φ) (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys) ++ b :: nil))).
    { rewrite (sb_of_list_app (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys)) (b :: nil)); cbn [sb_of_list].
      apply sb_extend_cong; unfold σ; apply sb_wk_sb_of_list. }
    rewrite List.map_app, <- List.app_assoc in Esb.
    replace (ups ++ ns ++ nv ++ ys ++ c' :: nil) with ((ups ++ ns ++ nv ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    rewrite env_args_snoc.
    eapply glu_ctx_env_sub_resp_sub_eq; [ exact HSbC' | exact Hσ' |].
    eapply wf_sub_eq_of_sb_eq; [ eapply glu_ctx_env_sub_escape; eassumption | exact Esb ].
  Qed.

  (** The type of a recursive argument after [k] of its shape's domains, at
      an instance [Us ++ Ys] of the shape's context glued to its values, is
      glued at the gluings of the domains. *)
  Lemma shape_typ_glu : forall m Mm c gs gs1 t gs2 ns nv, ind_member D m = Some Mm -> ind_con Mm c = Some gs ->
      gs = gs1 ++ ca_rec t :: gs2 ->
      tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
      tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) nv nv ->
      List.length ns = im_nn Mm -> List.length nv = List.length (cargs_nonrec gs1) ->
      forall t' k ys Δ τ Us Ys SbC, ptyp_skip k t = t' -> k <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel ups m) ns nv (ptyp_doms t)) k ys ys -> ⊢ Δ ->
        List.length Us = ind_nu D -> List.length Ys = k + List.length (cargs_nonrec gs1) + im_nn Mm ->
        EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mm
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC ->
        glu_shape_typ (canon_doms_rel ups m) (DP m) (DEl m) Δ (ns ++ nv ++ ys) t' (ptyp_ty_at p D Us (sb_of_list τ (Us ++ Ys)) t').
  Proof.
    intros m Mm c gs gs1 t gs2 ns nv HM Hcon Heq Hns Hnv Hnsl Hnvl t'.
    set (K := List.length (cargs_nonrec gs1)) in *.
    assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    induction t' as [? ? | B t'' IH]; intros k ys Δ τ Us Ys SbC Hsk Hk Hy HΔ HUl HYl HSbC Hσ;
      cbn [glu_shape_typ]; [ exact I |].
    intros IT OT HT; cbn [ptyp_ty_at] in HT; injection HT as <- <-.
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
    assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    pose proof (gid_dom _ HG _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as HBv.
    destruct (HeD _ _ _ _ _ _ _ _ _ _ _ _ HM Hns Hcon Heq Hnv HB Hy) as [b0 Hb0].
    pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hns Hcon Heq Hnv HB Hy Hb0) as Hgb0.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Pre := doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_nparams Mm).
    assert (EPre : doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_params D Mm = Pre ++ ind_uparams D)
      by (unfold Pre, im_params; rewrite <- !List.app_assoc; reflexivity).
    assert (HlPre : List.length Pre = k + K + im_nn Mm)
      by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix, length_im_nparams
            by exact HKl; lia).
    assert (HPre : ⊢ Pre ++ ind_uparams D)
      by (rewrite <- EPre; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HBv).
    assert (HSbCp : EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ SbC) by (rewrite <- EPre; exact HSbC).
    assert (HBvp : Pre ++ ind_uparams D ⊩ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ) by (rewrite <- EPre, HlPre; exact HBv).
    (** The domain, glued at its gluing at every weakening. *)
    assert (HTy : forall Δ' φ, Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ B[σ][φ]ʷ ® DP m (ns ++ nv ++ ys) B).
    { intros Δ' φ Hφ.
      pose proof (glu_ctx_env_sub_monotone _ _ HSbC _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (sort_typ_glued Pre B SbC Δ' (sb_wk σ φ) (ns ++ nv ++ ys) HPre
                  ltac:(rewrite HlPre, !List.length_app; destruct Hy as [Hyl _]; lia) HSbCp HBvp Hσφ) as (a & Ha & Hpa & HP).
      assert (a = b0) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
      rewrite exp_wk_sub.
      eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hgb0 | exact (HP _ _ Hgb) ]. }
    split; [ exact HTy |].
    intros Δ' φ b c' Hφ Hc' Hb.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    destruct (gid_dctx _ HG _ _ _ _ _ _ _ (S k) HM Hcon Heq ltac:(lia)) as [SbC' HSbC'].
    pose proof (shape_sub_step m Mm c gs gs1 t gs2 k B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c' HM Hcon Heq HB HSbC HSbC'
                  Hσ Hφ Hb0 Hgb0 (HTy _ _ Hφ) Hb) as Hσ''.
    unfold σ; rewrite ptyp_ty_at_shape_step by assumption.
    replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    apply (IH (S k) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil) SbC');
      [ exact Hs' | lia | | exact HΔ' | rewrite List.length_map; exact HUl
      | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'' ].
    apply tele_prefix_rel_snoc; [ exact Hy |].
    unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
  Qed.

  (** The types of the recursive arguments, at uniform parameters glued to
      [ups], are glued at the gluings of the domains of their shapes. *)
  Lemma comps_rec : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall m Mm c gs gs1 t gs2 Ns ns As vs T, ind_member D m = Some Mm -> ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        glu_nparams m Mm NEl Δ Us Ns ns -> tele_rel (canon_nparams_rel D ups m) (List.rev (im_nparams Mm)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl m ns c (List.length (cargs_nonrec hs1)) (nonrec_arg_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_prefix_rel (canon_args_rel D ups m ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs) (nonrec_arg_vals gs1 vs) ->
        glu_shape_typ (canon_doms_rel ups m) (DP m) (DEl m) Δ (ns ++ nonrec_arg_vals gs1 vs) t T.
  Proof.
    intros Δ Us HΔ HUs m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (HlAs : List.length gs1 < List.length As).
    { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
      rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; subst gs; rewrite List.length_app; cbn; lia. }
    destruct (gid_dctx _ HG _ _ _ _ _ _ _ 0 HM Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
    cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
    pose proof (nonrec_args_prefix_glu_sub Δ Us HΔ HUs m Mm c gs gs1 (ca_rec t) gs2 Ns ns As vs SbC0 HM Hcon Heq Hnp Hns Hvl
                  ltac:(lia) Hpre Hp HSbC0) as Hσ.
    pose proof (cargs_rec_type_sh p D Mm gs gs1 t gs2 (Us ++ Ns) As T Heq Hc
                  ltac:(rewrite List.length_app, LU, LN; unfold im_np, ind_nu in *; lia) HT) as ET.
    rewrite firstn_app_exact in ET by exact LU.
    assert (Hlnv : List.length (nonrec_arg_vals gs1 vs) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_arg_vals; exact Hvl).
    pose proof (shape_typ_glu m Mm c gs gs1 t gs2 ns (nonrec_arg_vals gs1 vs) HM Hcon Heq Hns Hp LNn Hlnv t 0 nil Δ Id Us
                  (Ns ++ nonrec_exps gs1 (List.firstn (List.length gs1) As)) SbC0 eq_refl ltac:(lia) (tele_prefix_rel_nil _) HΔ LU) as H.
    rewrite !List.app_nil_r, List.app_assoc in H.
    rewrite ET, <- List.app_assoc; apply H.
    - rewrite List.length_app, length_nonrec_exps by (rewrite List.length_firstn; lia); lia.
    - cbn [List.firstn doms_ctx List.map List.rev List.app]; exact HSbC0.
    - rewrite <- !List.app_assoc in Hσ; exact Hσ.
  Qed.

  (** The components, at uniform parameters glued to [ups]. *)
  Lemma comps_of_uparams : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us.
  Proof.
    intros * HΔ HUs; constructor.
    - intros m Mm k Ns ns T HM Hl' Hk HT Hpre Hp; eapply comps_npar; eassumption.
    - intros m Mm c gs gs1 A0 gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply comps_arg; eassumption.
    - intros m Mm c gs gs1 t gs2 Ns ns As vs T HM Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply comps_rec; eassumption.
  Qed.

End Comps.

End Fixed_GCtx.
