(** * The View Equations of a Filed Group, Read in the PER Model

    The semantic view equations of a group ([views_self_valid]) are
    judgments over the context of its members as variables
    ([grp_sctx]).  Once the group is filed at [p], the substitution
    [grp_sb p D] of its type formers at the uniform parameters for those
    variables is built from valid parts ([grp_sb_gsub]), and moves each
    equation to the filed group: a view's instance is typed at the uniform
    parameters, and its non-uniform parameters and the arguments of its
    constructors are its container's at the instance.  These are the
    semantic counterparts of the syntactic [dt_view_*] lemmas of
    [Core.Syntactic.System.Global.Presup]. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import UnitCases.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Inductives Require Import Decl Model.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma eval_sub_sb_eq : forall σ τ ρ ρσ, sb_eq σ τ -> ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ τ ⟧s ρ ↘ ρσ.
Proof. intros * E H x; rewrite <- (E x); exact (H x). Qed.

Section FiledViews.
  Variables (p : qname) (D : ind_decl) (IsS : nat -> list exp).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D) (Hvsv : views_self_valid D IsS).
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hl := vgr_lookup _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Let Hmp := vgr_mpath _ _ Hg.

  Lemma container_closed : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> decl_closed Dq.
  Proof. intros * Hk Hh Hq; exact (vgr_closed _ _ (Hcv _ _ _ _ _ _ _ Hk Hh Hq)). Qed.

  Lemma filed_link : grp_link p D IsS.
  Proof. exact (vsv_link _ _ Hvsv _ Hmp). Qed.

  Lemma grp_sb_valid : gsub (ind_uparams D) (grp_sb p D) (grp_sctx D).
  Proof. exact (grp_sb_gsub _ HD Hc Hsu p Hl Hass (dt_order _ _ _ Hdt) (dt_mvc _ _ _ Hdt)). Qed.

  (** What a view's equations share: the container is closed, the instance
      is at the container's uniform parameters, and the members the view
      takes the container's to have as many non-uniform parameters. *)
  Lemma filed_shared : forall k Mk qc k' Is vm Dq i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      decl_closed Dq /\ List.length (IsS k) = ind_nu Dq /\ im_nn Mv = im_nn Mi'.
  Proof.
    intros * Hk Hh Hq Hi' Hv HMv.
    split; [ exact (container_closed _ _ _ _ _ _ _ Hk Hh Hq) |].
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    split; [ rewrite (filed_link _ _ _ _ _ _ Hk Hh), List.length_map in HIl; exact HIl |].
    destruct (dt_vwrap _ _ _ Hdt _ _ _ _ _ _ Hk Hh) as (D2 & Hl2 & Hw).
    rewrite Hq in Hl2; injection Hl2 as <-.
    destruct (vwo_members _ _ _ Hw _ _ _ Hi' Hv) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
  Qed.

  (** A view's instance is typed at the uniform parameters. *)
  Lemma filed_view_is : forall k Mk qc k' Is vm Dq j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> List.nth_error Is j = Some I ->
      List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
      ind_uparams D ⊨ I : T.
  Proof.
    intros * Hk Hh Hq HI HT.
    pose proof (container_closed _ _ _ _ _ _ _ Hk Hh Hq) as Hc'.
    rewrite (filed_link _ _ _ _ _ _ Hk Hh) in HI, HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (grp_sb p D) (IsS k) (dc_ass _ Hc') (dc_uparams _ Hc')
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (rel_exp_under_ctx_gsub grp_sb_valid (vsv_is _ _ Hvsv _ _ _ _ _ _ _ _ _ _ Hk Hh Hq HI0 HT0)).
  Qed.

  (** A view of the container of a view's container's member that is a view
      too: the instance of the group's member the view takes it to is the
      container's member's at the view's instance ([dt_view_view_is]). *)
  Lemma filed_view_view_is : forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      ind_lookup gc_deps gc_stack q'' = Some D'' -> decl_closed D'' ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      List.nth_error X j' = Some C ->
      List.nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j' = Some C' ->
      List.nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
      ind_uparams D ⊨ C ≈ C' : T[sb_of_list Id Is].
  Proof.
    intros * Hk Hh Hq Hi' Hh' Hq'' Hc'' Hv HMv HhMv HC HC' HT.
    destruct (filed_shared _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hq Hi' Hv HMv) as (Hc' & HIl & _).
    pose proof (decl_closed_head_scoped _ Hc' _ _ _ _ _ _ Hi' Hh') as HsIs''.
    rewrite (filed_link _ _ _ _ _ _ HMv HhMv) in HC; apply nth_error_map_inv in HC as (C0 & HC0 & ->).
    apply nth_error_map_inv in HC' as (I'' & HI'' & ->).
    assert (HC0' : List.nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some I''[sb_of_list Id (IsS k)])
      by (rewrite List.nth_error_map, HI''; reflexivity).
    pose proof (vsv_view_is _ _ Hvsv k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' _ _ T
                  Hk Hh Hq Hi' Hh' Hq'' Hv HMv HhMv HC0 HC0' HT) as H.
    pose proof (rel_exp_under_ctx_gsub grp_sb_valid H) as H'; cbn [exp_sub] in H'.
    assert (HsI : exp_scoped (List.length (IsS k)) I'')
      by (rewrite HIl; rewrite List.Forall_forall in HsIs''; exact (HsIs'' _ (List.nth_error_In _ _ HI''))).
    rewrite (exp_list_grp_sb0 _ _ I'') in H' by exact HsI.
    assert (HTT : T[sb_of_list Id (IsS k)][grp_sb p D] = T[sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))]).
    { pose proof (tele_insts_closed_sub _ _ (sb_of_list Id (IsS k)) _ _ (dc_ass _ Hc'') (dc_uparams _ Hc'') HT) as H1.
      pose proof (tele_insts_closed_sub _ _ (grp_sb p D) _ _ (dc_ass _ Hc'') (dc_uparams _ Hc'') H1) as H2.
      pose proof (tele_insts_closed_sub _ _ (sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))) _ _
                    (dc_ass _ Hc'') (dc_uparams _ Hc'') HT) as H3.
      rewrite List.map_map in H2.
      rewrite (List.map_ext_in _ (fun I => I[sb_of_list Id (List.map (fun I => I[grp_sb p D]) (IsS k))])) in H2.
      - rewrite H2 in H3; injection H3 as E; exact E.
      - intros I HI; apply exp_list_grp_sb0; rewrite HIl.
        rewrite List.Forall_forall in HsIs''; exact (HsIs'' _ HI). }
    rewrite HTT, <- (filed_link _ _ _ _ _ _ Hk Hh) in H'; exact H'.
  Qed.

  (** A view's non-uniform parameters are its container's at the view's
      instance. *)
  Lemma filed_view_nparams : forall k Mk qc k' Is vm Dq i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      ind_uparams D ⊨ˣ im_nparams Mv ≈ tele_sub (im_nparams Mi') (sb_of_list Id Is).
  Proof.
    intros * Hk Hh Hq Hi' Hv HMv.
    destruct (filed_shared _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hq Hi' Hv HMv) as (Hc' & HIl & _).
    pose proof (vsv_nparams _ _ Hvsv _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hq Hi' Hv HMv) as H.
    pose proof (rel_ext_under_ctx_gsub _ _ _ _ _ grp_sb_valid
                  (tele_ass_wk _ _ (dt_nparams_ass _ _ _ Hdt _ _ HMv))
                  (tele_ass_sub _ _ (decl_closed_nparams_ass _ Hc' _ _ Hi')) H) as H'.
    rewrite (tele_self_wk_grp_sb p D 0) in H'.
    rewrite (nparams_sub Dq i' Mi' (IsS k) (grp_sb p D) Hc' Hi' HIl) in H'.
    rewrite <- (filed_link _ _ _ _ _ _ Hk Hh) in H'; exact H'.
  Qed.

  (** The arguments of a view's constructor are its container's at the
      view's instance. *)
  Lemma filed_view_args : forall k Mk qc k' Is vm Dq i' Mi' v Mv c gs' gs, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      im_params D Mv ⊨ˣ tele_sub (cargs_ctx qc Dq Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is)) ≈ cargs_ctx p D Mv gs.
  Proof.
    intros * Hk Hh Hq Hi' Hv HMv Hc1 Hc2.
    destruct (filed_shared _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hq Hi' Hv HMv) as (Hc' & HIl & Hnn).
    pose proof (vsv_args _ _ Hvsv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hh Hq Hi' Hv HMv Hc1 Hc2) as H.
    assert (Hass' : tele_ass (tele_wk (im_nparams Mv) (self_wk D 0)))
      by exact (tele_ass_wk _ _ (dt_nparams_ass _ _ _ Hdt _ _ HMv)).
    pose proof (gsub_qn _ _ _ _ grp_sb_valid Hass' (rel_ctx_wf_app_r _ _ (rxu_left _ _ _ H))) as Hq'.
    pose proof (rel_ext_under_ctx_gsub _ _ _ _ _ Hq' (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))
                  (scargs_ctx_aux_ass _ _ _ _ _) H) as H'.
    rewrite length_tele_wk, grp_sb_nparams in H'; fold (im_nn Mv) in H'.
    change (cargs_ctx_aux qc Dq (im_nn Mi') nil gs') with (cargs_ctx qc Dq Mi' gs') in H'.
    change (scargs_ctx_aux D IsS (im_nn Mv) nil gs) with (scargs_ctx D IsS Mv gs) in H'.
    rewrite tele_list_grp_sb, scargs_ctx_grp_sb in H' by
      (try exact Hc; try exact (dt_mvc _ _ _ Hdt); try exact (dt_order _ _ _ Hdt); try exact filed_link;
       rewrite Hnn, HIl; exact (decl_closed_cargs_scoped _ Hc' _ _ _ _ _ Hi' (cons_lookup_in _ _ _ Hc1))).
    rewrite <- (filed_link _ _ _ _ _ _ Hk Hh) in H'; exact H'.
  Qed.

  (** ** A View's Instance, Evaluated

      The substitution of a view's instance for its container's uniform
      parameters is built from valid parts, so at related uniform
      parameters of the group the instance evaluates to related uniform
      parameters of the container. *)
  Lemma view_args_gsub : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      gsub (ind_uparams D) (sb_of_list Id Is) (ind_uparams Dq ++ ind_uparams D).
  Proof.
    intros * Hk Hh Hq.
    pose proof (Hcv _ _ _ _ _ _ _ Hk Hh Hq) as HgQ.
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    pose proof (dc_ass _ (vgr_closed _ _ HgQ)) as HaQ.
    apply gsub_of_list;
      [ exact (gsub_id _ (vid_uparams _ HD)) | exact HaQ
      | exact (proj1 (closed_app_sem _ _ HaQ (vid_uparams _ (vgr_valid _ _ HgQ)) (vid_uparams _ HD))) | exact HIl |].
    intros j I T HI HT; exact (filed_view_is _ _ _ _ _ _ _ _ _ _ Hk Hh Hq HI HT).
  Qed.

  Lemma view_args_values : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      exists cups cups', ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups /\
        ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups' ↘ cups' /\
        per_gargs (List.rev (ind_uparams Dq)) nil nil cups cups'.
  Proof.
    intros * Hk Hh Hq ups ups' Hgu Hu.
    pose proof (Hcv _ _ _ _ _ _ _ Hk Hh Hq) as HgQ.
    pose proof (dc_ass _ (vgr_closed _ _ HgQ)) as HaQ.
    pose proof (vid_uparams _ (vgr_valid _ _ HgQ)) as HWQ.
    pose proof (vid_uparams _ HD) as HWD.
    pose proof (length_ups_gargs D _ _ Hgu Hu) as Hu'.
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    pose proof (gsub_valid (view_args_gsub _ _ _ _ _ _ _ Hk Hh Hq)) as Hσ.
    destruct (rel_sub_under_ctx_simple Hσ) as (RΓ0 & HRΓ0 & RΔ0 & HRΔ0 & Hs).
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRΓ0) as Hρ.
    (** The values of the instance at either side. *)
    assert (Hval : forall ρ ρ', RΓ0 ρ ρ' -> exists cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ cs).
    { intros ρ ρ' Hρρ; apply eval_exps_each; intros j I HI.
      assert (Hj : j < List.length (tele_insts (ind_uparams Dq) Id Is))
        by (rewrite length_tele_insts by exact HaQ;
            assert (j < List.length Is) by (apply List.nth_error_Some; congruence); unfold ind_nu in *; lia).
      destruct (nth_error_lt_some' _ _ Hj) as [T HT].
      destruct (rel_exp_under_ctx_simple_at HRΓ0 (filed_view_is _ _ _ _ _ _ _ _ _ _ Hk Hh Hq HI HT) _ _ Hρρ)
        as (m & _ & Em & _ & _); eauto. }
    assert (HP0 : PER RΓ0) by (eapply per_env_PER; exact HRΓ0).
    destruct (Hval _ _ Hρ) as [cups Ecups].
    assert (Hρ' : RΓ0 (env_args nil ups') (env_args nil ups')) by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    destruct (Hval _ _ Hρ') as [cups' Ecups'].
    exists cups, cups'; split; [ exact Ecups | split; [ exact Ecups' |] ].
    destruct (Hs _ _ Hρ) as (y1 & y2 & Ey1 & Ey2 & Hy).
    assert (E1 : env_eq y1 (env_args (env_args nil ups) cups))
      by (eapply functional_eval_sub; [ exact Ey1 | apply eval_sb_of_list; [ apply eval_sub_id | exact Ecups ] ]).
    assert (E2 : env_eq y2 (env_args (env_args nil ups') cups'))
      by (eapply functional_eval_sub; [ exact Ey2 | apply eval_sb_of_list; [ apply eval_sub_id | exact Ecups' ] ]).
    pose proof (per_ctx_env_resp_env_eq HRΔ0 _ _ _ _ E1 E2 Hy) as HE.
    destruct (rel_ctx_wf_per_ctx_env HWQ) as [RQ HRQ].
    pose proof (proj2 (closed_app_sem _ _ HaQ HWQ HWD) RQ RΔ0 HRQ HRΔ0 _ _ HE) as HEQ.
    assert (HWQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HWQ).
    assert (HRQ' : EF List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    pose proof (eval_exps_length _ _ _ Ecups) as Hl1; pose proof (eval_exps_length _ _ _ Ecups') as Hl2.
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HWQ' (List.Forall_rev HaQ) HRQ' _ _ cups cups'
                ltac:(rewrite List.length_rev; unfold ind_nu in *; lia) ltac:(rewrite List.length_rev; unfold ind_nu in *; lia) HEQ)
      as [_ Hgc].
    exact (per_gargs_base _ _ _ per_ctx_env_nil_true HWQ' (List.Forall_rev HaQ) _ _ nil nil _ _ I I I Hgc).
  Qed.

  (** The view's instance weakened past more variables, at an environment
      extending the group's uniform parameters [ups]: related to the
      instance at [ups] (the substitution of the instance moved along the
      weakening, [sub_link]). *)
  Lemma view_args_wk : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      forall Z RZ ups zs, ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
        List.length zs = List.length Z -> List.length ups = ind_nu D ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
        RZ (env_args (env_args nil ups) zs) (env_args (env_args nil ups) zs) ->
        exists cups cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups /\
          ⟦ List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args (env_args nil ups) zs ↘ cs /\
          per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs.
  Proof.
    intros * Hk Hh Hq Z RZ ups zs HZ HRZ Hlz Hu Hgu HE.
    pose proof (Hcv _ _ _ _ _ _ _ Hk Hh Hq) as HgQ.
    pose proof (dc_ass _ (vgr_closed _ _ HgQ)) as HaQ.
    pose proof (vid_uparams _ (vgr_valid _ _ HgQ)) as HWQ.
    pose proof (vid_uparams _ HD) as HWD.
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ Hk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    destruct (view_args_values _ _ _ _ _ _ _ Hk Hh Hq _ _ Hgu Hu) as (cups & _ & Ecups & _ & _).
    pose proof (rel_wk_under_ctx_shiftn _ _ HZ) as HwZ.
    pose proof (rel_sub_of_wk HwZ) as Hσ.
    destruct (gsub_props (view_args_gsub _ _ _ _ _ _ _ Hk Hh Hq)) as [_ Hlink].
    pose proof (closed_app_sem _ _ HaQ HWQ HWD) as [HWQD HresQ].
    destruct (rel_ctx_wf_per_ctx_env HWQD) as [RΔ HRΔ].
    set (E := env_args (env_args nil ups) zs) in *.
    assert (HwE : ⟪wk_shiftn (List.length Z)⟫ E = env_args nil ups) by (unfold E; rewrite <- Hlz; apply eval_wk_shiftn_args).
    destruct (Hlink _ _ HRZ _ _ Hσ _ HRΔ E _ HE (eval_sub_of_wk _ _ (Hφ := WkMono_shiftn _))) as (e1 & Ee1 & He1).
    rewrite HwE in He1.
    pose proof (He1 _ (eval_sb_of_list _ _ _ _ _ (eval_sub_id _) Ecups)) as HR1.
    assert (Hval : exists cs, ⟦ List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ cs).
    { apply eval_exps_each; intros j I' HI'.
      rewrite List.nth_error_map in HI'.
      destruct (List.nth_error Is j) as [I |] eqn:HI; cbn in HI'; [ injection HI' as <- | discriminate ].
      assert (Hj : j < List.length (tele_insts (ind_uparams Dq) Id Is))
        by (rewrite length_tele_insts by exact HaQ;
            assert (j < List.length Is) by (apply List.nth_error_Some; congruence); unfold ind_nu in *; lia).
      destruct (nth_error_lt_some' _ _ Hj) as [T HT].
      pose proof (rel_exp_under_ctx_wk HwZ (filed_view_is _ _ _ _ _ _ _ _ _ _ Hk Hh Hq HI HT)) as HIw.
      destruct (rel_exp_under_ctx_simple_at HRZ HIw _ _ HE) as (m & _ & Em & _ & _); eauto. }
    destruct Hval as [cs Ecs].
    exists cups, cs; split; [ exact Ecups | split; [ exact Ecs |] ].
    assert (Ee1' : ⟦ sb_of_list Id Is ⨟ sb_of_wk (wk_shiftn (List.length Z)) ⟧s E ↘ env_args (env_args nil ups) cs).
    { eapply eval_sub_sb_eq; [ symmetry; apply sb_of_list_id_wk |].
      apply eval_sb_of_list; [| exact Ecs ].
      rewrite <- HwE; apply eval_sub_of_wk; typeclasses eauto. }
    assert (E1 : env_eq e1 (env_args (env_args nil ups) cs)) by (eapply functional_eval_sub; eassumption).
    assert (HR2 : RΔ (env_args (env_args nil ups) cs) (env_args (env_args nil ups) cups))
      by (eapply per_ctx_env_resp_env_eq; [ exact HRΔ | exact E1 | reflexivity | exact HR1 ]).
    destruct (rel_ctx_wf_per_ctx_env HWQ) as [RQ HRQ].
    pose proof (HresQ RQ RΔ HRQ HRΔ _ _ HR2) as HEQ.
    assert (HWQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HWQ).
    assert (HRQ' : EF List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams Dq)) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    pose proof (eval_exps_length _ _ _ Ecups) as Hl1; pose proof (eval_exps_length _ _ _ Ecs) as Hl2.
    rewrite List.length_map in Hl2.
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HWQ' (List.Forall_rev HaQ) HRQ' _ _ cs cups
                ltac:(rewrite List.length_rev; unfold ind_nu in *; lia) ltac:(rewrite List.length_rev; unfold ind_nu in *; lia) HEQ)
      as [_ Hgc].
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true HWQ' (List.Forall_rev HaQ) _ _ nil nil _ _ I I I Hgc) as Hgc0.
    exact (uparams_sym _ (vgr_valid _ _ HgQ) (vgr_closed _ _ HgQ) _ _ Hgc0 ltac:(unfold ind_nu in *; lia)).
  Qed.
End FiledViews.

(** The same, for a valid group: its semantic view equations are those of
    its validity ([vid_views]). *)
Section ValidGroupViews.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).

  Lemma vg_view_is : forall k Mk qc k' Is vm Dq j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> List.nth_error Is j = Some I ->
      List.nth_error (tele_insts (ind_uparams Dq) Id Is) j = Some T ->
      ind_uparams D ⊨ I : T.
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (filed_view_is p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_view_is : forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
      ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
      ind_lookup gc_deps gc_stack q'' = Some D'' -> decl_closed D'' ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      List.nth_error X j' = Some C ->
      List.nth_error (List.map (fun I => I[sb_of_list Id Is]) Is'') j' = Some C' ->
      List.nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
      ind_uparams D ⊨ C ≈ C' : T[sb_of_list Id Is].
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (filed_view_view_is p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_nparams : forall k Mk qc k' Is vm Dq i' Mi' v Mv, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
      ind_member D v = Some Mv ->
      ind_uparams D ⊨ˣ im_nparams Mv ≈ tele_sub (im_nparams Mi') (sb_of_list Id Is).
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (filed_view_nparams p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_args : forall k Mk qc k' Is vm Dq i' Mi' v Mv c gs' gs, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v ->
      ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      im_params D Mv ⊨ˣ tele_sub (cargs_ctx qc Dq Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is)) ≈ cargs_ctx p D Mv gs.
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (filed_view_args p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_args_gsub : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      gsub (ind_uparams D) (sb_of_list Id Is) (ind_uparams Dq ++ ind_uparams D).
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (view_args_gsub p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_args_values : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      exists cups cups', ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups /\
        ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups' ↘ cups' /\
        per_gargs (List.rev (ind_uparams Dq)) nil nil cups cups'.
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (view_args_values p D IsS Hg Hcv Hvsv). Qed.

  Lemma vg_view_args_wk : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq ->
      forall Z RZ ups zs, ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
        List.length zs = List.length Z -> List.length ups = ind_nu D ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
        RZ (env_args (env_args nil ups) zs) (env_args (env_args nil ups) zs) ->
        exists cups cs, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups /\
          ⟦ List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args (env_args nil ups) zs ↘ cs /\
          per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs.
  Proof. destruct (vid_views _ (vgr_valid _ _ Hg)) as [IsS Hvsv]; exact (view_args_wk p D IsS Hg Hcv Hvsv). Qed.
End ValidGroupViews.

End Fixed_GCtx.
