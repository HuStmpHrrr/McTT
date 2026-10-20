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
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import UnitCases.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Section FiledViews.
  Variables (p : qname) (D : ind_decl) (IsS : nat -> list exp).
  Hypotheses (HD : valid_ind_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).
  Hypotheses (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : grp_tele_ass D).
  Hypotheses (Hdt : decl_typed gc_deps gc_stack D) (Hmp : ind_mpath D 0 = Some p).
  Hypothesis (Hvsv : views_self_valid D IsS).
  (** The containers of the views are closed. *)
  Hypothesis (Hcc : forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
                ind_lookup gc_deps gc_stack qc = Some Dq -> decl_closed Dq).

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
    split; [ exact (Hcc _ _ _ _ _ _ _ Hk Hh Hq) |].
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
    pose proof (Hcc _ _ _ _ _ _ _ Hk Hh Hq) as Hc'.
    rewrite (filed_link _ _ _ _ _ _ Hk Hh) in HI, HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (grp_sb p D) (IsS k) (dc_ass _ Hc') (dc_uparams _ Hc')
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HI as (I0 & HI0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (rel_exp_under_ctx_gsub grp_sb_valid (vsv_is _ _ Hvsv _ _ _ _ _ _ _ _ _ _ Hk Hh Hq HI0 HT0)).
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
End FiledViews.

End Fixed_GCtx.
