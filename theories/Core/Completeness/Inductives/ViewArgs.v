(** * The Arguments of a View's Constructor, Against its Container's

    A view [k] of a valid group [D] views the member [kc] of its
    container [Dq] at the instance [Is]; the container's member [i'] is
    taken to the group's member [v] ([vm]), and a constructor [c] of both
    has the container's arguments [gs'] and the group's [gs], position by
    position corresponding ([cargs_corr]).  At the group's uniform
    parameters [ups] and the instance's values [cups] there, with the
    values [ms] of the non-uniform parameters related at both, the semantic
    view equation of the arguments ([vg_view_args]) relates, position by
    position, the type of the group's argument to the container's
    ([view_arg_link]).  Hence arguments related at the container's
    non-recursive positions, completed by fresh variables at the positions
    recursive in both, are related at both telescopes
    ([view_args_complete]); and at a position the container has as
    non-recursive and the group as recursive (the view nests through it),
    the container's canonical relation of the argument is the group's
    relation of the shape ([nested_arg_rel_agree]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Section ViewArgs.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Hypothesis (HcvQ : containers_valid Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Variables (ups cups : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member Dq i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).
  Variables (c : String.string) (gs' gs : list carg).
  Hypotheses (Hcon' : ind_con Mi' c = Some gs') (Hcon : ind_con Mv c = Some gs) (Hcorr : cargs_corr vm gs' gs).
  Variable (ms : list domain).
  Hypothesis (Hlms : List.length ms = im_nn Mv).

  Lemma view_cups_rel : per_gargs (List.rev (ind_uparams Dq)) nil nil cups cups.
  Proof.
    destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hc0).
    pose proof (functional_eval_exps' _ _ _ _ E0 Ecups) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Ecups) as ->.
    exact Hc0.
  Qed.

  Lemma length_cups : List.length cups = ind_nu Dq.
  Proof.
    destruct (dt_view _ _ _ (vgr_typed _ _ Hg) _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    rewrite (eval_exps_length _ _ _ Ecups); exact HIl.
  Qed.

  Lemma view_nn : im_nn Mv = im_nn Mi'.
  Proof.
    destruct (dt_vwrap _ _ _ (vgr_typed _ _ Hg) _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (vwo_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
  Qed.

  (** ** The Types at a Position

      At arguments [vs] before a position related at both telescopes, the
      types there have the same head PER, the container's at [cups] and the
      group's at [ups]; both are types, related to each other. *)
  #[warnings="-cannot-define-projection"]
  Record arg_type_link (C G : typ) (Ec Eg : env) : Prop := mk_arg_type_link
    { heads_agree : per_head C C Ec Ec <~> per_head G G Eg Eg
    ; group_type_value : exists (i : nat) R b, ⟦ G ⟧ Eg ↘ b /\ DF b ≈ b ∈ per_univ_elem i ↘ R
    ; container_type_value : exists (i : nat) R a, ⟦ C ⟧ Ec ↘ a /\ DF a ≈ a ∈ per_univ_elem i ↘ R
    ; group_container_types_related : exists (i : nat) R b a, ⟦ G ⟧ Eg ↘ b /\ ⟦ C ⟧ Ec ↘ a /\
        DF b ≈ a ∈ per_univ_elem i ↘ R }.

  Lemma view_arg_link : forall gsA' g' gsB' gsA g gsB C G vs, gs' = gsA' ++ g' :: gsB' -> gs = gsA ++ g :: gsB ->
      List.length gsA = List.length gsA' -> List.length vs = List.length gsA ->
      cargs_ctx qc Dq Mi' (gsA' ++ g' :: nil) = ce_ass C :: cargs_ctx qc Dq Mi' gsA' ->
      cargs_ctx p D Mv (gsA ++ g :: nil) = ce_ass G :: cargs_ctx p D Mv gsA ->
      per_gargs (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)) nil nil (ups ++ ms ++ vs) (ups ++ ms ++ vs) ->
      per_gargs (List.rev (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi')) nil nil (cups ++ ms ++ vs) (cups ++ ms ++ vs) ->
      arg_type_link C G (env_args nil (cups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)).
  Proof.
    intros * Heq' Heq Hlen Hlv HC HG Hg1 Hg2.
    pose proof (vgr_valid _ _ Hg) as HD; pose proof (vgr_closed _ _ HgQ) as HcQ.
    pose proof (cargs_corr_len _ _ _ Hcorr) as Hlg; rewrite Heq', Heq, !List.length_app in Hlg; cbn in Hlg.
    (** The equation of the arguments, cut at the position. *)
    destruct (vg_view_args p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv Hcon' Hcon) as [_ _ [Rx HRx]].
    assert (Ec : cargs_ctx qc Dq Mi' gs' = cargs_ctx_aux qc Dq (im_nn Mi') (cargs_pat (gsA' ++ g' :: nil) ++ nil) gsB'
                                             ++ ce_ass C :: cargs_ctx qc Dq Mi' gsA').
    { rewrite Heq'; replace (gsA' ++ g' :: gsB') with ((gsA' ++ g' :: nil) ++ gsB') by (rewrite <- List.app_assoc; reflexivity).
      unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
      change (cargs_ctx_aux qc Dq (im_nn Mi') nil (gsA' ++ g' :: nil)) with (cargs_ctx qc Dq Mi' (gsA' ++ g' :: nil)).
      rewrite HC; reflexivity. }
    assert (Eg : cargs_ctx p D Mv gs = cargs_ctx_aux p D (im_nn Mv) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB
                                         ++ ce_ass G :: cargs_ctx p D Mv gsA).
    { rewrite Heq; replace (gsA ++ g :: gsB) with ((gsA ++ g :: nil) ++ gsB) by (rewrite <- List.app_assoc; reflexivity).
      unfold cargs_ctx at 1; rewrite cargs_ctx_aux_app.
      change (cargs_ctx_aux p D (im_nn Mv) nil (gsA ++ g :: nil)) with (cargs_ctx p D Mv (gsA ++ g :: nil)).
      rewrite HG; reflexivity. }
    rewrite Ec, Eg, tele_sub_app in HRx; cbn [tele_sub centry_sub List.length] in HRx.
    rewrite <- !List.app_assoc in HRx; cbn [List.app] in HRx.
    assert (Hlt : List.length (tele_sub (cargs_ctx_aux qc Dq (im_nn Mi') (cargs_pat (gsA' ++ g' :: nil) ++ nil) gsB')
                                (sb_qn (S (List.length (cargs_ctx qc Dq Mi' gsA'))) (sb_qn (im_nn Mv) (sb_of_list Id Is))))
                  = List.length (cargs_ctx_aux p D (im_nn Mv) (cargs_pat (gsA ++ g :: nil) ++ nil) gsB))
      by (rewrite length_tele_sub, !length_cargs_ctx_aux; lia).
    destruct (per_ctx_env_app_tail _ _ _ _ _ Hlt HRx) as (RT & HRT).
    destruct (per_ctx_env_ass_inv _ _ _ _ _ HRT) as (RT0 & HRT0 & _ & Hty).
    (** The group's prefix, at the arguments. *)
    destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gs HMv Hcon gsA (g :: gsB) Heq) as [HWg _].
    destruct (rel_ctx_wf_per_ctx_env HWg) as [RG HRG].
    assert (HρG : RG (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs))).
    { apply (gargs_env_rel _ _ _ _ _ _ HRG HWg); [| exact Hg1 ].
      rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np; lia. }
    assert (E0 : RG <~> RT0)
      by (destruct (per_ctx_env_sym _ _ _ HRT0) as [HRT0' _]; eapply per_ctx_env_right_irrel; [ exact HRG | exact HRT0' ]).
    destruct (Hty _ _ (proj1 (E0 _ _) HρG)) as (i0 & R0 & [a1 b Ea1 Eb HR0]).
    (** The container's type, at its arguments over [cups]. *)
    destruct (vg_cargs_sem_all qc Dq HgQ HcvQ i' Mi' c gs' HMi' Hcon' (gsA' ++ g' :: nil) gsB'
                ltac:(rewrite <- List.app_assoc; exact Heq')) as [HWc1 _].
    rewrite HC in HWc1.
    destruct (rel_ctx_wf_ass_inv HWc1) as [ic HCv].
    pose proof (rel_ctx_wf_tail HWc1) as HWc.
    set (Δc := cargs_ctx qc Dq Mi' gsA' ++ im_nparams Mi').
    assert (EΔc : cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi' = Δc ++ ind_uparams Dq)
      by (unfold Δc, im_params; rewrite <- List.app_assoc; reflexivity).
    assert (HaC : tele_ass (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi'))
      by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass Dq HcQ _ _ HMi') ]).
    pose proof (vid_uparams _ HD) as HUD.
    destruct (closed_app_sem _ (ind_uparams D) HaC HWc HUD) as [HWcU _].
    pose proof (closed_app_valid _ (ind_uparams D) _ _ _ HaC HWc HUD HCv) as HCvU.
    rewrite EΔc, <- List.app_assoc in HWcU, HCvU.
    assert (HaΔc : tele_ass Δc) by (rewrite EΔc in HaC; apply List.Forall_app in HaC as [HaC _]; exact HaC).
    destruct (gsub_props (vg_view_args_gsub p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq)) as [Hτ _].
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil ups)) Ecups) as Eτ.
    (** The arguments over [cups] at the container's prefix, moved to the
        base of the instance. *)
    pose proof (dc_ass _ HcQ) as HaQ.
    pose proof (vid_uparams _ (vgr_valid _ _ HgQ)) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (Hlc : List.length cups = List.length (ind_uparams Dq)) by (rewrite length_cups; reflexivity).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)).
    { assert (HUQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HUQ).
      apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ Hlc view_cups_rel). }
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ HaQ HUQ HRQ Hlc Hlc HQ0).
    assert (Hgc0 : per_gargs (List.rev Δc) (env_args nil cups) (env_args nil cups) (ms ++ vs) (ms ++ vs)).
    { rewrite EΔc, List.rev_app_distr in Hg2.
      assert (Hlr : List.length cups = List.length (List.rev (ind_uparams Dq))) by (rewrite List.length_rev; exact Hlc).
      destruct (per_gargs_app (List.rev (ind_uparams Dq)) (List.rev Δc) nil nil cups cups (ms ++ vs) (ms ++ vs) Hlr Hg2 Hlr)
        as [_ H]; exact H. }
    assert (HWΔ : ⊨ List.rev (List.rev Δc) ++ ind_uparams Dq) by (rewrite List.rev_involutive, <- EΔc; exact HWc).
    pose proof (per_gargs_base _ _ _ HRQ HWΔ (List.Forall_rev HaΔc) _ _ _ _ _ _ HQ0 HQ1 HQ1 Hgc0) as Hgc1.
    assert (Hlx : List.length (ms ++ vs) = List.length Δc)
      by (unfold Δc; rewrite !List.length_app, length_cargs_ctx, length_im_nparams; pose proof view_nn; lia).
    destruct (outer_typ_link Δc (ind_uparams Dq ++ ind_uparams D) (ind_uparams D) RU (sb_of_list Id Is) (env_args nil ups)
                (env_args (env_args nil ups) cups) C C ic HaΔc HWcU HCvU HRU Hτ HρU Eτ (ms ++ vs) Hgc1 Hlx)
      as (a2 & b2 & Ea2 & Eb2 & [R2 HR2]).
    rewrite <- env_args_app in Ea2.
    assert (EC : C[sb_qn (List.length Δc) (sb_of_list Id Is)]
                 = C[sb_qn (List.length (cargs_ctx qc Dq Mi' gsA')) (sb_qn (im_nn Mv) (sb_of_list Id Is))])
      by (rewrite <- sb_qn_plus; unfold Δc; rewrite List.length_app, length_im_nparams, view_nn; reflexivity).
    rewrite EC in Ea2.
    pose proof (functional_eval_exp _ _ _ _ Ea2 Ea1) as ->.
    (** From the instance's base to none: the container's telescope is
        closed. *)
    destruct (rel_ctx_wf_per_ctx_env HWc) as [RK HRK].
    assert (Hl3 : List.length (cups ++ ms ++ vs) = List.length (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi'))
      by (rewrite !List.length_app, length_cargs_ctx, length_im_params, length_cups; pose proof view_nn;
          unfold im_np, ind_nu in *; lia).
    assert (HKF : RK (env_args nil (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs)))
      by exact (gargs_env_rel _ _ _ _ _ _ HRK HWc Hl3 Hg2).
    assert (HKF' : RK (env_args (env_args nil ups) (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs)))
      by exact (closed_env_base _ _ _ _ nil nil (env_args nil ups) nil HaC HWc HRK Hl3 Hl3 HKF).
    destruct (rel_exp_of_typ_inversion_simple_at HRK HCv _ _ HKF') as (c1 & c2 & Ec1 & Ec2 & [Rk HRk]).
    replace (env_args (env_args (env_args nil ups) cups) (ms ++ vs)) with (env_args (env_args nil ups) (cups ++ ms ++ vs))
      in Eb2 by (rewrite env_args_app; reflexivity).
    clear HRx Ec Eg Hlt HRT HRT0 Hty HRG HρG E0 Hgc0 Hgc1 HWcU HCvU HQ0 HQ1 Ea2.
    pose proof (functional_eval_exp _ _ _ _ Eb2 Ec1) as ->.
    constructor.
    - etransitivity; [ symmetry; exact (per_head_right Ec1 Ec2 HRk) |].
      etransitivity; [ symmetry; exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR2 HRk) |].
      etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR2 | exact HR0 ] |].
      exact (per_head_right Ea1 Eb HR0).
    - exists i0, R0, b; split; [ exact Eb |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR0) HR0).
    - exists ic, Rk, c2; split; [ exact Ec2 |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRk) HRk).
    - (** One relation, at a common level, from the group's type to the
          container's. *)
        pose proof (per_univ_elem_cumu_max_left i0 ic _ _ _ HR0) as HR0n.
        pose proof (per_univ_elem_cumu_max_right i0 ic _ _ _ HR2) as HR2n.
        pose proof (per_univ_elem_cumu_max_right i0 ic _ _ _ HRk) as HRkn.
        assert (E20 : R2 <~> R0) by (eapply per_univ_elem_right_irrel; [ exact HR2 | exact HR0 ]).
        assert (E2k : R2 <~> Rk) by exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR2 HRk).
        pose proof (per_univ_elem_resp_iff HR2n E20) as H2.
        assert (Ek0 : Rk <~> R0) by (etransitivity; [ symmetry; exact E2k | exact E20 ]).
        pose proof (per_univ_elem_resp_iff HRkn Ek0) as H3.
        exists (max i0 ic), R0, b, c2; split; [ exact Eb | split; [ exact Ec2 |] ].
        exact (per_univ_trans _ _ _ _ _ _ (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR0n) H2) H3).
  Qed.

  (** ** Arguments Related at Both Telescopes

      Arguments [vp] whose values at the container's non-recursive
      positions are related canonically give arguments [vs] related at the
      group's telescope over [ups] and at the container's over [cups]: [vs]
      is [vp] at the container's non-recursive positions and a fresh
      variable at the positions recursive in both. *)
  Hypotheses (Hms_g : per_gargs (List.rev (im_params D Mv)) nil nil (ups ++ ms) (ups ++ ms))
    (Hms_c : per_gargs (List.rev (im_params Dq Mi')) nil nil (cups ++ ms) (cups ++ ms)).

  #[warnings="-cannot-define-projection"]
  Record view_args_inv (gsA' gsA : list carg) (vp vs : list domain) : Prop := mk_view_args_inv
    { vai_len : List.length vs = List.length gsA
    ; vai_nonrec_c : nonrec_arg_vals gsA' vs = nonrec_arg_vals gsA' vp
    ; vai_nonrec_g : nonrec_arg_vals gsA vs = nonrec_arg_vals gsA vp
    ; vai_grp : per_gargs (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)) nil nil (ups ++ ms ++ vs) (ups ++ ms ++ vs)
    ; vai_cnt : per_gargs (List.rev (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi')) nil nil (cups ++ ms ++ vs) (cups ++ ms ++ vs)
    ; vai_args : tele_prefix_rel (canon_args_rel D ups v ms c) (List.length (cargs_nonrec gsA))
        (nonrec_arg_vals gsA vs) (nonrec_arg_vals gsA vs) }.

  Lemma cargs_corr_split : forall gs1' gs2' gs1 gs2, cargs_corr vm (gs1' ++ gs2') (gs1 ++ gs2) ->
      List.length gs1' = List.length gs1 -> cargs_corr vm gs1' gs1 /\ cargs_corr vm gs2' gs2.
  Proof.
    induction gs1' as [| g' gs1' IH]; intros gs2' gs1 gs2 H Hl; destruct gs1 as [| g gs1]; cbn in Hl; try discriminate;
      [ split; [ exact I | exact H ] |].
    destruct g' as [A' | t'], g as [A | t]; cbn in H |- *; try contradiction.
    - exact (IH _ _ _ H ltac:(lia)).
    - exact (IH _ _ _ H ltac:(lia)).
    - destruct H as (Hm & Hd & H); destruct (IH _ _ _ H ltac:(lia)) as [H1 H2].
      split; [ exact (conj Hm (conj Hd H1)) | exact H2 ].
  Qed.

  Lemma gargs_snoc_entry : forall ts E zs G x (i : nat) R b, List.length zs = List.length ts -> per_gargs ts E E zs zs ->
      ⟦ G ⟧ env_args E zs ↘ b -> DF b ≈ b ∈ per_univ_elem i ↘ R -> R x x ->
      per_gargs (ts ++ ce_ass G :: nil) E E (zs ++ x :: nil) (zs ++ x :: nil).
  Proof. intros * Hl Hgs Eb HR Hx; eapply per_gargs_snoc; [ exact Hl | exact Hgs | econstructor; eassumption | exact Hx ]. Qed.

  Lemma view_args_complete : forall gsA gsA' gsB' gsB vp, gs' = gsA' ++ gsB' -> gs = gsA ++ gsB -> cargs_corr vm gsA' gsA ->
      List.length vp = List.length gsA ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gsA'))
        (nonrec_arg_vals gsA' vp) (nonrec_arg_vals gsA' vp) ->
      exists vs, view_args_inv gsA' gsA vp vs.
  Proof.
    pose proof view_nn as Hnn.
    induction gsA as [| g gsA IH] using List.rev_ind; intros gsA' gsB' gsB vp Heq' Heq Hc Hlp Hpre.
    - destruct gsA' as [| g' gsA']; [| destruct g'; cbn in Hc; contradiction ].
      destruct vp; [| discriminate ].
      exists nil; constructor; cbn [List.length nonrec_arg_vals cargs_nonrec]; try reflexivity.
      + unfold cargs_ctx; cbn [cargs_ctx_aux List.app]; rewrite List.app_nil_r; exact Hms_g.
      + unfold cargs_ctx; cbn [cargs_ctx_aux List.app]; rewrite List.app_nil_r; exact Hms_c.
      + rewrite tele_prefix_rel_iff; split; [ reflexivity | split; [ reflexivity |] ]; intros [|] ? ? H; discriminate.
    - pose proof (cargs_corr_len _ _ _ Hc) as HlA; rewrite List.length_app in HlA; cbn in HlA.
      destruct (List.exists_last (l := gsA') ltac:(intros ->; cbn in HlA; lia)) as (gsA0' & g' & ->).
      rewrite List.length_app in HlA; cbn in HlA.
      destruct (cargs_corr_split _ _ _ _ Hc ltac:(lia)) as [Hc0 Hc1].
      rewrite List.length_app in Hlp; cbn in Hlp.
      destruct (List.exists_last (l := vp) ltac:(intros ->; cbn in Hlp; lia)) as (vp0 & x & ->).
      rewrite List.length_app in Hlp; cbn in Hlp.
      rewrite <- List.app_assoc in Heq', Heq; cbn [List.app] in Heq', Heq.
      assert (Hlc0 : List.length vp0 = List.length gsA0') by lia.
      rewrite cargs_nonrec_app, nonrec_arg_vals_app in Hpre by exact Hlc0.
      assert (HK0 : List.length (nonrec_arg_vals gsA0' vp0) = List.length (cargs_nonrec gsA0'))
        by exact (length_nonrec_arg_vals _ _ Hlc0).
      assert (Hpre0 : tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gsA0'))
                        (nonrec_arg_vals gsA0' vp0) (nonrec_arg_vals gsA0' vp0)).
      { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec gsA0')) Hpre ltac:(rewrite List.length_app; lia)) as H.
        rewrite !firstn_app_exact in H by exact HK0; exact H. }
      destruct (IH gsA0' (g' :: gsB') (g :: gsB) vp0 Heq' Heq Hc0 ltac:(lia) Hpre0) as [vs0 [Hl0 Hn0 Hn0g Hg0 Hcn0 Ha0]].
      pose proof (cargs_ctx_snoc qc Dq Mi' gsA0' g') as ECc; pose proof (cargs_ctx_snoc p D Mv gsA g) as ECg.
      assert (Hl0' : List.length vs0 = List.length gsA0') by lia.
      assert (HlU : List.length (ups ++ ms ++ vs0) = List.length (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      assert (HlC : List.length (cups ++ ms ++ vs0) = List.length (List.rev (cargs_ctx qc Dq Mi' gsA0' ++ im_params Dq Mi')))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params, length_cups; unfold im_np, ind_nu in *; lia).
      destruct g' as [A' | t'], g as [A | t]; cbn in Hc1; try contradiction; cbn [cargs_ctx_aux List.app] in ECc, ECg.
      + (** Non-recursive in both. *)
        pose proof (view_arg_link gsA0' _ gsB' gsA _ gsB _ _ vs0 Heq' Heq ltac:(lia) Hl0 ECc ECg Hg0 Hcn0)
          as HL;
          pose proof (heads_agree _ _ _ _ HL) as EL;
          destruct (group_type_value _ _ _ _ HL) as (ig & Rg & bg & Ebg & HRg);
          destruct (container_type_value _ _ _ _ HL) as (ic & Rc & ac & Eac & HRc).
        destruct (vg_arg_head qc Dq HgQ HcvQ i' Mi' c gs' gsA0' A' gsB' cups ms vs0 HMi' Hcon' Heq' length_cups ltac:(lia) Hl0' Hcn0)
          as (i1 & R1 & a1 & Ea1 & HR1 & E1).
        destruct (vg_arg_head p D Hg Hcv v Mv c gs gsA A gsB ups ms vs0 HMv Hcon Heq Hu Hlms Hl0 Hg0)
          as (i2 & R2 & a2 & Ea2 & HR2 & E2).
        pose proof (functional_eval_exp _ _ _ _ Ea1 Eac) as <-; pose proof (functional_eval_exp _ _ _ _ Ea2 Ebg) as <-.
        assert (Hxc : canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gsA0')) (nonrec_arg_vals gsA0' vs0) x x).
        { rewrite Hn0; rewrite tele_prefix_rel_iff in Hpre; destruct Hpre as (_ & _ & Hr).
          cbn [nonrec_arg_vals] in Hr.
          assert (Ex : List.nth_error (nonrec_arg_vals gsA0' vp0 ++ x :: nil) (List.length (cargs_nonrec gsA0')) = Some x)
            by (rewrite List.nth_error_app2, HK0, Nat.sub_diag by lia; reflexivity).
          pose proof (Hr _ _ _ Ex Ex) as H; rewrite firstn_app_exact in H by exact HK0; exact H. }
        assert (Hx1 : R1 x x) by (apply E1; exact Hxc).
        assert (Hxg : per_head (A[wk_pat (cargs_pat gsA)]ʷ) (A[wk_pat (cargs_pat gsA)]ʷ) (env_args nil (ups ++ ms ++ vs0))
                        (env_args nil (ups ++ ms ++ vs0)) x x)
          by (apply EL, (per_head_left Ea1 Ea1 HR1); exact Hx1).
        exists (vs0 ++ x :: nil); constructor.
        * rewrite !List.length_app; cbn; lia.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0; reflexivity.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0g; reflexivity.
        * rewrite ECg; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc ups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ x _ _ _ HlU Hg0 Ea2 HR2 (proj2 (per_head_left Ea2 Ea2 HR2 _ _) Hxg)).
        * rewrite ECc; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc cups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ x _ _ _ HlC Hcn0 Ea1 HR1 Hx1).
        * rewrite cargs_nonrec_app, nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals]; rewrite List.length_app.
          cbn [List.length]; rewrite Nat.add_1_r.
          apply tele_prefix_rel_snoc; [ exact Ha0 |].
          apply E2; apply (per_head_left Ea2 Ea2 HR2); exact Hxg.
      + (** Non-recursive in the container, recursive in the group: the
            view nests through it. *)
        pose proof (view_arg_link gsA0' _ gsB' gsA _ gsB _ _ vs0 Heq' Heq ltac:(lia) Hl0 ECc ECg Hg0 Hcn0)
          as HL;
          pose proof (heads_agree _ _ _ _ HL) as EL;
          destruct (group_type_value _ _ _ _ HL) as (ig & Rg & bg & Ebg & HRg);
          destruct (container_type_value _ _ _ _ HL) as (ic & Rc & ac & Eac & HRc).
        destruct (vg_arg_head qc Dq HgQ HcvQ i' Mi' c gs' gsA0' A' gsB' cups ms vs0 HMi' Hcon' Heq' length_cups ltac:(lia) Hl0' Hcn0)
          as (i1 & R1 & a1 & Ea1 & HR1 & E1).
        pose proof (functional_eval_exp _ _ _ _ Ea1 Eac) as <-.
        assert (Hxc : canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gsA0')) (nonrec_arg_vals gsA0' vs0) x x).
        { rewrite Hn0; rewrite tele_prefix_rel_iff in Hpre; destruct Hpre as (_ & _ & Hr).
          cbn [nonrec_arg_vals] in Hr.
          assert (Ex : List.nth_error (nonrec_arg_vals gsA0' vp0 ++ x :: nil) (List.length (cargs_nonrec gsA0')) = Some x)
            by (rewrite List.nth_error_app2, HK0, Nat.sub_diag by lia; reflexivity).
          pose proof (Hr _ _ _ Ex Ex) as H; rewrite firstn_app_exact in H by exact HK0; exact H. }
        assert (Hx1 : R1 x x) by (apply E1; exact Hxc).
        assert (Hxg : Rg x x) by (apply (per_head_left Ebg Ebg HRg), EL, (per_head_left Ea1 Ea1 HR1); exact Hx1).
        exists (vs0 ++ x :: nil); constructor.
        * rewrite !List.length_app; cbn; lia.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0; reflexivity.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0g; reflexivity.
        * rewrite ECg; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc ups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ x _ _ _ HlU Hg0 Ebg HRg Hxg).
        * rewrite ECc; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc cups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ x _ _ _ HlC Hcn0 Ea1 HR1 Hx1).
        * rewrite cargs_nonrec_app, nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals].
          rewrite !List.app_nil_r; exact Ha0.
      + (** Recursive in both: a fresh variable. *)
        pose proof (view_arg_link gsA0' _ gsB' gsA _ gsB _ _ vs0 Heq' Heq ltac:(lia) Hl0 ECc ECg Hg0 Hcn0)
          as HL;
          pose proof (heads_agree _ _ _ _ HL) as EL;
          destruct (group_type_value _ _ _ _ HL) as (ig & Rg & bg & Ebg & HRg);
          destruct (container_type_value _ _ _ _ HL) as (ic & Rc & ac & Eac & HRc).
        set (y := ⇑! bg 0).
        assert (Hyg : Rg y y) by exact (var_per_elem 0 HRg).
        assert (Hyc : Rc y y) by (apply (per_head_left Eac Eac HRc), EL, (per_head_left Ebg Ebg HRg); exact Hyg).
        exists (vs0 ++ y :: nil); constructor.
        * rewrite !List.length_app; cbn; lia.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0; reflexivity.
        * rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals]; rewrite Hn0g; reflexivity.
        * rewrite ECg; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc ups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ y _ _ _ HlU Hg0 Ebg HRg Hyg).
        * rewrite ECc; cbn [List.app List.rev]; rewrite (List.app_assoc ms vs0), (List.app_assoc cups (ms ++ vs0)).
          exact (gargs_snoc_entry _ _ _ _ y _ _ _ HlC Hcn0 Eac HRc Hyc).
        * rewrite cargs_nonrec_app, nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals].
          rewrite !List.app_nil_r; exact Ha0.
  Qed.

  (** ** An Argument the View Nests Through

      Non-recursive in the container, of a shape [t] in the group: the
      container's canonical relation of the argument is the group's
      relation of the shape, given the relation of the type of the member
      the shape ends in ([view_end_rel]). *)
  Lemma nested_arg_rel_agree : forall gs1' A' gs2' gs1 t gs2 vp, gs' = gs1' ++ ca_arg A' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) ms ms ->
      view_end_rel p D ups ups (ptyp_mem t) ->
      (canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp)
         <~> rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups)
               (canon_doms_rel ups) v ups ups (ms ++ nonrec_arg_vals gs1 vp) (ms ++ nonrec_arg_vals gs1 vp) t).
  Proof.
    intros * Heq' Heq Hc Hlp Hpre Hnsd Hend.
    pose proof view_nn as Hnn.
    pose proof (cargs_corr_len _ _ _ Hc) as Hl1.
    destruct (view_args_complete gs1 gs1' (ca_arg A' :: gs2') (ca_rec t :: gs2) vp Heq' Heq Hc Hlp Hpre)
      as (vs & [Hl Hn Hng Hg1 Hcn Ha]).
    pose proof (cargs_ctx_snoc qc Dq Mi' gs1' (ca_arg A')) as ECc; pose proof (cargs_ctx_snoc p D Mv gs1 (ca_rec t)) as ECg.
    cbn [cargs_ctx_aux List.app] in ECc, ECg.
    pose proof (view_arg_link gs1' _ gs2' gs1 _ gs2 _ _ vs Heq' Heq ltac:(lia) Hl ECc ECg Hg1 Hcn)
      as HL;
          pose proof (heads_agree _ _ _ _ HL) as EL;
          destruct (group_type_value _ _ _ _ HL) as (ig & Rg & bg & Ebg & HRg);
          destruct (container_type_value _ _ _ _ HL) as (ic & Rc & ac & Eac & HRc).
    destruct (vg_arg_head qc Dq HgQ HcvQ i' Mi' c gs' gs1' A' gs2' cups ms vs HMi' Hcon' Heq' length_cups ltac:(lia) ltac:(lia) Hcn)
      as (i1 & R1 & a1 & Ea1 & HR1 & E1).
    pose proof (functional_eval_exp _ _ _ _ Ea1 Eac) as <-.
    (** The group's side: the shape's relation, by [shape_char]. *)
    pose proof (vg_cargs_sem p D Hg Hcv v Mv c gs HMv Hcon) as HΨ.
    destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gs HMv Hcon gs1 (ca_rec t :: gs2) Heq) as [HW1 _].
    assert (HpreR : forall R, EF cargs_ctx p D Mv gs1 ++ im_params D Mv ≈ cargs_ctx p D Mv gs1 ++ im_params D Mv ∈ per_ctx_env ↘ R ->
                      R (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs))).
    { intros R HR; apply (gargs_env_rel _ _ _ _ _ _ HR HW1); [| exact Hg1 ].
      rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
    assert (Hy0 : tele_prefix_rel (shape_doms_rel (canon_doms_rel ups v) ms (nonrec_arg_vals gs1 vs) (ptyp_doms t)) 0 nil nil)
      by (rewrite tele_prefix_rel_iff; split; [ reflexivity | split; [ reflexivity |] ]; intros [|] ? ? H; discriminate).
    assert (Hgy0 : per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn 0 (ptyp_doms t))))
                     (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)) nil nil) by (cbn; constructor).
    assert (Ebg0 : ⟦ ptyp_ty p D (im_nn Mv) (List.repeat false 0 ++ cargs_pat gs1) (ptyp_skip 0 t) ⟧
                     env_args nil (ups ++ ms ++ vs ++ nil) ↘ bg) by (rewrite List.app_nil_r; exact Ebg).
    pose proof (shape_char p D Hg Hcv v Mv c gs HMv Hcon HΨ gs1 t gs2 Heq ups ms vs Hu Hlms Hl Hgu Hnsd Ha HpreR Hend
                  (List.length (ptyp_doms t)) 0 nil bg ig Rg eq_refl Hy0 Hgy0 Ebg0 HRg) as Hsh.
    rewrite List.app_nil_r in Hsh; cbn [ptyp_skip] in Hsh.
    rewrite <- Hn, <- Hng.
    intros x y; split; intro Hxy.
    - apply Hsh, (per_head_left Ebg Ebg HRg), EL, (per_head_left Ea1 Ea1 HR1), E1; exact Hxy.
    - apply E1, (per_head_left Ea1 Ea1 HR1), EL, (per_head_left Ebg Ebg HRg), Hsh; exact Hxy.
  Qed.

  (** ** An Argument Non-Recursive in Both

      The container's canonical relation of the argument is the group's. *)
  Lemma view_arg_rel : forall gs1' A' gs2' gs1 A gs2 vp, gs' = gs1' ++ ca_arg A' :: gs2' -> gs = gs1 ++ ca_arg A :: gs2 ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      (canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp)
         <~> canon_args_rel D ups v ms c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp)).
  Proof.
    intros * Heq' Heq Hc Hlp Hpre.
    pose proof view_nn as Hnn.
    pose proof (cargs_corr_len _ _ _ Hc) as Hl1.
    destruct (view_args_complete gs1 gs1' (ca_arg A' :: gs2') (ca_arg A :: gs2) vp Heq' Heq Hc Hlp Hpre)
      as (vs & [Hl Hn Hng Hg1 Hcn Ha]).
    pose proof (cargs_ctx_snoc qc Dq Mi' gs1' (ca_arg A')) as ECc; pose proof (cargs_ctx_snoc p D Mv gs1 (ca_arg A)) as ECg.
    cbn [cargs_ctx_aux List.app] in ECc, ECg.
    pose proof (view_arg_link gs1' _ gs2' gs1 _ gs2 _ _ vs Heq' Heq ltac:(lia) Hl ECc ECg Hg1 Hcn) as HL; pose proof (heads_agree _ _ _ _ HL) as EL.
    destruct (vg_arg_head qc Dq HgQ HcvQ i' Mi' c gs' gs1' A' gs2' cups ms vs HMi' Hcon' Heq' length_cups ltac:(lia) ltac:(lia) Hcn)
      as (i1 & R1 & a1 & Ea1 & HR1 & E1).
    destruct (vg_arg_head p D Hg Hcv v Mv c gs gs1 A gs2 ups ms vs HMv Hcon Heq Hu Hlms Hl Hg1)
      as (i2 & R2 & a2 & Ea2 & HR2 & E2).
    rewrite <- Hn, <- Hng.
    intros x y; split; intro Hxy.
    - apply E2, (per_head_left Ea2 Ea2 HR2), EL, (per_head_left Ea1 Ea1 HR1), E1; exact Hxy.
    - apply E1, (per_head_left Ea1 Ea1 HR1), EL, (per_head_left Ea2 Ea2 HR2), E2; exact Hxy.
  Qed.

  (** ** The Non-Uniform Parameters

      The container's canonical relation of a non-uniform parameter at
      [cups] is the group's at [ups] of the member the view takes the
      container's to ([agree_nparams_rel] at the canonical relations). *)
  Lemma view_nparams_rel : forall j vs vs', j < im_nn Mi' -> tele_prefix_rel (canon_nparams_rel Dq cups i') j vs vs' ->
      (canon_nparams_rel Dq cups i' j vs <~> canon_nparams_rel D ups v j vs).
  Proof.
    intros j vs vs' Hj Hp.
    pose proof view_nn as Hnn.
    pose proof (vgr_valid _ _ Hg) as HD; pose proof (vgr_closed _ _ Hg) as Hc.
    pose proof (vgr_valid _ _ HgQ) as HDQ; pose proof (vgr_closed _ _ HgQ) as HcQ; pose proof (vgr_sort _ _ HgQ) as HsuQ.
    destruct (vg_canon qc Dq HgQ cups view_cups_rel length_cups) as [CnP CnI CaP CaI CdP CdI].
    set (tc := List.rev (im_nparams Mi')); set (tg := List.rev (im_nparams Mv)).
    assert (Hlr : j <= List.length tc) by (unfold tc; rewrite List.length_rev, length_im_nparams; lia).
    assert (Hlv : List.length vs = j) by (rewrite tele_prefix_rel_iff in Hp; tauto).
    pose proof (tele_prefix_rel_refl_l (List.length tc) _
                  (fun k0 a b Hk Ha => nparams_rel_per qc Dq cups _ _ _ (vgr_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' k0 a b Hk Ha)
                  (fun k0 a b Hk Ha => nparams_rel_invariant qc Dq cups _ _ _ (vgr_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' k0 a b Hk Ha)
                  j vs vs' Hlr Hp) as Hpp.
    destruct (sort_value Dq HDQ cups view_cups_rel length_cups) as [aQ EaQ].
    pose proof (nr_gargs Dq HDQ HcQ HsuQ i' Mi' HMi' cups cups aQ view_cups_rel length_cups EaQ j vs vs ltac:(lia) Hpp) as Hg0.
    (** The container's telescope, from no base to the instance's. *)
    pose proof (vid_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (Hlc : List.length cups = List.length (ind_uparams Dq)) by (rewrite length_cups; reflexivity).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)).
    { assert (HUQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HUQ).
      apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ Hlc view_cups_rel). }
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ (dc_ass _ HcQ) HUQ HRQ Hlc Hlc HQ0).
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass Dq HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams Dq) by (unfold tc; rewrite List.rev_involutive; exact (vid_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HDQ _ _ _ _ HMi' HA))).
    destruct (tele_base_change tc (ind_uparams Dq) RQ (env_args nil cups) (env_args (env_args nil ups) cups)
                Hac HWc0 HTc0 HRQ HQ1 j vs Hlv Hlr Hg0) as [Hg1 Hhd].
    (** The two telescopes, equal under the view's instance. *)
    pose proof (vid_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams Dq)) by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (dc_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams Dq ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams Dq))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (dc_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (vid_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HD _ _ _ _ HMv HA))).
    assert (Heq : ind_uparams D ⊨ˣ tele_sub (List.rev tg) Id ≈ tele_sub (List.rev tc) (sb_of_list Id Is)).
    { unfold tg, tc; rewrite !List.rev_involutive, tele_sub_id.
      exact (vg_view_nparams p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv). }
    assert (Hlen : List.length tg = List.length tc) by (unfold tg, tc; rewrite !List.length_rev, !length_im_nparams; exact Hnn).
    destruct (gsub_props (vg_view_args_gsub p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq)) as [Hτ _].
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil ups)) Ecups) as Eτ.
    destruct (nth_error_lt_some' tc j ltac:(unfold tc in *; rewrite List.length_rev, length_im_nparams; lia)) as [eC HeC].
    destruct (proj1 (List.Forall_forall _ _) Hac eC (List.nth_error_In _ _ HeC)) as [C ->].
    destruct (nth_error_lt_some' tg j ltac:(unfold tg in *; rewrite List.length_rev, length_im_nparams; lia)) as [eG HeG].
    destruct (proj1 (List.Forall_forall _ _) Hag eG (List.nth_error_In _ _ HeG)) as [G ->].
    pose proof (tele_link (ind_uparams D) RU (env_args nil ups) HRU HρU (ind_uparams D) (ind_uparams Dq ++ ind_uparams D)
                  Id (sb_of_list Id Is) (env_args nil ups) (env_args (env_args nil ups) cups)
                  (rel_sub_id (ex_intro _ _ HRU)) Hτ (eval_sub_id _) Eτ tg tc Hag Hac Hlen HWg HWc HTg HTc Heq
                  j vs G C Hlv HeG HeC Hg1) as EL.
    unfold canon_nparams_rel, member_nparams; rewrite HMi', HMv; fold tc tg; unfold nth_ctyp; rewrite HeC, HeG.
    rewrite !env_args_app.
    etransitivity; [ exact (Hhd _ HeC) | exact EL ].
  Qed.
End ViewArgs.

End Fixed_GCtx.
