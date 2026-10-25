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

Lemma cargs_corr_split : forall vm gs1' gs2' gs1 gs2, cargs_corr vm (gs1' ++ gs2') (gs1 ++ gs2) ->
    List.length gs1' = List.length gs1 -> cargs_corr vm gs1' gs1 /\ cargs_corr vm gs2' gs2.
Proof.
  intros vm; induction gs1' as [| g' gs1' IH]; intros gs2' gs1 gs2 H Hl; destruct gs1 as [| g gs1]; cbn in Hl; try discriminate;
    [ split; [ exact I | exact H ] |].
  destruct g' as [A' | t'], g as [A | t]; cbn in H |- *; try contradiction.
  - exact (IH _ _ _ H ltac:(lia)).
  - exact (IH _ _ _ H ltac:(lia)).
  - destruct H as (Hm & Hd & H); destruct (IH _ _ _ H ltac:(lia)) as [H1 H2].
    split; [ exact (conj Hm (conj Hd H1)) | exact H2 ].
Qed.

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
    destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-.
    rewrite (eval_exps_length _ _ _ Ecups); exact HIl.
  Qed.

  Lemma view_nn : im_nn Mv = im_nn Mi'.
  Proof.
    destruct (decl_typed_vwrap _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMk Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (vwrap_ok_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-; exact Hnn.
  Qed.

  (** ** The Types at a Position

      At arguments [vs] before a position related at both telescopes, the
      types there have the same head PER, the container's at [cups] and the
      group's at [ups]; both are types, related to each other. *)
  Record arg_type_link (C G : typ) (Ec Eg : env) : Prop := mk_arg_type_link
    { (** The two head PERs agree *)
      heads_agree : per_head C C Ec Ec <~> per_head G G Eg Eg
      (** The group's type evaluates to a type *)
    ; group_type_value : exists (i : nat) R b, ⟦ G ⟧ Eg ↘ b /\ DF b ≈ b ∈ per_univ_elem i ↘ R
      (** The container's type evaluates to a type *)
    ; container_type_value : exists (i : nat) R a, ⟦ C ⟧ Ec ↘ a /\ DF a ≈ a ∈ per_univ_elem i ↘ R
      (** The two values are related types *)
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
    pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ HgQ) as HcQ.
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
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
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
    pose proof (decl_closed_ass _ HcQ) as HaQ.
    pose proof (valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ)) as HUQ.
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

  (** The invariant of the walk through the arguments: after the prefixes
      [gsA'] and [gsA], the arguments [vs] built from [vp]. *)
  Record view_args_inv (gsA' gsA : list carg) (vp vs : list domain) : Prop := mk_view_args_inv
    { (** One value per argument *)
      view_args_inv_len : List.length vs = List.length gsA
      (** [vs] is [vp] at the container's non-recursive positions *)
    ; view_args_inv_nonrec_c : nonrec_arg_vals gsA' vs = nonrec_arg_vals gsA' vp
      (** and at the group's *)
    ; view_args_inv_nonrec_g : nonrec_arg_vals gsA vs = nonrec_arg_vals gsA vp
      (** [vs] is related at the group's telescope over [ups] *)
    ; view_args_inv_grp : per_gargs (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)) nil nil (ups ++ ms ++ vs) (ups ++ ms ++ vs)
      (** and at the container's over [cups] *)
    ; view_args_inv_cnt : per_gargs (List.rev (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi')) nil nil (cups ++ ms ++ vs) (cups ++ ms ++ vs)
      (** Its non-recursive values are related canonically *)
    ; view_args_inv_args : tele_prefix_rel (canon_args_rel D ups v ms c) (List.length (cargs_nonrec gsA))
        (nonrec_arg_vals gsA vs) (nonrec_arg_vals gsA vs) }.

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
      destruct (cargs_corr_split _ _ _ _ _ Hc ltac:(lia)) as [Hc0 Hc1].
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

  (** ** An Argument Recursive in Both: its Shape, Domain by Domain

      Through the domains of the two shapes: after [kk] domains [ys]
      related at both telescopes of domains, the types of the rests of the
      shapes are related to each other. *)
  Record shape_walk_state (gs1' gs1 : list carg) (t' t : ptyp) (vs : list domain) (kk : nat) (ys : list domain) : Prop :=
    mk_shape_walk_state
    { (** [ys] is related at the group shape's first [kk] domains *)
      walk_group_doms : per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
        (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)) ys ys
      (** and at the container shape's *)
    ; walk_container_doms : per_gargs (List.rev (sh_ctx (cargs_pat gs1') (List.firstn kk (ptyp_doms t'))))
        (env_args nil (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs)) ys ys
      (** The types of the rests of the two shapes are related *)
    ; walk_types_related : exists (i : nat) R ag ac,
        ⟦ ptyp_ty p D (im_nn Mv) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) ⟧ env_args nil (ups ++ ms ++ vs ++ ys) ↘ ag /\
        ⟦ ptyp_ty qc Dq (im_nn Mi') (List.repeat false kk ++ cargs_pat gs1') (ptyp_skip kk t') ⟧ env_args nil (cups ++ ms ++ vs ++ ys) ↘ ac /\
        DF ag ≈ ac ∈ per_univ_elem i ↘ R }.

  Lemma view_shape_walk : forall gs1' t' gs2' gs1 t gs2 vp vs, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
      cargs_corr vm gs1' gs1 -> view_args_inv gs1' gs1 vp vs ->
      forall kk ys, kk <= List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) kk ys ys ->
        shape_walk_state gs1' gs1 t' t vs kk ys.
  Proof.
    intros gs1' t' gs2' gs1 t gs2 vp vs Heq' Heq Hc [Hl Hn Hng Hg1 Hcn Ha].
    pose proof view_nn as Hnn.
    pose proof (cargs_corr_len _ _ _ Hc) as Hl1.
    assert (HlD : List.length (ptyp_doms t') = List.length (ptyp_doms t)).
    { rewrite Heq', Heq in Hcorr; destruct (cargs_corr_split _ _ _ _ _ Hcorr ltac:(lia)) as [_ H].
      cbn in H; destruct H as (_ & Hd & _); unfold ptyp_depth in Hd; exact Hd. }
    assert (Hgp : forall kk ys, per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
                    (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)) ys ys ->
                  per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv))
                    nil nil (ups ++ ms ++ vs ++ ys) (ups ++ ms ++ vs ++ ys)).
    { intros kk ys H; rewrite List.rev_app_distr.
      replace (ups ++ ms ++ vs ++ ys) with ((ups ++ ms ++ vs) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro; [| exact Hg1 | exact H ].
      rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
    assert (Hcp : forall kk ys, per_gargs (List.rev (sh_ctx (cargs_pat gs1') (List.firstn kk (ptyp_doms t'))))
                    (env_args nil (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs)) ys ys ->
                  per_gargs (List.rev (sh_ctx (cargs_pat gs1') (List.firstn kk (ptyp_doms t')) ++ cargs_ctx qc Dq Mi' gs1' ++ im_params Dq Mi'))
                    nil nil (cups ++ ms ++ vs ++ ys) (cups ++ ms ++ vs ++ ys)).
    { intros kk ys H; rewrite List.rev_app_distr.
      replace (cups ++ ms ++ vs ++ ys) with ((cups ++ ms ++ vs) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro; [| exact Hcn | exact H ].
      rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params, length_cups; unfold im_np, ind_nu in *; lia. }
    induction kk as [| kk IH]; intros ys Hk Hy.
    - destruct ys as [| y0 ys]; [| rewrite tele_prefix_rel_iff in Hy; destruct Hy as [Hy _]; discriminate ].
      pose proof (cargs_ctx_snoc qc Dq Mi' gs1' (ca_rec t')) as ECc; pose proof (cargs_ctx_snoc p D Mv gs1 (ca_rec t)) as ECg.
      cbn [cargs_ctx_aux List.app] in ECc, ECg.
      pose proof (view_arg_link gs1' _ gs2' gs1 _ gs2 _ _ vs Heq' Heq ltac:(lia) Hl ECc ECg Hg1 Hcn) as HL.
      destruct (group_container_types_related _ _ _ _ HL) as (i & R & ag & ac & Eag & Eac & HR).
      constructor; [ cbn; constructor | cbn; constructor |].
      exists i, R, ag, ac; rewrite !List.app_nil_r; cbn [List.repeat List.app ptyp_skip].
      split; [ exact Eag | split; [ exact Eac | exact HR ] ].
    - destruct (List.exists_last (l := ys) ltac:(intros ->; rewrite tele_prefix_rel_iff in Hy; destruct Hy as [Hy _]; discriminate))
        as (ys0 & y & ->).
      pose proof Hy as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (Hly & _ & Hyr).
      rewrite List.length_app in Hly; cbn in Hly.
      assert (Hly0 : List.length ys0 = kk) by lia.
      assert (Hy0 : tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) kk ys0 ys0).
      { pose proof (tele_prefix_rel_of_pre _ _ _ _ kk Hy ltac:(lia)) as H.
        rewrite !firstn_app_exact in H by exact Hly0; exact H. }
      destruct (IH ys0 ltac:(lia) Hy0) as [Hgd Hcd (i & R & ag & ac & Eag & Eac & HR)].
      destruct (ptyp_skip_lt kk t ltac:(lia)) as (B & HB & Hs).
      destruct (ptyp_skip_lt kk t' ltac:(lia)) as (B' & HB' & Hs').
      destruct (vg_dom_head p D Hg Hcv v Mv c gs gs1 t gs2 kk B ups ms vs ys0 HMv Hcon Heq HB Hu Hlms Hl Hly0 (Hgp _ _ Hgd))
        as (ig & Rg & bg & Ebg & HRg & Eg).
      destruct (vg_dom_head qc Dq HgQ HcvQ i' Mi' c gs' gs1' t' gs2' kk B' cups ms vs ys0 HMi' Hcon' Heq' HB' length_cups
                  ltac:(lia) ltac:(lia) Hly0 (Hcp _ _ Hcd)) as (ic & Rc & bc & Ebc & HRc & Ec).
      rewrite Hs in Eag; rewrite Hs' in Eac; cbn [ptyp_ty] in Eag, Eac.
      assert (Ag : ag = Πᵈ bg (env_args nil (ups ++ ms ++ vs ++ ys0))
                          (ptyp_ty p D (im_nn Mv) (false :: List.repeat false kk ++ cargs_pat gs1) (ptyp_skip (S kk) t)))
        by (eapply functional_eval_exp; [ exact Eag | econstructor; exact Ebg ]).
      assert (Ac : ac = Πᵈ bc (env_args nil (cups ++ ms ++ vs ++ ys0))
                          (ptyp_ty qc Dq (im_nn Mi') (false :: List.repeat false kk ++ cargs_pat gs1') (ptyp_skip (S kk) t')))
        by (eapply functional_eval_exp; [ exact Eac | econstructor; exact Ebc ]).
      subst ag ac; clear Eag Eac.
      basic_invert_per_univ_elem HR.
      match goal with H : per_univ_elem _ ?r bg bc |- _ => rename H into Hin; set (Rin := r) in * end.
      match goal with H : forall c c' (_ : Rin c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
      assert (Hyc : canon_doms_rel cups i' (ms ++ nonrec_arg_vals gs1' vs ++ ys0) B' y y).
      { assert (Ex : List.nth_error (ys0 ++ y :: nil) kk = Some y)
          by (rewrite List.nth_error_app2, Hly0, Nat.sub_diag by lia; reflexivity).
        pose proof (Hyr _ _ _ Ex Ex) as Hx; rewrite firstn_app_exact in Hx by exact Hly0.
        unfold shape_doms_rel in Hx; rewrite (List.nth_error_nth _ _ _ HB') in Hx; rewrite Hn; exact Hx. }
      assert (Hyin : Rin y y)
        by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRc Hin), Ec; exact Hyc).
      assert (Hyg : Rg y y) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRg Hin); exact Hyin).
      assert (Hyc' : Rc y y) by (apply Ec; exact Hyc).
      destruct (Hcod y y Hyin) as [a2 a2' Ea2 Ea2' HR2].
      constructor.
      + rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
        cbn [List.rev].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ ig Rg); [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgd | | exact Hyg ].
        replace (env_args (env_args nil (ups ++ ms ++ vs)) ys0) with (env_args nil (ups ++ ms ++ vs ++ ys0))
          by (rewrite <- env_args_app, <- !List.app_assoc; reflexivity).
        econstructor; [ exact Ebg | exact Ebg | exact HRg ].
      + rewrite (firstn_S_snoc _ _ _ HB'), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
        cbn [List.rev].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ ic Rc); [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hcd | | exact Hyc' ].
        replace (env_args (env_args nil (cups ++ ms ++ vs)) ys0) with (env_args nil (cups ++ ms ++ vs ++ ys0))
          by (rewrite <- env_args_app, <- !List.app_assoc; reflexivity).
        econstructor; [ exact Ebc | exact Ebc | exact HRc ].
      + exists i, (out_rel y y Hyin), a2, a2'.
        rewrite !env_args_snoc3; cbn [List.repeat List.app].
        split; [ exact Ea2 | split; [ exact Ea2' | exact HR2 ] ].
  Qed.

  Lemma walk_group_prefix : forall gs1 t vs kk ys, List.length vs = List.length gs1 ->
      per_gargs (List.rev (cargs_ctx p D Mv gs1 ++ im_params D Mv)) nil nil (ups ++ ms ++ vs) (ups ++ ms ++ vs) ->
      per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
        (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs)) ys ys ->
      per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mv gs1 ++ im_params D Mv))
        nil nil (ups ++ ms ++ vs ++ ys) (ups ++ ms ++ vs ++ ys).
  Proof.
    intros * Hl Hg1 H; rewrite List.rev_app_distr.
    replace (ups ++ ms ++ vs ++ ys) with ((ups ++ ms ++ vs) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
    apply per_gargs_app_intro; [| exact Hg1 | exact H ].
    rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia.
  Qed.

  Lemma walk_container_prefix : forall gs1' t' vs kk ys, List.length vs = List.length gs1' ->
      per_gargs (List.rev (cargs_ctx qc Dq Mi' gs1' ++ im_params Dq Mi')) nil nil (cups ++ ms ++ vs) (cups ++ ms ++ vs) ->
      per_gargs (List.rev (sh_ctx (cargs_pat gs1') (List.firstn kk (ptyp_doms t'))))
        (env_args nil (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs)) ys ys ->
      per_gargs (List.rev (sh_ctx (cargs_pat gs1') (List.firstn kk (ptyp_doms t')) ++ cargs_ctx qc Dq Mi' gs1' ++ im_params Dq Mi'))
        nil nil (cups ++ ms ++ vs ++ ys) (cups ++ ms ++ vs ++ ys).
  Proof.
    intros * Hl Hcn H; pose proof view_nn as Hnn; rewrite List.rev_app_distr.
    replace (cups ++ ms ++ vs ++ ys) with ((cups ++ ms ++ vs) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
    apply per_gargs_app_intro; [| exact Hcn | exact H ].
    rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params, length_cups; unfold im_np, ind_nu in *; lia.
  Qed.

  (** An argument recursive in both: the domains of the shapes
      ([agree_shape_doms_rel] at the canonical relations). *)
  Lemma shape_doms_rel_agree : forall gs1' t' gs2' gs1 t gs2 vp d B' B ys,
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      List.nth_error (ptyp_doms t') d = Some B' -> List.nth_error (ptyp_doms t) d = Some B ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys ->
      (canon_doms_rel cups i' (ms ++ nonrec_arg_vals gs1' vp ++ ys) B' <~> canon_doms_rel ups v (ms ++ nonrec_arg_vals gs1 vp ++ ys) B).
  Proof.
    intros * Heq' Heq Hc Hlp Hpre HB' HB Hy.
    pose proof view_nn as Hnn.
    pose proof (cargs_corr_len _ _ _ Hc) as Hl1.
    destruct (view_args_complete gs1 gs1' (ca_rec t' :: gs2') (ca_rec t :: gs2) vp Heq' Heq Hc Hlp Hpre) as (vs & Hinv).
    pose proof Hinv as [Hl Hn Hng Hg1 Hcn _].
    assert (Hd : d < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    assert (Hd' : d < List.length (ptyp_doms t')) by (apply List.nth_error_Some; congruence).
    destruct (view_shape_walk gs1' t' gs2' gs1 t gs2 vp vs Heq' Heq Hc Hinv d ys ltac:(lia) Hy)
      as [Hgd Hcd (i & R & ag & ac & Eag & Eac & HR)].
    pose proof Hy as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (Hly & _ & _).
    destruct (vg_dom_head p D Hg Hcv v Mv c gs gs1 t gs2 d B ups ms vs ys HMv Hcon Heq HB Hu Hlms Hl Hly
                (walk_group_prefix _ _ _ _ _ Hl Hg1 Hgd)) as (ig & Rg & bg & Ebg & HRg & Eg).
    destruct (vg_dom_head qc Dq HgQ HcvQ i' Mi' c gs' gs1' t' gs2' d B' cups ms vs ys HMi' Hcon' Heq' HB' length_cups
                ltac:(lia) ltac:(lia) Hly (walk_container_prefix gs1' t' vs d ys ltac:(lia) Hcn Hcd)) as (ic & Rc & bc & Ebc & HRc & Ec).
    destruct (ptyp_skip_lt d t Hd) as (B0 & HB0 & Hs); rewrite HB in HB0; injection HB0 as <-.
    destruct (ptyp_skip_lt d t' Hd') as (B0' & HB0' & Hs'); rewrite HB' in HB0'; injection HB0' as <-.
    rewrite Hs in Eag; rewrite Hs' in Eac; cbn [ptyp_ty] in Eag, Eac.
    assert (Ag : ag = Πᵈ bg (env_args nil (ups ++ ms ++ vs ++ ys))
                        (ptyp_ty p D (im_nn Mv) (false :: List.repeat false d ++ cargs_pat gs1) (ptyp_skip (S d) t)))
      by (eapply functional_eval_exp; [ exact Eag | econstructor; exact Ebg ]).
    assert (Ac : ac = Πᵈ bc (env_args nil (cups ++ ms ++ vs ++ ys))
                        (ptyp_ty qc Dq (im_nn Mi') (false :: List.repeat false d ++ cargs_pat gs1') (ptyp_skip (S d) t')))
      by (eapply functional_eval_exp; [ exact Eac | econstructor; exact Ebc ]).
    subst ag ac; clear Eag Eac.
    basic_invert_per_univ_elem HR.
    match goal with H : per_univ_elem _ ?r bg bc |- _ => rename H into Hin end.
    rewrite <- Hn, <- Hng.
    etransitivity; [ symmetry; exact Ec |].
    etransitivity; [ exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRc Hin) |].
    etransitivity; [ symmetry; exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRg Hin) | exact Eg ].
  Qed.

  (** ** The Non-Uniform Parameters

      The container's canonical relation of a non-uniform parameter at
      [cups] is the group's at [ups] of the member the view takes the
      container's to ([agree_nparams_rel] at the canonical relations). *)
  Lemma view_nparams_rel : forall j vs vs', j < im_nn Mi' -> tele_prefix_rel (canon_nparams_rel Dq cups i') j vs vs' ->
      (canon_nparams_rel Dq cups i' j vs <~> canon_nparams_rel D ups v j vs).
  Proof.
    clear Hms_g Hms_c Hlms ms.
    intros j vs vs' Hj Hp.
    pose proof view_nn as Hnn.
    pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
    pose proof (valid_group_valid _ _ HgQ) as HDQ; pose proof (valid_group_closed _ _ HgQ) as HcQ; pose proof (valid_group_sort _ _ HgQ) as HsuQ.
    destruct (vg_canon qc Dq HgQ cups view_cups_rel length_cups) as [CnP CnI CaP CaI CdP CdI].
    set (tc := List.rev (im_nparams Mi')); set (tg := List.rev (im_nparams Mv)).
    assert (Hlr : j <= List.length tc) by (unfold tc; rewrite List.length_rev, length_im_nparams; lia).
    assert (Hlv : List.length vs = j) by (rewrite tele_prefix_rel_iff in Hp; tauto).
    pose proof (tele_prefix_rel_refl_l (List.length tc) _
                  (fun k0 a b Hk Ha => nparams_rel_per qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' k0 a b Hk Ha)
                  (fun k0 a b Hk Ha => nparams_rel_invariant qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' k0 a b Hk Ha)
                  j vs vs' Hlr Hp) as Hpp.
    destruct (sort_value Dq HDQ cups view_cups_rel length_cups) as [aQ EaQ].
    pose proof (nr_gargs Dq HDQ HcQ HsuQ i' Mi' HMi' cups cups aQ view_cups_rel length_cups EaQ j vs vs ltac:(lia) Hpp) as Hg0.
    (** The container's telescope, from no base to the instance's. *)
    pose proof (valid_ind_decl_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (Hlc : List.length cups = List.length (ind_uparams Dq)) by (rewrite length_cups; reflexivity).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)).
    { assert (HUQ' : ⊨ List.rev (List.rev (ind_uparams Dq)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HUQ).
      apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ Hlc view_cups_rel). }
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ (decl_closed_ass _ HcQ) HUQ HRQ Hlc Hlc HQ0).
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass Dq HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams Dq) by (unfold tc; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HDQ _ _ _ _ HMi' HA))).
    destruct (tele_base_change tc (ind_uparams Dq) RQ (env_args nil cups) (env_args (env_args nil ups) cups)
                Hac HWc0 HTc0 HRQ HQ1 j vs Hlv Hlr Hg0) as [Hg1 Hhd].
    (** The two telescopes, equal under the view's instance. *)
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams Dq)) by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (decl_closed_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams Dq ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams Dq))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (decl_closed_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HD _ _ _ _ HMv HA))).
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

(** ** An Argument Recursive in Both: the Parameters its Shapes End In

    The container's shape ends in its member [j'], the group's in the
    member [j] the view takes [j'] to; after the domains, the parameters of
    the two ends are related at [j], canonically ([agree_shape_params] at
    the canonical relations).  Through the ends' types, related by the walk
    along the domains: at the container's member [j'] if it is declared
    (the view [j] is then of the same instance), else at the declared
    member both views view, moved to [j'] by the container's view [j']. *)
Section ViewAgreementParts.
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
  Hypotheses (Hms_g : per_gargs (List.rev (im_params D Mv)) nil nil (ups ++ ms) (ups ++ ms))
    (Hms_c : per_gargs (List.rev (im_params Dq Mi')) nil nil (cups ++ ms) (cups ++ ms)).
  Hypotheses (Hns_g : tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) ms ms)
    (Hns_c : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms).

  Lemma shape_params_agree : forall gs1' t' gs2' gs1 t gs2 vp ys,
      gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      tele_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) (ptyp_doms t') ys ys ->
      ps_link D (canon_nparams_rel D ups) (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups ++ ms ++ nonrec_arg_vals gs1' vp ++ ys)) (env_args nil (ups ++ ms ++ nonrec_arg_vals gs1 vp ++ ys)).
  Proof.
    intros gs1' t' gs2' gs1 t gs2 vp ys Heq' Heq Hc Hlp Hpre Hys.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (cargs_corr_len _ _ _ Hc) as Hl1.
    assert (Hrc : List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) /\ List.length (ptyp_doms t') = List.length (ptyp_doms t)).
    { rewrite Heq', Heq in Hcorr; destruct (cargs_corr_split _ _ _ _ _ Hcorr ltac:(lia)) as [_ H].
      cbn in H; destruct H as (Hm & Hd & _); unfold ptyp_depth in Hd; exact (conj Hm Hd). }
    destruct Hrc as [Hmem HlD].
    (** The arguments, related at both telescopes, and the walk along the
        domains to the ends' types. *)
    destruct (view_args_complete p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                c gs' gs Hcon' Hcon Hcorr ms Hlms Hms_g Hms_c gs1 gs1' (ca_rec t' :: gs2') (ca_rec t :: gs2) vp Heq' Heq Hc Hlp Hpre)
      as (vs & Hinv).
    pose proof Hinv as [Hl Hn Hng Hg1 Hcn Ha].
    assert (Hy : tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t'))
                   (List.length (ptyp_doms t)) ys ys)
      by (rewrite <- HlD; apply tele_rel_pre; exact Hys).
    destruct (view_shape_walk p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                c gs' gs Hcon' Hcon Hcorr ms Hlms gs1' t' gs2' gs1 t gs2 vp vs Heq' Heq Hc Hinv _ ys (le_n _) Hy)
      as [Hgd Hcd (i & R & ag & ac & Eag & Eac & HR)].
    pose proof (walk_group_prefix p D ups Hu Mv ms Hlms gs1 t vs _ ys Hl Hg1 Hgd) as Hctxg.
    rewrite List.firstn_all in Hctxg.
    pose proof (walk_container_prefix p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hu Ecups i' Mi' v Mv HMi' Hv HMv ms Hlms
                  gs1' t' vs _ ys ltac:(lia) Hcn Hcd) as Hctxc.
    rewrite <- HlD, List.firstn_all in Hctxc.
    rewrite <- HlD in Eac.
    rewrite ptyp_skip_end in Eag, Eac.
    cbn [ptyp_ty] in Eag, Eac.
    pose proof (view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups) as Hcr.
    pose proof (length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Ecups) as Hlc.
    (** The domains, related at the group's shape. *)
    assert (Hyg : tele_prefix_rel (shape_doms_rel (canon_doms_rel ups v) ms (nonrec_arg_vals gs1 vs) (ptyp_doms t))
                    (List.length (ptyp_doms t)) ys ys).
    { pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0 |- *; destruct Hy0 as (Hly & _ & Hyr).
      split; [ exact Hly | split; [ exact Hly |] ].
      intros j x x' Hx Hx'.
      assert (Hj : j < List.length (ptyp_doms t)) by (rewrite <- Hly; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' (ptyp_doms t) j Hj) as [B HB].
      destruct (nth_error_lt_some' (ptyp_doms t') j ltac:(lia)) as [B' HB'].
      pose proof (Hyr _ _ _ Hx Hx') as Hxy; unfold shape_doms_rel in Hxy |- *.
      rewrite (List.nth_error_nth _ _ _ HB') in Hxy; rewrite (List.nth_error_nth _ _ _ HB), Hng.
      apply (shape_doms_rel_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
               c gs' gs Hcon' Hcon Hcorr ms Hlms Hms_g Hms_c gs1' t' gs2' gs1 t gs2 vp j B' B (List.firstn j ys)
               Heq' Heq Hc Hlp Hpre HB' HB (tele_prefix_rel_of_pre _ _ _ _ j Hy ltac:(lia))).
      exact Hxy. }
    assert (Hyc : tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vs) (ptyp_doms t'))
                    (List.length (ptyp_doms t')) ys ys)
      by (rewrite Hn, HlD; exact Hy).
    assert (Hprec : tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
                      (nonrec_arg_vals gs1' vs) (nonrec_arg_vals gs1' vs))
      by (rewrite Hn; exact Hpre).
    (** Each side's parameters, at the non-recursive arguments and at all
        the arguments. *)
    destruct (shape_end_params_link p D Hg v Mv c gs HMv Hcon (vg_cargs_sem p D Hg Hcv v Mv c gs HMv Hcon) gs1 t gs2 Heq ups ms vs ys
                Hu Hlms Hl Hgu Hns_g Ha Hctxg Hyg) as [bsG bsG1 EbsG EbsG1 HtG].
    destruct (shape_end_params_link qc Dq HgQ i' Mi' c gs' HMi' Hcon' (vg_cargs_sem qc Dq HgQ HcvQ i' Mi' c gs' HMi' Hcon')
                gs1' t' gs2' Heq' cups ms vs ys Hlc ltac:(lia) ltac:(lia) Hcr Hns_c Hprec Hctxc Hyc) as [bsC bsC1 EbsC EbsC1 HtC].
    rewrite Hng in EbsG; rewrite Hn in EbsC.
    pose proof Hy as Hly; rewrite tele_prefix_rel_iff in Hly; destruct Hly as [Hly _].
    clear Hgd Hcd Hyg Hyc Hprec Hy Hys Hinv Hg1 Ha.
    apply (mk_ps_link _ _ _ _ _ _ _ bsC bsG EbsC EbsG).
    destruct (length_rec_ps D (valid_group_valid _ _ Hg) v Mv HMv c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
    destruct (length_rec_ps Dq (valid_group_valid _ _ HgQ) i' Mi' HMi' c gs' gs1' t' gs2' Hcon' Heq') as (Mj' & HMj' & HlPs').
    unfold ntele_rel in HtG, HtC |- *; rewrite HMj in HtG |- *; rewrite HMj' in HtC.
    (** The ends' types, related. *)
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj Eag) as (csg & bsg & Ecsg & Ebsg & ->).
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj' Eac) as (csc & bsc & Ecsc & Ebsc & ->).
    pose proof (functional_eval_exps' _ _ _ _ Ebsg EbsG1) as ->.
    pose proof (functional_eval_exps' _ _ _ _ Ebsc EbsC1) as ->.
    pose proof (per_univ_sym _ _ _ _ HR) as HRs.
    destruct (grp_tele_ass_vm D (valid_group_ass _ _ Hg) k Mk qc kc Is vm Dq (ptyp_mem t') Mj' HMk Hh Hq HMj') as [jj Mjj Hvj HMjj Hnnj Hhead].
    rewrite Hmem in Hvj; injection Hvj as <-; rewrite HMj in HMjj; injection HMjj as <-.
    pose proof HtG as HlbG; destruct HlbG as [HlbG _]; rewrite List.length_rev, length_im_nparams in HlbG.
    assert (HlbC1 : List.length bsC1 = im_nn Mj') by (rewrite (eval_exps_length _ _ _ EbsC1), List.length_map; exact HlPs').
    clear Eag Eac HR Ebsg Ebsc.
    (** The container's canonical relation at its member [j'] is the
        group's at [j], the member the view takes it to. *)
    assert (Hconv : forall a b, tele_rel (canon_nparams_rel Dq cups (ptyp_mem t')) (List.rev (im_nparams Mj')) a b ->
                      tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) a b).
    { intros a b Hab.
      assert (Hab' : tele_rel (canon_nparams_rel Dq cups (ptyp_mem t')) (List.rev (im_nparams Mj)) a b)
        by (destruct Hab as [Hla Hab]; split; [ rewrite Hla, !List.length_rev, !length_im_nparams; lia | exact Hab ]).
      apply (tele_rel_map _ (canon_nparams_rel Dq cups (ptyp_mem t'))); [| exact Hab' ].
      intros j pa pb x y Hj Hp1 _ Hxy.
      rewrite List.length_rev, length_im_nparams in Hj.
      apply (view_nparams_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups (ptyp_mem t') Mj' (ptyp_mem t) Mj
               HMj' Hmem HMj j pa pb ltac:(lia) Hp1); exact Hxy. }
    (** The two ends' parameters at all the arguments, related at the
        container's member [j']. *)
    assert (X1 : tele_rel (canon_nparams_rel Dq cups (ptyp_mem t')) (List.rev (im_nparams Mj')) bsC1 bsG1).
    { destruct (im_head Mj') as [pm' | qv kv Is'' vm''] eqn:Hh'.
      - (** [j'] declared: the view [j] is of it at the same instance. *)
        destruct Hhead as [vm' Hhj].
        unfold im_ref, im_pre in HRs, Ecsg, Ecsc; rewrite Hhj in HRs, Ecsg; rewrite Hh' in HRs, Ecsc; cbn [fst snd] in HRs.
        assert (HU : ⟦ ind_uvars Dq (im_nn Mi') (List.length (List.repeat false (List.length (ptyp_doms t')) ++ cargs_pat gs1')) ⟧*
                       gc_deps ⍮ gc_stack ⍮ env_args nil (cups ++ ms ++ vs ++ ys) ↘ cups).
        { unfold ind_uvars.
          replace (List.length (List.repeat false (List.length (ptyp_doms t')) ++ cargs_pat gs1') + im_nn Mi')
            with (List.length (ms ++ vs ++ ys)) by (rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia).
          rewrite <- Hlc; apply eval_vars_from_args. }
        pose proof (functional_eval_exps' _ _ _ _ Ecsc HU) as ->.
        assert (Hlcsg : List.length csg = ind_nu Dq)
          by (rewrite (eval_exps_length _ _ _ Ecsg), List.length_map, <- Hlc, (eval_exps_length _ _ _ Ecups); reflexivity).
        destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRs Hq Hlc Hlcsg) as [_ _ _ _ _ _ Hns _].
        unfold member_nparams in Hns; rewrite HMj' in Hns; exact Hns.
      - (** [j'] a view of the container: the view [j] is of the same
            declared member [kv] of the deeper container; at its instance
            there, its relation is the container's at [j']. *)
        destruct Hhead as (Is' & vm' & Hhj & HlIs).
        destruct (grp_tele_ass_views Dq (valid_group_ass _ _ HgQ) _ _ _ _ _ _ HMj' Hh') as (Dx & Mc & HqX & HMc & Hnnc & HIx).
        pose proof (HcvQ _ _ _ _ _ _ _ HMj' Hh' HqX) as HgX.
        destruct (decl_typed_view _ _ _ (valid_group_typed _ _ HgQ) _ _ _ _ _ _ HMj' Hh') as (Dx' & Mc' & HqX' & HMc' & Hkd & _ & _ & Hvmk & _).
        rewrite HqX in HqX'; injection HqX' as <-; rewrite HMc in HMc'; injection HMc' as <-.
        assert (Hhc : exists pm, im_head Mc = mh_decl pm).
        { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgX) _ _ HMc) Hkd) as Hd.
          unfold im_is_decl in Hd; destruct (im_head Mc); [ eauto | discriminate ]. }
        destruct Hhc as [pmc Hhc].
        destruct (vg_view_args_values qc Dq HgQ HcvQ _ _ _ _ _ _ _ HMj' Hh' HqX cups cups Hcr Hlc) as (xc & _ & Exc & _ & _).
        (** The end's uniform arguments, related to the view's instance. *)
        assert (HZ : ⊨ (sh_ctx (cargs_pat gs1') (ptyp_doms t') ++ cargs_ctx qc Dq Mi' gs1' ++ im_nparams Mi') ++ ind_uparams Dq).
        { pose proof (sh_sem Dq qc i' Mi' c gs' (valid_group_valid _ _ HgQ) HMi' Hcon' (vg_cargs_sem qc Dq HgQ HcvQ i' Mi' c gs' HMi' Hcon')
                        _ _ _ Heq' (List.length (ptyp_doms t')) (le_n _)) as H.
          rewrite List.firstn_all in H; unfold im_params in H; rewrite <- !List.app_assoc; exact H. }
        destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
        assert (Hlz : List.length (ms ++ vs ++ ys) = List.length (sh_ctx (cargs_pat gs1') (ptyp_doms t') ++ cargs_ctx qc Dq Mi' gs1' ++ im_nparams Mi'))
          by (rewrite !List.length_app, length_sh_ctx, length_cargs_ctx, length_im_nparams; lia).
        assert (HE : RZ (env_args nil (cups ++ ms ++ vs ++ ys)) (env_args nil (cups ++ ms ++ vs ++ ys))).
        { apply (gargs_env_rel _ _ _ _ _ _ HRZ HZ).
          - rewrite (List.length_app _ (ind_uparams Dq)), <- Hlz, !List.length_app; unfold ind_nu in Hlc; lia.
          - rewrite <- !List.app_assoc; unfold im_params in Hctxc; exact Hctxc. }
        destruct (view_pre_values qc Dq HgQ HcvQ _ _ _ _ _ _ _ cups _ RZ (ms ++ vs ++ ys) (im_nn Mi')
                    (List.length (List.repeat false (List.length (ptyp_doms t')) ++ cargs_pat gs1')) csc HMj' Hh' HqX Hlc Hcr HZ HRZ Hlz
                    ltac:(rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia) HE Ecsc) as (xc0 & Exc0 & Hgx).
        pose proof (functional_eval_exps' _ _ _ _ Exc0 Exc) as ->.
        unfold im_ref in HRs; rewrite Hhj, Hh' in HRs; cbn [fst snd] in HRs.
        assert (Hlcsc : List.length csc = ind_nu Dx)
          by (rewrite (eval_exps_length _ _ _ Ecsc); unfold im_pre; rewrite Hh', List.length_map; exact HIx).
        assert (Hlcsg : List.length csg = ind_nu Dx)
          by (rewrite (eval_exps_length _ _ _ Ecsg); unfold im_pre; rewrite Hhj, List.length_map; lia).
        assert (Hlxc : List.length xc = ind_nu Dx) by (rewrite (eval_exps_length _ _ _ Exc); exact HIx).
        destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRs HqX Hlcsc Hlcsg) as [_ _ _ _ _ _ Hns _].
        unfold member_nparams in Hns; rewrite HMc in Hns.
        pose proof (vg_nparams_base_change qv Dx HgX kv Mc pmc csc xc bsC1 bsG1 HMc Hhc
                      (uparams_sym Dx (valid_group_valid _ _ HgX) (valid_group_closed _ _ HgX) _ _ Hgx Hlxc) Hlcsc Hns) as Hns2.
        assert (Hns3 : tele_rel (canon_nparams_rel Dq cups (ptyp_mem t')) (List.rev (im_nparams Mc)) bsC1 bsG1).
        { apply (tele_rel_map _ (canon_nparams_rel Dx xc kv)); [| exact Hns2 ].
          intros j pa pb x y Hj Hp1 _ Hxy.
          rewrite List.length_rev, length_im_nparams in Hj.
          apply (view_nparams_rel qc Dq HgQ HcvQ (ptyp_mem t') Mj' qv kv Is'' vm'' Dx HMj' Hh' HqX cups xc Hcr Hlc Exc
                   kv Mc (ptyp_mem t') Mj' HMc Hvmk HMj' j pa pb ltac:(lia) Hp1); exact Hxy. }
        destruct Hns3 as [Hl3 Hns3]; split; [ rewrite Hl3, !List.length_rev, !length_im_nparams; lia | exact Hns3 ]. }
    destruct (vg_canon p D Hg ups Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
    apply (nparams_rel_trans p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI _ _ HMj _ bsC1); [ exact (Hconv _ _ HtC) |].
    apply (nparams_rel_trans p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI _ _ HMj _ bsG1); [ exact (Hconv _ _ X1) |].
    exact (nparams_rel_sym p D ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI _ _ HMj _ _ HtG).
  Qed.

  (** The non-uniform parameters related at the container's member are
      related at the group's member the view takes it to. *)
  Lemma view_nparams_transfer : forall a b, tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) a b ->
      tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) a b.
  Proof.
    clear Hms_g Hms_c Hns_g Hns_c Hlms ms.
    intros a b Hab.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    assert (Hab' : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mv)) a b)
      by (destruct Hab as [Hla Hab]; split; [ rewrite Hla, !List.length_rev, !length_im_nparams; lia | exact Hab ]).
    apply (tele_rel_map _ (canon_nparams_rel Dq cups i')); [| exact Hab' ].
    intros j pa pb x y Hj Hp1 _ Hxy.
    rewrite List.length_rev, length_im_nparams in Hj.
    apply (view_nparams_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
             j pa pb ltac:(lia) Hp1); exact Hxy.
  Qed.

  (** The non-recursive arguments related at the container's telescope are
      related at the group's: the group keeps those non-recursive in both. *)
  Lemma view_nonrec_prefix : forall gsA gsA' gsB' gsB vp vp', gs' = gsA' ++ gsB' -> gs = gsA ++ gsB -> cargs_corr vm gsA' gsA ->
      List.length vp = List.length gsA -> List.length vp' = List.length gsA ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gsA'))
        (nonrec_arg_vals gsA' vp) (nonrec_arg_vals gsA' vp') ->
      tele_prefix_rel (canon_args_rel D ups v ms c) (List.length (cargs_nonrec gsA))
        (nonrec_arg_vals gsA vp) (nonrec_arg_vals gsA vp').
  Proof.
    pose proof (view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups) as Hcr.
    pose proof (length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Ecups) as Hlc.
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    induction gsA as [| g gsA IH] using List.rev_ind; intros gsA' gsB' gsB vp vp' Heq' Heq Hc Hlp Hlp' Hpre.
    - destruct gsA' as [| g' gsA']; [| destruct g'; cbn in Hc; contradiction ].
      cbn; apply tele_prefix_rel_nil.
    - pose proof (cargs_corr_len _ _ _ Hc) as HlA; rewrite List.length_app in HlA; cbn in HlA.
      destruct (List.exists_last (l := gsA') ltac:(intros ->; cbn in HlA; lia)) as (gsA0' & g' & ->).
      rewrite List.length_app in HlA; cbn in HlA.
      destruct (cargs_corr_split _ _ _ _ _ Hc ltac:(lia)) as [Hc0 Hc1].
      rewrite List.length_app in Hlp, Hlp'; cbn in Hlp, Hlp'.
      destruct (List.exists_last (l := vp) ltac:(intros ->; cbn in Hlp; lia)) as (vp0 & x & ->).
      destruct (List.exists_last (l := vp') ltac:(intros ->; cbn in Hlp'; lia)) as (vp0' & x' & ->).
      rewrite List.length_app in Hlp, Hlp'; cbn in Hlp, Hlp'.
      rewrite <- List.app_assoc in Heq', Heq; cbn [List.app] in Heq', Heq.
      assert (Hlc0 : List.length vp0 = List.length gsA0') by lia.
      assert (Hlc0' : List.length vp0' = List.length gsA0') by lia.
      rewrite cargs_nonrec_app, !nonrec_arg_vals_app in Hpre by lia.
      assert (HK0 : List.length (nonrec_arg_vals gsA0' vp0) = List.length (cargs_nonrec gsA0'))
        by exact (length_nonrec_arg_vals _ _ Hlc0).
      assert (HK0' : List.length (nonrec_arg_vals gsA0' vp0') = List.length (cargs_nonrec gsA0'))
        by exact (length_nonrec_arg_vals _ _ Hlc0').
      assert (Hpre0 : tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gsA0'))
                        (nonrec_arg_vals gsA0' vp0) (nonrec_arg_vals gsA0' vp0')).
      { pose proof (tele_prefix_rel_of_pre _ _ _ _ (List.length (cargs_nonrec gsA0')) Hpre ltac:(rewrite List.length_app; lia)) as H.
        rewrite !firstn_app_exact in H by assumption; exact H. }
      pose proof (IH gsA0' (g' :: gsB') (g :: gsB) vp0 vp0' Heq' Heq Hc0 ltac:(lia) ltac:(lia) Hpre0) as IH0.
      rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia.
      destruct g' as [A' | t'], g as [A | t]; cbn in Hc1; try contradiction;
        cbn [cargs_nonrec nonrec_arg_vals] in Hpre |- *; rewrite ?List.app_nil_r; [| exact IH0 | exact IH0 ].
      (** Non-recursive in both. *)
      assert (Hxc : canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gsA0')) (nonrec_arg_vals gsA0' vp0) x x').
      { rewrite tele_prefix_rel_iff in Hpre; destruct Hpre as (_ & _ & Hr).
        assert (Ex : List.nth_error (nonrec_arg_vals gsA0' vp0 ++ x :: nil) (List.length (cargs_nonrec gsA0')) = Some x)
          by (rewrite List.nth_error_app2, HK0, Nat.sub_diag by lia; reflexivity).
        assert (Ex' : List.nth_error (nonrec_arg_vals gsA0' vp0' ++ x' :: nil) (List.length (cargs_nonrec gsA0')) = Some x')
          by (rewrite List.nth_error_app2, HK0', Nat.sub_diag by lia; reflexivity).
        pose proof (Hr _ _ _ Ex Ex') as H; rewrite firstn_app_exact in H by exact HK0; exact H. }
      assert (HK : List.length (cargs_nonrec gsA0') <= List.length (cargs_nonrec gs'))
        by (rewrite Heq', cargs_nonrec_app, List.length_app; lia).
      pose proof (args_rel_pre_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c gs' Hns_c Hcon'
                    _ _ _ HK Hpre0) as Hpre0d.
      pose proof (view_arg_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                    c gs' gs Hcon' Hcon Hcorr ms Hlms Hms_g Hms_c gsA0' A' gsB' gsA A gsB vp0 Heq' Heq Hc0 ltac:(lia) Hpre0d) as EA.
      rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
      apply tele_prefix_rel_snoc; [ exact IH0 |].
      apply EA; exact Hxc.
  Qed.
End ViewAgreementParts.

(** ** Non-Uniform Parameters Related at a Container's Member

    Values of the non-uniform parameters of the container's member [i'],
    related canonically to some others: they are related to themselves at
    both telescopes, the container's and that of the member [v] the view
    takes [i'] to, and so are the parameters with the uniform ones. *)
Section ViewMemberParams.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Variables (ups cups : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups).
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member Dq i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).

  (** Non-uniform parameters [ms] good for both the group's member [Mv] and
      the container's [Mi']. *)
  Record view_member_params (ms : list domain) : Prop := mk_view_member_params
    { (** One per non-uniform parameter of [Mv] *)
      params_length : List.length ms = im_nn Mv
      (** Related canonically at [Mv] over [ups] *)
    ; params_group_related : tele_rel (canon_nparams_rel D ups v) (List.rev (im_nparams Mv)) ms ms
      (** Related canonically at [Mi'] over [cups] *)
    ; params_container_related : tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms
      (** Related at [Mv]'s full telescope over [ups] *)
    ; params_group_values : per_gargs (List.rev (im_params D Mv)) nil nil (ups ++ ms) (ups ++ ms)
      (** Related at [Mi']'s full telescope over [cups] *)
    ; params_container_values : per_gargs (List.rev (im_params Dq Mi')) nil nil (cups ++ ms) (cups ++ ms) }.

  Lemma view_member_params_of : forall ms ms', tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms' ->
      view_member_params ms.
  Proof.
    intros ms ms' Hms.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups) as Hcr.
    pose proof (length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Ecups) as Hlc.
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    pose proof (nparams_rel_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' _ _ Hms) as Hns_c.
    pose proof (view_nparams_transfer p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                  _ _ Hns_c) as Hns_g.
    destruct (sort_value Dq (valid_group_valid _ _ HgQ) cups Hcr Hlc) as [aQ EaQ].
    destruct (sort_value D (valid_group_valid _ _ Hg) ups Hgu Hu) as [a Ea].
    constructor; [| exact Hns_g | exact Hns_c | |].
    - destruct Hns_c as [Hl _]; rewrite List.length_rev, length_im_nparams in Hl; lia.
    - exact (params_gargs D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) (valid_group_sort _ _ Hg) v Mv HMv ups ups a ms ms Hgu Hu Ea Hns_g).
    - exact (params_gargs Dq (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) (valid_group_sort _ _ HgQ) i' Mi' HMi' cups cups aQ ms ms Hcr Hlc EaQ Hns_c).
  Qed.
End ViewMemberParams.

(** ** The Agreement of a View at the Canonical Relations

    The fields of [view_agreement] for a view [k] at the canonical
    relations at [ups] and [ups'] ([view_agreement_canonical]), from the
    diagonal ones above: what a field reads at the right side is moved
    along related bases and prefixes. *)
Section ViewAgreementCanonical.
  Variables (p : qname) (D : ind_decl).
  Variable (P : qname -> ind_decl -> Prop).
  Hypotheses (Hg : valid_group p D) (HP : valid_groups P) (HPD : P p D).
  Let Hcv := containers_valid_of_groups P HP p D HPD.
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Let HcvQ := containers_valid_of_groups P HP qc Dq (valid_groups_containers P HP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq).
  Variables (ups ups' cups cups' : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups') (Hu : List.length ups = ind_nu D)
    (Ec : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups)
    (Ec' : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups' ↘ cups').
  Let Hgd := uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu.
  Let Hu' := length_ups_gargs D _ _ Hgu Hu.
  Let Hgd' := uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _
                (uparams_sym D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu Hu).
  Let Hcr := view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec.
  Let Hlc := length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Ec.
  Let Hcr' := view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups' cups' Hgd' Hu' Ec'.
  Let Hlc' := length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups' cups' Ec'.

  Lemma view_cups_related : per_gargs (List.rev (ind_uparams Dq)) nil nil cups cups'.
  Proof.
    destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hc0).
    pose proof (functional_eval_exps' _ _ _ _ E0 Ec) as ->; pose proof (functional_eval_exps' _ _ _ _ E0' Ec') as ->.
    exact Hc0.
  Qed.

  (** The non-uniform parameters ([agree_nparams_rel]). *)
  Lemma agree_nparams_canonical : forall i' Mi' v Mv j vs vs', ind_member Dq i' = Some Mi' ->
      view_member p D qc Dq vm i' Mi' v Mv -> j < im_nn Mi' -> tele_prefix_rel (canon_nparams_rel Dq cups i') j vs vs' ->
      (canon_nparams_rel Dq cups i' j vs <~> canon_nparams_rel D ups v j vs).
  Proof.
    intros * HMi' Hvm Hj Hp.
    exact (view_nparams_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi'
             (view_member_v _ _ _ _ _ _ _ _ _ Hvm) (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) j vs vs' Hj Hp).
  Qed.

  (** An argument non-recursive in both ([agree_args_rel]). *)
  Lemma agree_args_canonical : forall i' Mi' v Mv c gs1' A' gs2' gs1 A gs2 ms ms' vp vp' x y,
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_arg A :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      (canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) x y <->
       canon_args_rel D ups v ms c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vp) x y).
  Proof.
    intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre.
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm _ _ Hc') as (gs0 & Hc0 & Hcorr); rewrite Hc in Hc0; injection Hc0 as <-.
    destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv ms ms' Hms)
      as [Hlms Hns_g Hns_c Hms_g Hms_c].
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    assert (HK : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec (gs1' ++ ca_arg A' :: gs2')))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (args_rel_pre_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ Hns_c Hc'
                  _ _ _ HK Hpre) as Hpre_d.
    exact (view_arg_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
             c _ _ Hc' Hc Hcorr ms Hlms Hms_g Hms_c gs1' A' gs2' gs1 A gs2 vp eq_refl eq_refl Hc1 Hlp Hpre_d x y).
  Qed.

  (** An argument the view nests through ([agree_nested_arg_rel]), given
      the relation of the type of the member the shape ends in. *)
  Lemma agree_nested_canonical : forall i' Mi' v Mv c gs1' A' gs2' gs1 t gs2 ms ms' vp vp' x y,
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      view_end_rel p D ups ups (ptyp_mem t) ->
      (canon_args_rel Dq cups i' ms c (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) x y <->
       rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups)
         (canon_doms_rel ups) v ups ups' (ms ++ nonrec_arg_vals gs1 vp) (ms' ++ nonrec_arg_vals gs1 vp') t x y).
  Proof.
    intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre Hend.
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm _ _ Hc') as (gs0 & Hc0 & Hcorr); rewrite Hc in Hc0; injection Hc0 as <-.
    destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv ms ms' Hms)
      as [Hlms Hns_g Hns_c Hms_g Hms_c].
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    assert (HK : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec (gs1' ++ ca_arg A' :: gs2')))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (args_rel_pre_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ Hns_c Hc'
                  _ _ _ HK Hpre) as Hpre_d.
    pose proof (nested_arg_rel_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
                  c _ _ Hc' Hc Hcorr ms Hlms Hms_g Hms_c gs1' A' gs2' gs1 t gs2 vp eq_refl eq_refl Hc1 Hlp Hpre_d Hns_g Hend) as EN.
    pose proof (view_nparams_transfer p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
                  _ _ Hms) as Hms_v.
    pose proof (view_nonrec_prefix p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
                  c _ _ Hc' Hc Hcorr ms Hlms Hms_g Hms_c Hns_c gs1 gs1' (ca_arg A' :: gs2') (ca_rec t :: gs2) vp vp'
                  eq_refl eq_refl Hc1 Hlp Hlp' Hpre) as Hw.
    etransitivity; [ exact (EN x y) |].
    exact (vg_rec_arg_move_right p D Hg v Mv c gs1 t gs2 ups ups' ms ms' _ _ x y HMv Hc Hgu Hu Hms_v Hw).
  Qed.

  (** An argument recursive in both: the domains of the shapes
      ([agree_shape_doms_rel]). *)
  Lemma agree_doms_canonical : forall i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' d B' B ys ys',
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      List.nth_error (ptyp_doms t') d = Some B' -> List.nth_error (ptyp_doms t) d = Some B ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      tele_prefix_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) d ys ys' ->
      (canon_doms_rel cups i' (ms ++ nonrec_arg_vals gs1' vp ++ ys) B' <~> canon_doms_rel ups v (ms ++ nonrec_arg_vals gs1 vp ++ ys) B).
  Proof.
    intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' HB' HB Hms Hpre Hys.
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm _ _ Hc') as (gs0 & Hc0 & Hcorr); rewrite Hc in Hc0; injection Hc0 as <-.
    destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv ms ms' Hms)
      as [Hlms Hns_g Hns_c Hms_g Hms_c].
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    assert (HK : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec (gs1' ++ ca_rec t' :: gs2')))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (args_rel_pre_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ Hns_c Hc'
                  _ _ _ HK Hpre) as Hpre_d.
    assert (Hd : d <= List.length (ptyp_doms t')) by (assert (d < List.length (ptyp_doms t')) by (apply List.nth_error_Some; congruence); lia).
    pose proof (doms_rel_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ gs1' t' gs2'
                  (nonrec_arg_vals gs1' vp) Hns_c Hc' eq_refl Hpre_d d ys ys' Hd Hys) as Hyy.
    exact (shape_doms_rel_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
             c _ _ Hc' Hc Hcorr ms Hlms Hms_g Hms_c gs1' t' gs2' gs1 t gs2 vp d B' B ys eq_refl eq_refl Hc1 Hlp Hpre_d HB' HB Hyy).
  Qed.

  (** An argument recursive in both: the parameters the shapes end in
      ([agree_shape_params]), at the left prefix, at the right one over
      the right bases, and at the right one over the left bases. *)
  Lemma agree_params_canonical : forall i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms' vp vp' ys ys',
      ind_member Dq i' = Some Mi' -> view_member p D qc Dq vm i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_corr vm gs1' gs1 -> List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
      tele_rel (canon_nparams_rel Dq cups i') (List.rev (im_nparams Mi')) ms ms' ->
      tele_prefix_rel (canon_args_rel Dq cups i' ms c) (List.length (cargs_nonrec gs1'))
        (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') ->
      tele_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) (ptyp_doms t') ys ys' ->
      ps_link D (canon_nparams_rel D ups) (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups ++ ms ++ nonrec_arg_vals gs1' vp ++ ys)) (env_args nil (ups ++ ms ++ nonrec_arg_vals gs1 vp ++ ys)) /\
      ps_link D (canon_nparams_rel D ups) (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups' ++ ms' ++ nonrec_arg_vals gs1' vp' ++ ys')) (env_args nil (ups' ++ ms' ++ nonrec_arg_vals gs1 vp' ++ ys')) /\
      ps_link D (canon_nparams_rel D ups) (ptyp_ps t') (ptyp_ps t) (ptyp_mem t)
        (env_args nil (cups ++ ms' ++ nonrec_arg_vals gs1' vp' ++ ys')) (env_args nil (ups ++ ms' ++ nonrec_arg_vals gs1 vp' ++ ys')).
  Proof.
    intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre Hys.
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv; pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm _ _ Hc') as (gs0 & Hc0 & Hcorr); rewrite Hc in Hc0; injection Hc0 as <-.
    destruct (vg_canon qc Dq HgQ cups Hcr Hlc) as [CnP CnI CaP CaI CdP CdI].
    pose proof (nparams_rel_sym qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' _ _ Hms) as Hm'm.
    destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv ms ms' Hms)
      as [Hlms Hns_g Hns_c Hms_g Hms_c].
    destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv ms' ms Hm'm)
      as [Hlms' Hns_g' Hns_c' Hms_g' Hms_c'].
    assert (HK : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec (gs1' ++ ca_rec t' :: gs2')))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (args_rel_pre_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ Hns_c Hc'
                  _ _ _ HK Hpre) as Hpre_d.
    pose proof (args_prefix_rel_refl_r qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms ms' c _ _ _ _
                  Hms Hc' HK Hpre) as Hpre'.
    pose proof (tele_rel_pre _ _ _ _ Hys) as Hysp.
    assert (Hyy : tele_rel (shape_doms_rel (canon_doms_rel cups i') ms (nonrec_arg_vals gs1' vp) (ptyp_doms t')) (ptyp_doms t') ys ys)
      by (apply tele_rel_of_pre;
          exact (doms_rel_refl_l qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms c _ gs1' t' gs2'
                   (nonrec_arg_vals gs1' vp) Hns_c Hc' eq_refl Hpre_d _ ys ys' (le_n _) Hysp)).
    assert (Hyy' : tele_rel (shape_doms_rel (canon_doms_rel cups i') ms' (nonrec_arg_vals gs1' vp') (ptyp_doms t')) (ptyp_doms t') ys' ys')
      by (apply tele_rel_of_pre;
          exact (doms_rel_refl_inst qc Dq cups _ _ _ (valid_group_ass _ _ HgQ) CnP CnI CaP CaI CdP CdI i' Mi' HMi' ms ms' c _ gs1' t' gs2'
                   (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp') _ ys ys' Hms Hc' eq_refl Hpre (le_n _) Hysp)).
    split; [| split ].
    - exact (shape_params_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
               c _ _ Hc' Hc Hcorr ms Hlms Hms_g Hms_c Hns_g Hns_c gs1' t' gs2' gs1 t gs2 vp ys eq_refl eq_refl Hc1 Hlp Hpre_d Hyy).
    - (** Over the right bases: the container's relations at [cups'], the
          group's at [ups'] moved back to [ups]. *)
      destruct (vg_fam_agree qc Dq HgQ cups cups' view_cups_related Hlc) as [Hn Ha Hd].
      pose proof (tele_rel_nr_change qc Dq cups _ _ _ _ _ _ Hn Ha Hd i' Mi' HMi' _ _ Hns_c') as Hns_c2.
      pose proof (tele_prefix_rel_ar_change qc Dq cups _ _ _ _ _ _ Hn Ha Hd i' Mi' HMi' ms' ms' ms' c _ _ _ _ Hns_c' Hns_c2 Hc' HK Hpre')
        as Hpre2.
      assert (Hyy2 : tele_rel (shape_doms_rel (canon_doms_rel cups' i') ms' (nonrec_arg_vals gs1' vp') (ptyp_doms t')) (ptyp_doms t') ys' ys')
        by (apply tele_rel_of_pre;
            exact (tele_prefix_rel_sh_change qc Dq cups _ _ _ _ _ _ Hn Ha Hd i' Mi' HMi' ms' ms' ms' c _ gs1' t' gs2'
                     (nonrec_arg_vals gs1' vp') (nonrec_arg_vals gs1' vp') (nonrec_arg_vals gs1' vp') _ _ _
                     Hns_c' Hns_c2 Hc' eq_refl Hpre' Hpre2 (le_n _) (tele_rel_pre _ _ _ _ Hyy'))).
      destruct (view_member_params_of p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups' cups' Hgd' Hu' Ec' i' Mi' v Mv HMi' Hv HMv
                  ms' ms' Hns_c2) as [Hlms2 Hns_g2 Hns_c3 Hms_g2 Hms_c2].
      destruct (shape_params_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups' cups' Hgd' Hu' Ec' i' Mi' v Mv HMi' Hv HMv
                  c _ _ Hc' Hc Hcorr ms' Hlms2 Hms_g2 Hms_c2 Hns_g2 Hns_c3 gs1' t' gs2' gs1 t gs2 vp' ys' eq_refl eq_refl Hc1 Hlp'
                  Hpre2 Hyy2) as [b b' Eb Eb' Hbb].
      apply (mk_ps_link _ _ _ _ _ _ _ b b' Eb Eb').
      destruct (ind_fam_agree_sym _ _ _ _ _ _ _ (vg_fam_agree p D Hg ups ups' Hgu Hu)) as [Hn0 Ha0 Hd0].
      exact (ntele_rel_nr_change p D ups' _ _ _ _ _ _ Hn0 Ha0 Hd0 _ _ _ Hbb).
    - exact (shape_params_agree p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cups Hgd Hu Ec i' Mi' v Mv HMi' Hv HMv
               c _ _ Hc' Hc Hcorr ms' Hlms' Hms_g' Hms_c' Hns_g' Hns_c' gs1' t' gs2' gs1 t gs2 vp' ys' eq_refl eq_refl Hc1 Hlp'
               Hpre' Hyy').
  Qed.
End ViewAgreementCanonical.

(** A view's agreement at the canonical relations, given the relations of
    the types of the members the shapes it nests through end in. *)
Lemma view_agreement_canonical_of_ends : forall P p D, valid_groups P -> P p D ->
    forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall k, (forall Mk qc kc Is vm Dq i' Mi' v Mv c gs1' A' gs2' gs1 t gs2, ind_member D k = Some Mk ->
                 im_head Mk = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> ind_member Dq i' = Some Mi' ->
                 List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
                 ind_con Mi' c = Some (gs1' ++ ca_arg A' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
                 cargs_corr vm gs1' gs1 -> view_end_rel p D ups ups (ptyp_mem t)) ->
      view_agreement_canonical p D ups ups' k.
Proof.
  intros P p D HP HPD ups ups' Hgu Hu k Hend Mk qc kc Is vm Dq cups cups' HMk Hh Hq Ec Ec'.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  constructor.
  - exact (view_agree_members p D k Mk qc kc Is vm Dq (valid_group_ass _ _ Hg) HMk Hh Hq).
  - exact (view_agree_recursive_targets Dq (valid_group_ass _ _ (Hcv _ _ _ _ _ _ _ HMk Hh Hq))).
  - intros * HMi' Hvm Hj Hp.
    eapply (agree_nparams_canonical p D P Hg HP HPD k Mk qc kc Is vm Dq HMk Hh Hq); eassumption.
  - intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre.
    eapply (agree_args_canonical p D P Hg HP HPD k Mk qc kc Is vm Dq HMk Hh Hq); eassumption.
  - intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre.
    pose proof (Hend _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' (view_member_v _ _ _ _ _ _ _ _ _ Hvm)
                  (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) Hc' Hc Hc1) as He.
    eapply (agree_nested_canonical p D P Hg HP HPD k Mk qc kc Is vm Dq HMk Hh Hq); eassumption.
  - intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' HB' HB Hms Hpre Hys.
    eapply (agree_doms_canonical p D P Hg HP HPD k Mk qc kc Is vm Dq HMk Hh Hq); eassumption.
  - intros * HMi' Hvm Hc' Hc Hc1 Hlp Hlp' Hms Hpre Hys.
    eapply (agree_params_canonical p D P Hg HP HPD k Mk qc kc Is vm Dq HMk Hh Hq); eassumption.
Qed.

(** The rank of a view bounds the ranks of the members the shapes it nests
    through end in. *)
Lemma cargs_nest_ok_at : forall rk r gs1' A' gs2' gs1 t gs2, List.length gs1' = List.length gs1 ->
    cargs_nest_ok rk r (gs1' ++ ca_arg A' :: gs2') (gs1 ++ ca_rec t :: gs2) -> rk (ptyp_mem t) < r.
Proof.
  intros rk r; induction gs1' as [| g' gs1' IH]; intros A' gs2' [| g gs1] t gs2 Hl H; cbn in Hl; try discriminate.
  - cbn in H; exact (proj1 H).
  - destruct g' as [B' | t'], g as [B | t0]; cbn [List.app cargs_nest_ok] in H;
      [ exact (IH A' gs2' gs1 t gs2 ltac:(lia) H) | exact (IH A' gs2' gs1 t gs2 ltac:(lia) (proj2 H))
      | exact (IH A' gs2' gs1 t gs2 ltac:(lia) H) | exact (IH A' gs2' gs1 t gs2 ltac:(lia) H) ].
Qed.

(** ** Every View Agrees with its Container

    By induction on the views' ranks: the members a view nests through are
    of lower rank, so their types' relations are the group's
    ([view_end_rel_of_agreement]). *)
Theorem view_agreement_canonical_all : forall P p D, valid_groups P -> P p D ->
    forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall k, view_agreement_canonical p D ups ups' k.
Proof.
  intros P p D HP HPD ups ups' Hgu Hu k.
  pose proof (valid_groups_valid P HP p D HPD) as Hg.
  pose proof (containers_valid_of_groups P HP p D HPD) as Hcv.
  pose proof (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu) as Hgd.
  destruct (decl_typed_rank _ _ _ (valid_group_typed _ _ Hg)) as [rk Hrk].
  assert (Hall : forall n j u', rk j < n -> per_gargs (List.rev (ind_uparams D)) nil nil ups u' ->
                   view_agreement_canonical p D ups u' j).
  { induction n as [| n IH]; intros j u' Hj Hgu'; [ lia |].
    apply (view_agreement_canonical_of_ends P p D HP HPD ups u' Hgu' Hu j).
    intros * HMj Hh Hq HMi' Hv HMv Hc' Hc Hc1.
    pose proof (view_rank_ok_nest _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hq HMi' Hv HMv Hc' Hc) as Hn.
    pose proof (cargs_nest_ok_at _ _ _ _ _ _ _ _ (cargs_corr_len _ _ _ Hc1) Hn) as Hlt.
    exact (view_end_rel_of_agreement p D Hg Hcv ups ups Hgd Hu _ (IH (ptyp_mem t) ups ltac:(lia) Hgd)). }
  exact (Hall (S (rk k)) k ups' ltac:(lia) Hgu).
Qed.

End Fixed_GCtx.
