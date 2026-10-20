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
    relation of the shape ([view_nest_rel]). *)

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
      group's at [ups]. *)
  Lemma view_arg_link : forall gsA' g' gsB' gsA g gsB C G vs, gs' = gsA' ++ g' :: gsB' -> gs = gsA ++ g :: gsB ->
      List.length gsA = List.length gsA' -> List.length vs = List.length gsA ->
      cargs_ctx qc Dq Mi' (gsA' ++ g' :: nil) = ce_ass C :: cargs_ctx qc Dq Mi' gsA' ->
      cargs_ctx p D Mv (gsA ++ g :: nil) = ce_ass G :: cargs_ctx p D Mv gsA ->
      per_gargs (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)) nil nil (ups ++ ms ++ vs) (ups ++ ms ++ vs) ->
      per_gargs (List.rev (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi')) nil nil (cups ++ ms ++ vs) (cups ++ ms ++ vs) ->
      (per_head C C (env_args nil (cups ++ ms ++ vs)) (env_args nil (cups ++ ms ++ vs))
         <~> per_head G G (env_args nil (ups ++ ms ++ vs)) (env_args nil (ups ++ ms ++ vs))) /\
      exists (i : nat) R b, ⟦ G ⟧ env_args nil (ups ++ ms ++ vs) ↘ b /\ DF b ≈ b ∈ per_univ_elem i ↘ R.
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
    split.
    - etransitivity; [ symmetry; exact (per_head_right Ec1 Ec2 HRk) |].
      etransitivity; [ symmetry; exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ HR2 HRk) |].
      etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR2 | exact HR0 ] |].
      exact (per_head_right Ea1 Eb HR0).
    - exists i0, R0, b; split; [ exact Eb |].
      exact (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR0) HR0).
  Qed.
End ViewArgs.

End Fixed_GCtx.
