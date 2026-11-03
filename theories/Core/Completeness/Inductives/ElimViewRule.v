(** * The Eliminator at a View, as Its Container's

    The semantic rule E1′: the eliminator of a valid group at its view [m]
    of the container's member [k'] is the container's eliminator at [k']
    with the wrapped blocks ([view_wrap]).  At a semantic substitution of
    values [C1] and [C2], the chain of four values links through the
    group's eliminator at [C2]: the group's eliminator against itself
    ([elim_stage]), and the container's at [C2] and at the moved blocks
    against the group's at [C2] ([cross_elim_all], with its stuck
    eliminators read alike by [cross_bot_all]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim Iota
  ViewBranch ElimView ViewReadback.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim ReadPairs.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The value of an eliminator. *)
#[warnings="-cannot-define-projection"]
Record elim_exp_value (p : qname) (Us : list exp) (j : nat) (Bks : list eblock) (M : exp) (ρ : env) (r : domain) : Prop :=
  mk_elim_exp_value
  { (** The uniform parameters' values *)
    elim_exp_value_ups : list domain
    (** The scrutinee's value *)
  ; elim_exp_value_scrut : domain
    (** [Us] evaluate to [elim_exp_value_ups] *)
  ; elim_exp_value_ups_eval : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ elim_exp_value_ups
    (** [M] evaluates to [elim_exp_value_scrut] *)
  ; elim_exp_value_scrut_eval : ⟦ M ⟧ ρ ↘ elim_exp_value_scrut
    (** The eliminator on the scrutinee's value gives [r] *)
  ; elim_exp_value_elim : ⟦elim elim_exp_value_scrut at j of p elim_exp_value_ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r }.

Lemma elim_exp_value_of : forall p Us j Bks M ρ r, ⟦ a_elim relevant p Us j Bks M ⟧ ρ ↘ r -> elim_exp_value p Us j Bks M ρ r.
Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

(** A valid group's uniform parameters related to themselves are an
    eliminator's uniform parameters ([elim_ups_ok]) at their own canonical
    relations: [ups_ok] at the parameters' own context, its variables at
    the parameters' environment. *)
Lemma group_ups_ok : forall VP pg Dg, valid_groups VP -> VP pg Dg ->
    forall u, per_gargs (List.rev (ind_uparams Dg)) nil nil u u -> List.length u = ind_nu Dg ->
    elim_ups_ok pg Dg u (canon_nparams_rel Dg u) (canon_args_rel Dg u) (canon_doms_rel Dg u) u u.
Proof.
  intros VP pg Dg HP HPG u Hgu Hu.
  pose proof (valid_groups_valid VP HP pg Dg HPG) as Hg.
  pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
  pose proof (valid_ind_decl_uparams _ HD) as HUD.
  destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
  assert (HVs : forall k N T, List.nth_error (vars_from 0 (ind_nu Dg)) k = Some N ->
             List.nth_error (tele_insts (ind_uparams Dg) Id (vars_from 0 (ind_nu Dg))) k = Some T -> ind_uparams Dg ⊨ N : T).
  { intros k N T HN HT.
    destruct (uniform_param_vars_lookup Dg (decl_closed_ass _ Hc) (decl_mvc_uparams _ (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)))
                (decl_closed_uparams _ Hc) k N T HN HT) as (x & -> & Hx).
    exact (valid_exp_under_ctx_vlookup Hx HUD). }
  pose proof (vars_from_scoped 0 (ind_nu Dg) (List.length (ind_uparams Dg)) ltac:(unfold ind_nu; lia)) as HVss.
  pose proof (uparams_rel_env Dg HD u u Hgu Hu RU HRU) as HC.
  pose proof (eval_uvars_components Dg u nil nil 0 0 Hu eq_refl) as HE.
  unfold ind_uvars in HE; cbn [Nat.add components_env env_tele] in HE.
  exact (ups_ok VP pg Dg HP HPG (ind_uparams Dg) RU HRU HUD RU HRU (vars_from 0 (ind_nu Dg)) (length_vars_from _ _) HVs HVss
           (decl_env Dg u) u HC HE u u HC HC Hu Hu).
Qed.

Section ElimViewRule.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T)
    (HUss : List.Forall (exp_scoped (List.length Γ)) Us).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA) (HBss : blocks_scoped (List.length Γ) Bks).
  Let HBks := valid_blocks_has _ _ _ _ _ _ Hdt HBk.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBk.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBk.
  Let τU := sb_of_list Id Us.
  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Let HVQ := valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq.
  Let HgQ := valid_groups_valid VP HP qc D' HVQ.
  Let HaQ : tele_ass (ind_uparams D') := uparams_ass D' (valid_group_closed _ _ HgQ).
  Let HWQ : ⊨ ind_uparams D' := valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ).
  Let VB := view_wrap relevant p qc D D' vm Us (im_pre Mm Us) Bks.
  Let HUr := valid_ind_decl_uparams_relevant _ HD.
  Let HQr := valid_ind_decl_uparams_relevant _ (valid_group_valid _ _ HgQ).

  (** *** The Container's Uniform Parameters

      [m]'s instance at the group's uniform parameters [Us], at an
      environment [C2], related to the instance at the values [u3] of [Us]
      there; and moved by a semantic substitution of value [C2]. *)
    Lemma pre_typed : forall j I T, List.nth_error Is j = Some I ->
        List.nth_error (tele_insts (ind_uparams D') Id Is) j = Some T -> ind_uparams D ⊨ I : T.
    Proof. intros * HI HT; exact (valid_group_views_view_is p D Hvg Hcv _ _ _ _ _ _ _ _ _ _ HMm Hh Hq HI HT). Qed.

    Lemma pre_length : List.length Is = List.length (ind_uparams D').
    Proof.
      destruct (grp_tele_ass_views _ Hass _ _ _ _ _ _ HMm Hh) as (D5 & Mc5 & Hq5 & _ & _ & HlIs).
      rewrite Hq in Hq5; injection Hq5 as <-; exact HlIs.
    Qed.

    Lemma pre_types : forall j I, List.nth_error Is j = Some I ->
        exists T, List.nth_error (tele_insts (ind_uparams D') Id Is) j = Some T.
    Proof.
      intros j I HI; apply nth_error_lt_some'.
      rewrite length_tele_insts by exact HaQ.
      assert (j < List.length Is) by (apply List.nth_error_Some; congruence); pose proof pre_length; lia.
    Qed.

  Section Pre.
    Variable (C2 : env) (u3 cups : list domain).
    Hypotheses (HC22 : RΓ C2 C2) (HUC2 : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ u3)
      (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D u3 ↘ cups).

    (** The view's instance is scoped over the group's uniform parameters. *)
    Lemma pre_scoped : List.Forall (exp_scoped (List.length (ind_uparams D))) Is.
    Proof. exact (member_closed_head _ _ (decl_closed_members _ Hc _ _ HMm) _ _ _ _ Hh). Qed.

    (** The instance at [C2], related to it at [u3]: [Is] moved by [τU] at
        [C2] against [Is] at [τU]'s value, and that value against the
        uniform parameters' own environment. *)
    Lemma pre_base : exists uB, ⟦ im_pre Mm Us ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ uB /\
        per_gargs (List.rev (ind_uparams D')) nil nil uB cups.
    Proof.
      pose proof pre_length as HlIs.
      pose proof (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2) as Hgu3.
      pose proof (u0_len D Us HUl C2 u3 HUC2) as Hlu3.
      destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ _].
      destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
      pose proof (gsub_valid (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs HUss)) as HτU.
      (** The value of [τU] at [C2]. *)
      destruct (instance_values_of_sub _ _ Us RΓ RUΓ Ua HRΓ HRUΓ (closed_relevant_over _ _ Ua Usem HΓ HUr) HτU
                  ltac:(rewrite HUl; reflexivity) C2 C2 HC22) as [u1 u2 Eu1 Eu2 HE12 EτU _].
      pose proof (functional_eval_exps' _ _ _ _ Eu1 HUC2) as ->; pose proof (functional_eval_exps' _ _ _ _ Eu2 HUC2) as ->.
      set (E := env_extend_tagged Γ (List.rev (ind_uparams D)) (ctx_retag Γ C2) u3) in *.
      (** [Is] at [E], and moved by [τU] at [C2] against it. *)
      assert (HsIs : List.Forall (exp_scoped (List.length (ind_uparams D ++ Γ))) Is)
        by (eapply List.Forall_impl; [| exact pre_scoped ]; intros I0 HI0; eapply exp_scoped_mono; [| exact HI0 ];
            rewrite List.length_app; lia).
      destruct (closed_inst_cross _ (ind_uparams D ++ Γ) Is Is HaQ HWQ HUΓ HQr HlIs HlIs) as [HsI Hlk];
        [ intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-;
          exact (closed_app_valid _ _ _ _ _ Ua Usem HΓ (pre_typed _ _ _ HN HT))
        | exact HsIs | exact HsIs |].
      destruct (closed_instance_gargs _ _ _ _ RUΓ HaQ HWQ HUΓ HRUΓ HQr HsI HlIs HlIs E E HE12) as (u & _ & Eu & _ & _).
      destruct (closed_instance_moved_gargs _ _ Is HaQ HWQ HUΓ HQr HlIs HsI Hlk _ _ τU C2 E u HRΓ HτU HC22 EτU Eu)
        as (w & Ew & H1).
      (** [E] against the uniform parameters' own environment: their values
          stored at readable types on each side. *)
      assert (HWU' : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact Usem).
      assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
      assert (HaU' : tele_ass (List.rev (ind_uparams D))) by exact (List.Forall_rev Ua).
      assert (HUΓ' : ⊨ List.rev (List.rev (ind_uparams D)) ++ Γ) by (rewrite List.rev_involutive; exact HUΓ).
      assert (HRUΓ' : EF List.rev (List.rev (ind_uparams D)) ++ Γ ≈ List.rev (List.rev (ind_uparams D)) ++ Γ ∈ per_ctx_env ↘ RUΓ)
        by (rewrite List.rev_involutive; exact HRUΓ).
      assert (Lv : List.length (tagged_entries Γ (List.rev (ind_uparams D)) (ctx_retag Γ C2) u3) = List.length (List.rev (ind_uparams D)))
        by (rewrite tagged_entries_length, List.length_rev by (rewrite List.length_rev; unfold ind_nu in Hlu3; lia);
            unfold ind_nu in Hlu3; lia).
      assert (HE12' := HE12); unfold E in HE12'; rewrite env_extend_tagged_typed in HE12'.
      destruct (rel_gargs_readable _ _ _ _ HRΓ HUΓ' HaU' HRUΓ' _ _ _ _ Lv Lv HE12') as [Rv _].
      pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true HWU' HaU' nil nil (ctx_retag Γ C2) nil _ _ I I I Hgu3) as Hgu3'.
      assert (HE : RU E (decl_env D u3)).
      { unfold E, decl_env, env_tele; rewrite env_extend_tagged_typed.
        assert (Lv' : List.length (tele_entries nil (List.rev (ind_uparams D)) u3) = List.length (List.rev (ind_uparams D)))
          by (rewrite tele_entries_length, List.length_rev; unfold ind_nu in Hlu3; lia).
        apply (gargs_env_rel_typed _ _ _ _ per_ctx_env_nil_true HWU' HaU' HRU' (ctx_retag Γ C2) nil
                 (tagged_entries Γ (List.rev (ind_uparams D)) (ctx_retag Γ C2) u3) (tele_entries nil (List.rev (ind_uparams D)) u3)
                 I Lv Lv').
        - rewrite tagged_entries_fst, tele_entries_fst by (rewrite List.length_rev; unfold ind_nu in Hlu3; lia); exact Hgu3'.
        - exact Rv.
        - exact (proj2 (per_gargs_entries_readable _ _ _ _ _ Hgu3')). }
      pose proof (gsub_valid (valid_group_views_view_args_gsub p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq)) as HσI.
      destruct (closed_instance_gargs _ _ _ _ RU HaQ HWQ Usem HRU HQr HσI HlIs HlIs E (decl_env D u3) HE)
        as (u' & cs & Eu' & Ecs & H2).
      pose proof (functional_eval_exps' _ _ _ _ Eu' Eu) as ->; pose proof (functional_eval_exps' _ _ _ _ Ecs Ecups) as ->.
      exists w; split; [ unfold im_pre; rewrite Hh; exact Ew |].
      exact (uparams_trans D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ _ H1
               ltac:(rewrite (eval_exps_length _ _ _ Ew), List.length_map; exact pre_length) H2).
    Qed.

    (** Moved by a semantic substitution of value [C2]. *)
    Lemma pre_moved : forall Γ' RΓ' σ0 ρ0, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ -> RΓ' ρ0 ρ0 ->
        ⟦ σ0 : Γ ⟧s ρ0 ↘ C2 ->
        exists ub, ⟦ List.map (fun U => U[σ0]) (im_pre Mm Us) ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ ub /\
          per_gargs (List.rev (ind_uparams D')) nil nil ub cups.
    Proof.
      intros Γ' RΓ' σ0 ρ0 HRΓ' Hσ0 Hρ0 Hev0.
      pose proof pre_length as HlIs.
      destruct pre_base as (uB & EuB & HB).
      pose proof (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs HUss) as HgU.
      assert (Hlp : List.length (im_pre Mm Us) = List.length (ind_uparams D'))
        by (unfold im_pre; rewrite Hh, List.length_map; exact HlIs).
      assert (Hpt : forall j N T, List.nth_error (im_pre Mm Us) j = Some N ->
                 List.nth_error (tele_insts (ind_uparams D') Id (im_pre Mm Us)) j = Some T -> Γ ⊨ N : T).
      { intros j N T HN HT; unfold im_pre in HN, HT; rewrite Hh in HN, HT.
        apply nth_error_map_inv in HN as (I & HI & ->).
        destruct (pre_types _ _ HI) as [T0 HT0].
        pose proof (tele_insts_closed_sub _ _ (sb_of_list Id Us) _ _ HaQ (decl_closed_uparams _ (valid_group_closed _ _ HgQ)) HT0) as HT0'.
        rewrite HT in HT0'; injection HT0' as ->.
        pose proof (rel_exp_under_ctx_gsub HgU (closed_app_valid _ _ _ _ _ Ua Usem HΓ (pre_typed _ _ _ HI HT0))) as H.
        exact H. }
      pose proof (im_pre_scoped D m Mm Us _ Hc HMm HUl HUss) as HsP0.
      destruct (closed_inst_cross _ Γ (im_pre Mm Us) (im_pre Mm Us) HaQ HWQ HΓ HQr Hlp Hlp) as [HsP Hlk];
        [ intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; exact (Hpt _ _ _ HN HT) | exact HsP0 | exact HsP0 |].
      destruct (closed_instance_moved_gargs _ _ (im_pre Mm Us) HaQ HWQ HΓ HQr Hlp HsP Hlk _ _ σ0 ρ0 C2 uB
                  HRΓ' Hσ0 Hρ0 Hev0 EuB) as (ub & Eub & H3).
      exists ub; split; [ exact Eub |].
      exact (uparams_trans D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ _ H3
               ltac:(rewrite (eval_exps_length _ _ _ Eub), !List.length_map; exact Hlp) HB).
    Qed.
  End Pre.

  (** *** The Chain *)
  Variable (oq : option qname) (bm : eblock) (Ns : list exp) (M : exp).
  Hypotheses (Hgr : elim_grp D oq p m) (Hbm : List.nth_error Bks m = Some bm) (HNl : List.length Ns = im_nn Mm)
    (HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ))
    (Hg : gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D m Mm Us ++ Γ))
    (HM : Γ ⊨ M : ind_mty p D m Us Ns).

  Lemma view_stage : forall Γ' RΓ' σ σ' ρ ρ' C1 C2, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
      ⟦ σ : Γ ⟧s ρ ↘ C1 -> ⟦ σ' : Γ ⟧s ρ' ↘ C2 ->
      exists R, rel_exp ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ ρ C1
                  ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ' ρ' C2 (per_univ_elem iA R) /\
        rel_exp (a_elim relevant oq Us m Bks M) σ ρ C1 (a_elim relevant (Some qc) (im_pre Mm Us) k' VB M) σ' ρ' C2 R.
  Proof.
    intros * HRΓ' Hσ Hρ Hev Hev'.
    pose proof HBk as [HLb0 HnmA _ _ HnaA HBc HarA HBv].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (HPΓ' : PER RΓ') by (eapply per_env_PER; exact HRΓ').
    assert (HC12 : RΓ C1 C2) by (eapply (rel_sub_under_ctx_at' Hσ HRΓ' HRΓ); eassumption).
    assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
    assert (HC22 : RΓ C2 C2) by (etransitivity; [ symmetry; exact HC12 | exact HC12 ]).
    assert (Hρ'ρ' : RΓ' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 C1 HC11) as (u0 & _ & HUC1 & _ & _).
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 C2 HC22) as (u3 & _ & HUC2 & _ & _).
    (** The group's eliminator against itself. *)
    assert (HUU : forall j U U' T, List.nth_error Us j = Some U -> List.nth_error Us j = Some U' ->
               List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊨ U ≈ U' : T)
      by (intros * HU HU' HT; rewrite HU in HU'; injection HU' as <-; exact (HUs _ _ _ HU HT)).
    assert (HAA : forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks k = Some b' ->
               elim_mctx p D k Mk Us ++ Γ ⊨ eb_motive b ≈ eb_motive b' : Typeω@iA)
      by (intros * HMk Hb Hb'; rewrite Hb in Hb'; injection Hb' as <-; exact (HAv _ _ _ HMk Hb)).
    assert (HBB : forall k Mk b b' c0 gs0 n0 B0 B0', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
               List.nth_error Bks k = Some b' -> ind_con Mk c0 = Some gs0 ->
               brs_lookup (eb_brs b) c0 = Some (n0, B0) -> brs_lookup (eb_brs b') c0 = Some (n0, B0') ->
               elim_bctx relevant p D Mk gs0 (blocks_motives Bks) Us ++ Γ ⊨ B0 ≈ B0' : elim_branch_type p D k Mk c0 gs0 (eb_motive b) Us)
      by (intros * HMk Hb Hb' Hc0 Hl1 Hl2; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hl1 in Hl2; injection Hl2 as <-;
          exact (HBv _ _ _ _ _ _ _ HMk Hb Hc0 (brs_lookup_in _ _ _ _ Hl1))).
    destruct (elim_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC1 C2 HC12 Bks iA HBks HMall HAv
                oq oq Us m Mm bm Bks Ns M M Hgr Hgr HMm Hbm HLb0 HLb0 HnmA HnmA HnaA
                (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HarA HBc HAA HBB HNl HgN Hg HM
                HUl HUU Γ' RΓ' σ σ' ρ ρ' HRΓ' Hσ Hρ Hev Hev') as (RT & HTy & HLv).
    exists RT; split; [ exact HTy |].
    destruct HLv as [r1 r2 r3 r4 Er1 Er2 Er3 Er4 Hch].
    destruct (elim_exp_value_of _ _ _ _ _ _ _ Er3) as [u3' m3 pg Eu3 Em3 Egr3 Eel3].
    pose proof (functional_eval_exps' _ _ _ _ Eu3 HUC2) as ->.
    (** The scrutinee at [C2]. *)
    destruct (presup_rel_exp_under_ctx HM) as [iT HTM].
    destruct (rel_type_inversion_simple_at HRΓ HTM _ _ HC22) as (t3 & t3' & Et3 & Et3' & [Rt Ht]).
    assert (t3' = t3) as -> by (eapply functional_eval_exp; eassumption).
    (** The scrutinee's type is an inductive type, relevant. *)
    assert (Ht3r : rel_typ_sort (ind_mty p D m Us Ns) C2 relevant).
    { exists t3; split; [ exact Et3 |].
      destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Et3) as (? & ? & _ & _ & ->).
      reflexivity. }
    destruct (rel_exp_under_ctx_simple_at_relevant HRΓ HM _ _ HC22 Ht3r) as (m3' & m3'' & Em3' & Em3'' & Hmm).
    assert (m3' = m3) as -> by (eapply functional_eval_exp; eassumption).
    assert (m3'' = m3) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (Hmm _ _ _ _ Et3 Et3 Ht) as Hm33.
    assert (HrvM : im_is_rview Mm = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm HrvM Et3) as (cs3 & ns3 & _ & Ens3 & _).
    destruct (scrut_rel VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 m Mm HMm (HMall _ _ HMm) Ns HNl HgN
                C2 HC22 ns3 ns3 Ens3 Ens3 t3 t3 _ Rt Et3 Et3 Ht) as [_ ERt].
    pose proof (proj1 (ERt _ _) Hm33) as G33.
    (** The scrutinee moved by [σ'] at [ρ']. *)
    pose proof (rel_sub_under_ctx_refl_right Hσ) as Hσ'.
    pose proof HM as [RΓm HRΓm iM HMg].
    destruct (HMg _ _ HRΓ' _ _ Hσ' _ _ _ _ Hρ'ρ' Hev' Hev') as (RMe & HTyM & HMor).
    pose proof (rel_exp_or_prop_relevant HTyM Ht3r HMor) as [m4 m2 m5 m6 Em4 Em2 Em5 Em6 Hmc].
    destruct HTyM as [t1 t2 t5 t4 Et1 Et2 Et5 Et4 Htc].
    assert (t2 = t3) as -> by (eapply functional_eval_exp; eassumption).
    assert (m2 = m3) as -> by (eapply functional_eval_exp; eassumption).
    destruct Htc as (_ & Ht23 & _); destruct Hmc as (H12 & _ & _).
    assert (ERM : Rt <~> RMe) by (eapply per_univ_elem_right_irrel; [ exact Ht | exact Ht23 ]).
    pose proof (proj1 (ERt _ _) (proj2 (ERM _ _) H12)) as G43.
    (** The group's eliminator at [C2]. *)
    destruct (elim_grp_of_elem _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMm G33 (decl_typed_order _ _ _ Hdt) oq Hgr) as [Hgr3 _].
    rewrite Hgr3 in Egr3; injection Egr3 as <-.
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (D2 & Mk' & Hl2 & HMk' & _ & _ & _ & Hvk & _).
    (** The view's instance at [C2] and moved. *)
    destruct (rel_ctx_wf_per_ctx_env HWQ) as [RQ HRQ].
    assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
    pose proof (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2) as Hgu3.
    pose proof (u0_len D Us HUl C2 u3 HUC2) as Hlu3.
    destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq u3 u3 Hgu3 Hlu3) as (cups & _ & Ecups & _ & _).
    assert (Lcups : List.length cups = List.length (ind_uparams D'))
      by (rewrite (eval_exps_length _ _ _ Ecups); exact pre_length).
    destruct (pre_base C2 u3 cups HC22 HUC2 Ecups RQ HRQ) as (uB & EuB & HB).
    assert (LuB : List.length uB = List.length (ind_uparams D'))
      by (rewrite (eval_exps_length _ _ _ EuB); unfold im_pre; rewrite Hh, List.length_map; exact pre_length).
    pose proof (gargs_of_rq _ _ _ HRQ LuB Lcups HB) as HubB.
    destruct (pre_moved C2 u3 cups HC22 HUC2 Ecups Γ' RΓ' σ' ρ' RQ HRΓ' Hσ' Hρ'ρ' Hev' HRQ) as (ub' & Eub' & HB').
    assert (Lub' : List.length ub' = List.length (ind_uparams D'))
      by (rewrite (eval_exps_length _ _ _ Eub'), !List.length_map; unfold im_pre; rewrite Hh, List.length_map;
          exact pre_length).
    pose proof (gargs_of_rq _ _ _ HRQ Lub' Lcups HB') as HubB'.
    (** The container's eliminator at [C2], against the group's. *)
    pose proof (wrapped_at_has VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as HbB.
    pose proof (wrapped_at_binder_count VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as HnmB.
    pose proof (wrapped_at_names VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as HnaB.
    pose proof (wrapped_at_arity VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as HarB.
    pose proof (wrapped_at_motive VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as Hmot.
    pose proof (wrapped_at_branch VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh) as Hbr.
    pose proof (cross_bot_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh C2 VB uB HbB HnmB HnaB HarB Hmot Hbr cups Ecups HubB) as Hbot.
    destruct (cross_elim_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                Hq HMm Hh C2 VB uB HbB HnmB HnaB HarB Hmot Hbr (fun i' j => Hbot j i')) as [CE _].
    destruct (CE _ _ _ _ _ _ _ G33 k' Hvk) as [Mi1 Mj1 rc rg _ _ _ _ Erc Erg HRc | ? Mj1 ? ? ? ? ? ? ? ? ? ? ? ? _ _ _ HMj1 Hhj1 _ _ _ _ _ _];
      [| exfalso; rewrite HMm in HMj1; injection HMj1 as <-; rewrite Hh in Hhj1; discriminate Hhj1 ].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Erg Eel3) as ->.
    (** The container's eliminator at the moved blocks, against the group's. *)
    pose proof (moved_at_has VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HbB'.
    pose proof (moved_at_binder_count VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HnmB'.
    pose proof (moved_at_names VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HnaB'.
    pose proof (moved_at_arity VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HarB'.
    pose proof (moved_at_motive VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as Hmot'.
    pose proof (moved_at_branch VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as Hbr'.
    pose proof (cross_bot_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh ρ' (blocks_sub VB σ') ub' HbB' HnmB' HnaB' HarB' Hmot' Hbr' cups Ecups HubB') as Hbot'.
    destruct (cross_elim_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                Hq HMm Hh ρ' (blocks_sub VB σ') ub' HbB' HnmB' HnaB' HarB' Hmot' Hbr' (fun i' j => Hbot' j i')) as [CE' _].
    destruct (CE' _ _ _ _ _ _ _ G43 k' Hvk) as [Mi2 Mj2 rd rg' _ _ _ _ Erd Erg' HRd | ? Mj2 ? ? ? ? ? ? ? ? ? ? ? ? _ _ _ HMj2 Hhj2 _ _ _ _ _ _];
      [| exfalso; rewrite HMm in HMj2; injection HMj2 as <-; rewrite Hh in Hhj2; discriminate Hhj2 ].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Erg' Eel3) as ->.
    (** The family's relation at [C2], the type's. *)
    destruct HTy as [y1 y2 y3 y4 Ey1 Ey2 Ey3 Ey4 Hyc].
    destruct Hyc as (_ & Hy23 & _).
    assert (HPR : PER RT) by (eapply per_elem_PER; exact Hy23).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hy23) Hy23) as Hy33.
    pose proof (per_head_iff Ey3 Ey3 Hy33) as ER1.
    (** The motive's instance at [C2]: the terms' values, the motive's
        context being relevant. *)
    destruct (rel_ctx_wf_per_ctx_env (HMall _ _ HMm)) as [RM HRM].
    assert (Lτ : List.length (Ns ++ M :: nil) = List.length (elim_mctx p D m Mm Us))
      by (rewrite List.length_app, length_elim_mctx, HNl; cbn [List.length]; lia).
    destruct (sb_of_list_values_of_sub (elim_mctx p D m Mm Us) Γ Γ Id (Ns ++ M :: nil) RΓ RM C2 C2
                (elim_mctx_ass p D m Mm Us Hc HMm) HRΓ HRM
                (mctx_relevant VP p D HP HPD Γ HΓ Us HUl HUs m Mm HMm (HMall _ _ HMm)) (gsub_valid Hg) Lτ HC22
                (eval_sub_id _ _ (proj1 (per_ctx_env_proofs _ _ _ HRΓ _ _ HC22)))) as (q3 & Eq3 & Hτ3 & _).
    assert (Eq3' : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ ns3 ++ m3 :: nil)
      by (apply eval_exps_app; [ exact Ens3 | econstructor; [ exact Em3 | constructor ] ]).
    pose proof (functional_eval_exps' _ _ _ _ Eq3 Eq3') as ->.
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMm Hbm) HRΓ (gsub_valid Hg) HC22 Hτ3 Hτ3) as ER2.
    assert (Hfin : forall a b, per_head (List.nth m (blocks_motives Bks) a_placeholder_type) (List.nth m (blocks_motives Bks) a_placeholder_type)
                     (env_args C2 (ns3 ++ m3 :: nil)) (env_args C2 (ns3 ++ m3 :: nil)) a b -> RT a b).
    { intros a b H; apply ER1, ER2; rewrite (blocks_motives_nth _ _ _ Hbm) in H; exact H. }
    pose proof (rel_resp VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 C2 HC22 Bks iA HBks HMall HAv
                  m Mm HMm HrvM _ _ _ _ _ _ ns3 m4 ns3 m3 ns3 m3 ns3 m3 G43 G33 G33) as ER3.
    assert (Hrc : RT rc r3) by (apply Hfin; exact HRc).
    assert (Hrd : RT rd r3) by (apply Hfin, ER3; exact HRd).
    destruct Hch as (Hr12 & Hr23 & _).
    apply (mk_rel_exp r1 r2 rc rd).
    - exact Er1.
    - exact Er2.
    - eapply eval_exp_elim; [ exact EuB | exact Em3 | reflexivity | exact Erc ].
    - rewrite exp_sub_elim; eapply eval_exp_elim; [ exact Eub' | exact Em4 | reflexivity | exact Erd ].
    - apply rel_chain_cons; [ exact Hr12 |].
      apply rel_chain_cons; [ etransitivity; [ exact Hr23 | symmetry; exact Hrc ] |].
      apply rel_chain_of_pair; etransitivity; [ exact Hrc | symmetry; exact Hrd ].
  Qed.
End ElimViewRule.

(** ** The Rule *)
Theorem rel_exp_under_ctx_elim_view : forall VP p D, valid_groups VP -> VP p D ->
    forall Γ oq m Mm qc k' Is vm D' bm Bks Ps M (i : nat),
    ⊨ Γ -> elim_grp D oq p m ->
    ind_member D m = Some Mm -> im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ Pk : T) ->
    Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       ⊨ elim_bctx relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) ->
       elim_bctx relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊨ a_elim relevant oq (List.firstn (ind_nu D) Ps) m Bks M
      ≈ a_elim relevant (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
          (view_wrap relevant p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros VP p D HP HPD * HΓ Hgr HMm Hh Hq Hbm HLb HPl HPs HM HnmA HMall HAv HnaA HBc HarA HBv.
  pose proof (valid_groups_valid VP HP p D HPD) as Hvg.
  pose proof (valid_group_closed _ _ Hvg) as Hc; pose proof (valid_group_valid _ _ Hvg) as HD.
  destruct (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs) as [HUs HNs].
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (mk_valid_blocks p D Γ Us Bks i HLb HnmA HMall HAv HnaA HBc HarA HBv) as HBk.
  pose proof (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns HNl HNs) as HgN.
  pose proof (gsub_tau VP p D HP HPD Γ HΓ Us HUl m Mm HMm (HMall _ _ HMm) Ns M HNl HNs HM) as Hg.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ i _).
  intros Γ' RΓ' HRΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (view_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs Bks i HBk qc D' m Mm k' Is vm Hq HMm Hh
              oq bm Ns M Hgr Hbm HNl HgN Hg HM Γ' RΓ' σ σ' ρ ρ' ρσ ρ'σ' HRΓ' Hσ Hρ Hev Hev') as (R & HT & HE).
  exists R; split; [ exact HT | right; exact HE ].
Qed.

End Fixed_GCtx.
