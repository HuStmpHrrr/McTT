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
  ViewBranch ElimView ViewReadback ContainerReadable.
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

Lemma elim_exp_value_of : forall p Us j Bks M ρ r, ⟦ a_elim ak_relevant p Us j Bks M ⟧ ρ ↘ r -> elim_exp_value p Us j Bks M ρ r.
Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

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
  Let Ua : all_assumptions (ind_uparams D) := uparams_ass D Hc.
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
  Let HaQ : all_assumptions (ind_uparams D') := uparams_ass D' (valid_group_closed _ _ HgQ).
  Let HWQ : ⊨ ind_uparams D' := valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ).
  Let VB := view_wrap ak_relevant p qc D D' vm Us (im_pre Mm Us) Bks.
  Let HUr := valid_ind_decl_uparams_evaluated _ HD.
  Let HQr := valid_ind_decl_uparams_evaluated _ (valid_group_valid _ _ HgQ).

  (** *** The Container's Uniform Parameters

      [m]'s instance at the group's uniform parameters [Us], at an
      environment [C2], related to the instance at the values [u3] of [Us]
      there; and moved by a semantic substitution of value [C2]. *)
    Lemma pre_typed : forall j I T, List.nth_error Is j = Some I ->
        List.nth_error (tele_insts (ind_uparams D') Id Is) j = Some T -> ind_uparams D ⊨ I : T.
    Proof. intros * HI HT; exact (valid_group_views_view_is p D Hvg Hcv _ _ _ _ _ _ _ _ _ _ HMm Hh Hq HI HT). Qed.

    Lemma pre_length : List.length Is = List.length (ind_uparams D').
    Proof.
      destruct (group_structure_views _ Hass _ _ _ _ _ _ HMm Hh) as (D5 & Mc5 & Hq5 & _ & _ & HlIs).
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
        per_tele_args (List.rev (ind_uparams D')) nil nil uB cups.
    Proof.
      pose proof pre_length as HlIs.
      pose proof (u0_tele_args VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2) as Hgu3.
      pose proof (u0_len D Us HUl C2 u3 HUC2) as Hlu3.
      destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ _].
      destruct (rel_ctx_wf_per_ctx_env HUΓ) as [RUΓ HRUΓ].
      pose proof (gsub_valid (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs HUss)) as HτU.
      (** The value of [τU] at [C2]. *)
      destruct (instance_values_of_sub _ _ Us RΓ RUΓ Ua HRΓ HRUΓ (closed_evaluated_over _ _ Ua Usem HΓ HUr) HτU
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
      destruct (closed_instance_tele_args _ _ _ _ RUΓ HaQ HWQ HUΓ HRUΓ HQr HsI HlIs HlIs E E HE12) as (u & _ & Eu & _ & _).
      destruct (closed_instance_moved_tele_args _ _ Is HaQ HWQ HUΓ HQr HlIs HsI Hlk _ _ τU C2 E u HRΓ HτU HC22 EτU Eu)
        as (w & Ew & H1).
      (** [E] against the uniform parameters' own environment: their values
          stored at readable types on each side. *)
      assert (HWU' : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact Usem).
      assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
      assert (HaU' : all_assumptions (List.rev (ind_uparams D))) by exact (List.Forall_rev Ua).
      assert (HUΓ' : ⊨ List.rev (List.rev (ind_uparams D)) ++ Γ) by (rewrite List.rev_involutive; exact HUΓ).
      assert (HRUΓ' : EF List.rev (List.rev (ind_uparams D)) ++ Γ ≈ List.rev (List.rev (ind_uparams D)) ++ Γ ∈ per_ctx_env ↘ RUΓ)
        by (rewrite List.rev_involutive; exact HRUΓ).
      assert (Lv : List.length (tagged_entries Γ (List.rev (ind_uparams D)) (ctx_retag Γ C2) u3) = List.length (List.rev (ind_uparams D)))
        by (rewrite tagged_entries_length, List.length_rev by (rewrite List.length_rev; unfold ind_nu in Hlu3; lia);
            unfold ind_nu in Hlu3; lia).
      assert (HE12' := HE12); unfold E in HE12'; rewrite env_extend_tagged_typed in HE12'.
      destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HUΓ' HaU' HRUΓ' _ _ _ _ Lv Lv HE12') as [Rv _].
      pose proof (per_tele_args_base _ _ _ per_ctx_env_nil_true HWU' HaU' nil nil (ctx_retag Γ C2) nil _ _ I I I Hgu3) as Hgu3'.
      assert (HE : RU E (decl_env D u3)).
      { unfold E, decl_env, env_tele; rewrite env_extend_tagged_typed.
        assert (Lv' : List.length (tele_entries nil (List.rev (ind_uparams D)) u3) = List.length (List.rev (ind_uparams D)))
          by (rewrite tele_entries_length, List.length_rev; unfold ind_nu in Hlu3; lia).
        apply (tele_args_env_rel_typed _ _ _ _ per_ctx_env_nil_true HWU' HaU' HRU' (ctx_retag Γ C2) nil
                 (tagged_entries Γ (List.rev (ind_uparams D)) (ctx_retag Γ C2) u3) (tele_entries nil (List.rev (ind_uparams D)) u3)
                 I Lv Lv').
        - rewrite tagged_entries_fst, tele_entries_values by (rewrite List.length_rev; unfold ind_nu in Hlu3; lia); exact Hgu3'.
        - exact Rv.
        - exact (proj2 (per_tele_args_entries_readable _ _ _ _ _ Hgu3')). }
      pose proof (gsub_valid (valid_group_views_view_args_gsub p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq)) as HσI.
      destruct (closed_instance_tele_args _ _ _ _ RU HaQ HWQ Usem HRU HQr HσI HlIs HlIs E (decl_env D u3) HE)
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
          per_tele_args (List.rev (ind_uparams D')) nil nil ub cups.
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
      destruct (closed_instance_moved_tele_args _ _ (im_pre Mm Us) HaQ HWQ HΓ HQr Hlp HsP Hlk _ _ σ0 ρ0 C2 uB
                  HRΓ' Hσ0 Hρ0 Hev0 EuB) as (ub & Eub & H3).
      exists ub; split; [ exact Eub |].
      exact (uparams_trans D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ _ H3
               ltac:(rewrite (eval_exps_length _ _ _ Eub), !List.length_map; exact Hlp) HB).
    Qed.
  End Pre.

  (** *** The Chain *)
  Variable (bm : eblock) (Ns : list exp) (M : exp).
  Hypotheses (Hbm : List.nth_error Bks m = Some bm) (HNl : List.length Ns = im_nn Mm)
    (HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ))
    (Hg : gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D m Mm Us ++ Γ))
    (HM : Γ ⊨ M : ind_mty p D m Us Ns).

  Lemma view_stage : forall Γ' RΓ' σ σ' ρ ρ' C1 C2, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
      ⟦ σ : Γ ⟧s ρ ↘ C1 -> ⟦ σ' : Γ ⟧s ρ' ↘ C2 ->
      exists R, rel_exp ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ ρ C1
                  ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ' ρ' C2 (per_univ_elem iA R) /\
        rel_exp (a_elim ak_relevant p Us m Bks M) σ ρ C1 (a_elim ak_relevant qc (im_pre Mm Us) k' VB M) σ' ρ' C2 R.
  Proof.
    intros * HRΓ' Hσ Hρ Hev Hev'.
    pose proof HBk as [HLb0 HnmA _ _ HnaA HBc HarA HBv].
    assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HRΓ).
    assert (HPΓ' : PER RΓ') by (eapply per_env_PER; exact HRΓ').
    assert (HC12 : RΓ C1 C2) by (eapply (rel_sub_under_ctx_at' Hσ HRΓ' HRΓ); eassumption).
    assert (HC11 : RΓ C1 C1) by (etransitivity; [ exact HC12 | symmetry; exact HC12 ]).
    assert (HC22 : RΓ C2 C2) by (etransitivity; [ symmetry; exact HC12 | exact HC12 ]).
    assert (Hρ'ρ' : RΓ' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C1 C1 HC11) as (u0 & _ & HUC1 & _ & _).
    destruct (us_vals VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 C2 HC22) as (u3 & _ & HUC2 & _ & _).
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
               elim_bctx ak_relevant p D Mk gs0 (blocks_motives Bks) Us ++ Γ ⊨ B0 ≈ B0' : elim_branch_type p D k Mk c0 gs0 (eb_motive b) Us)
      by (intros * HMk Hb Hb' Hc0 Hl1 Hl2; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hl1 in Hl2; injection Hl2 as <-;
          exact (HBv _ _ _ _ _ _ _ HMk Hb Hc0 (brs_lookup_in _ _ _ _ Hl1))).
    destruct (elim_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C1 u0 HC11 HUC1 C2 HC12 Bks iA HBks HMall HAv
                Us m Mm bm Bks Ns M M HMm Hbm HLb0 HLb0 HnmA HnmA HnaA
                (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HarA HBc HAA HBB HNl HgN Hg HM
                HUl HUss HUU Γ' RΓ' σ σ' ρ ρ' HRΓ' Hσ Hρ Hev Hev') as (RT & HTy & HLv).
    exists RT; split; [ exact HTy |].
    destruct HLv as [r1 r2 r3 r4 Er1 Er2 Er3 Er4 Hch].
    destruct (elim_exp_value_of _ _ _ _ _ _ _ Er3) as [u3' m3 Eu3 Em3 Eel3].
    pose proof (functional_eval_exps' _ _ _ _ Eu3 HUC2) as ->.
    (** The scrutinee at [C2]. *)
    destruct (presup_rel_exp_under_ctx_mty _ _ _ _ _ _ _ _ _ HMm HM) as [iT HTM].
    destruct (rel_type_inversion_simple_at HRΓ HTM _ _ HC22) as (t3 & t3' & Et3 & Et3' & [Rt Ht]).
    assert (t3' = t3) as -> by (eapply functional_eval_exp; eassumption).
    (** The scrutinee's type is an inductive type, relevant. *)
    assert (Ht3r : rel_typ_kind (ind_mty p D m Us Ns) C2 ak_relevant).
    { exists t3; split; [ exact Et3 |].
      destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Et3) as (? & ? & _ & _ & ->).
      reflexivity. }
    destruct (rel_exp_under_ctx_simple_at_evaluated HRΓ HM _ _ HC22 (rel_typ_evaluated_of_kind Ht3r evaluated_kind_relevant)) as (m3' & m3'' & Em3' & Em3'' & Hmm).
    assert (m3' = m3) as -> by (eapply functional_eval_exp; eassumption).
    assert (m3'' = m3) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (Hmm _ _ _ _ Et3 Et3 Ht) as Hm33.
    assert (HrvM : im_is_rview Mm = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm HrvM Et3) as (cs3 & ns3 & _ & Ens3 & _).
    destruct (scrut_rel VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 m Mm HMm (HMall _ _ HMm) Ns HNl HgN
                C2 HC22 ns3 ns3 Ens3 Ens3 t3 t3 _ Rt Et3 Et3 Ht) as [_ ERt].
    pose proof (proj1 (ERt _ _) Hm33) as G33.
    (** The scrutinee moved by [σ'] at [ρ']. *)
    pose proof (rel_sub_under_ctx_refl_right Hσ) as Hσ'.
    pose proof HM as [RΓm HRΓm iM HMg].
    destruct (HMg _ _ HRΓ' _ _ Hσ' _ _ _ _ Hρ'ρ' Hev' Hev') as (RMe & HTyM & HMor).
    pose proof (rel_exp_or_prop_evaluated HTyM (rel_typ_evaluated_of_kind Ht3r evaluated_kind_relevant) HMor) as [m4 m2 m5 m6 Em4 Em2 Em5 Em6 Hmc].
    destruct HTyM as [t1 t2 t5 t4 Et1 Et2 Et5 Et4 Htc].
    assert (t2 = t3) as -> by (eapply functional_eval_exp; eassumption).
    assert (m2 = m3) as -> by (eapply functional_eval_exp; eassumption).
    destruct Htc as (_ & Ht23 & _); destruct Hmc as (H12 & _ & _).
    assert (ERM : Rt <~> RMe) by (eapply per_univ_elem_right_irrel; [ exact Ht | exact Ht23 ]).
    pose proof (proj1 (ERt _ _) (proj2 (ERM _ _) H12)) as G43.
    (** The group's eliminator at [C2]. *)
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (D2 & Mk' & Hl2 & HMk' & _ & _ & _ & Hvk & _).
    (** The view's instance at [C2] and moved: related to the instance at
        [u3] ([pre_base], [pre_moved]). *)
    pose proof (u0_tele_args VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2) as Hgu3.
    pose proof (u0_len D Us HUl C2 u3 HUC2) as Hlu3.
    pose proof (valid_group_adm p D Hvg u3 u3 Hgu3 Hlu3 Hgu3) as Had3.
    destruct (valid_group_views_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq u3 u3 Hgu3 Hlu3) as (cups & _ & Ecups & _ & _).
    destruct (pre_base C2 u3 cups HC22 HUC2 Ecups) as (uB & EuB & HubB).
    assert (LuB : List.length uB = ind_nu D')
      by (rewrite (eval_exps_length _ _ _ EuB); unfold im_pre; rewrite Hh, List.length_map; exact pre_length).
    destruct (pre_moved C2 u3 cups HC22 HUC2 Ecups Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as (ub' & Eub' & HubB').
    assert (Lub' : List.length ub' = ind_nu D')
      by (rewrite (eval_exps_length _ _ _ Eub'), List.length_map; unfold im_pre; rewrite Hh, List.length_map; exact pre_length).
    pose proof (valid_group_valid _ _ HgQ) as HDQ; pose proof (valid_group_closed _ _ HgQ) as HcQ.
    pose proof (group_ups_ok VP qc D' HP HVQ uB (uparams_refl_l D' HDQ HcQ _ _ HubB) LuB) as HcupsB.
    pose proof (group_ups_ok VP qc D' HP HVQ ub' (uparams_refl_l D' HDQ HcQ _ _ HubB') Lub') as HcupsB'.
    (** [C2] agrees with its retagging on [Γ]. *)
    pose proof (eval_sub_agree_retag _ _ _ _ Hev') as HCa2.
    (** The container's eliminator at [C2], against the group's. *)
    pose proof (wrapped_at_has VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as HbB.
    pose proof (wrapped_at_binder_count VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as HnmB.
    pose proof (wrapped_at_names VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as HnaB.
    pose proof (wrapped_at_arity VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as HarB.
    pose proof (wrapped_at_motive VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as Hmot.
    pose proof (wrapped_at_branch VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh) as Hbr.
    pose proof (container_motive_entries_readable VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh C2 VB uB LuB HbB HnmB HnaB HarB Hmot cups Ecups HubB HcupsB) as Hcmot.
    pose proof (container_branch_entries_readable VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh C2 VB uB LuB HbB HnmB HnaB HarB Hmot cups Ecups HubB HcupsB) as Hcbr.
    pose proof (cross_bot_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss qc D' m Mm k' Is vm
                  Hq HMm Hh C2 VB uB LuB HbB HnmB HnaB HarB Hmot Hbr Hcbr Hcmot cups Ecups HubB HcupsB) as Hbot.
    destruct (cross_elim_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss qc D' m Mm k' Is vm
                Hq HMm Hh C2 VB uB LuB HbB HnmB HnaB HarB Hmot Hbr Hcbr Hcmot (fun i' j => Hbot j i')) as [CE _].
    destruct (CE _ _ _ _ _ _ _ G33 Had3 Had3 k' Hvk)
      as [Mi1 Mj1 rc rg _ _ _ _ Erc Erg HRc | ? Mj1 ? ? ? ? ? ? ? ? ? ? ? ? _ _ _ HMj1 Hhj1 _ _ _ _ _ _];
      [| exfalso; rewrite HMm in HMj1; injection HMj1 as <-; rewrite Hh in Hhj1; discriminate Hhj1 ].
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Erg Eel3) as ->.
    (** The container's eliminator at the moved blocks, against the group's. *)
    pose proof (moved_at_has VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HbB'.
    pose proof (moved_at_binder_count VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HnmB'.
    pose proof (moved_at_names VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HnaB'.
    pose proof (moved_at_arity VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HarB'.
    pose proof (moved_at_motive VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as Hmot'.
    pose proof (moved_at_branch VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HCa2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as Hbr'.
    pose proof (container_motive_entries_readable VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh ρ' (blocks_sub VB σ') ub' Lub' HbB' HnmB' HnaB' HarB' Hmot' cups Ecups HubB' HcupsB')
      as Hcmot'.
    pose proof (container_branch_entries_readable VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss
                  qc D' m Mm k' Is vm Hq HMm Hh ρ' (blocks_sub VB σ') ub' Lub' HbB' HnmB' HnaB' HarB' Hmot' cups Ecups HubB' HcupsB')
      as Hcbr'.
    pose proof (cross_bot_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss qc D' m Mm k' Is vm
                  Hq HMm Hh ρ' (blocks_sub VB σ') ub' Lub' HbB' HnmB' HnaB' HarB' Hmot' Hbr' Hcbr' Hcmot' cups Ecups HubB' HcupsB')
      as Hbot'.
    destruct (cross_elim_all VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 Bks iA HBk HBss qc D' m Mm k' Is vm
                Hq HMm Hh ρ' (blocks_sub VB σ') ub' Lub' HbB' HnmB' HnaB' HarB' Hmot' Hbr' Hcbr' Hcmot' (fun i' j => Hbot' j i'))
      as [CE' _].
    destruct (CE' _ _ _ _ _ _ _ G43 Had3 Had3 k' Hvk)
      as [Mi2 Mj2 rd rg' _ _ _ _ Erd Erg' HRd | ? Mj2 ? ? ? ? ? ? ? ? ? ? ? ? _ _ _ HMj2 Hhj2 _ _ _ _ _ _];
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
    destruct (sb_of_list_values_of_sub (elim_mctx p D m Mm Us) Γ Γ Id (Ns ++ M :: nil) RΓ RM C2 (ctx_retag Γ C2)
                (elim_mctx_ass p D m Mm Us Hc HMm) HRΓ HRM
                (mctx_evaluated VP p D HP HPD Γ HΓ Us HUl HUs HUss m Mm HMm (HMall _ _ HMm)) (gsub_valid Hg) Lτ HC22
                (eval_sub_id _ _)) as (q3 & Eq3 & Hτ3 & _).
    assert (Eq3' : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ ns3 ++ m3 :: nil)
      by (apply eval_exps_app; [ exact Ens3 | econstructor; [ exact Em3 | constructor ] ]).
    pose proof (functional_eval_exps' _ _ _ _ Eq3 Eq3') as ->.
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMm Hbm) HRΓ (gsub_valid Hg) HC22 Hτ3 Hτ3) as ER2.
    (** The instance's environment at [C2], against the canonical one of
        the motive's family ([Elim.v]'s chain, at [C2] on both sides). *)
    assert (HPM : PER RM) by (eapply per_env_PER; exact HRM).
    pose proof (rel_sub_under_ctx_at' (gsub_valid Hg) HRΓ HRM _ _ _ _ HC22 Hτ3 Hτ3) as L1.
    pose proof (L1 : RM _ _) as L1'.
    rewrite !env_extend_tagged_typed in L1.
    destruct (mctx_rev_sem VP p D HP HPD Γ Us HMall _ _ HMm RM HRM) as (HMr & HRMr & Hta).
    destruct (mctx_len VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 _ _ HMm _ _ _ _ _ _ G33) as [Ll _].
    assert (Lt : List.length (tagged_entries Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C2) (ns3 ++ m3 :: nil))
                 = List.length (List.rev (elim_mctx p D m Mm Us)))
      by (rewrite tagged_entries_length by exact (eq_sym Ll); exact Ll).
    destruct (per_tele_args_of_env_extend_readable _ _ _ _ HRΓ HMr Hta HRMr _ _ _ _ Lt Lt L1) as [Hrd0 _].
    destruct (mctx_readable VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HMall
                _ _ HMm C2 C2 HC22 HC22 _ _ _ _ _ _ G33) as [Hrc0 _].
    pose proof (mctx_at_typed VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HMall
                  _ _ HMm _ _ (per_ctx_env_retag_left HRΓ _ _ HC22) HC22 RM HRM _ _ _ _ _ _ G33 _ _
                  (tagged_entries_fst _ Γ (ctx_retag Γ C2) (ns3 ++ m3 :: nil) (eq_sym Ll))
                  (tele_entries_values _ _ _) Hrd0 Hrc0) as Lc.
    pose proof (mctx_at VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 HMall
                  _ _ HMm C2 C2 HC22 HC22 RM HRM _ _ _ _ _ _ G33) as L3.
    assert (Ch : rel_chain RM (env_extend_tagged Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C2) (ns3 ++ m3 :: nil)
                               :: env_extend_tagged Γ (List.rev (elim_mctx p D m Mm Us)) (ctx_retag Γ C2) (ns3 ++ m3 :: nil)
                               :: env_tele C2 (List.rev (elim_mctx p D m Mm Us)) (ns3 ++ m3 :: nil)
                               :: env_tele C2 (List.rev (elim_mctx p D m Mm Us)) (ns3 ++ m3 :: nil) :: nil)).
    { apply rel_chain_cons; [ exact L1' |].
      apply rel_chain_cons; [ rewrite env_extend_tagged_typed; etransitivity; [ symmetry; exact L1 | exact Lc ] |].
      apply rel_chain_of_pair; exact L3. }
    pose proof (per_head_of_typ_resp HRM (HAv _ _ _ HMm Hbm) _ _ _ _ Ch) as ER4.
    assert (Hfin : forall a b, per_head (List.nth m (blocks_motives Bks) a_prop) (List.nth m (blocks_motives Bks) a_prop)
                     (env_tele C2 (List.rev (elim_mctx p D m Mm Us)) (ns3 ++ m3 :: nil))
                     (env_tele C2 (List.rev (elim_mctx p D m Mm Us)) (ns3 ++ m3 :: nil)) a b -> RT a b).
    { intros a b H; apply ER1, ER2, ER4; rewrite (blocks_motives_nth _ _ _ Hbm) in H; exact H. }
    pose proof (rel_resp VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C2 u3 HC22 HUC2 C2 HC22 Bks iA HBks HMall HAv
                  m Mm HMm HrvM _ _ _ _ _ _ ns3 m4 ns3 m3 ns3 m3 ns3 m3 G43 G33 G33) as ER3.
    rewrite HMm in HRc, HRd.
    assert (Hrc : RT rc r3) by (apply Hfin; exact HRc).
    cbn beta in ER3; rewrite HMm in ER3.
    assert (Hrd : RT rd r3) by (apply Hfin; exact (proj1 (ER3 rd r3) HRd)).
    destruct Hch as (Hr12 & Hr23 & _).
    apply (mk_rel_exp r1 r2 rc rd).
    - exact Er1.
    - exact Er2.
    - eapply eval_exp_elim; [ exact EuB | exact Em3 | exact Erc ].
    - rewrite exp_sub_elim; eapply eval_exp_elim; [ exact Eub' | exact Em4 | exact Erd ].
    - apply rel_chain_cons; [ exact Hr12 |].
      apply rel_chain_cons; [ etransitivity; [ exact Hr23 | symmetry; exact Hrc ] |].
      apply rel_chain_of_pair; etransitivity; [ exact Hrc | symmetry; exact Hrd ].
  Qed.
End ElimViewRule.

(** ** The Rule *)
Theorem rel_exp_under_ctx_elim_view : forall VP p D, valid_groups VP -> VP p D ->
    forall Γ m Mm qc k' Is vm D' bm Bks Ps M (i : nat),
    ⊨ Γ ->
    ind_member D m = Some Mm -> im_head Mm = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ Pk : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ps ->
    Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    exp_scoped (List.length Γ) M ->
    blocks_scoped (List.length Γ) Bks ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       ⊨ elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) ->
       elim_bctx ak_relevant p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊨ a_elim ak_relevant p (List.firstn (ind_nu D) Ps) m Bks M
      ≈ a_elim ak_relevant qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
          (view_wrap ak_relevant p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M
      : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros VP p D HP HPD * HΓ HMm Hh Hq Hbm HLb HPl HPs HPss HM HMs HBss HnmA HMall HAv HnaA HBc HarA HBv.
  pose proof (valid_groups_valid VP HP p D HPD) as Hvg.
  pose proof (valid_group_closed _ _ Hvg) as Hc; pose proof (valid_group_valid _ _ Hvg) as HD.
  destruct (params_valid_split D m Mm Γ Ps Hc HMm HPl HPs) as [HUs HNs].
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
  pose proof (Forall_firstn' _ (ind_nu D) _ HPss) as HUss; pose proof (Forall_skipn' _ (ind_nu D) _ HPss) as HNss.
  fold Us in HUss; fold Ns in HNss.
  pose proof (mk_valid_blocks p D Γ Us Bks i HLb HnmA HMall HAv HnaA HBc HarA HBv) as HBk.
  pose proof (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns HNl HNs HNss) as HgN.
  pose proof (gsub_tau VP p D HP HPD Γ HΓ Us HUl m Mm HMm (HMall _ _ HMm) Ns M HNl HNs HM
                (proj2 (List.Forall_app _ _ _) (conj HNss (List.Forall_cons _ HMs (List.Forall_nil _))))) as Hg.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ i _).
  intros Γ' RΓ' HRΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (view_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss Bks i HBk HBss qc D' m Mm k' Is vm Hq HMm Hh
              bm Ns M Hbm HNl HgN Hg HM Γ' RΓ' σ σ' ρ ρ' ρσ ρ'σ' HRΓ' Hσ Hρ Hev Hev') as (R & HT & HE).
  exists R; split; [ exact HT | right; exact HE ].
Qed.

End Fixed_GCtx.
