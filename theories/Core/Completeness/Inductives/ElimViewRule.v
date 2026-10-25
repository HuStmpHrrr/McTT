(** * The Eliminator at a View, as Its Container's

    The semantic rule E1′: the eliminator of a valid group at its view [m]
    of the container's member [k'] is the container's eliminator at [k']
    with the wrapped blocks ([vwrap]).  At a semantic substitution of
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
Record elim_exp_value (oq : option qname) (Us : list exp) (j : nat) (Bks : list eblock) (M : exp) (ρ : env) (r : domain) : Prop :=
  mk_elim_exp_value
  { (** The uniform parameters' values *)
    elim_exp_value_ups : list domain
    (** The scrutinee's value *)
  ; elim_exp_value_scrut : domain
    (** The group eliminated *)
  ; elim_exp_value_grp : qname
    (** [Us] evaluate to [elim_exp_value_ups] *)
  ; elim_exp_value_ups_eval : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ elim_exp_value_ups
    (** [M] evaluates to [elim_exp_value_scrut] *)
  ; elim_exp_value_scrut_eval : ⟦ M ⟧ ρ ↘ elim_exp_value_scrut
    (** The group is the annotation's, or the scrutinee's *)
  ; elim_exp_value_grp_of : elim_grp_of oq elim_exp_value_scrut = Some elim_exp_value_grp
    (** The eliminator on the scrutinee's value gives [r] *)
  ; elim_exp_value_elim : ⟦elim elim_exp_value_scrut at j of elim_exp_value_grp elim_exp_value_ups Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r }.

Lemma elim_exp_value_of : forall oq Us j Bks M ρ r, ⟦ a_elim oq Us j Bks M ⟧ ρ ↘ r -> elim_exp_value oq Us j Bks M ρ r.
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
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := valid_ind_decl_uparams _ HD.
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := valid_blocks_has _ _ _ _ _ _ HBk.
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
  Let VB := vwrap p D D' vm Us Bks.

  (** *** The Container's Uniform Parameters

      [m]'s instance at the group's uniform parameters [Us], at an
      environment [C2], related to the instance at the values [u3] of [Us]
      there; and moved by a semantic substitution of value [C2]. *)
    Lemma pre_typed : forall j I T, List.nth_error Is j = Some I ->
        List.nth_error (tele_insts (ind_uparams D') Id Is) j = Some T -> ind_uparams D ⊨ I : T.
    Proof. intros * HI HT; exact (vg_view_is p D Hvg Hcv _ _ _ _ _ _ _ _ _ _ HMm Hh Hq HI HT). Qed.

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
      (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil u3 ↘ cups).

    (** The instance at [C2], related to it at [u3]. *)
    Lemma pre_base : forall RQ, EF ind_uparams D' ≈ ind_uparams D' ∈ per_ctx_env ↘ RQ ->
        exists uB, ⟦ im_pre Mm Us ⟧* gc_deps ⍮ gc_stack ⍮ C2 ↘ uB /\ RQ (env_args nil uB) (env_args nil cups).
    Proof.
      intros RQ HRQ.
      pose proof pre_length as HlIs.
      assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
      pose proof (u0_gargs VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2) as Hgu3.
      pose proof (u0_len D Us HUl C2 u3 HUC2) as Hlu3.
      assert (HU3 : RU (env_args nil u3) (env_args nil u3)) by exact (uparams_rel_env D HD u3 u3 Hgu3 Hlu3 RU HRU).
      assert (HU33 : RU (env_args C2 u3) (env_args nil u3))
        by (eapply closed_env_base; [ exact Ua | exact Usem | exact HRU | exact Hlu3 | exact Hlu3 | exact HU3 ]).
      (** [Is] at the two bases of [u3]. *)
      pose proof (gsub_valid (vg_view_args_gsub p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq)) as HσI.
      destruct (sb_of_list_vals_rel _ _ _ _ RQ RU HaQ HWQ Usem HRQ HRU HσI HlIs HlIs _ _ HU33)
        as (cs0 & cups' & Ecs0 & Ecups' & H2).
      pose proof (functional_eval_exps' _ _ _ _ Ecups' Ecups) as ->.
      (** [Is] moved by [τU] at [C2], against at its value. *)
      destruct (closed_app_sem _ _ Ua Usem HΓ) as [HUΓ _].
      destruct (closed_inst_cross _ (ind_uparams D ++ Γ) Is Is HaQ HWQ HUΓ HlIs HlIs) as [_ Hlk].
      { intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-.
        exact (closed_app_valid _ _ _ _ _ Ua Usem HΓ (pre_typed _ _ _ HN HT)). }
      assert (HTy : forall j I, List.nth_error Is j = Some I -> exists T, ind_uparams D ++ Γ ⊨ I : T).
      { intros j I HI; destruct (pre_types _ _ HI) as [T HT]; exists T.
        exact (closed_app_valid _ _ _ _ _ Ua Usem HΓ (pre_typed _ _ _ HI HT)). }
      pose proof (gsub_valid (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs)) as HτU.
      pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id C2) HUC2) as EτU.
      destruct (closed_vals_sub_link _ _ Is RQ HaQ HWQ HUΓ HRQ HlIs HTy Hlk _ _ τU C2 (env_args C2 u3) cs0
                  HRΓ HτU HC22 EτU Ecs0) as (w & Ew & H1).
      exists w; split; [ unfold im_pre; rewrite Hh; exact Ew |].
      etransitivity; [ exact H1 | exact H2 ].
    Qed.

    (** Moved by a semantic substitution of value [C2]. *)
    Lemma pre_moved : forall Γ' RΓ' σ0 ρ0 RQ, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ0 ≈ σ0 : Γ -> RΓ' ρ0 ρ0 ->
        ⟦ σ0 ⟧s ρ0 ↘ C2 -> EF ind_uparams D' ≈ ind_uparams D' ∈ per_ctx_env ↘ RQ ->
        exists ub, ⟦ List.map (fun U => U[σ0]) (im_pre Mm Us) ⟧* gc_deps ⍮ gc_stack ⍮ ρ0 ↘ ub /\
          RQ (env_args nil ub) (env_args nil cups).
    Proof.
      intros Γ' RΓ' σ0 ρ0 RQ HRΓ' Hσ0 Hρ0 Hev0 HRQ.
      pose proof pre_length as HlIs.
      assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
      destruct (pre_base RQ HRQ) as (uB & EuB & HB).
      pose proof (gsub_U VP p D HP HPD Γ HΓ Us HUl HUs) as HgU.
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
      destruct (closed_inst_cross _ Γ (im_pre Mm Us) (im_pre Mm Us) HaQ HWQ HΓ Hlp Hlp) as [_ Hlk].
      { intros j N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; exact (Hpt _ _ _ HN HT). }
      assert (HTy : forall j N, List.nth_error (im_pre Mm Us) j = Some N -> exists T, Γ ⊨ N : T).
      { intros j N HN.
        destruct (nth_error_lt_some' (tele_insts (ind_uparams D') Id (im_pre Mm Us)) j) as [T HT].
        { rewrite length_tele_insts by exact HaQ.
          assert (j < List.length (im_pre Mm Us)) by (apply List.nth_error_Some; congruence); lia. }
        exists T; exact (Hpt _ _ _ HN HT). }
      destruct (closed_vals_sub_link _ _ (im_pre Mm Us) RQ HaQ HWQ HΓ HRQ Hlp HTy Hlk _ _ σ0 ρ0 C2 uB
                  HRΓ' Hσ0 Hρ0 Hev0 EuB) as (ub & Eub & H3).
      exists ub; split; [ exact Eub | etransitivity; [ exact H3 | exact HB ] ].
    Qed.
  End Pre.

  Lemma gargs_of_rq : forall RQ xs ys, EF ind_uparams D' ≈ ind_uparams D' ∈ per_ctx_env ↘ RQ ->
      List.length xs = List.length (ind_uparams D') -> List.length ys = List.length (ind_uparams D') ->
      RQ (env_args nil xs) (env_args nil ys) -> per_gargs (List.rev (ind_uparams D')) nil nil xs ys.
  Proof.
    intros * HRQ Hx Hy H.
    assert (HWQ' : ⊨ List.rev (List.rev (ind_uparams D')) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HWQ).
    assert (HRQ' : EF List.rev (List.rev (ind_uparams D')) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D')) ++ ⋅ ∈ per_ctx_env ↘ RQ)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRQ).
    destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HWQ' (List.Forall_rev HaQ) HRQ' nil nil xs ys
                ltac:(rewrite List.length_rev; exact Hx) ltac:(rewrite List.length_rev; exact Hy) H) as [_ Hg].
    exact Hg.
  Qed.

  (** *** The Chain *)
  Variable (oq : option qname) (bm : eblock) (Ns : list exp) (M : exp).
  Hypotheses (Hgr : elim_grp D oq p m) (Hbm : List.nth_error Bks m = Some bm) (HNl : List.length Ns = im_nn Mm)
    (HgN : gsub Γ (sb_of_list Id Ns) (tele_sub (im_nparams Mm) τU ++ Γ))
    (Hg : gsub Γ (sb_of_list Id (Ns ++ M :: nil)) (elim_mctx p D m Mm Us ++ Γ))
    (HM : Γ ⊨ M : ind_mty p D m Us Ns).

  Lemma view_stage : forall Γ' RΓ' σ σ' ρ ρ' C1 C2, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ' : Γ -> RΓ' ρ ρ' ->
      ⟦ σ ⟧s ρ ↘ C1 -> ⟦ σ' ⟧s ρ' ↘ C2 ->
      exists R, rel_exp ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ ρ C1
                  ((eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)]) σ' ρ' C2 (per_univ_elem iA R) /\
        rel_exp (a_elim oq Us m Bks M) σ ρ C1 (a_elim (Some qc) (im_pre Mm Us) k' VB M) σ' ρ' C2 R.
  Proof.
    intros * HRΓ' Hσ Hρ Hev Hev'.
    pose proof HBk as [_ HnmA _ _ HnaA HBc HarA HBv].
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
               elim_bctx p D Mk gs0 (blocks_motives Bks) Us ++ Γ ⊨ B0 ≈ B0' : elim_bty p k Mk c0 gs0 (eb_motive b) Us)
      by (intros * HMk Hb Hb' Hc0 Hl1 Hl2; rewrite Hb in Hb'; injection Hb' as <-; rewrite Hl1 in Hl2; injection Hl2 as <-;
          exact (HBv _ _ _ _ _ _ _ HMk Hb Hc0 (brs_lookup_in _ _ _ _ Hl1))).
    destruct (elim_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC1 C2 HC12 Bks iA HBks HMall HAv
                oq oq Us m Mm bm Bks Ns M M Hgr Hgr HMm Hbm HBks HnmA HnmA HnaA
                (fun _ _ _ H1 H2 => ltac:(rewrite H1 in H2; injection H2 as <-; reflexivity)) HarA HBc HAA HBB HNl HgN Hg HM
                HUl HUU Γ' RΓ' σ σ' ρ ρ' HRΓ' Hσ Hρ Hev Hev') as (RT & HTy & HLv).
    exists RT; split; [ exact HTy |].
    destruct HLv as [r1 r2 r3 r4 Er1 Er2 Er3 Er4 Hch].
    destruct (elim_exp_value_of _ _ _ _ _ _ _ Er3) as [u3' m3 pg Eu3 Em3 Egr3 Eel3].
    pose proof (functional_eval_exps' _ _ _ _ Eu3 HUC2) as ->.
    (** The scrutinee at [C2]. *)
    destruct (presup_rel_exp_under_ctx HM) as [iT HTM].
    destruct (rel_exp_of_typ_inversion_simple_at HRΓ HTM _ _ HC22) as (t3 & t3' & Et3 & Et3' & [Rt Ht]).
    assert (t3' = t3) as -> by (eapply functional_eval_exp; eassumption).
    destruct (rel_exp_under_ctx_simple_at HRΓ HM _ _ HC22) as (m3' & m3'' & Em3' & Em3'' & Hmm).
    assert (m3' = m3) as -> by (eapply functional_eval_exp; eassumption).
    assert (m3'' = m3) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (Hmm _ _ _ _ Et3 Et3 Ht) as Hm33.
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMm Et3) as (cs3 & ns3 & _ & Ens3 & _).
    destruct (scrut_rel VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 m Mm HMm (HMall _ _ HMm) Ns HNl HgN
                C2 HC22 ns3 ns3 Ens3 Ens3 t3 t3 _ Rt Et3 Et3 Ht) as [_ ERt].
    pose proof (proj1 (ERt _ _) Hm33) as G33.
    (** The scrutinee moved by [σ'] at [ρ']. *)
    pose proof (rel_sub_under_ctx_refl_right Hσ) as Hσ'.
    pose proof HM as [RΓm HRΓm iM HMg].
    destruct (HMg _ _ HRΓ' _ _ Hσ' _ _ _ _ Hρ'ρ' Hev' Hev')
      as (RMe & [t1 t2 t5 t4 Et1 Et2 Et5 Et4 Htc] & [m4 m2 m5 m6 Em4 Em2 Em5 Em6 Hmc]).
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
    destruct (vg_view_args_values p D Hvg Hcv _ _ _ _ _ _ _ HMm Hh Hq u3 u3 Hgu3 Hlu3) as (cups & _ & Ecups & _ & _).
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
    pose proof (wrapped_at_nm VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
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
    destruct (CE _ _ _ _ _ _ _ G33 k' Hvk) as (rc & rg & Erc & Erg & HRc).
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Erg Eel3) as ->.
    (** The container's eliminator at the moved blocks, against the group's. *)
    pose proof (moved_at_has VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
                  Hq HMm Hh Γ' RΓ' σ' ρ' HRΓ' Hσ' Hρ'ρ' Hev') as HbB'.
    pose proof (moved_at_nm VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 Bks iA HBk qc D' m Mm k' Is vm
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
    destruct (CE' _ _ _ _ _ _ _ G43 k' Hvk) as (rd & rg' & Erd & Erg' & HRd).
    pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Erg' Eel3) as ->.
    (** The family's relation at [C2], the type's. *)
    destruct HTy as [y1 y2 y3 y4 Ey1 Ey2 Ey3 Ey4 Hyc].
    destruct Hyc as (_ & Hy23 & _).
    assert (HPR : PER RT) by (eapply per_elem_PER; exact Hy23).
    pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hy23) Hy23) as Hy33.
    pose proof (per_head_iff Ey3 Ey3 Hy33) as ER1.
    assert (Hτ3 : ⟦ sb_of_list Id (Ns ++ M :: nil) ⟧s C2 ↘ env_args C2 (ns3 ++ m3 :: nil))
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply eval_exps_app; [ exact Ens3 | econstructor; [ exact Em3 | constructor ] ] ]).
    pose proof (per_head_inst _ _ _ _ _ _ _ _ _ _ (HAv _ _ _ HMm Hbm) HRΓ (gsub_valid Hg) HC22 Hτ3 Hτ3) as ER2.
    assert (Hfin : forall a b, per_head (List.nth m (blocks_motives Bks) a_True) (List.nth m (blocks_motives Bks) a_True)
                     (env_args C2 (ns3 ++ m3 :: nil)) (env_args C2 (ns3 ++ m3 :: nil)) a b -> RT a b).
    { intros a b H; apply ER1, ER2; rewrite (blocks_motives_nth _ _ _ Hbm) in H; exact H. }
    pose proof (rel_resp VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C2 u3 HC22 HUC2 C2 HC22 Bks iA HBks HMall HAv
                  m Mm HMm _ _ _ _ _ _ ns3 m4 ns3 m3 ns3 m3 ns3 m3 G43 G33 G33) as ER3.
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
    List.nth_error Bks m = Some bm -> List.length Bks = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k Pk T, List.nth_error Ps k = Some Pk -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Γ ⊨ Pk : T) ->
    Γ ⊨ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> ⊨ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊨ eb_motive b : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       ⊨ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> ind_con Mk c = Some gs ->
       In (c, n, B) (eb_brs b) ->
       elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊨ B
         : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊨ a_elim oq (List.firstn (ind_nu D) Ps) m Bks M
      ≈ a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k' (vwrap p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
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
  assert (HBks : forall j Mj, ind_member D j = Some Mj -> exists b, List.nth_error Bks j = Some b).
  { intros * HMj; apply nth_error_lt_some'; rewrite HLb; apply List.nth_error_Some; unfold ind_member in HMj; congruence. }
  pose proof (mk_valid_blocks p D Γ Us Bks i HBks HnmA HMall HAv HnaA HBc HarA HBv) as HBk.
  pose proof (gsub_ns VP p D HP HPD Γ HΓ Us m Mm HMm (HMall _ _ HMm) Ns HNl HNs) as HgN.
  pose proof (gsub_tau VP p D HP HPD Γ HΓ Us HUl m Mm HMm (HMall _ _ HMm) Ns M HNl HNs HM) as Hg.
  destruct (rel_ctx_wf_per_ctx_env HΓ) as [RΓ HRΓ].
  destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_uparams _ HD)) as [RU HRU].
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HRΓ i _).
  intros Γ' RΓ' HRΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exact (view_stage VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs Bks i HBk qc D' m Mm k' Is vm Hq HMm Hh
           oq bm Ns M Hgr Hbm HNl HgN Hg HM Γ' RΓ' σ σ' ρ ρ' ρσ ρ'σ' HRΓ' Hσ Hρ Hev Hev').
Qed.

End Fixed_GCtx.
