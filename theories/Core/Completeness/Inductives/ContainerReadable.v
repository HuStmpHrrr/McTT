(** * The Container's Eliminator's Entries Read Back

    The container's eliminator at a view's wrapped blocks ([view_wrap])
    stores the variables of its motives and branches at the container's
    types at its uniform parameters [ub]: the non-uniform parameters at the
    container's telescope, the arguments at the container's constructor's,
    the recursive results at the container's motives' instances.  The
    elements it takes them from are the group's at the view
    ([ElimView.CrossElim]): related at the group's canonical relations.
    They read back at the container's types: the group's elements at a
    view are the container's at the view's instance [cups]
    ([ViewCoherence.view_group_to_container]), and so at any uniform
    parameters related to it, as [ub] is; the container's own uniform
    parameters at [ub] then read them back ([elim_ups_ok]).

    These are [ElimView.CrossElim]'s and [ViewReadback.CrossBot]'s
    hypotheses [Hcmot_x] and [Hcbr_x], which [ElimViewRule] discharges
    here. *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con CargsRel Elim
  Iota ViewBranch ElimView ViewReadback.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence ViewCount IndElim ReadPairs.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** A Valid Group at Its Own Uniform Parameters

    [Elim.v]'s model of a valid group's eliminator at the group's own
    uniform parameters' context, the parameters as variables
    ([vars_from]), at the environment of values [u] related to themselves:
    the eliminator's uniform parameters at [u] ([elim_ups_ok]), and the
    relation of a member's type at uniform parameters related to [u]. *)

(** The uniform parameters' variables are typed at their own telescope. *)
Lemma group_uparams_vars_typed : forall pg Dg, valid_group pg Dg ->
    forall k N T, List.nth_error (vars_from 0 (ind_nu Dg)) k = Some N ->
      List.nth_error (tele_insts (ind_uparams Dg) Id (vars_from 0 (ind_nu Dg))) k = Some T -> ind_uparams Dg ⊨ N : T.
Proof.
  intros pg Dg Hg k N T HN HT.
  pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
  destruct (uniform_param_vars_lookup Dg (decl_closed_ass _ Hc) (decl_mvc_uparams _ (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)))
              (decl_closed_uparams _ Hc) k N T HN HT) as (x & -> & Hx).
  exact (valid_exp_under_ctx_vlookup Hx (valid_ind_decl_uparams _ HD)).
Qed.

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
  pose proof (valid_group_valid _ _ Hg) as HD.
  pose proof (valid_ind_decl_uparams _ HD) as HUD.
  destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
  pose proof (vars_from_scoped 0 (ind_nu Dg) (List.length (ind_uparams Dg)) ltac:(unfold ind_nu; lia)) as HVss.
  pose proof (uparams_rel_env Dg HD u u Hgu Hu RU HRU) as HC.
  pose proof (eval_uvars_components Dg u nil nil 0 0 Hu eq_refl) as HE.
  unfold ind_uvars in HE; cbn [Nat.add components_env env_tele] in HE.
  exact (ups_ok VP pg Dg HP HPG (ind_uparams Dg) RU HRU HUD RU HRU (vars_from 0 (ind_nu Dg)) (length_vars_from _ _)
           (group_uparams_vars_typed pg Dg Hg) HVss (decl_env Dg u) u HC HE u u HC HC Hu Hu).
Qed.

(** The type of a member of a valid group at uniform parameters [w]
    related to [u], against it at [u]: related, at the group's elements at
    the canonical relations at [u], at the bases [u] and [w]
    ([member_type_from_u0]). *)
Lemma group_member_type : forall VP pg Dg, valid_groups VP -> VP pg Dg ->
    forall u w, per_gargs (List.rev (ind_uparams Dg)) nil nil u u -> List.length u = ind_nu Dg ->
    per_gargs (List.rev (ind_uparams Dg)) nil nil w u -> List.length w = ind_nu Dg ->
    forall j Mj hd0 k0 p0 hd k pw bs bs', ind_member Dg j = Some Mj -> im_is_rview Mj = false ->
      ⟦mref j of pg u ⟧ gc_deps ⍮ gc_stack ↘ (hd0, k0, p0) -> ⟦mref j of pg w ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pw) ->
      tele_rel (canon_nparams_rel Dg u j) (List.rev (im_nparams Mj)) bs bs' ->
      exists (i : universe_index) R, DF d_ind hd0 k0 (p0 ++ bs) ≈ d_ind hd k (pw ++ bs') ∈ per_univ_elem i ↘ R /\
        (R <~> grp_rel pg Dg u (canon_nparams_rel Dg u) (canon_args_rel Dg u) (canon_doms_rel Dg u) j u w bs bs').
Proof.
  intros VP pg Dg HP HPG u w Hgu Hu Hwu Lw * HMj Hrv E0 Ew Hbs.
  pose proof (valid_groups_valid VP HP pg Dg HPG) as Hg.
  pose proof (valid_group_valid _ _ Hg) as HD.
  pose proof (valid_ind_decl_uparams _ HD) as HUD.
  destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
  pose proof (vars_from_scoped 0 (ind_nu Dg) (List.length (ind_uparams Dg)) ltac:(unfold ind_nu; lia)) as HVss.
  pose proof (uparams_rel_env Dg HD u u Hgu Hu RU HRU) as HC.
  pose proof (uparams_rel_env Dg HD w u Hwu Lw RU HRU) as Hw.
  pose proof (eval_uvars_components Dg u nil nil 0 0 Hu eq_refl) as HE.
  unfold ind_uvars in HE; cbn [Nat.add components_env env_tele] in HE.
  exact (member_type_from_u0 VP pg Dg HP HPG (ind_uparams Dg) RU HRU HUD RU HRU (vars_from 0 (ind_nu Dg)) (length_vars_from _ _)
           (group_uparams_vars_typed pg Dg Hg) HVss (decl_env Dg u) u HC HE w j Mj hd0 k0 p0 hd k pw bs bs' Hw Lw HMj Hrv E0 Ew Hbs).
Qed.

(** ** The Domains of a Container's Shape in the Group's Relation

    [container_doms_link dr k drQ kQ pre Ts preQ TsQ t' t]: the domains of
    the container's shape [t'], after the prefix [preQ] of the telescope
    [TsQ] in the container's relation [drQ], against those of the group's
    shape [t] after [pre] of [Ts] in the group's [dr]: an element of the
    container's domain is one of the group's, and the rests after it. *)
(** [container_doms_link] nests through a conjunction; its nested
    induction principle needs the [All] scheme of [and]. *)
Scheme All for and.

Inductive container_doms_link (dr : nat -> list domain -> list centry -> exp -> relation domain) (k : nat)
    (drQ : nat -> list domain -> list centry -> exp -> relation domain) (kQ : nat) :
    list domain -> list centry -> list domain -> list centry -> ptyp -> ptyp -> Prop :=
(** At the ends, nothing *)
| container_doms_link_self : forall pre Ts preQ TsQ j' Ps' j Ps,
    container_doms_link dr k drQ kQ pre Ts preQ TsQ (pt_self j' Ps') (pt_self j Ps)
(** At a domain on each side: the container's elements are the group's,
    and the rests after each *)
| container_doms_link_pi : forall pre Ts preQ TsQ B' t' B t,
    (forall c c', drQ kQ preQ TsQ B' c c' ->
       dr k pre Ts B c c /\
       container_doms_link dr k drQ kQ (pre ++ c :: nil) (Ts ++ ce_ass B :: nil) (preQ ++ c :: nil) (TsQ ++ ce_ass B' :: nil) t' t) ->
    container_doms_link dr k drQ kQ pre Ts preQ TsQ (pt_pi B' t') (pt_pi B t).

(** The non-dependent induction over the cross relations of
    [ElimView.CrossRel]. *)
Scheme cross_result_rel_min_ind := Minimality for cross_result_rel Sort Prop
with cross_result_app_rel_min_ind := Minimality for cross_result_app_rel Sort Prop
with cross_fields_rel_min_ind := Minimality for cross_fields_rel Sort Prop.
Combined Scheme cross_result_rel_min_ind_all from cross_result_rel_min_ind, cross_result_app_rel_min_ind, cross_fields_rel_min_ind.

(** ** The Container's Entries at the Group's Elements

    The setting of [ElimView.CrossElim], without the hypotheses on the
    container's readback this section proves: the group's eliminator at
    [C1], the view [m] of the container's member [k'], the container's
    eliminator at blocks [VBb] in [ρb], at uniform parameters [ub] related
    to the view's instance [cups], with the container's own eliminator's
    uniform parameters at [ub] ([Hcups_x]). *)
Section ContainerReadable.
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
  Let Hrs : rview_struct_ok gc_deps gc_stack D := grp_tele_ass_record_struct _ Hass.
  Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ Hrs).
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T)
    (HUss : List.Forall (exp_scoped (List.length Γ)) Us).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA) (HBss : blocks_scoped (List.length Γ) Bks).
  Let HBks := valid_blocks_has p D Γ Us Bks iA Hdt HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel D u0.
  Let G := grp_rel p D u0 nr ar dr.
  (** The family of the motives at [C1], as [Elim.v] has it. *)
  Let mctx_tele j := match ind_member D j with Some Mj => List.rev (elim_mctx p D j Mj Us) | None => nil end.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) exp_default) (List.nth j (blocks_motives Bks) exp_default)
      (env_tele C1 (mctx_tele j) (ns ++ m :: nil)) (env_tele C1 (mctx_tele j) (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C1 u0 HC11 HUC).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (valid_group_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation Had := (valid_group_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs').

  (** The view [m] of the container's member [k'], its map [vm]. *)
  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Let HVQ := valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq.
  Let HgQ := valid_groups_valid VP HP qc D' HVQ.
  Let HcvQ := containers_valid_of_groups VP HP qc D' HVQ.
  Let HDQ := valid_group_valid _ _ HgQ.
  Let HcQ := valid_group_closed _ _ HgQ.
  Let HassQ := valid_group_ass _ _ HgQ.
  Let HrsQ : rview_struct_ok gc_deps gc_stack D' := grp_tele_ass_record_struct _ HassQ.
  Let HlcQ : leaves_coherent D' := leaves_coherent_of_order D' (rview_struct_order _ _ _ HrsQ).

  (** The container's eliminator: a block for each member with one. *)
  Variable (ρb : env) (VBb : list eblock) (ub : list domain).
  Hypotheses (Lub : List.length ub = ind_nu D')
    (HbB : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> exists b, List.nth_error VBb i' = Some b)
    (HnmB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> eb_binder_count b = S (im_nn Mi'))
    (HnaB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> brs_names (im_cons Mi') (eb_brs b))
    (HarB : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b ->
              ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec D' gs')%nat).
  (** The motives, at related indices and elements stored at any types they
      read back at ([ElimView.CrossElim]). *)
  Hypothesis (Hmot_x : forall i' Mi' v bb ba u u' ns ns' x x' ts ts', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
                List.nth_error vm i' = Some v -> List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                G v u u' ns ns' x x' ->
                List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ x :: nil) ts ->
                List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ x' :: nil) ts' ->
                exists a a', ⟦ eb_motive bb ⟧ env_extend_typed ρb (List.combine (ns ++ x :: nil) ts) ↘ a /\
                  ⟦ eb_motive ba ⟧ env_extend_typed C1 (List.combine (ns' ++ x' :: nil) ts') ↘ a' /\
                  DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x').
  (** The view's instance at [u0], and [ub] related to it. *)
  Variable (cups : list domain).
  Hypotheses (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D u0 ↘ cups)
    (Hub : per_gargs (List.rev (ind_uparams D')) nil nil ub cups).
  (** The container's canonical relations at [cups] and at [ub]. *)
  Let nrC := canon_nparams_rel D' cups.
  Let arC := canon_args_rel D' cups.
  Let drC := canon_doms_rel D' cups.
  Let nrQ := canon_nparams_rel D' ub.
  Let arQ := canon_args_rel D' ub.
  Let drQ := canon_doms_rel D' ub.
  #[local] Abbreviation Hcc := (view_container_uparams_rel p D Hvg Hcv m Mm qc k' Is vm D' HMm Hh Hq u0 cups u0_gargs' u0_len' Ecups).
  #[local] Abbreviation Lc := (length_container_uparams p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups).
  #[local] Abbreviation Hcu := (uparams_sym D' HDQ HcQ _ _ Hub Lub).
  #[local] Abbreviation Hubub := (uparams_refl_l D' HDQ HcQ _ _ Hub).
  #[local] Abbreviation HcpC := (valid_group_canon qc D' HgQ cups Hcc Lc).
  #[local] Abbreviation HcpQ := (valid_group_canon qc D' HgQ ub Hubub Lub).
  #[local] Abbreviation HadC := (valid_group_adm qc D' HgQ cups cups Hcc Lc Hcc).
  #[local] Abbreviation HadCu := (valid_group_adm qc D' HgQ cups ub Hcc Lc Hcu).
  (** The view's coherence at the canonical relations at [u0] and [cups]. *)
  #[local] Abbreviation Hvc := (view_agreement_canonical_all VP p D HP HPD u0 u0 u0_gargs' u0_len' m Mm qc k' Is vm D' cups cups
                                  HMm Hh Hq Ecups Ecups).
  (** The container's eliminator's uniform parameters [ub], at the
      container's own canonical relations. *)
  Hypothesis (Hcups_x : elim_ups_ok qc D' ub nrQ arQ drQ ub ub).

  (** The members of the container's group and those of the group the
      view's map takes them to ([ElimView.cross_member]). *)
  Lemma container_view_member : forall i' j, List.nth_error vm i' = Some j ->
      exists Mi' Mj, ind_member D' i' = Some Mi' /\ view_member p D qc D' vm i' Mi' j Mj.
  Proof.
    intros i' j Hv.
    destruct (grp_tele_ass_view_wrap _ Hass _ _ _ _ _ _ HMm Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    assert (Hi : i' < List.length (ind_members D')) by (rewrite <- (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' _ _ Hi) as [Mi' HMi'].
    destruct (view_agree_members p D m Mm qc k' Is vm D' Hass HMm Hh Hq i' Mi' HMi') as (v & Mv & Hvm).
    pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm) as Hv'; rewrite Hv in Hv'; injection Hv' as <-.
    exists Mi', Mv; split; [ exact HMi' | exact Hvm ].
  Qed.

  (** The group's non-uniform parameters of a member the view takes the
      container's member [i'] to are the container's at [ub]: at [cups]
      by the view ([nr_from]), and [ub] and [cups] are related. *)
  Lemma group_nparams_to_container : forall i' Mi' v Mv a b, ind_member D' i' = Some Mi' ->
      view_member p D qc D' vm i' Mi' v Mv -> tele_rel (nr v) (List.rev (im_nparams Mv)) a b ->
      tele_rel (nrQ i') (List.rev (im_nparams Mi')) a b.
  Proof.
    intros * HM Hvm Hab.
    pose proof (nr_from p D u0 u0 nr ar dr qc D' cups cups nrC arC drC vm Hvc i' Mi' v Mv a b HM Hvm Hab) as HabC.
    exact (canon_nparams_base qc D' HgQ cups ub Hcc Lc Hcu i' Mi' HM a b HabC).
  Qed.

  (** The elements of a member of the container at the canonical relations
      at [cups], at the bases [cups] and [ub], are those at [ub]: both are
      the elements of the member's type at [ub] ([group_member_type]). *)
  Lemma container_rel_base_iff : forall i' Mi' ns ns', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      tele_rel (nrC i') (List.rev (im_nparams Mi')) ns ns' ->
      forall x y, grp_rel qc D' cups nrC arC drC i' cups ub ns ns' x y <-> grp_rel qc D' ub nrQ arQ drQ i' ub ub ns ns' x y.
  Proof.
    intros * HM Hrv Hns x y.
    pose proof (group_ups_ok VP qc D' HP HVQ cups Hcc Lc) as [_ _ _ _ MaC _ _ _ _ _ _ _].
    pose proof Hcups_x as [_ _ _ _ MaQ _ _ _ _ _ _ _].
    destruct (proj1 (MaC i' Mi' HM) Hrv) as [[[hd0 k0] p0] E0].
    destruct (proj1 (MaQ i' Mi' HM) Hrv) as [[[hd k] pw] Ew].
    pose proof (canon_nparams_base qc D' HgQ cups ub Hcc Lc Hcu i' Mi' HM _ _ Hns) as HnsQ.
    destruct (group_member_type VP qc D' HP HVQ cups ub Hcc Lc Hub Lub i' Mi' hd0 k0 p0 hd k pw ns ns' HM Hrv E0 Ew Hns)
      as (i1 & R1 & T1 & ER1).
    destruct (group_member_type VP qc D' HP HVQ ub ub Hubub Lub Hubub Lub i' Mi' hd k pw hd k pw ns ns' HM Hrv Ew Ew HnsQ)
      as (i2 & R2 & T2 & ER2).
    pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ T1 T2) as E12.
    split; intros Hxy; [ apply ER2, E12, ER1; exact Hxy | apply ER1, E12, ER2; exact Hxy ].
  Qed.

  Lemma container_rel_base : forall i' Mi' ns ns' x y, ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      grp_rel qc D' cups nrC arC drC i' cups ub ns ns' x y -> grp_rel qc D' ub nrQ arQ drQ i' ub ub ns ns' x y.
  Proof.
    intros * HM Hrv Hxy.
    destruct HcpC as [CnP CnI CaP CaI CdP CdI].
    pose proof (ind_rel_ns qc D' cups nrC arC drC HassQ CnP CnI CaP CaI CdP CdI _ i' Mi' _ _ _ _ _ _ HM Hxy) as Hns.
    exact (proj1 (container_rel_base_iff i' Mi' ns ns' HM Hrv Hns x y) Hxy).
  Qed.

  (** An element of a member of the group the view takes the container's
      member [i'] to, at any bases, is one of the container's at [ub]:
      at [u0] ([ind_rel_rebase]), then the container's at [cups]
      ([view_group_to_container]), at the bases [cups] and [ub]
      ([ind_rel_rebase]), and at [ub] ([container_rel_base]). *)
  Lemma group_to_container_rel : forall i' Mi' v Mv u u' ns ns' x y, ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      view_member p D qc D' vm i' Mi' v Mv -> G v u u' ns ns' x y -> grp_rel qc D' ub nrQ arQ drQ i' ub ub ns ns' x y.
  Proof.
    intros * HM Hrv Hvm Hxy.
    pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI v u u' u0 u0 ns ns' x y Had Had Had Hxy) as H0.
    destruct HcpC as [CnP CnI CaP CaI CdP CdI].
    pose proof (view_group_to_container p D u0 u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI qc D' cups cups nrC arC drC HassQ
                  CnP CnI CaP CaI CdP CdI vm Hvc i' Mi' v Mv ns ns' x y HM Hvm H0) as H1.
    pose proof (ind_rel_rebase qc D' cups nrC arC drC HassQ CnP CnI CaP CaI CdP CdI i' cups cups cups ub ns ns' x y HadC HadC HadCu H1)
      as H2.
    exact (container_rel_base i' Mi' ns ns' x y HM Hrv H2).
  Qed.

  (** Conversely, an element of the container's member [i'] at [ub] is one
      of the group's member the view takes [i'] to, at [u0]. *)
  Lemma container_to_group_rel : forall i' Mi' v Mv ns ns' x y, ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      view_member p D qc D' vm i' Mi' v Mv -> grp_rel qc D' ub nrQ arQ drQ i' ub ub ns ns' x y -> G v u0 u0 ns ns' x y.
  Proof.
    intros * HM Hrv Hvm Hxy.
    destruct HcpQ as [QnP QnI QaP QaI QdP QdI].
    pose proof (ind_rel_ns qc D' ub nrQ arQ drQ HassQ QnP QnI QaP QaI QdP QdI _ i' Mi' _ _ _ _ _ _ HM Hxy) as HnsQ.
    pose proof (canon_nparams_base qc D' HgQ ub cups Hubub Lub Hub i' Mi' HM _ _ HnsQ) as Hns.
    pose proof (proj2 (container_rel_base_iff i' Mi' ns ns' HM Hrv Hns x y) Hxy) as H1.
    destruct HcpC as [CnP CnI CaP CaI CdP CdI].
    pose proof (ind_rel_rebase qc D' cups nrC arC drC HassQ CnP CnI CaP CaI CdP CdI i' cups ub cups cups ns ns' x y HadC HadC HadC H1)
      as H2.
    exact (view_container_to_group p D u0 u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI qc D' cups cups nrC arC drC HassQ
             CnP CnI CaP CaI CdP CdI vm Hvc i' Mi' v Mv ns ns' x y HM Hvm H2).
  Qed.

  (** [ElimView.CrossElim]'s [Hcmot_x]: the container's motive's variables
      at a neutral read back at the types its stuck eliminator stores them
      at, the container's non-uniform parameters' types at [ub] and its
      member's type there ([elim_ups_ok] at [ub]). *)
  Lemma container_motive_entries_readable : forall i' Mi' v Mv hd k as1 as2 e e' u u' ns ns',
      ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      G v u u' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
      exists cups, ⟦mref i' of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, cups) /\
        List.Forall2 (fun v t => entry_readable (de_term v t))
          (List.skipn (im_unu D Mv) as1 ++ ⇑ (d_ind hd k as1) e :: nil)
          (List.map snd (motive_entries D' Mi' ub (List.skipn (im_unu D Mv) as1)
                           (d_ind hd k (cups ++ List.skipn (im_unu D Mv) as1)) (⇑ (d_ind hd k as1) e))).
  Proof.
    intros * HMi' Hrv' Hv HMv Hcur.
    destruct (container_view_member i' v Hv) as (Mi0 & Mv0 & HMi0 & Hvm).
    rewrite HMi' in HMi0; injection HMi0 as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv0; rewrite HMv in HMv0; injection HMv0 as <-.
    pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvm) as Erv.
    assert (Hrv : im_is_rview Mv = false) by congruence.
    inversion Hcur as [| v0 Mv0 hd0 k0 ns0 ns0' as1' as2' e0 e0' w0 w0' HM0 Hrv0 Href Hn L1 L2 Hs1 Hs2 He |]; subst;
      [| rewrite HMv in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end;
         exfalso; eapply not_rview_record; eassumption ].
    rewrite HMv in HM0; injection HM0 as <-.
    set (X := List.skipn (im_unu D Mv) as1) in *.
    pose proof (nparams_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HMv _ _ Hs1) as HXX.
    (** The neutral at the group at its own indices, then at the
        container's at [ub]. *)
    assert (Hee : Dom e ≈ e ∈ per_bot) by (etransitivity; [ exact He | symmetry; exact He ]).
    assert (HG : G v u u' X X (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as1) e))
      by (eapply ind_rel_neut; [ exact HMv | exact Hrv | exact Href | exact HXX | exact L1 | exact L1 | exact HXX | exact HXX
                               | exact Hee ]).
    pose proof (group_to_container_rel i' Mi' v Mv u u' X X _ _ HMi' Hrv' Hvm HG) as HQ.
    pose proof (group_nparams_to_container i' Mi' v Mv X X HMi' Hvm HXX) as HXQ.
    (** The container's member's type at [ub]. *)
    pose proof Hcups_x as [_ _ Aa _ Ma _ _ Ra _ _ _ _].
    destruct (proj1 (Ma i' Mi' HMi') Hrv') as [r Hr'].
    pose proof (view_member_ref _ _ _ _ _ _ _ _ _ Hvm Hrv') as Er; rewrite Href in Er.
    assert (Hcm : exists cups0, ⟦mref i' of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, cups0)).
    { unfold im_ref in Er; destruct (im_head Mi') as [pm | qv kv Iv vmv | qr Ir fl] eqn:Hhj; injection Er as -> ->.
      - rewrite (mref_decl_inv _ _ _ _ _ _ _ Hq HMi' Hhj Hr') in Hr'; eexists; exact Hr'.
      - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hq HMi' Hhj Hr') as (py & -> & _); eexists; exact Hr'.
      - unfold im_is_rview in Hrv'; rewrite Hhj in Hrv'; discriminate. }
    destruct Hcm as [cupsm Hcm].
    exists cupsm; split; [ exact Hcm |].
    unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
      [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ HassQ Aa HMi' HXQ) | constructor; [| constructor ] ].
    exact (Ra _ _ _ _ _ _ _ _ _ _ _ _ HMi' Hrv' Aa Aa Hcm HQ HXQ).
  Qed.

  (** The container's canonical relations at [ub] and at [cups] agree. *)
  #[local] Abbreviation FA := (valid_group_fam_agree qc D' HgQ ub cups Hub Lub).
  #[local] Abbreviation FC f := (f qc D' ub nrQ nrC arQ arC drQ drC (ind_fam_agree_np _ _ _ _ _ _ _ FA)
                                   (ind_fam_agree_arg _ _ _ _ _ _ _ FA) (ind_fam_agree_dom _ _ _ _ _ _ _ FA)).

  (** The domains of a recursive argument's shape at the container's
      constructor, against the group's at the view, after [d] of them on
      the diagonal of the container's relation at [ub]: linked
      ([container_doms_link]), by the container's relation at [cups]
      ([ind_fam_agree]) and the view's agreement there
      ([agree_shape_doms_rel]). *)
  Lemma container_doms_link_at : forall i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms vp,
      ind_member D' i' = Some Mi' -> view_member p D qc D' vm i' Mi' v Mv ->
      ind_con Mi' c = Some (gs1' ++ ca_rec t' :: gs2') -> ind_con Mv c = Some (gs1 ++ ca_rec t :: gs2) ->
      cargs_correspond vm gs1' gs1 -> ptyp_depth t' = ptyp_depth t -> List.length vp = List.length gs1 ->
      tele_rel (nrQ i') (List.rev (im_nparams Mi')) ms ms ->
      tele_prefix_rel (arQ i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
      forall n d ys, d + n = ptyp_depth t' -> List.length ys = d ->
        tele_prefix_rel (shape_doms_rel (drQ i') (List.rev (im_nparams Mi')) (cargs_nonrec_tele gs1') ms (nonrec_arg_vals gs1' vp) t')
          d ys ys ->
        container_doms_link dr v drQ i' (ms ++ nonrec_arg_vals gs1 vp ++ ys)
          (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t))
          (ms ++ nonrec_arg_vals gs1' vp ++ ys)
          (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1' ++ List.firstn d (shape_doms_tele t'))
          (ptyp_skip d t') (ptyp_skip d t).
  Proof.
    intros * HM Hvm Hc' Hcm Hcorr Hdp Lvp Hms Hpw.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv.
    destruct HcpQ as [QnP QnI QaP QaI QdP QdI].
    pose proof (canon_nparams_base qc D' HgQ ub cups Hubub Lub Hub i' Mi' HM _ _ Hms) as HmsC.
    assert (HK : List.length (cargs_nonrec gs1') <= List.length (cargs_nonrec (gs1' ++ ca_rec t' :: gs2')))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (FC tele_prefix_rel_ar_change i' Mi' HM ms ms ms c _ _ _ _ Hms HmsC Hc' HK Hpw) as HpwC.
    induction n as [| n IH]; intros d ys Hdn Lys Hys.
    - rewrite Nat.add_0_r in Hdn; subst d.
      unfold ptyp_depth in *.
      replace (ptyp_skip (List.length (ptyp_doms t')) t) with (ptyp_skip (List.length (ptyp_doms t)) t) by (rewrite Hdp; reflexivity).
      rewrite !ptyp_skip_end; constructor.
    - unfold ptyp_depth in Hdn, Hdp.
      destruct (ptyp_skip_lt d t' ltac:(lia)) as (B' & HB' & Hs'); destruct (ptyp_skip_lt d t ltac:(lia)) as (B & HB & Hs).
      rewrite Hs', Hs; apply container_doms_link_pi; intros c0 c0' Hc0.
      (** The element on the container's diagonal, then at [cups], then
          the group's. *)
      assert (HkB : d < List.length (ptyp_doms t')) by lia.
      assert (Hc0Q : shape_doms_rel (drQ i') (List.rev (im_nparams Mi')) (cargs_nonrec_tele gs1') ms (nonrec_arg_vals gs1' vp) t'
                       d ys c0 c0') by (unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB'); exact Hc0).
      pose proof (QdP i' Mi' ms ms c _ gs1' t' gs2' _ _ d B' ys ys HM Hms Hc' eq_refl Hpw HB' Hys) as HPQ.
      assert (Hc00 : drQ i' (ms ++ nonrec_arg_vals gs1' vp ++ ys)
                       (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1' ++ List.firstn d (shape_doms_tele t')) B' c0 c0)
        by (etransitivity; [ exact Hc0 | symmetry; exact Hc0 ]).
      assert (Hc00Q : shape_doms_rel (drQ i') (List.rev (im_nparams Mi')) (cargs_nonrec_tele gs1') ms (nonrec_arg_vals gs1' vp) t'
                        d ys c0 c0) by (unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB'); exact Hc00).
      pose proof (FC tele_prefix_rel_sh_change i' Mi' HM ms ms ms c _ gs1' t' gs2' _ _ _ d ys ys Hms HmsC Hc' eq_refl Hpw HpwC
                    ltac:(lia) Hys) as HysC.
      pose proof (proj1 (ind_fam_agree_dom _ _ _ _ _ _ _ FA i' Mi' ms ms ms c _ gs1' t' gs2' _ _ _ d ys ys ys HM Hms HmsC Hc' eq_refl
                           Hpw HpwC HkB Hys HysC _ _) Hc00Q) as Hc0C.
      pose proof (agree_shape_doms_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc i' Mi' v Mv c gs1' t' gs2' gs1 t gs2 ms ms vp vp d B' B ys ys
                    HM Hvm Hc' Hcm Hcorr Lvp Lvp HB' HB HmsC HpwC HysC) as EG.
      unfold shape_doms_rel in Hc0C; rewrite (List.nth_error_nth _ _ _ HB') in Hc0C.
      split; [ exact (proj1 (EG _ _) Hc0C) |].
      (** The rests, one domain more. *)
      rewrite (prefix_tele_snoc_dom _ _ _ _ _ HB), (prefix_tele_snoc_dom _ _ _ _ _ HB').
      rewrite <- !List.app_assoc.
      apply (IH (S d) (ys ++ c0 :: nil) ltac:(unfold ptyp_depth; lia) ltac:(rewrite List.length_app; cbn; lia)).
      apply tele_prefix_rel_snoc; [ exact Hys | exact Hc00Q ].
  Qed.

  (** The container's motive's entries at the end of a container's shape,
      as [eval_ihty_self] types them at [ub]: the shape's parameters and an
      element of the member there ([ViewReadback]'s
      [container_self_entries_readable]). *)
  Lemma container_end_entries_readable : forall ρ j Mj Ps bs base hd k v u u' bs' v',
      ind_member D' j = Some Mj -> im_is_rview Mj = false -> im_ref qc j Mj = (hd, k) ->
      ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs -> tele_rel (nrQ j) (List.rev (im_nparams Mj)) base bs ->
      adm_uparams D' ub nrQ arQ drQ u -> adm_uparams D' ub nrQ arQ drQ u' ->
      grp_rel qc D' ub nrQ arQ drQ j u u' base bs' v v' ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (bs ++ v :: nil)
        (List.map snd (tele_entries (decl_env D' ub) (List.rev (im_nparams Mj)) bs
                         ++ (v, entry_type_shape qc ub ρ (pt_self j Ps)) :: nil)).
  Proof.
    intros * HM Hrv Hr Eb Hn Hau Hau' Hi.
    pose proof Hcups_x as [_ _ Aa _ Ma _ _ Ra _ _ _ _].
    destruct (proj1 (Ma j Mj HM) Hrv) as [r Hr'].
    assert (Hcm : exists cups0, ⟦mref j of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, cups0)).
    { unfold im_ref in Hr; destruct (im_head Mj) as [pm | qv kv Iv vmv | qr Ir fl] eqn:Hhj; injection Hr as <- <-.
      - rewrite (mref_decl_inv _ _ _ _ _ _ _ Hq HM Hhj Hr') in Hr'; eexists; exact Hr'.
      - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hq HM Hhj Hr') as (py & -> & _); eexists; exact Hr'.
      - unfold im_is_rview in Hrv; rewrite Hhj in Hrv; discriminate. }
    destruct Hcm as [cups0 Hcm].
    destruct HcpQ as [CnP CnI CaP CaI CdP CdI].
    pose proof (nparams_rel_refl_r qc D' ub nrQ arQ drQ HassQ CnP CnI CaP CaI CdP CdI j Mj HM _ _ Hn) as Hbb.
    rewrite List.map_app; apply List.Forall2_app;
      [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ HassQ Aa HM Hbb) | constructor; [| constructor ] ].
    eapply entry_readable_at_evaluated; [ apply eval_entry_type_shape; econstructor; [ exact Eb | exact Hcm ] |].
    exact (Ra _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hau Hau' Hcm Hi Hn).
  Qed.

  (** The group's eliminator against itself at [C1] ([ElimView.SelfElim]). *)
  #[local] Abbreviation SE f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs HUss C1 u0 HC11 HUC Bks iA HBk HBss).
  #[local] Abbreviation itrans := (proj1 (ind_rel_trans_all p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI (admissible_index_at D u0 nr))).

  (** *** The Container's Recursive Results

      Related recursive results of the container's eliminator against the
      group's ([cross_result_rel]), at arguments related at the group's
      relation and the container's own at [ub], the domains of their
      shapes linked ([container_doms_link]): the container's read back at
      the types its eliminator stores them at ([eval_ihty]).  At the end
      of a shape, the container's motive's instance, whose relation with
      the group's ([Hmot_x], at the container's indices, related to the
      group's ones by the argument's own) the result is an element of; at
      a domain, a [Π] over it, whose fresh variables are the group's
      domain's elements. *)
  Lemma container_results_readable_all : forall k u u',
    (forall pre pre' Ts t' t v v' rs rs', cross_result_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' Ts t' t v v' rs rs' ->
       forall kQ preQ TsQ, List.length preQ = List.length TsQ -> shape_correspond vm t' t ->
       rec_arg_rel p D (admissible_index_at D u0 nr) nr ar dr k u u' pre pre' Ts t v v' ->
       rec_arg_rel qc D' (admissible_index_at D' ub nrQ) nrQ arQ drQ kQ ub ub preQ preQ TsQ t' v v ->
       shape_doms_ok D' ub nrQ drQ ub ub kQ preQ preQ TsQ t' ->
       container_doms_link dr k drQ kQ pre Ts preQ TsQ t' t ->
       exists as1, ⟦ihty v of t' at qc ub under ρb (blocks_motives VBb) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D' ub TsQ preQ ↘ as1 /\
         List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rs as1) /\
    (forall pre pre' Ts t' t v c v' c' rs rs', cross_result_app_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' Ts t' t v c v' c' rs rs' ->
       forall kQ preQ TsQ, List.length preQ = List.length TsQ -> shape_correspond vm t' t ->
       rec_arg_app_rel p D (admissible_index_at D u0 nr) nr ar dr k u u' pre pre' Ts t v c v' c' ->
       rec_arg_app_rel qc D' (admissible_index_at D' ub nrQ) nrQ arQ drQ kQ ub ub preQ preQ TsQ t' v c v c ->
       shape_doms_ok D' ub nrQ drQ ub ub kQ preQ preQ TsQ t' ->
       container_doms_link dr k drQ kQ pre Ts preQ TsQ t' t ->
       exists fc rcs as1, $| v & c | gc_deps ⍮ gc_stack ↘ fc /\
         List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs /\
         ⟦ihty fc of t' at qc ub under ρb (blocks_motives VBb) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D' ub TsQ preQ ↘ as1 /\
         List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs as1) /\
    (forall pre pre' Ts gs' gs vs vs' w ihs, cross_fields_rel D D' dr Rel C1 p u0 Bks k u u' pre pre' Ts gs' gs vs vs' w ihs ->
       forall i' Mi' Mk c gs1' gs1 ms vp,
         ind_member D' i' = Some Mi' -> view_member p D qc D' vm i' Mi' k Mk ->
         ind_con Mi' c = Some (gs1' ++ gs') -> ind_con Mk c = Some (gs1 ++ gs) ->
         cargs_correspond vm gs1' gs1 -> cargs_correspond vm gs' gs -> List.length vp = List.length gs1 ->
         pre = ms ++ nonrec_arg_vals gs1 vp -> Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ->
         List.length ms = im_nn Mi' ->
         tele_rel (nrQ i') (List.rev (im_nparams Mi')) ms ms ->
         tele_prefix_rel (arQ i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp) (nonrec_arg_vals gs1' vp) ->
         tele_rel_from (arQ i' ms c) (List.length (cargs_nonrec gs1')) (nonrec_arg_vals gs1' vp)
           (nonrec_arg_vals gs' vs) (nonrec_arg_vals gs' vs) ->
         con_args_rel p D (admissible_index_at D u0 nr) nr ar dr k u u' pre pre' Ts gs vs vs' ->
         con_args_rel qc D' (admissible_index_at D' ub nrQ) nrQ arQ drQ i' ub ub (ms ++ nonrec_arg_vals gs1' vp)
           (ms ++ nonrec_arg_vals gs1' vp) (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1') gs' vs vs ->
         cargs_doms_ok D' ub nrQ drQ ub ub i' (ms ++ nonrec_arg_vals gs1' vp) (ms ++ nonrec_arg_vals gs1' vp)
           (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1') gs' vs vs ->
         exists as1, ⟦ihtys vs of gs' at qc ub under ρb (blocks_motives VBb) ⟧ gc_deps ⍮ gc_stack ⍮
             components_env D' ub (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1') (ms ++ nonrec_arg_vals gs1' vp) ↘ as1 /\
           List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) w as1).
  Proof.
    pose proof Hcups_x as [_ _ AaQ _ _ _ _ _ _ _ _ _].
    pose proof HcpQ as [QnP QnI QaP QaI QdP QdI].
    pose proof (valid_group_adm qc D' HgQ ub ub Hubub Lub Hubub) as HadQ.
    match goal with
    | |- forall k u u',
         (forall p1 p1' T1 s1' s1 x1 x1' r1 r1', cross_result_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
            @?Q k u u' p1 p1' T1 s1' s1 x1 x1' r1 r1') /\
         (forall p2 p2' T2 s2' s2 x2 c2 x2' c2' r2 r2', cross_result_app_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
            @?Q0 k u u' p2 p2' T2 s2' s2 x2 c2 x2' c2' r2 r2') /\
         (forall p3 p3' T3 g3' g3 x3 x3' i3 i3', cross_fields_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
            @?Q1 k u u' p3 p3' T3 g3' g3 x3 x3' i3 i3') =>
        apply (cross_result_rel_min_ind_all _ D D' dr Rel C1 p u0 Bks Q Q0 Q1)
    end.
    - (** At the end, at members with a block: the container's motive's
          instance, at the container's indices. *)
      intros k u u' pre pre' Ts j' Mj' Ps' j Mj Ps bs bs' v v' ih ih' HMj' Hrv' HMj Hrv Eb Eb' HR kQ preQ TsQ LQ Hsc Hrg HrQ HdQ _.
      cbn [shape_correspond] in Hsc.
      destruct (container_view_member j' j Hsc) as (Mj0' & Mj0 & HMj0' & Hvm).
      rewrite HMj' in HMj0'; injection HMj0' as <-.
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMj0; rewrite HMj in HMj0; injection HMj0 as <-.
      pose proof Hrg as Hrg0; apply rec_arg_self_inv in Hrg0 as (bs0 & bs0' & Eb0 & Eb0' & _ & _ & Hi).
      pose proof (functional_eval_exps' _ _ _ _ Eb Eb0) as <-; pose proof (functional_eval_exps' _ _ _ _ Eb' Eb0') as <-.
      pose proof HrQ as HrQ0; apply rec_arg_self_inv in HrQ0 as (bsQ & bsQ' & EbQ & EbQ' & _ & _ & HiQ).
      pose proof (functional_eval_exps' _ _ _ _ EbQ EbQ') as <-.
      (** The container's element at the group, at [u0], against the
          group's own. *)
      pose proof (container_to_group_rel j' Mj' j Mj bsQ bsQ v v HMj' Hrv' Hvm HiQ) as HG1.
      pose proof (ind_rel_rebase p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI j u u' u0 u0 bs bs' v v' Had Had Had Hi) as Hi0.
      pose proof (itrans _ _ _ _ _ _ _ HG1 _ _ _ _ Hi0) as HG.
      pose proof (ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ HMj HG) as HnG.
      pose proof (ind_rel_ns p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ j Mj _ _ _ _ _ _ HMj Hi) as Hni.
      pose proof (nparams_rel_trans p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HMj _ _ _ Hni
                    (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HMj _ _ HnG)) as Hbq.
      pose proof (nparams_rel_refl_r p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HMj _ _ Hni) as Hbb'.
      (** The entries of the two motives read back. *)
      pose proof (ind_rel_ns qc D' ub nrQ arQ drQ HassQ QnP QnI QaP QaI QdP QdI _ j' Mj' _ _ _ _ _ _ HMj' HiQ) as HnQ.
      destruct (im_ref qc j' Mj') as [hd k1] eqn:Href.
      pose proof (container_end_entries_readable _ _ _ _ _ _ _ _ _ _ _ _ _ HMj' Hrv' Href EbQ HnQ AaQ AaQ HiQ) as Hra.
      destruct (SE self_index_readable j Mj u0 u0 bsQ bs' v v' HMj Hrv HG) as [_ [ts' Hrb]].
      destruct (HbB _ _ HMj' Hrv') as [bb Hbb]; destruct (HBks _ _ HMj Hrv) as [ba Hba].
      destruct (Hmot_x j' Mj' j bb ba u0 u0 bsQ bs' v v' _ _ HMj' Hrv' Hsc Hbb Hba HG Hra Hrb) as (a1 & a2 & Ea1 & Ea2 & HRa).
      rewrite combine_tele_entries_snoc in Ea1.
      pose proof (proj1 (SE self_motive_move j Mj u u' bs bs' v v' bsQ bs' HMj Hrv Hi Hbq Hbb' _ _) HR) as HRQ.
      exists (a1 :: nil); split.
      + eapply eval_ihty_self; [ exact Hq | exact HMj' | exact Hrv' | exact EbQ | rewrite (nth_blocks_motives _ _ _ Hbb); exact Ea1 ].
      + constructor; [ exact (proj1 (entry_readable_of_elem HRa HRQ)) | constructor ].
    - (** At the end, at record views: their fields', at the projections. *)
      intros k u u' pre pre' Ts j' Mj' qr Is' fl c' gs' Ps' j Mj Is0 c gs Ps v v' ws ws' rs rs' HMj' Hh' Hcs' HMj Hhj Hcs Ew Ew' _ IH
        kQ preQ TsQ LQ Hsc Hrg HrQ HdQ _.
      cbn [shape_correspond] in Hsc.
      destruct (container_view_member j' j Hsc) as (Mj0' & Mj0 & HMj0' & Hvm).
      rewrite HMj' in HMj0'; injection HMj0' as <-.
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMj0; rewrite HMj in HMj0; injection HMj0 as <-.
      (** The two constructors are the same. *)
      assert (Ec : c' = c).
      { pose proof (view_member_names _ _ _ _ _ _ _ _ _ Hvm) as En; rewrite Hcs, Hcs' in En; injection En as ->; reflexivity. }
      subst c'.
      (** The group's fields. *)
      pose proof Hrg as Hrg0; apply rec_arg_self_inv in Hrg0 as (bs & bs' & _ & _ & _ & _ & Hi).
      inversion Hi as [| | ? Mx qrx Isx flx cx gsx ? wsx ? wsx' ? ? HMx Hhx Hnpx Hcsx Ewx Ewx' Hnrx Hcax]; subst;
        [ rewrite HMj in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end; exfalso; eapply not_rview_record; eassumption
        | rewrite HMj in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end; exfalso; eapply not_rview_record; eassumption
        |].
      rewrite HMj in HMx; injection HMx as <-.
      rewrite Hhj in Hhx; injection Hhx as <- <- <-; rewrite Hcs in Hcsx; injection Hcsx as <- <-.
      pose proof (functional_eval_projs _ _ _ _ Ewx Ew) as ->; pose proof (functional_eval_projs _ _ _ _ Ewx' Ew') as ->.
      (** The container's fields. *)
      pose proof HrQ as HrQ0; apply rec_arg_self_inv in HrQ0 as (bsQ & bsQ' & _ & _ & _ & _ & HiQ).
      inversion HiQ as [| | ? My qry Isy fly cy gsy ? wsQ ? wsQ' ? ? HMy Hhy Hnpy Hcsy EwQ EwQ' HnrQ HcaQ]; subst;
        [ rewrite HMj' in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end; exfalso; eapply not_rview_record; eassumption
        | rewrite HMj' in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end; exfalso; eapply not_rview_record; eassumption
        |].
      rewrite HMj' in HMy; injection HMy as <-.
      rewrite Hh' in Hhy; injection Hhy as <- <- <-; rewrite Hcs' in Hcsy; injection Hcsy as <- <-.
      pose proof (functional_eval_projs _ _ _ _ EwQ Ew) as ->; pose proof (functional_eval_projs _ _ _ _ EwQ' Ew) as ->.
      assert (HcA : ind_con Mj' c = Some gs') by (unfold ind_con; rewrite Hcs'; cbn; rewrite ?String.eqb_refl; reflexivity).
      assert (HcB : ind_con Mj c = Some gs) by (unfold ind_con; rewrite Hcs; cbn; rewrite ?String.eqb_refl; reflexivity).
      destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm c gs' HcA) as (g0 & Hc0 & Hcorr).
      rewrite HcB in Hc0; injection Hc0 as <-.
      pose proof HcaQ as LwQ; apply con_args_rel_len in LwQ as [LwQ _].
      pose proof (rview_fields_doms qc D' ub nrQ arQ drQ Hq HassQ QnP QnI QaP QaI QdP QdI HadQ ub ub AaQ AaQ j' Mj' qr Is' fl c gs'
                    ws ws HMj' Hh' Hcs' LwQ LwQ HnrQ) as HdsQ.
      destruct HnrQ as [_ HnrQ].
      assert (Hnn : im_nn Mj' = 0) by (unfold im_nn; rewrite Hnpy; reflexivity).
      destruct (IH j' Mj' Mj c nil nil nil nil HMj' Hvm HcA HcB I Hcorr eq_refl eq_refl ltac:(rewrite Hnpx; reflexivity)
                  ltac:(rewrite Hnn; reflexivity) ltac:(rewrite Hnpy; split; [ reflexivity | exact I ]) (tele_prefix_rel_nil _)
                  HnrQ Hcax ltac:(rewrite Hnpy; exact HcaQ) ltac:(rewrite Hnpy; exact HdsQ))
        as (as1 & T1 & R1).
      rewrite Hnpy in T1; cbn [List.rev List.app cargs_nonrec_tele cargs_nonrec List.map nonrec_arg_vals components_env env_tele] in T1.
      exists as1; split; [ eapply eval_ihty_rview; [ exact Hq | exact HMj' | exact Hh' | exact Hcs' | exact Ew | exact T1 ] | exact R1 ].
    - (** At a domain: a [Π] over the container's, its fresh variables the
          group's domain's elements. *)
      intros k u u' pre pre' Ts B' t' B t v v' rs rs' Happ IH _ _ kQ preQ TsQ LQ Hsc Hrg HrQ HdQ Hlk.
      cbn [shape_correspond] in Hsc.
      destruct (shape_doms_ok_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ HdQ) as (b & b0 & Eb & Eb0 & Hrest & Hty & Hvar).
      pose proof (functional_eval_exp _ _ _ _ Eb0 Eb) as ->.
      inversion Hlk as [| ? ? ? ? ? ? ? ? Hlk']; subst.
      assert (Hext : forall s, exists fc rcs as1, $| v & ⇑! b s | gc_deps ⍮ gc_stack ↘ fc /\
                 List.Forall2 (fun f r => $| f & ⇑! b s | gc_deps ⍮ gc_stack ↘ r) rs rcs /\
                 ⟦ihty fc of t' at qc ub under ρb (blocks_motives VBb) ⟧ gc_deps ⍮ gc_stack ⍮
                   components_env D' ub TsQ preQ ↦ ⇑! b s ⦂ entry_type_closure B' (components_env D' ub TsQ preQ) ↘ as1 /\
                 List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs as1).
      { intros s.
        destruct (Hlk' _ _ (Hvar s)) as [Hdr Hlk1].
        destruct (rec_arg_rel_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrg _ _ Hdr) as (r & r' & Er & Er' & Hr').
        assert (HvQ : drQ kQ preQ TsQ B' (⇑! b s) (⇑! b s)) by exact (Hvar s).
        destruct (rec_arg_rel_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HrQ _ _ HvQ) as (fq & fq' & Eq1 & Eq1' & HrQ').
        pose proof (functional_eval_app _ _ _ _ Eq1 Eq1') as <-.
        assert (LQ1 : List.length (preQ ++ ⇑! b s :: nil) = List.length (TsQ ++ ce_ass B' :: nil))
          by (rewrite !List.length_app, LQ; reflexivity).
        destruct (IH _ _ Hdr _ _ _ LQ1 Hsc ltac:(econstructor; [ exact Er | exact Er' | exact Hr' ])
                    ltac:(econstructor; [ exact Eq1 | exact Eq1 | exact HrQ' ]) (Hrest _ _ HvQ) Hlk1)
          as (fc & rcs & as1 & Ef & F1 & T1 & R1).
        rewrite (components_env_snoc _ _ _ _ _ _ LQ) in T1.
        exists fc, rcs, as1; repeat split; assumption. }
      set (N := List.length (shape_leaves (rview_leaves D') 0 t')).
      assert (LN : List.length rs = N).
      { destruct (Hext 0) as (fc & rcs & as1 & _ & F1 & T1 & R1).
        pose proof (proj1 eval_ihty_length_all _ _ _ _ _ _ _ _ T1 D' Hq HlcQ).
        pose proof (List.Forall2_length F1); pose proof (List.Forall2_length R1).
        unfold N; congruence. }
      exists (List.map (fun i => Πᵈ b (nil ↦ d_ihfam ρb (blocks_motives VBb) qc ub (components_env D' ub TsQ preQ) B' t' i v
                                         ⦂ entry_type_none) fam_cod) (List.seq 0 N)).
      split; [ eapply eval_ihty_pi; [ exact Hq | exact Eb ] |].
      rewrite <- LN; apply forall2_map_seq; intros n r Hri s; cbn [Nat.add].
      destruct (Hext s) as (fc & rcs & as1 & Ef & F1 & T1 & R1).
      destruct (forall2_nth_left _ _ _ _ _ F1 Hri) as (rc & Hrc & Erc).
      destruct (forall2_nth_left _ _ _ _ _ R1 Hrc) as (ai & Hai & Rai).
      destruct (entry_readable_term_at _ _ (S s) Rai) as (a0 & C & W & Ev & RC & RW); inversion Ev; subst.
      destruct (Hty s) as [A A' RA RA' _].
      eexists; eapply read_entry_term;
        [ apply eval_entry_type_value
        | eapply read_typ_pi; [ exact RA | eapply eval_fam_cod_ihfam; [ exact Ef | exact T1 | exact Hai ] | exact RC ]
        | eapply read_nf_fn; [ exact RA | exact Erc | eapply eval_fam_cod_ihfam; [ exact Ef | exact T1 | exact Hai ] | exact RW ] ].
    - (** An application: the rest at the function's values. *)
      intros k u u' pre pre' Ts t' t v c v' c' rs rs' fc fc' rcs rcs' Ev Ev' F1 F2 _ IH kQ preQ TsQ LQ Hsc Hrg HrQ HdQ Hlk.
      destruct (rec_arg_app_rel_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrg) as (r & r' & Er & Er' & Hr).
      pose proof (functional_eval_app _ _ _ _ Ev Er) as <-; pose proof (functional_eval_app _ _ _ _ Ev' Er') as <-.
      destruct (rec_arg_app_rel_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HrQ) as (fq & fq' & Eq1 & Eq1' & HrQ').
      pose proof (functional_eval_app _ _ _ _ Ev Eq1) as <-; pose proof (functional_eval_app _ _ _ _ Ev Eq1') as <-.
      destruct (IH kQ preQ TsQ LQ Hsc Hr HrQ' HdQ Hlk) as (as1 & T1 & R1).
      exists fc, rcs, as1; repeat split; assumption.
    - (** No argument. *)
      intros k u u' pre pre' Ts * _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
      exists nil; split; [ constructor | constructor ].
    - (** Non-recursive in both: the argument joins the prefixes. *)
      intros k u u' pre pre' Ts rA' A' rA A gs' gs v v' vs vs' w ihs _ IH i' Mi' Mk c gs1' gs1 ms vp HMi' Hvm Hc' HcB Hcorr1 Hcorr Lvp
        Hpre HTs Lms Hms Hpw Hfr Hcg HcaQ HdQ.
      cbn [cargs_correspond] in Hcorr; destruct Hcorr as [Err Hcorr].
      assert (Lvc : List.length vp = List.length gs1') by (rewrite Lvp; symmetry; exact (cargs_correspond_len _ _ _ Hcorr1)).
      cbn [nonrec_arg_vals tele_rel_from] in Hfr; destruct Hfr as [Hx Hfr].
      pose proof Hcg as Hcg1; apply con_args_rel_arg_inv in Hcg1.
      pose proof HcaQ as HcQ1; apply con_args_rel_arg_inv in HcQ1.
      pose proof HdQ as HdQ1; apply cargs_doms_ok_arg_inv in HdQ1.
      assert (LTQ : List.length (ms ++ nonrec_arg_vals gs1' vp) = List.length (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1'))
        by (unfold cargs_nonrec_tele; rewrite !List.length_app, List.length_rev, length_im_nparams, List.length_map,
              length_nonrec_arg_vals by exact Lvc; lia).
      (** The prefixes one argument more, on each side. *)
      assert (EnQ : nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1' vp ++ v :: nil)
        by (rewrite nonrec_arg_vals_app by exact Lvc; reflexivity).
      assert (EnG : nonrec_arg_vals (gs1 ++ ca_arg rA A :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1 vp ++ v :: nil)
        by (rewrite nonrec_arg_vals_app by exact Lvp; reflexivity).
      pose proof (eq_sym (prefix_tele_snoc_arg (List.rev (im_nparams Mi')) gs1' rA' A')) as ETQ.
      assert (ELQ : List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)) = S (List.length (cargs_nonrec gs1')))
        by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
      rewrite <- ETQ in HcQ1, HdQ1.
      rewrite <- List.app_assoc, <- EnQ in HcQ1; rewrite <- List.app_assoc, <- EnQ in HdQ1.
      assert (Hpw1 : tele_prefix_rel (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil)))
        by (rewrite ELQ, EnQ; apply tele_prefix_rel_snoc; [ exact Hpw | exact Hx ]).
      assert (Hfr1 : tele_rel_from (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil)) (nonrec_arg_vals gs' vs)
                       (nonrec_arg_vals gs' vs))
        by (rewrite ELQ, EnQ; exact Hfr).
      destruct (IH i' Mi' Mk c (gs1' ++ ca_arg rA' A' :: nil) (gs1 ++ ca_arg rA A :: nil) ms (vp ++ v :: nil) HMi' Hvm
                  ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact HcB)
                  (cargs_correspond_app _ _ _ (ca_arg rA' A' :: nil) (ca_arg rA A :: nil) Hcorr1 ltac:(cbn; split; [ exact Err | exact I ])) Hcorr
                  ltac:(rewrite ?List.length_app; cbn; lia)
                  ltac:(rewrite EnG, Hpre, <- List.app_assoc; reflexivity)
                  ltac:(rewrite HTs; exact (prefix_tele_snoc_arg _ gs1 rA A)) Lms Hms Hpw1 Hfr1 Hcg1 HcQ1 HdQ1)
        as (as1 & T1 & R1).
      rewrite ETQ, EnQ, List.app_assoc, (components_env_snoc _ _ _ _ _ _ LTQ) in T1.
      exists as1; split; [ constructor; exact T1 | exact R1 ].
    - (** Nested through by the group: no result of the container's. *)
      intros k u u' pre pre' Ts rA' A' t gs' gs v v' vs vs' w rs' ihs _ _ IH i' Mi' Mk c gs1' gs1 ms vp HMi' Hvm Hc' HcB Hcorr1 Hcorr Lvp
        Hpre HTs Lms Hms Hpw Hfr Hcg HcaQ HdQ.
      cbn [cargs_correspond] in Hcorr; destruct Hcorr as [Err Hcorr].
      assert (Lvc : List.length vp = List.length gs1') by (rewrite Lvp; symmetry; exact (cargs_correspond_len _ _ _ Hcorr1)).
      cbn [nonrec_arg_vals tele_rel_from] in Hfr; destruct Hfr as [Hx Hfr].
      pose proof Hcg as Hcg1; apply con_args_rel_rec_inv in Hcg1 as [_ Hcg1].
      pose proof HcaQ as HcQ1; apply con_args_rel_arg_inv in HcQ1.
      pose proof HdQ as HdQ1; apply cargs_doms_ok_arg_inv in HdQ1.
      assert (LTQ : List.length (ms ++ nonrec_arg_vals gs1' vp) = List.length (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1'))
        by (unfold cargs_nonrec_tele; rewrite !List.length_app, List.length_rev, length_im_nparams, List.length_map,
              length_nonrec_arg_vals by exact Lvc; lia).
      (** The container's prefix one argument more, the group's the same. *)
      assert (EnQ : nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1' vp ++ v :: nil)
        by (rewrite nonrec_arg_vals_app by exact Lvc; reflexivity).
      assert (EnG : nonrec_arg_vals (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1 vp)
        by (rewrite nonrec_arg_vals_app by exact Lvp; cbn [nonrec_arg_vals]; rewrite List.app_nil_r; reflexivity).
      pose proof (eq_sym (prefix_tele_snoc_arg (List.rev (im_nparams Mi')) gs1' rA' A')) as ETQ.
      assert (ELQ : List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)) = S (List.length (cargs_nonrec gs1')))
        by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
      rewrite <- ETQ in HcQ1, HdQ1.
      rewrite <- List.app_assoc, <- EnQ in HcQ1; rewrite <- List.app_assoc, <- EnQ in HdQ1.
      assert (Hpw1 : tele_prefix_rel (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil)))
        by (rewrite ELQ, EnQ; apply tele_prefix_rel_snoc; [ exact Hpw | exact Hx ]).
      assert (Hfr1 : tele_rel_from (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_arg rA' A' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_arg rA' A' :: nil) (vp ++ v :: nil)) (nonrec_arg_vals gs' vs)
                       (nonrec_arg_vals gs' vs))
        by (rewrite ELQ, EnQ; exact Hfr).
      destruct (IH i' Mi' Mk c (gs1' ++ ca_arg rA' A' :: nil) (gs1 ++ ca_rec t :: nil) ms (vp ++ v :: nil) HMi' Hvm
                  ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact HcB)
                  (cargs_correspond_app _ _ _ (ca_arg rA' A' :: nil) (ca_rec t :: nil) Hcorr1 ltac:(cbn; split; [ exact Err | exact I ])) Hcorr
                  ltac:(rewrite ?List.length_app; cbn; lia)
                  ltac:(rewrite EnG; exact Hpre)
                  ltac:(rewrite HTs; exact (prefix_tele_snoc_rec _ gs1 t)) Lms Hms Hpw1 Hfr1 Hcg1 HcQ1 HdQ1)
        as (as1 & T1 & R1).
      rewrite ETQ, EnQ, List.app_assoc, (components_env_snoc _ _ _ _ _ _ LTQ) in T1.
      exists as1; split; [ constructor; exact T1 | exact R1 ].
    - (** Recursive in both: the results of its shape, then the rest's. *)
      intros k u u' pre pre' Ts t' t gs' gs v v' vs vs' rs rs' w ihs _ _ _ IHr _ IHf i' Mi' Mk c gs1' gs1 ms vp HMi' Hvm Hc' HcB Hcorr1 Hcorr
        Lvp Hpre HTs Lms Hms Hpw Hfr Hcg HcaQ HdQ.
      cbn [cargs_correspond] in Hcorr; destruct Hcorr as (Hmt & Hdp & Hcorr).
      assert (Lvc : List.length vp = List.length gs1') by (rewrite Lvp; symmetry; exact (cargs_correspond_len _ _ _ Hcorr1)).
      cbn [nonrec_arg_vals] in Hfr.
      pose proof Hcg as Hcg0; apply con_args_rel_rec_inv in Hcg0 as [Hcg1 Hcg2].
      pose proof HcaQ as HcQ0; apply con_args_rel_rec_inv in HcQ0 as [HcQ1 HcQ2].
      pose proof HdQ as HdQ0; apply cargs_doms_ok_rec_inv in HdQ0 as [HdQ1 HdQ2].
      assert (LTQ : List.length (ms ++ nonrec_arg_vals gs1' vp) = List.length (List.rev (im_nparams Mi') ++ cargs_nonrec_tele gs1'))
        by (unfold cargs_nonrec_tele; rewrite !List.length_app, List.length_rev, length_im_nparams, List.length_map,
              length_nonrec_arg_vals by exact Lvc; lia).
      (** The domains of the shapes, linked. *)
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMk.
      pose proof (container_doms_link_at i' Mi' k Mk c gs1' t' gs' gs1 t gs ms vp HMi' Hvm Hc' HcB Hcorr1 Hdp Lvp Hms Hpw
                    (ptyp_depth t') 0 nil eq_refl eq_refl (tele_prefix_rel_nil _)) as Hlk.
      cbn [List.firstn ptyp_skip] in Hlk; rewrite !List.app_nil_r in Hlk.
      destruct (IHr i' _ _ LTQ (shape_correspond_of _ _ _ Hmt Hdp) Hcg1 HcQ1 HdQ1 ltac:(rewrite Hpre, HTs; exact Hlk))
        as (as1 & T1 & R1).
      (** The prefixes the same on each side, one recursive argument more. *)
      assert (EnQ : nonrec_arg_vals (gs1' ++ ca_rec t' :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1' vp)
        by (rewrite nonrec_arg_vals_app by exact Lvc; cbn [nonrec_arg_vals]; rewrite List.app_nil_r; reflexivity).
      assert (EnG : nonrec_arg_vals (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) = nonrec_arg_vals gs1 vp)
        by (rewrite nonrec_arg_vals_app by exact Lvp; cbn [nonrec_arg_vals]; rewrite List.app_nil_r; reflexivity).
      pose proof (eq_sym (prefix_tele_snoc_rec (List.rev (im_nparams Mi')) gs1' t')) as ETQ.
      assert (ELQ : List.length (cargs_nonrec (gs1' ++ ca_rec t' :: nil)) = List.length (cargs_nonrec gs1'))
        by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
      rewrite <- EnQ, <- ETQ in HcQ2; rewrite <- EnQ, <- ETQ in HdQ2.
      assert (Hpw1 : tele_prefix_rel (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_rec t' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_rec t' :: nil) (vp ++ v :: nil))
                       (nonrec_arg_vals (gs1' ++ ca_rec t' :: nil) (vp ++ v :: nil)))
        by (rewrite ELQ, EnQ; exact Hpw).
      assert (Hfr1 : tele_rel_from (arQ i' ms c) (List.length (cargs_nonrec (gs1' ++ ca_rec t' :: nil)))
                       (nonrec_arg_vals (gs1' ++ ca_rec t' :: nil) (vp ++ v :: nil)) (nonrec_arg_vals gs' vs)
                       (nonrec_arg_vals gs' vs))
        by (rewrite ELQ, EnQ; exact Hfr).
      destruct (IHf i' Mi' Mk c (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil) ms (vp ++ v :: nil) HMi' Hvm
                  ltac:(rewrite <- List.app_assoc; exact Hc') ltac:(rewrite <- List.app_assoc; exact HcB)
                  (cargs_correspond_app _ _ _ (ca_rec t' :: nil) (ca_rec t :: nil) Hcorr1 ltac:(cbn; split; [ exact Hmt | split; [ exact Hdp | exact I ] ])) Hcorr
                  ltac:(rewrite ?List.length_app; cbn; lia)
                  ltac:(rewrite EnG; exact Hpre)
                  ltac:(rewrite HTs; exact (prefix_tele_snoc_rec _ gs1 t)) Lms Hms Hpw1 Hfr1 Hcg2 HcQ2 HdQ2)
        as (bs1 & U1 & Q1).
      rewrite ETQ, EnQ in U1.
      exists (as1 ++ bs1); split; [ eapply eval_ihtys_rec; [ exact T1 | exact U1 ] | apply List.Forall2_app; assumption ].
  Qed.

  #[local] Abbreviation isymQ := (proj1 (ind_rel_sym_all qc D' ub nrQ arQ drQ HassQ
                                           (ind_canon_props_np_per _ _ HcpQ) (ind_canon_props_np_iff _ _ HcpQ)
                                           (ind_canon_props_arg_per _ _ HcpQ) (ind_canon_props_arg_iff _ _ HcpQ)
                                           (ind_canon_props_dom_per _ _ HcpQ) (ind_canon_props_dom_iff _ _ HcpQ)
                                           (admissible_index_at D' ub nrQ))).
  #[local] Abbreviation itransQ := (proj1 (ind_rel_trans_all qc D' ub nrQ arQ drQ HassQ
                                             (ind_canon_props_np_per _ _ HcpQ) (ind_canon_props_np_iff _ _ HcpQ)
                                             (ind_canon_props_arg_per _ _ HcpQ) (ind_canon_props_arg_iff _ _ HcpQ)
                                             (ind_canon_props_dom_per _ _ HcpQ) (ind_canon_props_dom_iff _ _ HcpQ)
                                             (admissible_index_at D' ub nrQ))).

  (** [ElimView.CrossElim]'s [Hcbr_x]: the container's branch's variables
      read back at the types its eliminator stores them at: the
      constructor, the group's at the view, is the container's at [ub]
      ([group_to_container_rel]), whose non-uniform parameters and
      arguments read back at the container's types there ([elim_ups_ok]),
      and the recursive results at the container's motives' instances
      ([container_results_readable_all]). *)
  Lemma container_branch_entries_readable : forall i' Mi' v Mv c gs' gs u u' bs bs' vs vs' w ihs hd k,
      ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs')
        (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
      cross_fields_rel D D' dr Rel C1 p u0 Bks v u u'
        (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') (List.rev (im_nparams Mv)) gs' gs vs vs' w ihs ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mv) bs ++ vs ++ w)
        (List.map snd (branch_entries D' Mi' qc ub (blocks_motives VBb) ρb gs' (List.skipn (im_unu D Mv) bs) vs w)).
  Proof.
    intros * HMi' Hrv' Hv HMv Hc' Hcv0 HG Hcr.
    destruct (container_view_member i' v Hv) as (Mi0 & Mv0 & HMi0 & Hvm).
    rewrite HMi' in HMi0; injection HMi0 as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvm) as HMv0; rewrite HMv in HMv0; injection HMv0 as <-.
    assert (Hrv : im_is_rview Mv = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvm); exact Hrv').
    pose proof (view_member_unu _ _ _ _ _ _ _ _ _ Hvm Hrv') as Hunu.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvm) as Hnn.
    pose proof HcpQ as [QnP QnI QaP QaI QdP QdI].
    pose proof Hcups_x as [_ _ AaQ _ _ _ _ _ _ _ _ _].
    pose proof (valid_group_adm qc D' HgQ ub ub Hubub Lub Hubub) as HadQ.
    pose proof Hcr as Lvs; apply cross_fields_rel_vs_len in Lvs as [Lvs Lvs'].
    (** The constructor's stored parameters, as many as the member's. *)
    assert (Lb : List.length bs = (im_unu D Mv + im_nn Mv)%nat).
    { inversion HG as [k0 Mk0 hd0 k1 ns0 ns0' c0 gs0 bs0 bs0' vs0 vs0' u2 u2' HM0 _ _ _ Hcn Hb _ _ _ _ Hia | | ]; subst.
      - rewrite HMv in HM0; injection HM0 as <-; rewrite Hcv0 in Hcn; injection Hcn as <-.
        pose proof Hia as Lv0; apply con_args_rel_len in Lv0 as [Lv0 _].
        match goal with He : bs0 ++ vs0 = bs ++ vs |- _ =>
          pose proof (f_equal (@List.length domain) He) as Le; rewrite !List.length_app in Le end.
        lia.
      - match goal with HM0 : ind_member D v = Some ?M0, Hh0 : im_head ?M0 = mh_record _ _ _ |- _ =>
          rewrite HMv in HM0; injection HM0 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv Hh0) end. }
    destruct (ind_rel_con_inv p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ _ _ HG HMv Hrv Lb)
      as (gs0 & bs0' & vs0' & Ez & _ & _ & Hcn & Lb' & _ & _ & _ & Hca).
    rewrite Hcv0 in Hcn; injection Hcn as <-.
    injection Ez as Ez.
    pose proof Hca as Lv0; apply con_args_rel_len in Lv0 as [_ Lv0].
    assert (Lbb : List.length bs' = List.length bs0')
      by (pose proof (f_equal (@List.length domain) Ez) as Le; rewrite !List.length_app in Le; lia).
    destruct (app_split_eq _ _ _ _ Ez Lbb) as [<- <-].
    (** The constructor at the container, on its diagonal at [ub]. *)
    pose proof (group_to_container_rel i' Mi' v Mv u u' _ _ _ _ HMi' Hrv' Hvm HG) as HQ0.
    pose proof (itransQ _ _ _ _ _ _ _ HQ0 _ _ _ _ (isymQ _ _ _ _ _ _ _ HQ0)) as HQ.
    assert (LbQ : List.length bs = (im_unu D' Mi' + im_nn Mi')%nat) by (rewrite <- Hunu, <- Hnn; exact Lb).
    destruct (ind_rel_con_inv qc D' ub nrQ arQ drQ HassQ QnP QnI QaP QaI QdP QdI _ _ _ _ _ _ _ _ _ _ _ _ _ HQ HMi' Hrv' LbQ)
      as (gsQ & bsQ & vsQ & EzQ & _ & HnQ & HcnQ & _ & _ & _ & HnrQ & HcaQ).
    rewrite Hc' in HcnQ; injection HcnQ as <-.
    injection EzQ as EzQ.
    pose proof HcaQ as LvQ; apply con_args_rel_len in LvQ as [LvQa LvQ].
    assert (LbbQ : List.length bs = List.length bsQ)
      by (pose proof (f_equal (@List.length domain) EzQ) as Le; rewrite !List.length_app in Le; lia).
    destruct (app_split_eq _ _ _ _ EzQ LbbQ) as [<- <-].
    rewrite <- Hunu in HnrQ, HcaQ.
    set (X := List.skipn (im_unu D Mv) bs) in *.
    destruct HnrQ as [_ HnrQ].
    (** The arguments at the container's types. *)
    pose proof (cargs_doms_adm qc D' ub nrQ arQ drQ Hq HassQ QnP QnI QaP QaI QdP QdI HadQ ub ub AaQ AaQ i' Mi' c gs' X X
                  HMi' Hc' HnQ gs' nil nil nil vs vs eq_refl LvQ LvQ (tele_prefix_rel_nil _) HnrQ) as HdQ.
    cbn [cargs_nonrec_tele cargs_nonrec List.map] in HdQ; rewrite !List.app_nil_r in HdQ.
    destruct (cargs_entries_readable qc D' ub nrQ arQ drQ Hq HassQ QnP QnI QaP QaI QdP QdI ub ub Hcups_x i' Mi' c gs' ub ub X X
                AaQ AaQ HMi' Hc' HnQ gs' nil nil nil vs vs eq_refl (tele_prefix_rel_nil _) HnrQ
                ltac:(rewrite ?List.app_nil_r; cbn [cargs_nonrec_tele List.map]; rewrite ?List.app_nil_r; exact HcaQ)
                ltac:(rewrite ?List.app_nil_r; cbn [cargs_nonrec_tele List.map]; rewrite ?List.app_nil_r; exact HdQ))
      as [Rargs _].
    cbn [cargs_nonrec_tele List.map] in Rargs; rewrite !List.app_nil_r in Rargs.
    (** The recursive results at the container's motives' instances. *)
    destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm c gs' Hc') as (g0 & Hc0 & Hcorr).
    rewrite Hcv0 in Hc0; injection Hc0 as <-.
    pose proof (proj1 (tele_rel_iff _ _ _ _) HnQ) as (LX & _ & _).
    rewrite List.length_rev, length_im_nparams in LX.
    destruct (proj2 (proj2 (container_results_readable_all v u u')) _ _ _ _ _ _ _ _ _ Hcr i' Mi' Mv c nil nil X nil HMi' Hvm
                Hc' Hcv0 I Hcorr eq_refl ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                ltac:(cbn; rewrite List.app_nil_r; reflexivity) LX HnQ (tele_prefix_rel_nil _) HnrQ Hca
                ltac:(cbn [nonrec_arg_vals cargs_nonrec_tele List.map]; rewrite ?List.app_nil_r; exact HcaQ)
                ltac:(cbn [nonrec_arg_vals cargs_nonrec_tele List.map]; rewrite ?List.app_nil_r; exact HdQ))
      as (as1 & T1 & R1).
    cbn [nonrec_arg_vals cargs_nonrec_tele List.map] in T1; rewrite !List.app_nil_r in T1.
    pose proof (ihs_types_eval qc D' Hq HassQ _ _ _ _ _ _ _ T1) as E1.
    assert (Hit : forall ihs0 as0 ts, List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) ihs0 as0 ->
               List.Forall2 (fun t a => eval_entry_type gc_deps gc_stack t a) ts as0 ->
               List.Forall2 (fun v t => entry_readable (de_term v t)) ihs0 ts /\ List.length ihs0 = List.length ts).
    { intros ihs0 as0 ts H1 H2; revert ts H2; induction H1 as [| r a ihs0 as0 Hra H1 IH1]; intros ts H2;
        inversion H2 as [| t a' ts' as0' Ht H2']; subst; [ split; [ constructor | reflexivity ] |].
      destruct (IH1 _ H2') as [F L]; split; [ constructor; [ exact (entry_readable_at_evaluated _ _ _ Ht Hra) | exact F ] | cbn; f_equal; exact L ]. }
    destruct (Hit _ _ _ R1 E1) as [I1 L1].
    assert (L1' : List.length w = List.length (ihs_types D' qc ub ρb (blocks_motives VBb)
                    (env_extend_typed (decl_env D' ub) (tele_entries (decl_env D' ub) (List.rev (im_nparams Mi')) X)) gs' vs))
      by exact L1.
    unfold branch_entries; rewrite !List.map_app, (pair_values_with_types_types _ _ L1').
    apply List.Forall2_app; [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ HassQ AaQ HMi' HnQ) |].
    apply List.Forall2_app; [ exact Rargs | exact I1 ].
  Qed.
End ContainerReadable.

End Fixed_GCtx.
