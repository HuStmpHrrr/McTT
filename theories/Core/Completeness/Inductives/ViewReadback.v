(** * The Stuck Eliminator at a View, Read as the Container's

    A view's stuck eliminator reads back as its container's ([read_ne_elim]
    at [im_sel], E1′).  The container's stuck eliminator at the wrapped
    blocks and the group's at the view's member read back alike: block by
    block over the members of the group read, the blocks they read are
    the group's own by the agreement of the views' maps
    ([view_maps_coherent]), under fresh variables of the container's
    telescopes on one side and of the group's on the other.  Those fresh
    variables are related at the group's relations: a container's type at
    its uniform parameters [ub] is related to the container's at the
    view's instance [cups] at the group's uniform parameters, which is
    related to the group's by the view's equations
    ([ViewEquations.tele_link_types]).  The recursive results at the
    positions a view nests through are the eliminators' at members of
    lower rank. *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim Iota ViewBranch ElimView.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim ReadPairs.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Fresh Variables of a View's Container and of the Group

    The view [m] of the container's member [k'] at the instance [Is], its
    map [vm]; the group's uniform parameters [u0], the instance's value
    [cups] there, and uniform parameters [ub] of the container related to
    [cups].  The container's member [i'] and the group's member [v] the
    view takes it to. *)
Lemma fresh_tele_cons_inv : forall A T ρ s vs, Ftele ce_ass A :: T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦ A ⟧ ρ ↘ a /\ Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** The type of a view [j] of a group at uniform parameters [ups]: the
    container's member's at the view's instance [cups], against it at
    uniform parameters [cs] related to [cups], at non-uniform parameters
    related at the view: related types (the view's relation is the
    container's, [nr_from]).  The premise [Hend] of [shty_link]. *)
Lemma view_end_type : forall VP, valid_groups VP -> forall pq G, VP pq G ->
    forall ups, per_gargs (List.rev (ind_uparams G)) nil nil ups ups -> List.length ups = ind_nu G ->
    forall j Mj qc kc Is vm Dq cups cs bs bs', ind_member G j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups ->
      per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs ->
      ntele_rel G (canon_nparams_rel G ups) j bs bs' ->
      exists (i : uidx) R, DF d_ind qc kc (cups ++ bs) ≈ d_ind qc kc (cs ++ bs') ∈ per_univ_elem i ↘ R.
Proof.
  intros VP HP pq G HPG ups Hgu Hu j Mj qc kc Is vm Dq cups cs bs bs' HMj Hh Hq Ecups Hcs Hbs.
  pose proof (valid_groups_valid VP HP pq G HPG) as Hg.
  pose proof (containers_valid_of_groups VP HP pq G HPG) as Hcv.
  pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
  destruct (dt_view _ _ _ (vgr_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (D2 & Mk' & Hl2 & HMk' & Hkd & HIl & _ & Hvm & _).
  rewrite Hq in Hl2; injection Hl2 as <-.
  assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
  { pose proof (proj2 (dt_order _ _ _ (vgr_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
    unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate ]. }
  destruct Hhd as [pm Hhd].
  destruct (vg_view_args_values pq G Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hcu).
  pose proof (functional_eval_exps' _ _ _ _ E0 Ecups) as ->.
  pose proof (functional_eval_exps' _ _ _ _ E0' Ecups) as ->.
  assert (Hlc : List.length cups = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Ecups); exact HIl).
  pose proof (view_agreement_canonical_all VP pq G HP HPG ups ups Hgu Hu j _ _ _ _ _ _ _ _ HMj Hh Hq Ecups Ecups) as Hvc.
  destruct (agree_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc _ _ HMk') as (v & Mv & Hvmb).
  assert (v = j) as -> by (pose proof (vmb_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mj) as -> by (pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HMj in HMv; congruence).
  unfold ntele_rel in Hbs; rewrite HMj in Hbs.
  pose proof (nr_from pq G ups ups _ _ _ qc Dq cups cups _ _ _ vm Hvc kc Mk' j Mj bs bs' HMk' Hvmb Hbs) as Hbs'.
  destruct (vg_relate qc Dq HgQ kc Mk' pm cups cs bs bs' HMk' Hhd Hcs Hlc Hbs') as [i W].
  exists i; eexists; exact W.
Qed.

Section CrossFresh.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Variables (m : nat) (Mm : imember) (qc : qname) (k' : nat) (Is : list exp) (vm : list nat) (D' : ind_decl).
  Hypotheses (HMm : ind_member D m = Some Mm) (Hh : im_head Mm = mh_view qc k' Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some D').
  Let HVQ := valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq.
  Let HgQ := valid_groups_valid VP HP qc D' HVQ.
  Let HcvQ := containers_valid_of_groups VP HP qc D' HVQ.
  Variables (u0 cups ub : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0) (Hu : List.length u0 = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ cups)
    (Hub : per_gargs (List.rev (ind_uparams D')) nil nil ub cups).
  Let nr := canon_nparams_rel D u0.
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member D' i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).

  (** The fresh non-uniform parameters of the container's member at [ub]
      and of the group's at [u0] are related at the group's relation. *)
  Record cross_params (nsA nsB : list domain) : Prop := mk_cross_params
    { cp_rel : tele_rel (nr v) (List.rev (im_nparams Mv)) nsA nsB
    ; cp_container : per_gargs (List.rev (im_params D' Mi')) nil nil (ub ++ nsA) (cups ++ nsB)
    ; cp_container_right : per_gargs (List.rev (im_params D' Mi')) nil nil (cups ++ nsB) (cups ++ nsB)
    ; cp_group_right : per_gargs (List.rev (im_params D Mv)) nil nil (u0 ++ nsB) (u0 ++ nsB) }.

  Lemma cross_fresh_nparams : forall s nsA nsB,
      Ftele List.rev (im_nparams Mi') in gc_deps ⍮ gc_stack ⍮ env_args nil ub ⍮ s ↘ nsA ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil u0 ⍮ s ↘ nsB ->
      cross_params nsA nsB.
  Proof.
    pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (vgr_valid _ _ Hg) as HD; pose proof (vgr_closed _ _ Hg) as Hc.
    pose proof (vgr_valid _ _ HgQ) as HDQ; pose proof (vgr_closed _ _ HgQ) as HcQ.
    pose proof (view_cups_rel p D Hg Hcv m Mm qc k' Is vm D' HMm Hh Hq u0 cups Hgu Hu Ecups) as Hcc.
    pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    set (tc := List.rev (im_nparams Mi')); set (tg := List.rev (im_nparams Mv)).
    (** The container's base: [ub] and [cups] over no base, and [cups]
        over [u0] as the instance gives it. *)
    pose proof (vid_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
    assert (HQb : RQ (env_args nil ub) (env_args nil cups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ); [ unfold ind_nu in Hlb; exact Hlb | exact Hub ]).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ); [ exact Hlc | exact Hcc ]).
    set (Ec := env_args (env_args nil u0) cups); set (Eg := env_args nil u0).
    assert (HQc : RQ (env_args nil cups) Ec) by exact (closed_env_base _ _ _ _ _ _ _ _ (dc_ass _ HcQ) HUQ HRQ Hlc Hlc HQ0).
    assert (HQbE : RQ (env_args nil ub) Ec) by (etransitivity; [ exact HQb | exact HQc ]).
    assert (HQEE : RQ Ec Ec) by (etransitivity; [ symmetry; exact HQc | exact HQc ]).
    (** The two telescopes, equal under the view's instance. *)
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass D' HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams D') by (unfold tc; rewrite List.rev_involutive; exact (vid_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams D' ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HDQ _ _ _ _ HMi' HA))).
    pose proof (vid_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams D'))
      by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (dc_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams D' ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams D' ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams D'))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (dc_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (vid_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HD _ _ _ _ HMv HA))).
    assert (Heq : ind_uparams D ⊨ˣ tele_sub (List.rev tg) Id ≈ tele_sub (List.rev tc) (sb_of_list Id Is)).
    { unfold tg, tc; rewrite !List.rev_involutive, tele_sub_id.
      exact (vg_view_nparams p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ HMm Hh Hq HMi' Hv HMv). }
    assert (Hlen : List.length tg = List.length tc) by (unfold tg, tc; rewrite !List.length_rev, !length_im_nparams; exact Hnn).
    destruct (gsub_props (vg_view_args_gsub p D Hg Hcv _ _ _ _ _ _ _ HMm Hh Hq)) as [Hτ _].
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil u0)) Ecups) as Eτ.
    pose proof (tele_link_types (ind_uparams D) RU (env_args nil u0) HRU HρU (ind_uparams D) (ind_uparams D' ++ ind_uparams D)
                  Id (sb_of_list Id Is) Eg Ec (rel_sub_id (ex_intro _ _ HRU)) Hτ (eval_sub_id _) Eτ tg tc Hag Hac Hlen HWg HWc
                  HTg HTc Heq) as Hlink.
    (** Step by step along the two telescopes. *)
    assert (Main : forall n j preA preB, j + n = List.length tg -> List.length preA = j -> List.length preB = j ->
               per_gargs (List.firstn j tc) (env_args nil ub) Ec preA preB ->
               per_gargs (List.firstn j tc) Ec Ec preB preB ->
               per_gargs (List.firstn j tg) Eg Eg preA preB ->
               per_gargs (List.firstn j tg) Eg Eg preB preB ->
               tele_prefix_rel (nr v) j preA preB ->
               forall s rA rB, Ftele List.skipn j tc in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preA) ⍮ s ↘ rA ->
                 Ftele List.skipn j tg in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ preB) ⍮ s ↘ rB ->
                 tele_prefix_rel (nr v) (List.length tg) (preA ++ rA) (preB ++ rB) /\
                 per_gargs tc (env_args nil ub) Ec (preA ++ rA) (preB ++ rB) /\
                 per_gargs tc Ec Ec (preB ++ rB) (preB ++ rB) /\
                 per_gargs tg Eg Eg (preB ++ rB) (preB ++ rB)).
    { induction n as [| n IH]; intros j preA preB Hjn LA LB G1 G2 G3 G4 Hpre s rA rB FA FB.
      - rewrite List.skipn_all2 in FA by (rewrite <- Hlen; lia).
        rewrite List.skipn_all2 in FB by lia.
        rewrite Nat.add_0_r in Hjn.
        rewrite List.firstn_all2 in G1, G2 by (rewrite <- Hlen; lia).
        rewrite List.firstn_all2 in G4 by lia.
        inversion FA; inversion FB; subst; rewrite !List.app_nil_r.
        split; [ exact Hpre | split; [ exact G1 | split; [ exact G2 | exact G4 ] ] ].
      - destruct (List.nth_error tc j) as [ec |] eqn:HC; [| apply List.nth_error_None in HC; lia ].
        destruct (List.nth_error tg j) as [eg |] eqn:HG; [| apply List.nth_error_None in HG; lia ].
        destruct (proj1 (List.Forall_forall _ _) Hac ec (List.nth_error_In _ _ HC)) as [C ->].
        destruct (proj1 (List.Forall_forall _ _) Hag eg (List.nth_error_In _ _ HG)) as [G ->].
        rewrite (skipn_nth_cons _ _ _ HC) in FA; rewrite (skipn_nth_cons _ _ _ HG) in FB.
        destruct (fresh_tele_cons_inv _ _ _ _ _ FA) as (aA & rA0 & -> & EaA & FA'); clear FA.
        destruct (fresh_tele_cons_inv _ _ _ _ _ FB) as (aB & rB0 & -> & EaB & FB'); clear FB.
        assert (HlA : List.length preA = List.length (List.rev (List.firstn j tc))) by (rewrite List.length_rev, List.length_firstn; lia).
        assert (HlB : List.length preA = List.length (List.rev (List.firstn j tg))) by (rewrite List.length_rev, List.length_firstn; lia).
        (** The container's type at [ub] against it at the instance. *)
        destruct (HTc0 _ _ HC) as [iC HCv].
        destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_firstn _ _ j HWc0)) as [RC HRC].
        pose proof G1 as G1'; rewrite <- (List.rev_involutive (List.firstn j tc)) in G1'.
        pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRQ HRC (rel_ctx_wf_firstn _ _ j HWc0) HQbE HlA G1') as E1.
        destruct (rel_exp_of_typ_inversion_simple_at HRC HCv _ _ E1) as (a1 & a2 & Ea1 & Ea2 & [R12 H12]).
        rewrite <- env_args_app in Ea1.
        assert (a1 = aA) as -> by (eapply functional_eval_exp; eassumption).
        (** The container's at the instance against the group's. *)
        destruct (Hlink j preB G C LB HG HC G4 G2) as (iL & RL & b & a & Eb & Ea & Hba).
        unfold Eg in Eb; rewrite <- env_args_app in Eb.
        assert (b = aB) as -> by (eapply functional_eval_exp; eassumption).
        assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
        destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H12 (per_univ_sym _ _ _ _ Hba)) as (Rx & Hx & _).
        (** The group's type at the two prefixes. *)
        destruct (HTg _ _ HG) as [iG HGv].
        destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_firstn _ _ j HWg)) as [RG HRG].
        pose proof G3 as G3'; rewrite <- (List.rev_involutive (List.firstn j tg)) in G3'.
        pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRU HRG (rel_ctx_wf_firstn _ _ j HWg) HρU HlB G3') as E3.
        destruct (rel_exp_of_typ_inversion_simple_at HRG HGv _ _ E3) as (g1 & g2 & Eg1 & Eg2 & [Rg Hg12]).
        unfold Eg in Eg1, Eg2; rewrite <- env_args_app in Eg1, Eg2.
        assert (g2 = aB) as -> by (eapply functional_eval_exp; eassumption).
        (** The fresh variables. *)
        assert (Hxx : Rx (⇑! aA s) (⇑! aB s)) by exact (per_bot_then_per_elem Hx var_per_bot).
        assert (HRg : Rg (⇑! aA s) (⇑! aB s)) by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hg12 Hx); exact Hxx).
        assert (H12x : R12 (⇑! aA s) (⇑! aB s)) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H12 Hx); exact Hxx).
        pose proof (per_univ_trans _ _ _ _ _ _ Hba (per_univ_sym _ _ _ _ Hba)) as Hbb.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hba) Hba) as Haa.
        assert (Hbbx : RL (⇑! aB s) (⇑! aB s)) by exact (per_bot_then_per_elem Hbb var_per_bot).
        assert (Hnrx : nr v j preA (⇑! aA s) (⇑! aB s)).
        { unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMv HG).
          apply (per_head_left Eg1 Eg2 Hg12); exact HRg. }
        assert (HfC : List.firstn (S j) tc = List.firstn j tc ++ ce_ass C :: nil) by exact (firstn_S_nth _ _ _ HC).
        assert (HfG : List.firstn (S j) tg = List.firstn j tg ++ ce_ass G :: nil) by exact (firstn_S_nth _ _ _ HG).
        assert (LfC : List.length preA = List.length (List.firstn j tc)) by (rewrite List.length_firstn; lia).
        assert (LfC' : List.length preB = List.length (List.firstn j tc)) by (rewrite List.length_firstn; lia).
        assert (LfG : List.length preA = List.length (List.firstn j tg)) by (rewrite List.length_firstn; lia).
        assert (LfG' : List.length preB = List.length (List.firstn j tg)) by (rewrite List.length_firstn; lia).
        pose proof (IH (S j) (preA ++ ⇑! aA s :: nil) (preB ++ ⇑! aB s :: nil) ltac:(lia)
                      ltac:(rewrite List.length_app; cbn; lia) ltac:(rewrite List.length_app; cbn; lia)) as IH'.
        rewrite HfC, HfG in IH'.
        replace (preA ++ ⇑! aA s :: rA0) with ((preA ++ ⇑! aA s :: nil) ++ rA0) by (rewrite <- List.app_assoc; reflexivity).
        replace (preB ++ ⇑! aB s :: rB0) with ((preB ++ ⇑! aB s :: nil) ++ rB0) by (rewrite <- List.app_assoc; reflexivity).
        refine (IH' _ _ _ _ _ (S s) _ _ _ _).
        + apply (per_gargs_snoc _ C _ _ _ _ _ _ iC R12 LfC G1); [ econstructor; [ rewrite <- env_args_app; exact EaA | exact Ea | exact H12 ] | exact H12x ].
        + apply (per_gargs_snoc _ C _ _ _ _ _ _ iL RL LfC' G2); [ econstructor; [ exact Ea | exact Ea | exact Haa ] | exact Hbbx ].
        + assert (Eg1' : ⟦ G ⟧ env_args Eg preA ↘ g1) by (unfold Eg; rewrite <- env_args_app; exact Eg1).
          assert (EaB' : ⟦ G ⟧ env_args Eg preB ↘ aB) by (unfold Eg; rewrite <- env_args_app; exact EaB).
          apply (per_gargs_snoc _ G _ _ _ _ _ _ iG Rg LfG G3); [ econstructor; [ exact Eg1' | exact EaB' | exact Hg12 ] | exact HRg ].
        + assert (EaB' : ⟦ G ⟧ env_args Eg preB ↘ aB) by (unfold Eg; rewrite <- env_args_app; exact EaB).
          apply (per_gargs_snoc _ G _ _ _ _ _ _ iL RL LfG' G4); [ econstructor; [ exact EaB' | exact EaB' | exact Hbb ] | exact Hbbx ].
        + apply tele_prefix_rel_snoc; [ exact Hpre | exact Hnrx ].
        + rewrite List.app_assoc, env_args_snoc; exact FA'.
        + rewrite List.app_assoc, env_args_snoc; exact FB'.
    }
    intros s nsA nsB FA FB.
    pose proof (Main (List.length tg) 0 nil nil eq_refl eq_refl eq_refl ltac:(constructor) ltac:(constructor) ltac:(constructor)
                  ltac:(constructor) (tele_prefix_rel_nil _) s nsA nsB) as H.
    cbn [List.skipn List.app] in H; rewrite !List.app_nil_r in H.
    destruct (H FA FB) as (Hpre & G1 & G2 & G4).
    assert (HWt : ⊨ List.rev tc ++ ind_uparams D') by exact HWc0.
    assert (HQcb : RQ Ec (env_args nil cups)) by (symmetry; exact HQc).
    assert (HQbb : RQ (env_args nil ub) (env_args nil ub)) by (etransitivity; [ exact HQb | symmetry; exact HQb ]).
    pose proof (per_gargs_base _ _ _ HRQ HWt Hac _ _ _ _ _ _ HQbE HQbb HQcb G1) as G1'.
    pose proof (per_gargs_base _ _ _ HRQ HWt Hac _ _ _ _ _ _ HQEE HQcb HQcb G2) as G2'.
    assert (Hub' : per_gargs (List.rev (ind_uparams D')) nil nil ub cups) by exact Hub.
    constructor; unfold im_params; rewrite ?List.rev_app_distr.
    - apply tele_rel_of_pre; exact Hpre.
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlb | exact Hub' | exact G1' ].
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlc | exact Hcc | exact G2' ].
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hgu | exact G4 ].
  Qed.
End CrossFresh.

End Fixed_GCtx.
