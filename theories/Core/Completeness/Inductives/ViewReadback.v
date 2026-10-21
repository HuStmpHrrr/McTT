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
(** The relations of types linked by a related pair agree. *)
Lemma rel_link : forall (i j k : uidx) R T S a b c d, DF a ≈ b ∈ per_univ_elem i ↘ R -> DF b ≈ c ∈ per_univ_elem j ↘ T ->
    DF c ≈ d ∈ per_univ_elem k ↘ S -> (R <~> S).
Proof.
  intros * H1 H2 H3.
  etransitivity; [ exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ H1 H2) | exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ H2 H3) ].
Qed.

(** A fresh variable of a type is related to one of a related type. *)
Lemma fresh_var_rel : forall (i : uidx) R a b s, DF a ≈ b ∈ per_univ_elem i ↘ R -> R (⇑! a s) (⇑! b s).
Proof. intros * H; exact (per_bot_then_per_elem H var_per_bot). Qed.

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

Lemma fresh_cargs_arg_inv : forall pq U A gs ρ s vs, Fcargs ca_arg A :: gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦ A ⟧ ρ ↘ a /\ Fcargs gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma fresh_cargs_rec_inv : forall pq U t gs ρ s vs, Fcargs ca_rec t :: gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦shty t of pq U ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a /\
      Fcargs gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

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

  (** *** The Fresh Arguments of a Constructor

      Of the constructor [c] of the container's member (kinds [gsA]) and of
      the group's (kinds [gsB]), after the fresh non-uniform parameters
      [nsA] and [nsB]: related at the group's relations ([con_args_rel] and
      its non-recursive ones), position by position.  The invariant is the
      container's telescope between the two sides and at the group's side,
      and the group's telescope at its side; each type the container's
      variable has is related to the group's through them. *)
  Section CrossArgs.
    Variables (c : String.string) (gsA gsB : list carg).
    Hypotheses (HconA : ind_con Mi' c = Some gsA) (HconB : ind_con Mv c = Some gsB) (Hcorr : cargs_corr vm gsA gsB).
    Variables (nsA nsB : list domain).
    Hypothesis (Hcp : cross_params nsA nsB).
    Hypothesis (HnsA : tele_rel (canon_nparams_rel D' ub i') (List.rev (im_nparams Mi')) nsA nsA).
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel u0.

    (** One position: the container's type there [CA], the group's [CG],
        the container's variable's type [aA] related to [CA] at its side,
        the group's [aB] to [CG] at its: the invariant extends, and the
        variables are related at the group's type. *)
    Lemma cross_position : forall gA1 gA gA2 gB1 gB gB2 vA1 vB1 CA CG aA aB s,
        gsA = gA1 ++ gA :: gA2 -> gsB = gB1 ++ gB :: gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) = ce_ass CA :: cargs_ctx qc D' Mi' gA1 ->
        cargs_ctx p D Mv (gB1 ++ gB :: nil) = ce_ass CG :: cargs_ctx p D Mv gB1 ->
        (exists (i : nat) R cA, ⟦ CA ⟧ env_args nil (ub ++ nsA ++ vA1) ↘ cA /\ DF cA ≈ aA ∈ per_univ_elem i ↘ R) ->
        (exists (i : nat) R gB0, ⟦ CG ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\ DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) /\
        per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) /\
        per_gargs (List.rev (cargs_ctx p D Mv (gB1 ++ gB :: nil) ++ im_params D Mv)) nil nil
          (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) /\
        per_head CG CG (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)) (⇑! aA s) (⇑! aB s) /\
        (exists (i : uidx) R, DF aA ≈ aB ∈ per_univ_elem i ↘ R).
    Proof.
      intros * HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg [iA [RA [cA' [EcA' HcaA]]]] [iB [RB [gB' [EgB' HgaB]]]].
      destruct Hcp as [Hns HpA HpC HpG].
      pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
      pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
      assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
      pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
      rewrite List.length_rev, length_im_nparams in LnA, LnB.
      assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
      (** The container's type, at the two sides. *)
      destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ gA :: nil) gA2
                  ltac:(rewrite <- List.app_assoc; exact HeA)) as [HWc1 _].
      rewrite ECc in HWc1.
      destruct (rel_ctx_wf_ass_inv HWc1) as [ic HCv].
      pose proof (rel_ctx_wf_tail HWc1) as HWc.
      destruct (rel_ctx_wf_per_ctx_env HWc) as [RW HRW].
      assert (LW : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
        by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      pose proof (gargs_env_rel _ _ _ _ _ _ HRW HWc LW K1) as E1.
      destruct (rel_exp_of_typ_inversion_simple_at HRW HCv _ _ E1) as (cA & cB & EcA & EcB & [RC HRC]).
      assert (cA' = cA) as -> by (eapply functional_eval_exp; eassumption).
      (** The container's type at the group's side against the group's. *)
      pose proof (view_arg_link p D Hg Hcv m Mm qc k' Is vm D' HMm Hh Hq HcvQ u0 cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                    c gsA gsB HconA HconB Hcorr nsB LnB gA1 gA gA2 gB1 gB gB2 CA CG vB1 HeA HeB (eq_sym Hl1) LB ECc ECg K3 K2) as HL.
      destruct (group_container_types_related _ _ _ _ HL) as (iL & RL & gB0 & cB0 & EgB & EcB0 & HgcL).
      assert (cB0 = cB) as -> by (eapply functional_eval_exp; eassumption).
      assert (gB' = gB0) as -> by (eapply functional_eval_exp; eassumption).
      (** The chain from the container's variable to the group's. *)
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HcaA) HRC) as (R1 & H1 & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 (per_univ_sym _ _ _ _ HgcL)) as (R2 & H2 & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H2 HgaB) as (Rx & Hx & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HgcL) HgaB) as (R3 & H3 & _).
      pose proof (fresh_var_rel _ _ _ _ s Hx) as Hxx.
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hx) Hx) as Hbb.
      pose proof (fresh_var_rel _ _ _ _ s Hbb) as Hxb.
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRC) HRC) as HCC.
      pose proof (per_univ_trans _ _ _ _ _ _ HgcL (per_univ_sym _ _ _ _ HgcL)) as HGG.
      assert (HRCx : RC (⇑! aA s) (⇑! aB s))
        by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HRC (per_univ_sym _ _ _ _ H1) Hx); exact Hxx).
      assert (HCCx : RC (⇑! aB s) (⇑! aB s)) by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HCC H3 Hbb); exact Hxb).
      assert (HGGx : RL (⇑! aB s) (⇑! aB s)) by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HGG HgaB Hbb); exact Hxb).
      assert (HGAx : RL (⇑! aA s) (⇑! aB s))
        by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HGG (per_univ_sym _ _ _ _ H2) Hx); exact Hxx).
      rewrite ECc, ECg.
      cbn [List.app List.rev].
      replace (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) with ((ub ++ nsA ++ vA1) ++ ⇑! aA s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
      replace (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((cups ++ nsB ++ vB1) ++ ⇑! aB s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
      replace (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((u0 ++ nsB ++ vB1) ++ ⇑! aB s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
      assert (LW' : List.length (ub ++ nsA ++ vA1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev; exact LW).
      assert (LW2 : List.length (cups ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      assert (LW3 : List.length (u0 ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      split; [| split; [| split; [| split ] ] ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW' K1); [ econstructor; [ exact EcA | exact EcB | exact HRC ] | exact HRCx ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW2 K2); [ econstructor; [ exact EcB | exact EcB | exact HCC ] | exact HCCx ].
      - apply (per_gargs_snoc _ CG _ _ _ _ _ _ iL RL LW3 K3); [ econstructor; [ exact EgB | exact EgB | exact HGG ] | exact HGGx ].
      - apply (per_head_left EgB EgB HGG); exact HGAx.
      - exists iA, Rx; exact Hx.
    Qed.

    (** A recursive argument related at the group's side's prefix on both
        sides is related at the two prefixes. *)
    Lemma cross_rec_move : forall gB1 t gB2 vA1 vB1 x y, gsB = gB1 ++ ca_rec t :: gB2 ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y.
    Proof.
      intros * HeB K4 K6 H.
      destruct Hcp as [Hns _ _ _].
      destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
      pose proof (vgr_ass _ _ Hg) as Hass.
      pose proof (nparams_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as Hsn.
      pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HBB.
      pose proof (nparams_rel_refl_l p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HAA.
      assert (HconB' : ind_con Mv c = Some (gB1 ++ ca_rec t :: gB2)) by (rewrite <- HeB; exact HconB).
      assert (HK : List.length (cargs_nonrec gB1) <= List.length (cargs_nonrec gsB))
        by (rewrite HeB, cargs_nonrec_app, List.length_app; lia).
      pose proof (args_prefix_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA c gsB _ _ _ HAA HconB HK K4) as K4A.
      pose proof (args_prefix_rel_inst p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA nsB c gsB _ _ _ Hns HconB HK K4A) as K4s.
      destruct (ind_rel_sym_all p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI (okr_at D u0 nr)) as (_ & _ & Hsym & _).
      pose proof (Hsym _ _ _ _ _ _ _ _ H Mv nsB nsB c gB1 t gB2 _ _ 0 nil nil HMv
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) HBB HconB' K6
                    eq_refl ltac:(lia) (tele_prefix_rel_nil _)) as H1.
      pose proof (proj1 (vg_rec_arg_move_right p D Hg v Mv c gB1 t gB2 u0 u0 nsB nsA _ _ _ _ HMv HconB' Hgu Hu Hsn K4s) H1) as H2.
      exact (Hsym _ _ _ _ _ _ _ _ H2 Mv nsB nsA c gB1 t gB2 _ _ 0 nil nil HMv
               ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) Hsn HconB' K4s
               eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
    Qed.

    Lemma cross_fresh_cargs : forall gA2 gB2 gA1 gB1 vA1 vB1, gsA = gA1 ++ gA2 -> gsB = gB1 ++ gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (canon_args_rel D' ub i' nsA c) (List.length (cargs_nonrec gA1))
          (nonrec_arg_vals gA1 vA1) (nonrec_arg_vals gA1 vA1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        forall s vA2 vB2, Fcargs gA2 of qc ub in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ⍮ s ↘ vA2 ->
          Fcargs gB2 of p u0 in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ⍮ s ↘ vB2 ->
          con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1) (nsB ++ nonrec_arg_vals gB1 vB1)
            gB2 vA2 vB2 /\
          tele_rel_from (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1)
            (nonrec_arg_vals gB2 vA2) (nonrec_arg_vals gB2 vB2).
    Proof.
      induction gA2 as [| gA gA2 IH]; intros [| gB gB2] gA1 gB1 vA1 vB1 HeA HeB Hc1 LA LB K1 K2 K3 K4 K5 K6 s vA2 vB2 FA FB.
      - inversion FA; inversion FB; subst; split; [ constructor | exact I ].
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
        assert (Hco : cargs_corr vm (gA :: gA2) (gB :: gB2))
          by (rewrite HeA, HeB in Hcorr; exact (proj2 (cargs_corr_split _ _ _ _ _ Hcorr Hl1))).
        pose proof Hcp as [Hns HpA HpC HpG].
        pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
        rewrite List.length_rev, length_im_nparams in LnA, LnB.
        pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
        pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
        assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
        pose proof (uparams_refl_l D' (vgr_valid _ _ HgQ) (vgr_closed _ _ HgQ) _ _ Hub) as Hubub.
        destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
        pose proof (vgr_ass _ _ Hg) as Hass.
        pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HnsB.
        assert (HeA'' : gsA = (gA1 ++ gA :: nil) ++ gA2) by (rewrite <- List.app_assoc; exact HeA).
        assert (HeB'' : gsB = (gB1 ++ gB :: nil) ++ gB2) by (rewrite <- List.app_assoc; exact HeB).
        assert (Hc1' : cargs_corr vm (gA1 ++ gA :: nil) (gB1 ++ gB :: nil)).
        { apply cargs_corr_app; [ exact Hc1 |].
          destruct gA, gB; cbn in Hco |- *; try contradiction; try exact I; tauto. }
        (** The container's telescope at its side, and the group's at its. *)
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gA1 (gA :: gA2) HeA) as [HWA0 _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gB1 (gB :: gB2) HeB) as [HWB0 _].
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gsA nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨA _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gsB nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨB _].
        assert (LWA : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (LWB : List.length (u0 ++ nsB ++ vB1) = List.length (cargs_ctx p D Mv gB1 ++ im_params D Mv))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (K1A : per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (ub ++ nsA ++ vA1)).
        { assert (HW' : ⊨ List.rev (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) ++ ⋅)
            by (rewrite List.rev_involutive, List.app_nil_r; exact HWA0).
          assert (Hta : tele_ass (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
            by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D' (vgr_closed _ _ HgQ) i' Mi' HMi') ]).
          exact (per_gargs_refl_l _ _ _ per_ctx_env_nil_true HW' Hta _ _ _ _ I K1). }
        assert (RenvA : forall R, EF cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ≈ cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ∈ per_ctx_env ↘ R ->
                          R (env_args nil (ub ++ nsA ++ vA1)) (env_args nil (ub ++ nsA ++ vA1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWA0 LWA K1A)).
        assert (RenvB : forall R, EF cargs_ctx p D Mv gB1 ++ im_params D Mv ≈ cargs_ctx p D Mv gB1 ++ im_params D Mv ∈ per_ctx_env ↘ R ->
                          R (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWB0 LWB K3)).
        pose proof (cargs_ctx_snoc qc D' Mi' gA1 gA) as ECc; pose proof (cargs_ctx_snoc p D Mv gB1 gB) as ECg.
        cbn [cargs_ctx_aux List.app] in ECc, ECg.
        assert (LAB : List.length vA1 = List.length gB1) by lia.
        assert (LBA : List.length vB1 = List.length gA1) by lia.
        (** The group's type at a recursive position, at its side. *)
        assert (Hgrec : forall t, gB = ca_rec t -> exists (iG : nat) RGG gB0,
                   ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                   DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG).
        { intros t ->.
          destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB (gB1 ++ ca_rec t :: nil) gB2 HeB'') as [HWB1 _].
          rewrite ECg in HWB1; destruct (rel_ctx_wf_ass_inv HWB1) as [iG HGv].
          pose proof (rel_ctx_wf_tail HWB1) as HWB.
          destruct (rel_ctx_wf_per_ctx_env HWB) as [RWB HRWB].
          destruct (rel_exp_of_typ_inversion_simple_at HRWB HGv _ _ (gargs_env_rel _ _ _ _ _ _ HRWB HWB LWB K3))
            as (gB0 & gB0' & EgB & EgB' & [RGG HGG]).
          assert (gB0' = gB0) as -> by (eapply functional_eval_exp; eassumption).
          exists iG, RGG, gB0; split; [ exact EgB | exact HGG ]. }
        (** At a recursive position of the group: its variable and the
            relation of its type, the recursive argument's. *)
        assert (Hglink : forall t aB, gB = ca_rec t ->
                   ⟦shty t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ↘ aB ->
                   exists (iG : nat) RGG gB0, ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                     DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG /\
                     (exists (i : nat) R, DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) /\
                     (RGG <~> rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                                (nsB ++ nonrec_arg_vals gB1 vB1) t)).
        { intros t aB -> EaB.
          destruct (Hgrec t eq_refl) as (iG & RGG & gB0 & EgB & HGG).
          destruct (shty_link p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB
                      (view_end_type VP HP p D HPD u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EgB) HGG)
            as (b & Eb & [RB HgaB]).
          rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
          assert (b = aB) as -> by (eapply functional_eval_shty; eassumption).
          pose proof (view_end_rel_of_agreement p D Hg Hcv u0 u0 Hgu Hu (ptyp_mem t)
                        (view_agreement_canonical_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t))) as Hendr.
          pose proof (shape_char p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB Hendr
                        (List.length (ptyp_doms t)) 0 nil gB0 iG RGG eq_refl (tele_prefix_rel_nil _) ltac:(constructor)
                        ltac:(rewrite List.app_nil_r; exact EgB) HGG) as ERG.
          rewrite List.app_nil_r in ERG; cbn [ptyp_skip] in ERG.
          exists iG, RGG, gB0; split; [ exact EgB | split; [ exact HGG | split; [ exists iG, RB; exact HgaB | exact ERG ] ] ]. }
        destruct gA as [A' | t'], gB as [A | t]; cbn [cargs_corr] in Hco; try contradiction.
        + (** Non-recursive in both. *)
          destruct (fresh_cargs_arg_inv _ _ _ _ _ _ _ FA) as (aA & vA2' & -> & EaA & FA').
          destruct (fresh_cargs_arg_inv _ _ _ _ _ _ _ FB) as (aB & vB2' & -> & EaB & FB').
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA' & EcA & EaA' & HcaA).
          assert (aA' = aA) as -> by (eapply functional_eval_exp; eassumption).
          destruct (vg_arg_types p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (iB & RB & gB0 & aB' & EgB & EaB' & HgaB).
          assert (aB' = aB) as -> by (eapply functional_eval_exp; eassumption).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_arg A) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as (K1' & K2' & K3' & Hrel & ix & Rx & Hx).
          (** The non-recursive relations at the position. *)
          assert (HnthB : List.nth_error (cargs_nonrec gsB) (List.length (cargs_nonrec gB1)) = Some A)
            by (rewrite HeB, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          assert (HnthA : List.nth_error (cargs_nonrec gsA) (List.length (cargs_nonrec gA1)) = Some A')
            by (rewrite HeA, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (vg_arg_head p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (i2 & R2 & a2 & Ea2 & HR2 & E2).
          assert (a2 = gB0) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hx) Hx) as Hbb.
          pose proof (per_univ_trans _ _ _ _ _ _ Hx (per_univ_sym _ _ _ _ Hx)) as Haa.
          assert (HarB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (⇑! aA s) (⇑! aB s))
            by (apply E2, (per_head_left Ea2 Ea2 HR2); exact Hrel).
          assert (HarA : ar v nsA c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (⇑! aA s) (⇑! aB s))
            by (apply (CaI v Mv nsA nsB c gsB _ A _ _ HMv Hns HconB HnthB K4); exact HarB).
          assert (HbbB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (⇑! aB s) (⇑! aB s)).
          { apply E2, (rel_link _ _ _ _ _ _ _ _ _ _ HR2 HgaB Hbb); exact (fresh_var_rel _ _ _ _ s Hbb). }
          assert (HaaA : canon_args_rel D' ub i' nsA c (List.length (cargs_nonrec gA1)) (nonrec_arg_vals gA1 vA1) (⇑! aA s) (⇑! aA s)).
          { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMi' HconA HnthA).
            apply (per_head_left EaA EaA Haa); exact (fresh_var_rel _ _ _ _ s Haa). }
          destruct (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_arg A :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) (vA2 := vA2') (vB2 := vB2') as [IHc IHf].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K4 | exact HarA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K6 | exact HbbB ].
          * rewrite nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals].
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact FA'.
          * rewrite nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals].
            replace (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1 ++ ⇑! aB s :: nil)
              with ((u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ++ ⇑! aB s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact FB'.
          * rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf; cbn [nonrec_arg_vals] in IHf.
            rewrite cargs_nonrec_app, List.length_app in IHf; cbn [cargs_nonrec List.length] in IHf; rewrite Nat.add_1_r in IHf.
            split.
            -- apply con_args_arg; rewrite <- !List.app_assoc; exact IHc.
            -- cbn [nonrec_arg_vals tele_rel_from]; split; [ exact HarA | exact IHf ].
        + (** Non-recursive in the container, recursive in the group. *)
          destruct (fresh_cargs_arg_inv _ _ _ _ _ _ _ FA) as (aA & vA2' & -> & EaA & FA').
          destruct (fresh_cargs_rec_inv _ _ _ _ _ _ _ FB) as (aB & vB2' & -> & EaB & FB').
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA' & EcA & EaA' & HcaA).
          assert (aA' = aA) as -> by (eapply functional_eval_exp; eassumption).
          destruct (Hglink t aB eq_refl EaB) as (iG & RGG & gB0 & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as (K1' & K2' & K3' & Hrel & ix & Rx & Hx).
          assert (Hrr : rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                          (nsB ++ nonrec_arg_vals gB1 vB1) t (⇑! aA s) (⇑! aB s))
            by (apply ERG, (per_head_left EgB EgB HGG); exact Hrel).
          pose proof (cross_rec_move gB1 t gB2 vA1 vB1 _ _ HeB K4 K6 Hrr) as HrrA.
          assert (HnthA : List.nth_error (cargs_nonrec gsA) (List.length (cargs_nonrec gA1)) = Some A')
            by (rewrite HeA, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          pose proof (per_univ_trans _ _ _ _ _ _ Hx (per_univ_sym _ _ _ _ Hx)) as Haa.
          assert (HaaA : canon_args_rel D' ub i' nsA c (List.length (cargs_nonrec gA1)) (nonrec_arg_vals gA1 vA1) (⇑! aA s) (⇑! aA s)).
          { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMi' HconA HnthA).
            apply (per_head_left EaA EaA Haa); exact (fresh_var_rel _ _ _ _ s Haa). }
          destruct (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) (vA2 := vA2') (vB2 := vB2') as [IHc IHf].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [nonrec_arg_vals].
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact FA'.
          * rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [nonrec_arg_vals]; rewrite List.app_nil_r; exact FB'.
          * rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf; cbn [nonrec_arg_vals] in IHf; rewrite List.app_nil_r in IHf.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            split.
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
        + (** Recursive in both. *)
          destruct Hco as (Hmt & Hdt & Hco).
          destruct (fresh_cargs_rec_inv _ _ _ _ _ _ _ FA) as (aA & vA2' & -> & EaA & FA').
          destruct (fresh_cargs_rec_inv _ _ _ _ _ _ _ FB) as (aB & vB2' & -> & EaB & FB').
          (** The container's type at its side, against its variable's. *)
          destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ ca_rec t' :: nil) gA2 HeA'') as [HWA1 _].
          rewrite ECc in HWA1; destruct (rel_ctx_wf_ass_inv HWA1) as [iC HCv].
          pose proof (rel_ctx_wf_tail HWA1) as HWA.
          destruct (rel_ctx_wf_per_ctx_env HWA) as [RWA HRWA].
          destruct (rel_exp_of_typ_inversion_simple_at HRWA HCv _ _ (gargs_env_rel _ _ _ _ _ _ HRWA HWA LWA K1A))
            as (cA & cA' & EcA & EcA' & [RCC HCC]).
          assert (cA' = cA) as -> by (eapply functional_eval_exp; eassumption).
          destruct (shty_link qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA HΨA gA1 t' gA2 HeA ub nsA vA1 Hlb ltac:(lia) LA Hubub HnsA K5 RenvA
                      (view_end_type VP HP qc D' HVQ ub Hubub Hlb (ptyp_mem t')) (List.length (ptyp_doms t')) 0 nil cA iC RCC
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EcA) HCC)
            as (b & Eb & [RA HcaA]).
          rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
          assert (b = aA) as -> by (eapply functional_eval_shty; eassumption).
          destruct (Hglink t aB eq_refl EaB) as (iG & RGG & gB0 & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_rec t') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iC, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as (K1' & K2' & K3' & Hrel & ix & Rx & Hx).
          assert (Hrr : rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                          (nsB ++ nonrec_arg_vals gB1 vB1) t (⇑! aA s) (⇑! aB s))
            by (apply ERG, (per_head_left EgB EgB HGG); exact Hrel).
          pose proof (cross_rec_move gB1 t gB2 vA1 vB1 _ _ HeB K4 K6 Hrr) as HrrA.
          destruct (IH gB2 (gA1 ++ ca_rec t' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) (vA2 := vA2') (vB2 := vB2') as [IHc IHf].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K5.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [nonrec_arg_vals]; rewrite List.app_nil_r; exact FA'.
          * rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [nonrec_arg_vals]; rewrite List.app_nil_r; exact FB'.
          * rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf; cbn [nonrec_arg_vals] in IHf; rewrite List.app_nil_r in IHf.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            split.
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
    Qed.
  End CrossArgs.
End CrossFresh.

End Fixed_GCtx.
