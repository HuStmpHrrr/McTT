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

(** The type of a recursive argument of a group at its uniform parameters
    [u0], after the prefix [ms'], [ws'], [ys'], against any type related
    to it: their domains at arguments related at the group's relation of
    the domain at the prefix [ms], [ws], [ys] read back alike. *)
Lemma shape_tops_cross : forall p D, valid_group p D -> forall u0, per_gargs (List.rev (ind_uparams D)) nil nil u0 u0 ->
    List.length u0 = ind_nu D ->
    forall v Mv c gs gs1 t gs2 ms ms' ws ws', ind_member D v = Some Mv -> ind_con Mv c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_rel (canon_nparams_rel D u0 v) (List.rev (im_nparams Mv)) ms ms' ->
      tele_prefix_rel (canon_args_rel D u0 v ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      forall n kk ys ys' a1 a2 (i : uidx) R, kk + n = List.length (ptyp_doms t) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel u0 v) ms ws (ptyp_doms t)) kk ys ys' ->
        ⟦shty ptyp_skip kk t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ms' ++ ws' ++ ys') ↘ a2 ->
        DF a1 ≈ a2 ∈ per_univ_elem i ↘ R ->
        shape_tops (canon_doms_rel u0) v (ms ++ ws ++ ys) (ptyp_skip kk t) a1 a2.
Proof.
  intros p D Hg u0 Hgu Hu v Mv c gs gs1 t gs2 ms ms' ws ws' HM Hc Heq Hm Hw.
  destruct (vg_doms_related p D Hg u0 u0 Hgu Hu Hgu) as [ud Hdr].
  induction n as [| n IH]; intros kk ys ys' a1 a2 i R Hkn Hy E2 HR.
  - rewrite Nat.add_0_r in Hkn; subst kk; rewrite ptyp_skip_end; constructor.
  - destruct (ptyp_skip_lt kk t ltac:(lia)) as (B & HB & Hs); rewrite Hs in E2 |- *.
    remember (ptyp_skip (S kk) t) as t1 eqn:Ht1.
    inversion E2 as [| B0 ρ0 b2 t0 ? ? Eb2]; subst B0 ρ0 t0 a2.
    basic_invert_per_univ_elem HR.
    rename equiv_a_a' into Hab.
    destruct (Hdr v Mv ms ms' c gs gs1 t gs2 ws ws' kk B ys ys' HM Hm Hc Heq Hw HB Hy) as (d & d' & Ed & Ed' & [Rd Hdd]).
    assert (d' = b2) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_trans _ _ _ _ _ _ Hdd (per_univ_sym _ _ _ _ Hdd)) as Hd0.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Hdd (per_univ_sym _ _ _ _ Hab)) as (Rx & Hx & _).
    assert (Hin : forall c0 c0', canon_doms_rel u0 v (ms ++ ws ++ ys) B c0 c0' -> in_rel c0 c0').
    { intros c0 c0' Hcc; apply (rel_link _ _ _ _ _ _ _ _ _ _ Hd0 Hx Hab); exact (Hcc _ _ _ _ Ed Ed Hd0). }
    constructor.
    + intros c0 c0' Hcc; exact (per_elem_then_per_top Hab (Hin _ _ Hcc)).
    + intros c0 c0' x x' Hcc Ex Ex'.
      pose proof (Hin _ _ Hcc) as Hcc'.
      match goal with
      | Hcod : forall c c' (equiv_c_c' : in_rel c c'), rel_mod_eval _ _ _ _ _ _ |- _ =>
          destruct (Hcod _ _ Hcc') as [x0 x0' Ex0 Ex0' HRx]
      end.
      assert (x0 = x) as -> by (eapply functional_eval_exp; eassumption).
      assert (x0' = x') as -> by (eapply functional_eval_exp; eassumption).
      apply fam_cod_shfam_inv in Ex'; rewrite <- env_args_snoc3 in Ex'.
      replace ((ms ++ ws ++ ys) ++ c0 :: nil) with (ms ++ ws ++ (ys ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
      subst t1.
      apply (IH (S kk) (ys ++ c0 :: nil) (ys' ++ c0' :: nil) x x' i (out_rel c0 c0' Hcc') ltac:(lia)); [| exact Ex' | exact HRx ].
      apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ].
Qed.

(** The arguments [vsA] of a container's constructor (kinds [gsA]) and
    [vsB] of the group's at the view (kinds [gsB]), after the container's
    side's prefix [pre], extended as [con_args_rel] does: at each argument
    recursive in both, a fresh variable on each side whose types' domains
    read back alike. *)
Inductive cross_tops (dr : nat -> list domain -> exp -> relation domain) (k : nat) :
    list domain -> list carg -> list carg -> list domain -> list domain -> Prop :=
| cross_tops_nil : forall pre, cross_tops dr k pre nil nil nil nil
| cross_tops_arg : forall pre A' A gsA gsB vA vB vsA vsB,
    cross_tops dr k (pre ++ vA :: nil) gsA gsB vsA vsB ->
    cross_tops dr k pre (ca_arg A' :: gsA) (ca_arg A :: gsB) (vA :: vsA) (vB :: vsB)
| cross_tops_nest : forall pre A' t gsA gsB vA vB vsA vsB,
    cross_tops dr k pre gsA gsB vsA vsB ->
    cross_tops dr k pre (ca_arg A' :: gsA) (ca_rec t :: gsB) (vA :: vsA) (vB :: vsB)
| cross_tops_rec : forall pre t' t gsA gsB aA aB sA sB vsA vsB,
    shape_tops dr k pre t aA aB ->
    cross_tops dr k pre gsA gsB vsA vsB ->
    cross_tops dr k pre (ca_rec t' :: gsA) (ca_rec t :: gsB) (⇑! aA sA :: vsA) (⇑! aB sB :: vsB).

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

    (** The invariant past one position, the container's variable [aA] and
        the group's [aB] there, at the group's type [CG]: the container's
        prefixes related across and at the group's side, the group's at its
        side, the two variables related at [CG], and their types related. *)
    Record cross_position_step (gA1 : list carg) (gA : carg) (gB1 : list carg) (gB : carg) (vA1 vB1 : list domain)
        (CG : exp) (aA aB : domain) (s : nat) : Prop := mk_cross_position_step
      { container_prefix_rel : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
      ; container_right_prefix : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
      ; group_right_prefix : per_gargs (List.rev (cargs_ctx p D Mv (gB1 ++ gB :: nil) ++ im_params D Mv)) nil nil
          (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
      ; fresh_heads_agree : per_head CG CG (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)) (⇑! aA s) (⇑! aB s)
      ; fresh_types_related : exists (i : uidx) R, DF aA ≈ aB ∈ per_univ_elem i ↘ R }.

    (** One position:the container's type there [CA], the group's [CG],
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
        cross_position_step gA1 gA gB1 gB vA1 vB1 CG aA aB s.
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
      assert (LW' : List.length (ub ++ nsA ++ vA1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev; exact LW).
      assert (LW2 : List.length (cups ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      assert (LW3 : List.length (u0 ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      constructor; [ rewrite ECc | rewrite ECc | rewrite ECg | idtac | idtac ];
        cbn [List.app List.rev];
        [ replace (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) with ((ub ++ nsA ++ vA1) ++ ⇑! aA s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity);
          replace (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((cups ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((cups ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((u0 ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | idtac | idtac ].
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

    (** The rest of the arguments after the positions [gA1] and [gB1], at
        the prefixes [vA1] and [vB1]: the fresh variables on each side, the
        arguments related at the group's relation, the non-recursive ones
        at their types, and the types of the ones recursive in both read
        alike at their domains. *)
    #[warnings="-cannot-define-projection"]
    Record cross_fresh_tail (gA1 gB1 gA2 gB2 : list carg) (vA1 vB1 : list domain) (s : nat) : Prop := mk_cross_fresh_tail
      { cft_vsA : list domain
      ; cft_vsB : list domain
      ; cft_args_a : Fcargs gA2 of qc ub in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ⍮ s ↘ cft_vsA
      ; cft_args_b : Fcargs gB2 of p u0 in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ⍮ s ↘ cft_vsB
      ; cft_related : con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1)
          (nsB ++ nonrec_arg_vals gB1 vB1) gB2 cft_vsA cft_vsB
      ; cft_nonrec : tele_rel_from (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1)
          (nonrec_arg_vals gB2 cft_vsA) (nonrec_arg_vals gB2 cft_vsB)
      ; cft_tops : cross_tops dr v (nsA ++ nonrec_arg_vals gB1 vA1) gA2 gB2 cft_vsA cft_vsB }.

    Lemma cross_fresh_cargs : forall gA2 gB2 gA1 gB1 vA1 vB1, gsA = gA1 ++ gA2 -> gsB = gB1 ++ gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (canon_args_rel D' ub i' nsA c) (List.length (cargs_nonrec gA1))
          (nonrec_arg_vals gA1 vA1) (nonrec_arg_vals gA1 vA1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        forall s, cross_fresh_tail gA1 gB1 gA2 gB2 vA1 vB1 s.
    Proof.
      induction gA2 as [| gA gA2 IH]; intros [| gB gB2] gA1 gB1 vA1 vB1 HeA HeB Hc1 LA LB K1 K2 K3 K4 K5 K6 s.
      - apply (mk_cross_fresh_tail _ _ _ _ _ _ _ nil nil); first [ constructor | exact I ].
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
        assert (Hglink : forall t, gB = ca_rec t ->
                   exists aB (iG : nat) RGG gB0,
                     ⟦shty t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ↘ aB /\
                     ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                     DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG /\
                     (exists (i : nat) R, DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) /\
                     (RGG <~> rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                                (nsB ++ nonrec_arg_vals gB1 vB1) t)).
        { intros t ->.
          destruct (Hgrec t eq_refl) as (iG & RGG & gB0 & EgB & HGG).
          destruct (shty_link p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB
                      (view_end_type VP HP p D HPD u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EgB) HGG)
            as (aB & EaB & [RB HgaB]).
          rewrite List.app_nil_r in EaB; cbn [ptyp_skip] in EaB.
          pose proof (view_end_rel_of_agreement p D Hg Hcv u0 u0 Hgu Hu (ptyp_mem t)
                        (view_agreement_canonical_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t))) as Hendr.
          pose proof (shape_char p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB Hendr
                        (List.length (ptyp_doms t)) 0 nil gB0 iG RGG eq_refl (tele_prefix_rel_nil _) ltac:(constructor)
                        ltac:(rewrite List.app_nil_r; exact EgB) HGG) as ERG.
          rewrite List.app_nil_r in ERG; cbn [ptyp_skip] in ERG.
          exists aB, iG, RGG, gB0; split; [ exact EaB | split; [ exact EgB | split; [ exact HGG | split; [ exists iG, RB; exact HgaB | exact ERG ] ] ] ]. }
        destruct gA as [A' | t'], gB as [A | t]; cbn [cargs_corr] in Hco; try contradiction.
        + (** Non-recursive in both. *)
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA & EcA & EaA & HcaA).
          destruct (vg_arg_types p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (iB & RB & gB0 & aB & EgB & EaB & HgaB).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_arg A) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
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
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K4 | exact HarA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K6 | exact HbbB ].
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'.
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) in FA' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'.
            replace (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1 ++ ⇑! aB s :: nil)
              with ((u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ++ ⇑! aB s :: nil) in FB' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt.
            rewrite cargs_nonrec_app, List.length_app in IHf; cbn [cargs_nonrec List.length] in IHf; rewrite Nat.add_1_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- apply con_args_arg; rewrite <- !List.app_assoc; exact IHc.
            -- cbn [nonrec_arg_vals tele_rel_from]; split; [ exact HarA | exact IHf ].
            -- apply cross_tops_arg; rewrite <- !List.app_assoc; exact IHt.
        + (** Non-recursive in the container, recursive in the group. *)
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA & EcA & EaA & HcaA).
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
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
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'.
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) in FA' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'; rewrite List.app_nil_r in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt;
              rewrite List.app_nil_r in IHf, IHt.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
            -- apply cross_tops_nest; exact IHt.
        + (** Recursive in both. *)
          destruct Hco as (Hmt & Hdt & Hco).
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
            as (aA & EaA & [RA HcaA]).
          rewrite List.app_nil_r in EaA; cbn [ptyp_skip] in EaA.
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_rec t') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iC, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
          assert (Hrr : rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                          (nsB ++ nonrec_arg_vals gB1 vB1) t (⇑! aA s) (⇑! aB s))
            by (apply ERG, (per_head_left EgB EgB HGG); exact Hrel).
          pose proof (cross_rec_move gB1 t gB2 vA1 vB1 _ _ HeB K4 K6 Hrr) as HrrA.
          (** The domains of the two types read alike. *)
          pose proof (shape_tops_cross p D Hg u0 Hgu Hu v Mv c gsB gB1 t gB2 nsA nsB (nonrec_arg_vals gB1 vA1)
                        (nonrec_arg_vals gB1 vB1) HMv HconB HeB Hns K4 (List.length (ptyp_doms t)) 0 nil nil aA aB ix Rx
                        eq_refl (tele_prefix_rel_nil _) ltac:(rewrite List.app_nil_r; exact EaB) Hx) as Hts.
          cbn [ptyp_skip] in Hts; rewrite List.app_nil_r in Hts.
          destruct (IH gB2 (gA1 ++ ca_rec t' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K5.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'; rewrite List.app_nil_r in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'; rewrite List.app_nil_r in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt;
              rewrite List.app_nil_r in IHf, IHt.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
            -- apply cross_tops_rec; [ exact Hts | exact IHt ].
    Qed.
  End CrossArgs.
End CrossFresh.

(** ** The Stuck Eliminators, Read Alike

    The setting of [ElimView.cross_elim_all], without its premise on the
    stuck eliminators, and the container's uniform parameters [ub] related
    to the view's instance [cups] at the group's [u0]. *)
Section CrossBot.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := vgr_valid _ _ Hvg.
  Let Hc := vgr_closed _ _ Hvg.
  Let Hl := vgr_lookup _ _ Hvg.
  Let Hdt := vgr_typed _ _ Hvg.
  Let Hass := vgr_ass _ _ Hvg.
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := vbs_has _ _ _ _ _ _ HBk.
  Let HMall := vbs_mctx _ _ _ _ _ _ HBk.
  Let HAv := vbs_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).

  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Variable (ρb : env) (VBb : list eblock) (ub : list domain).
  Hypotheses (HbB : forall i' Mi', ind_member D' i' = Some Mi' -> exists b, List.nth_error VBb i' = Some b)
    (HnmB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> eb_nm b = S (im_nn Mi'))
    (HnaB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> brs_names (im_cons Mi') (eb_brs b))
    (HarB : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b ->
              ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec gs')%nat).
  Hypothesis (Hmot_x : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba -> G v u u' ns ns' x x' ->
                exists a a', ⟦ eb_motive bb ⟧ env_args ρb (ns ++ x :: nil) ↘ a /\
                  ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
                  DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x').
  Hypothesis (Hbr_x : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
                ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
                G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs')
                  (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
                cross_results_rel dr Rel v u u' C1 p u0 Bks
                  (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
                exists r r', ⟦ Bb ⟧ env_args ρb (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
                  ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
                  Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs))
                    (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r').
  Variable (cups : list domain).
  Hypotheses (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ cups)
    (Hub : per_gargs (List.rev (ind_uparams D')) nil nil ub cups).
  #[local] Abbreviation XE f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC Bks iA HBk qc D' m Mm k' Is vm
     Hq HMm Hh ρb VBb ub HbB HnmB HnaB HarB Hmot_x Hbr_x).
  #[local] Abbreviation CF f := (f VP p D HP HPD m Mm qc k' Is vm D' HMm Hh Hq u0 cups ub u0_gargs' u0_len' Ecups Hub).

  (** The stuck eliminators at the member [j] of the group and the
      container's members the view takes to [j]. *)
  Definition cross_bot (j : nat) : Prop :=
    forall i' Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j -> ind_member D j = Some Mj ->
      G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
      Dom d_elim ρb VBb qc ub i' as1 e ≈ d_elim C1 Bks p u0 j as2 e' ∈ per_bot.

  (** *** The Recursive Results at a Neutral

      An argument both nest through but the group read does not: the two
      eliminators at it, stuck at the members its shapes end in. *)

  (** The recursive results at the arguments [x] and [x'] of the shapes
      [t'] (the container's) and [t] (the group's): the container's under
      its eliminator, the group's under its own, related as recursive
      results. *)
  #[warnings="-cannot-define-projection"]
  Record cross_ih_pair (t t' : ptyp) (k : nat) (u u' pre pre' : list domain) (x x' : domain) : Prop :=
    mk_cross_ih_pair
    { cip_container : domain
    ; cip_group : domain
    ; cip_container_eval : ⟦ih x of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cip_container
    ; cip_group_eval : ⟦ih x' of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ cip_group
    ; cip_related : rec_result_rel dr Rel k u u' pre pre' t x x' cip_container cip_group }.

  Lemma cross_ih_neut : forall t t' k u u' pre pre' a1 a2 e e', shape_corr vm t' t ->
      rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') ->
      cross_bot (ptyp_mem t) ->
      cross_ih_pair t t' k u u' pre pre' (⇑ a1 e) (⇑ a2 e').
  Proof.
    induction t as [j Ps | B t IH]; intros [j' Ps' | B' t'] * Hsc H Hbot; cbn in Hsc; try contradiction.
    - destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (bs & bs' & Eb & Eb' & _ & _ & Hr).
      pose proof Hr as Hr0.
      inversion Hr0 as [| jx Mj hdx kx nsx nsx' as1 as2 ex ex' ux ux' HM Href Hn L1 L2 Hs1 Hs2 He]; subst.
      destruct (XE cross_neut_elim j' j Mj hdx kx as1 as2 e e' u u' bs bs' Hsc HM Hr
                  (Hbot j' Mj hdx kx as1 as2 e e' u u' bs bs' Hsc HM Hr)) as (r & r' & Er & Er' & HR).
      apply (mk_cross_ih_pair _ _ _ _ _ _ _ _ _ r r'); [ constructor; exact Er | constructor; exact Er' |].
      econstructor; [ exact Eb | exact Eb' | exact HR ].
    - apply (mk_cross_ih_pair _ _ _ _ _ _ _ _ _ (d_ihfn ρb VBb qc ub t' (⇑ a1 e)) (d_ihfn C1 Bks p u0 t (⇑ a2 e')));
        [ constructor | constructor |].
      constructor; intros c c' Hcc.
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H c c' Hcc) as (r & r' & Ea & Ea' & Hr).
      inversion Ea; subst; inversion Ea'; subst.
      destruct (IH t' _ _ _ _ _ _ _ _ _ Hsc Hr Hbot) as [ih ih' I1 I2 HI].
      econstructor; [ exact Ea | exact Ea' | econstructor; [ exact Ea | exact I1 ] | econstructor; [ exact Ea' | exact I2 ] | exact HI ].
  Qed.

  (** *** The Fresh Recursive Results

      A recursive argument both the group read and the two sides have: the
      fresh variables of the types of its recursive results, the
      container's by its shape [t'] under its motives, the group's by [t]
      under its own, related as recursive results. *)

  (** The types of the recursive results at the arguments [x] and [x'] of
      the shapes [t'] and [t], in [ρ1] and [ρ2]: the container's under its
      motives, the group's under its own, their fresh variables related as
      recursive results. *)
  #[warnings="-cannot-define-projection"]
  Record cross_ih_types (t t' : ptyp) (k : nat) (u u' pre pre' : list domain) (ρ1 ρ2 : env) (x x' : domain) : Prop :=
    mk_cross_ih_types
    { cit_container : domain
    ; cit_group : domain
    ; cit_container_eval : ⟦ihty x of t' under ρb (blocks_motives VBb) ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ cit_container
    ; cit_group_eval : ⟦ihty x' of t under C1 (blocks_motives Bks) ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ cit_group
    ; cit_related : forall e2 e2', Dom e2 ≈ e2' ∈ per_bot ->
        rec_result_rel dr Rel k u u' pre pre' t x x' (⇑ cit_container e2) (⇑ cit_group e2') }.

  Lemma cross_ih_fresh : forall t t' k u u' pre pre' ρ1 ρ2 a1 a2 e e', shape_corr vm t' t ->
      rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u u' pre pre' t (⇑ a1 e) (⇑ a2 e') ->
      shape_tops dr k pre t a1 a2 ->
      ⟦shty t' of qc ub ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ a1 -> ⟦shty t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ a2 ->
      (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t') = im_nn Mj /\ List.length (ptyp_ps t) = im_nn Mj) ->
      cross_ih_types t t' k u u' pre pre' ρ1 ρ2 (⇑ a1 e) (⇑ a2 e').
  Proof.
    destruct (vg_canon p D Hvg u0 u0_gargs' u0_len') as [CnP CnI CaP CaI CdP CdI].
    pose proof (nparams_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI) as tsym.
    induction t as [j Ps | B t IH]; intros [j' Ps' | B' t'] k u u' pre pre' ρ1 ρ2 a1 a2 e e' Hsc H Ht E1 E2 Hpl;
      cbn in Hsc; try contradiction.
    - inversion E1 as [Ps0 ρ0 bs1 j0 hd1 k1 pre1 ? ? Ebs1 Em1 |]; subst.
      inversion E2 as [Ps0 ρ0 bs2 j0 hd2 k2 pre2 ? ? Ebs2 Em2 |]; subst.
      destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (bs & bs' & Eb & Eb' & _ & _ & Hr).
      pose proof Hr as Hr0.
      inversion Hr0 as [| jx Mj hdx kx nsx nsx' as1 as2 ex ex' ux ux' HM Href Hn L1 L2 Hs1 Hs2 He]; subst.
      cbn in Hpl; destruct (Hpl _ HM) as [Hp1 Hp2].
      assert (Lb1 : List.length bs1 = im_nn Mj) by (rewrite (eval_exps_length _ _ _ Ebs1); exact Hp1).
      assert (Lb2 : List.length bs2 = im_nn Mj) by (rewrite (eval_exps_length _ _ _ Ebs2); exact Hp2).
      rewrite List.length_app in L1, L2.
      rewrite skipn_app_exact in Hs1 by lia; rewrite skipn_app_exact in Hs2 by lia.
      pose proof (ind_rel_idx p D u0 nr ar dr Hass CnP CnI CaP CaI CdP CdI _ _ _ _ _ _ _ _ _ _ _ HM Hr Hs1 Hs2) as Hm1.
      destruct (XE cross_member j' j Hsc) as (Mj' & Mj0 & HMj' & Hvmb).
      pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj0; rewrite HM in HMj0; injection HMj0 as <-.
      destruct (HbB _ _ HMj') as [bb Hbb]; destruct (HBks _ _ HM) as [ba Hba].
      destruct (Hmot_x j' Mj' j bb ba u u' bs1 bs2 _ _ HMj' Hsc Hbb Hba Hm1) as (h1 & h2 & Eh1 & Eh2 & HR).
      apply (mk_cross_ih_types _ _ _ _ _ _ _ _ _ _ _ h1 h2).
      + econstructor; [ exact Ebs1 | rewrite (nth_blocks_motives _ _ _ Hbb); exact Eh1 ].
      + econstructor; [ exact Ebs2 | rewrite (nth_blocks_motives _ _ _ Hba); exact Eh2 ].
      + intros e2 e2' He2; econstructor; [ exact Eb | exact Eb' |].
        apply (proj1 (XE self_motive_move j Mj u u' bs1 bs2 _ _ bs bs' HM Hm1 (tsym _ _ HM _ _ Hs1) (tsym _ _ HM _ _ Hs2) _ _)).
        exact (per_bot_then_per_elem HR He2).
    - inversion E1 as [| B0 ρ0 b1 t0 ? ? Eb1]; subst.
      inversion E2 as [| B0 ρ0 b2 t0 ? ? Eb2]; subst.
      inversion Ht as [| pre0 B0 t0 b0 ρ0 F0 b0' ρ0' F0' Htop Hnext]; subst.
      apply (mk_cross_ih_types _ _ _ _ _ _ _ _ _ _ _
               (Πᵈ b1 (nil ↦ d_ihfam ρb (blocks_motives VBb) ρ1 t' (⇑ (Πᵈ b1 (nil ↦ d_shfam qc ub ρ1 t') fam_cod) e)) fam_cod)
               (Πᵈ b2 (nil ↦ d_ihfam C1 (blocks_motives Bks) ρ2 t (⇑ (Πᵈ b2 (nil ↦ d_shfam p u0 ρ2 t) fam_cod) e')) fam_cod));
        [ econstructor; exact Eb1 | econstructor; exact Eb2 |].
      intros e2 e2' He2; constructor; intros c c' Hcc.
      destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H c c' Hcc) as (r & r' & Ea & Ea' & Hr).
      inversion Ea; subst.
      match goal with Ex0 : ⟦ fam_cod ⟧ _ ⍮ _ ⍮ _ ↦ c ↘ _ |- _ => rename Ex0 into Ex end.
      inversion Ea'; subst.
      match goal with Ex0 : ⟦ fam_cod ⟧ _ ⍮ _ ⍮ _ ↦ c' ↘ _ |- _ => rename Ex0 into Ex' end.
      pose proof (fam_cod_shfam_inv _ _ _ _ _ _ Ex) as Sx.
      pose proof (fam_cod_shfam_inv _ _ _ _ _ _ Ex') as Sx'.
      cbn in Hpl.
      destruct (IH t' _ _ _ _ _ _ _ _ _ _ _ Hsc Hr (Hnext _ _ _ _ Hcc Ex Ex') Sx Sx' Hpl) as [h1 h2 I1 I2 HI].
      econstructor; [ exact Ea | exact Ea'
                    | eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ea | exact I1 ]
                    | eapply eval_app_neut, eval_fam_cod_ihfam; [ exact Ea' | exact I2 ] |].
      apply HI, per_bot_app; [ exact He2 | exact (Htop _ _ Hcc) ].
  Qed.
End CrossBot.

End Fixed_GCtx.
