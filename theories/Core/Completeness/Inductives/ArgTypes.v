(** * The Types of a Constructor's Arguments, in the PER Model

    The arguments of a constructor of a member of a group are typed over
    its parameters: a non-recursive one by a type over the non-recursive
    arguments before it, which [wk_pat] weakens past the recursive ones; a
    recursive one by the [Π] over its shape's domains of the member the
    shape ends in ([ptyp_ty]).  Given the context of the arguments
    semantically well formed, this file proves the weakenings valid
    ([cargs_wk], [sh_wk]) and characterizes the relation of a recursive
    argument's type: it is the shape's relation ([rec_arg_rel]) of the
    group's canonical model ([shape_char]).  At a shape that ends in a view,
    the type is the container's at the view's instance, whose relation is
    the group's at the view when the view's elements cohere
    ([view_type_rel]). *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type of a recursive argument: its end under the shape's
    domains. *)
Lemma ptyp_ty_ctx_pi : forall p D nn t pat,
    ptyp_ty p D nn pat t
    = ctx_pi (sh_ctx pat (ptyp_doms t))
        (ptyp_ty p D nn (List.repeat false (List.length (ptyp_doms t)) ++ pat) (pt_self (ptyp_mem t) (ptyp_ps t))).
Proof.
  intros p0 D0 nn; induction t as [j Ps | B t IH]; intros pat; [ reflexivity |].
  cbn [ptyp_ty ptyp_doms sh_ctx List.length ptyp_ps ptyp_mem].
  rewrite ctx_pi_app; cbn [ctx_pi].
  rewrite (IH (false :: pat)), repeat_false_cons; reflexivity.
Qed.

(** ** The Contexts of the Arguments and of the Domains *)

Section ArgsCtx.
  Variables (D : ind_decl) (p : qname) (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HD : valid_ind_decl D) (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Hypothesis (HΨ : ⊨ cargs_ctx p D Mk gs ++ im_params D Mk).

  Lemma cargs_prefix_sem : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; pose proof HΨ as H.
    rewrite Heq in H; unfold cargs_ctx in H; rewrite cargs_ctx_aux_app, <- List.app_assoc in H.
    exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  (** The weakening of a prefix of the arguments to its non-recursive
      ones. *)
  Lemma cargs_wk : forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ im_params D Mk.
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (rel_ctx_wf_per_ctx_env (vid_params _ HD _ _ HM)) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (vid_arg _ HD _ _ _ _ _ _ HM Hcon HA) as (_ & j & HAv).
        rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
        exact (rel_wk_under_ctx_q IHw HAv).
      + rewrite cargs_strat_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
  Qed.

  (** The weakening of the context of a recursive argument's domains to
      that of their types, from the one of the arguments before it. *)
  Lemma sh_wk : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊨ʷ (wk_pat (List.repeat false j ++ cargs_pat gs1))
          : doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_strat gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; induction j as [| j IH]; intros Hj.
    - exact (cargs_wk _ _ Heq).
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, doms_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.repeat List.app wk_pat].
      destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      exact (rel_wk_under_ctx_q (IH ltac:(lia)) HBv).
  Qed.

  Lemma sh_sem : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        ⊨ sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq; induction j as [| j IH]; intros Hj.
    - exact (cargs_prefix_sem _ _ Heq).
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      pose proof (sh_wk _ _ _ Heq j ltac:(lia)) as Hw.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      exact (rel_ctx_wf_ext_typ _ _ _ (IH ltac:(lia)) HBw).
  Qed.
End ArgsCtx.

(** ** The Canonical Model of a Valid Group *)

Section GroupFacts.
  Variables (p : qname) (D : ind_decl).
  Hypothesis (Hg : valid_group p D).
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hl := vgr_lookup _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.

  Lemma vg_canon : forall ups, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      ind_canon_props D ups.
  Proof.
    intros ups Hgd Hu; destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    exact (canon_props_at D HD Hc Hsu ups a Hgd Hu Ha Hass).
  Qed.

  Lemma vg_adm : forall ups ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
      adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups2.
  Proof.
    intros ups ups2 Hgd Hu Hg2; destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    exact (canon_adm_at D HD Hc Hsu ups a Hu Ha ups2 Hg2).
  Qed.

  Lemma vg_relate : forall k Mk pm ups ups' ns ns', ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns' ->
      exists i, DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i
        ↘ grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) k ups ups' ns ns'.
  Proof.
    intros * HM Hh Hgu Hu Hns.
    destruct (sort_value D HD ups (uparams_refl_l D HD Hc _ _ Hgu) Hu) as [a Ha].
    exists (univ_idx a); exact (ind_relate D HD Hc Hsu p Hl Hass k Mk pm ups ups' ns ns' a HM Hh Hgu Hu Ha Hns).
  Qed.

  (** A declared member at uniform parameters related to [cups] and
      [cups']: its relation is the canonical one at [cups] and [cups'],
      whatever the related bases. *)
  Lemma vg_type_rel_base : forall k Mk pm cups cups' cs cs' ns ns' i R, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_gargs (List.rev (ind_uparams D)) nil nil cups cups' -> List.length cups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil cups cs -> per_gargs (List.rev (ind_uparams D)) nil nil cups' cs' ->
      DF d_ind p k (cs ++ ns) ≈ d_ind p k (cs' ++ ns') ∈ per_univ_elem i ↘ R ->
      (R <~> grp_rel p D cups (canon_nparams_rel D cups) (canon_args_rel D cups) (canon_doms_rel cups) k cups cups' ns ns') /\
      tele_rel (canon_nparams_rel D cups k) (List.rev (im_nparams Mk)) ns ns'.
  Proof.
    intros * HM Hh Hgu Hu Hcs Hcs' HR.
    pose proof (length_ups_gargs D _ _ Hgu Hu) as Hu'.
    pose proof (length_ups_gargs D _ _ Hcs Hu) as Hlc.
    pose proof (length_ups_gargs D _ _ Hcs' Hu') as Hlc'.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR Hl Hlc Hlc') as [_ _ Hcp _ _ _ Hns _].
    unfold member_nparams in Hns; rewrite HM in Hns.
    pose proof (uparams_sym D HD Hc _ _ Hcs Hu) as Hcsc.
    pose proof (canon_nparams_rel_refl_l' p D cs Hass Hcp k Mk ns ns' HM Hns) as Hnsns.
    destruct (vg_relate k Mk pm cs cups ns ns HM Hh Hcsc Hlc Hnsns) as [i1 W1].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ W1 Hl Hlc Hu) as [_ _ _ [Hn0 Ha0 Hd0] _ _ _ _].
    pose proof (tele_rel_nr_change p D cs _ _ _ _ _ _ Hn0 Ha0 Hd0 k Mk HM ns ns' Hns) as Hns2.
    destruct (vg_relate k Mk pm cups cups' ns ns' HM Hh Hgu Hu Hns2) as [i2 T].
    split; [| exact Hns2 ].
    etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR | exact W1 ] |].
    eapply per_univ_elem_right_irrel; [ exact (per_univ_sym _ _ _ _ W1) | exact T ].
  Qed.
End GroupFacts.

(** ** Coherence of a View, and the Relation of its Type

    [view_coh_at p D ups ups' j]: the elements of the view [j] of [D] at
    the canonical relations at [ups] and [ups'] cohere with those of its
    container's member at the view's instance there ([view_coh_ok]).
    [view_end_rel]: the relation of the view's type, the container's at
    any uniform parameters related to the instance, is the group's at the
    view. *)
Definition view_coh_at (p : qname) (D : ind_decl) (ups ups' : list domain) (j : nat) : Prop :=
  forall Mj qc kc Is vm Dq cups cups', ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups' ↘ cups' ->
    view_coh_ok p D ups ups' (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
      qc Dq cups cups' (canon_nparams_rel Dq cups) (canon_args_rel Dq cups) (canon_doms_rel cups) vm.

Definition view_end_rel (p : qname) (D : ind_decl) (ups ups' : list domain) (j : nat) : Prop :=
  forall Mj qc kc Is vm Dq cups cups', ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups' ↘ cups' ->
    forall cs cs' ns ns' (i : uidx) R,
      per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs -> per_gargs (List.rev (ind_uparams Dq)) nil nil cups' cs' ->
      DF d_ind qc kc (cs ++ ns) ≈ d_ind qc kc (cs' ++ ns') ∈ per_univ_elem i ↘ R ->
      (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) j ups ups' ns ns').

Lemma view_end_rel_of_coh : forall p D, valid_group p D -> containers_valid D ->
    forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall j, view_coh_at p D ups ups' j -> view_end_rel p D ups ups' j.
Proof.
  intros p D Hg Hcv ups ups' Hgu Hu j Hcoh Mj qc kc Is vm Dq cups cups' HMj Hh Hq Ec Ec' cs cs' ns ns' i R Hcs Hcs' HR.
  pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
  pose proof (vgr_typed _ _ Hg) as Hdt.
  destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (D2 & Mk' & Hl2 & HMk' & Hkd & HIl & _ & Hvm & _).
  rewrite Hq in Hl2; injection Hl2 as <-.
  assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
  { pose proof (proj2 (dt_order _ _ _ (vgr_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
    unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate ]. }
  destruct Hhd as [pm Hhd].
  destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hcu).
  pose proof (functional_eval_exps' _ _ _ _ E0 Ec) as <-; pose proof (functional_eval_exps' _ _ _ _ E0' Ec') as <-.
  assert (Hlc : List.length c0 = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ E0); exact HIl).
  destruct (vg_type_rel_base qc Dq HgQ _ _ _ _ _ _ _ _ _ _ _ HMk' Hhd Hcu Hlc Hcs Hcs' HR) as [Hbase _].
  pose proof (Hcoh _ _ _ _ _ _ _ _ HMj Hh Hq E0 E0') as Hvc.
  destruct (vco_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc _ _ HMk') as (v & Mv & Hvmb).
  assert (v = j) as -> by (pose proof (vmb_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mj) as -> by (pose proof (vmb_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HMj in HMv; congruence).
  pose proof (vg_canon p D Hg ups (uparams_refl_l D (vgr_valid _ _ Hg) (vgr_closed _ _ Hg) _ _ Hgu) Hu) as Hcp.
  pose proof (vg_canon qc Dq HgQ c0 (uparams_refl_l Dq (vgr_valid _ _ HgQ) (vgr_closed _ _ HgQ) _ _ Hcu) Hlc) as HcpQ.
  destruct Hcp as [HnP HnI HaP HaI HdP HdI]; destruct HcpQ as [HnP' HnI' HaP' HaI' HdP' HdI'].
  intros x y; split; intro Hxy.
  - apply Hbase in Hxy.
    exact (view_coh_to p D ups ups' _ _ _ (vgr_ass _ _ Hg) HnP HnI HaP HaI HdP HdI qc Dq c0 c0' _ _ _ (vgr_ass _ _ HgQ)
             HnP' HnI' HaP' HaI' HdP' HdI' vm Hvc kc Mk' j Mj ns ns' x y HMk' Hvmb Hxy).
  - apply Hbase.
    exact (view_coh_from p D ups ups' _ _ _ (vgr_ass _ _ Hg) HnP HnI HaP HaI HdP HdI qc Dq c0 c0' _ _ _ (vgr_ass _ _ HgQ)
             HnP' HnI' HaP' HaI' HdP' HdI' vm Hvc kc Mk' j Mj ns ns' x y HMk' Hvmb Hxy).
Qed.

End Fixed_GCtx.
