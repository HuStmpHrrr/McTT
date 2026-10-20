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

(** ** The Type of the End of a Shape

    The type of a member at uniform arguments and non-uniform ones: its
    head's type former at the values of the arguments. *)
Lemma apps_ind_val : forall (qn : qname) (kn : nat) ys xs r,
    $*| d_ind qn kn xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_ind qn kn (xs ++ ys).
Proof.
  induction ys as [| y ys IH]; intros xs r H; inversion H; subst; [ rewrite List.app_nil_r; reflexivity |].
  match goal with Ha : $| d_ind _ _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion Ha; subst end.
  match goal with Hr : $*| d_ind _ _ (xs ++ y :: nil) & ys | _ ⍮ _ ↘ _ |- _ => rewrite (IH _ _ Hr), <- List.app_assoc; reflexivity end.
Qed.

Lemma eval_mty_inv : forall (pq : qname) D j Mj Us Ns ρ a, ind_member D j = Some Mj ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ a ->
    exists cs bs, ⟦ im_pre Mj Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ cs /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs /\
      a = d_ind (fst (im_ref pq j Mj)) (snd (im_ref pq j Mj)) (cs ++ bs).
Proof.
  intros * HM Ea; unfold ind_mty, im_ty_at in Ea; rewrite HM in Ea.
  apply eval_apps_exp in Ea as (f & ls & Ef & Els & Eap).
  inversion Ef; subst.
  apply eval_exps_app_inv in Els as (cs & bs & -> & Ecs & Ebs).
  exists cs, bs; split; [ exact Ecs | split; [ exact Ebs |] ].
  exact (apps_ind_val _ _ _ _ _ Eap).
Qed.

Section ShapeChar.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.

  (** At a declared member there is no view to cohere. *)
  Lemma view_end_rel_decl : forall ups ups' j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      view_end_rel p D ups ups' j.
  Proof.
    intros * HM Hh Mj' qc kc Is vm Dq cups cups' HM' Hh'.
    rewrite HM in HM'; injection HM' as <-; rewrite Hh in Hh'; discriminate.
  Qed.

  (** The type of the member [j] at the group's uniform parameters as
      variables, after more variables [zs] related to themselves, and at
      non-uniform arguments of values [bs]: its relation is the group's at
      [j], at a view by [view_end_rel]. *)
  Lemma mty_end_rel : forall j Mj ups Z RZ zs nn L Ns bs a i R, ind_member D j = Some Mj ->
      List.length ups = ind_nu D -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
      ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
      List.length zs = List.length Z -> L + nn = List.length zs ->
      RZ (env_args nil (ups ++ zs)) (env_args nil (ups ++ zs)) ->
      ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ zs) ↘ bs ->
      ⟦ ind_mty p D j (ind_uvars D nn L) Ns ⟧ env_args nil (ups ++ zs) ↘ a ->
      DF a ≈ a ∈ per_univ_elem i ↘ R -> view_end_rel p D ups ups j ->
      (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) j ups ups bs bs).
  Proof.
    intros * HMj Hu Hgu HZ HRZ Hlz HL HE Ebs Ea HR Hend.
    destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj Ea) as (cs & bs' & Ecs & Ebs' & ->).
    pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
    unfold im_pre, im_ref in *; destruct (im_head Mj) as [pm | qc kc Is vm] eqn:Hh; cbn [fst snd] in *.
    - assert (HU : ⟦ ind_uvars D nn L ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ zs) ↘ ups)
        by (unfold ind_uvars; rewrite HL, <- Hu; apply eval_vars_from_args).
      pose proof (functional_eval_exps' _ _ _ _ Ecs HU) as ->.
      exact (proj1 (vg_type_rel_base p D Hg j Mj pm ups ups ups ups bs bs i R HMj Hh Hgu Hu Hgu Hgu HR)).
    - destruct (dt_view _ _ _ (vgr_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & _).
      assert (HIs : List.map (fun I => I[sb_of_list Id (ind_uvars D nn L)]) Is = List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is).
      { pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ HMj Hh) as Hs.
        pose proof (proj1 (proj2 (dmv_members _ (dt_mvc _ _ _ (vgr_typed _ _ Hg)) _ _ HMj))) as Hm.
        rewrite Hh in Hm; cbn in Hm.
        apply List.map_ext_in; intros I HI; unfold ind_uvars.
        rewrite (exp_at_vars _ _ _ (proj1 (List.Forall_forall _ _) Hs I HI) (proj1 (List.Forall_forall _ _) Hm I HI)), HL, Hlz.
        reflexivity. }
      rewrite HIs in Ecs.
      rewrite env_args_app in HE.
      destruct (vg_view_args_wk p D Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq Z RZ ups zs HZ HRZ Hlz Hu Hgu HE)
        as (cups & cs0 & Ecups & Ecs0 & Hgc).
      rewrite <- env_args_app in Ecs0.
      pose proof (functional_eval_exps' _ _ _ _ Ecs0 Ecs) as ->.
      exact (Hend _ _ _ _ _ _ _ _ HMj Hh Hq Ecups Ecups cs cs bs bs i R Hgc Hgc HR).
  Qed.

  Section ShapeMember.
    Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
    Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
    Hypothesis (HΨ : ⊨ cargs_ctx p D Mk gs ++ im_params D Mk).

    (** ** A Recursive Argument of a Function Shape

        After [kk] domains [ys] of a recursive argument's shape, related to
        themselves canonically, the relation of the type of the rest of the
        shape is the shape's relation ([rec_arg_rel]) of its rest, given the
        relation of the type of the member the shape ends in
        ([view_end_rel], nothing at a declared member). *)
    Lemma shape_char : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall ups ns fa, List.length ups = ind_nu D -> List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
        tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
        (forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
           R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
        view_end_rel p D ups ups (ptyp_mem t) ->
        forall n kk ys a i R, kk + n = List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (canon_doms_rel ups k) ns (nonrec_arg_vals gs1 fa) (ptyp_doms t)) kk ys ys ->
          per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
            (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
          ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          (R <~> rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
                   k ups ups (ns ++ nonrec_arg_vals gs1 fa ++ ys) (ns ++ nonrec_arg_vals gs1 fa ++ ys) (ptyp_skip kk t)).
    Proof.
      intros gs1 t gs2 Heq ups ns fa Hlu Hlns Hlk Hgu0 Hnsd INV Hpre Hend.
      destruct (vg_canon p D Hg ups Hgu0 Hlu) as [CnP CnI CaP CaI CdP CdI].
      pose proof (vg_adm p D Hg ups ups Hgu0 Hlu Hgu0) as Cad.
      destruct (sort_value D HD ups Hgu0 Hlu) as [a0 Ha0].
      destruct (ind_rel_pre_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups Cad Cad) as (_ & _ & Hprer & _).
      set (nv := nonrec_arg_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (pat := cargs_pat gs1) in *.
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlk).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (HwkE : forall ys, ⟪wk_pat (List.repeat false (List.length ys) ++ pat)⟫ (env_args nil (ups ++ ns ++ fa ++ ys))
                                = env_args nil (ups ++ ns ++ nv ++ ys)).
      { intros ys.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite env_args_app, eval_wk_pat_falses by reflexivity.
        unfold pat; replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite env_args_app, eval_wk_pat_args by exact Hlk.
        rewrite <- !env_args_app, <- !List.app_assoc; reflexivity. }
      (** The arguments before, as arguments of their telescope. *)
      assert (Hgpf : per_gargs (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
      { pose proof (cargs_prefix_sem D p Mk gs HΨ gs1 (ca_rec t :: gs2) Heq) as HC.
        destruct (rel_ctx_wf_per_ctx_env HC) as [R0 HR0].
        assert (HC' : ⊨ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅)
          by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
        assert (HR0' : EF List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅
                         ≈ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅ ∈ per_ctx_env ↘ R0)
          by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
        assert (Hl0 : List.length (ups ++ ns ++ fa) = List.length (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)))
          by (rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx, length_im_params; unfold im_np; lia).
        assert (Hta : tele_ass (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)))
          by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HM) ]).
        exact (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (Hpre _ HR0))). }
      (** The environment of the arguments and [kk] domains, in the context
          of their types. *)
      assert (Henv : forall kk ys, kk <= List.length (ptyp_doms t) -> List.length ys = kk ->
                 per_gargs (List.rev (sh_ctx pat (List.firstn kk (ptyp_doms t)))) (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
                 forall R0, EF sh_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
                              ≈ sh_ctx pat (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R0 ->
                   R0 (env_args nil (ups ++ ns ++ fa ++ ys)) (env_args nil (ups ++ ns ++ fa ++ ys))).
      { intros kk ys Hk Hly Hgy R0 HR0.
        apply (gargs_env_rel _ _ _ _ _ _ HR0 (sh_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk Hk)).
        - rewrite !List.length_app, length_sh_ctx, List.length_firstn, length_cargs_ctx, length_im_params; unfold im_np; lia.
        - rewrite List.rev_app_distr.
          replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
          apply per_gargs_app_intro;
            [ rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx, length_im_params; unfold im_np; lia
            | exact Hgpf |].
          exact Hgy. }
      induction n as [| n IH]; intros kk ys a i R Hkn Hy Hgy Ea HR.
      2: { (** A domain: related arguments of it give related results. *)
           assert (Hk : kk < List.length (ptyp_doms t)) by lia.
           destruct (ptyp_skip_lt kk t Hk) as (B & HB & Hs).
           rewrite Hs in Ea |- *.
           set (t' := ptyp_skip (S kk) t) in *.
           set (pat' := List.repeat false kk ++ pat) in *.
           cbn [ptyp_ty] in Ea.
           inversion Ea; subst a.
           basic_invert_per_univ_elem HR.
           rename H3 into Eb, H1 into HE, H0 into Hcod, H into HPin.
           pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
           pose proof (sh_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia)) as Hw; fold pat in Hw.
           destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
           rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
           destruct (rel_exp_under_ctx_wk_simple Hw HBv) as (RΓ & HΓ & i0 & Hwk).
           pose proof (Henv kk ys ltac:(lia) Hly Hgy RΓ HΓ) as Hρ.
           destruct (Hwk _ _ Hρ) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
           assert (Hy1 : y = d_univ j) by (cbn in Ey; inversion Ey; reflexivity).
           rewrite Hy1 in HRy; clear Hy1 Ey Ey'.
           destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
           apply ERy in Hmm; destruct Hmm as [Rm HRm].
           assert (m = a1) as -> by (eapply functional_eval_exp; eassumption).
           rewrite <- Hly, HwkE in Em'.
           assert (Ein : in_rel <~> Rm) by (eapply per_univ_elem_right_irrel; [ exact equiv_a_a' | exact HRm ]).
           pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRm) HRm) as HRm'.
           (** The domain's relation is the one of its type, weakened. *)
           assert (Edr : canon_doms_rel ups k (ns ++ nv ++ ys) B <~> in_rel).
           { unfold canon_doms_rel.
             pose proof (per_head_iff Em' Em' HRm') as Q.
             intros u v; split; intro Huv.
             - apply Ein; apply Q in Huv; exact Huv.
             - apply Q; apply Ein; exact Huv. }
           assert (HdrP : PER (canon_doms_rel ups k (ns ++ nv ++ ys) B)).
           { split; intros u v; [ intro Huv | intros w Huv Hvw ]; apply Edr; apply Edr in Huv;
               [ symmetry; exact Huv | apply Edr in Hvw; etransitivity; eassumption ]. }
           (** The codomain at related arguments, by the induction. *)
           assert (Hcodr : forall c0 c0' (Hin : in_rel c0 c0'), exists a2,
                      ⟦ ptyp_ty p D (im_nn Mk) (false :: pat') t' ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↦ c0 ↘ a2 /\
                      (out_rel c0 c0' Hin <~> rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups))
                                                (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) k ups ups
                                                ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c0 :: nil) t')).
           { intros c0 c0' Hin.
             assert (Hin0 : in_rel c0 c0) by (etransitivity; [ exact Hin | symmetry; exact Hin ]).
             destruct (Hcod _ _ Hin) as [a2 a2' Ea2 Ea2' HR2].
             pose proof (per_univ_trans _ _ _ _ _ _ HR2 (per_univ_sym _ _ _ _ HR2)) as HR2d.
             exists a2; split; [ exact Ea2 |].
             replace ((ns ++ nv ++ ys) ++ c0 :: nil) with (ns ++ nv ++ (ys ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
             change t' with (ptyp_skip (S kk) t).
             eapply (IH (S kk) (ys ++ c0 :: nil) a2 i (out_rel _ _ Hin)); [ lia | | | | exact HR2d ].
             + apply tele_prefix_rel_snoc; [ exact Hy |].
               unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB).
               apply Edr; exact Hin0.
             + rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
               cbn [List.rev].
               pose proof (per_univ_trans _ _ _ _ _ _ HRm (per_univ_sym _ _ _ _ HRm)) as HRmd.
               change (per_univ_elem j Rm a1 a1) in HRmd.
               apply (per_gargs_snoc _ _ _ _ _ _ _ _ j Rm);
                 [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgy | | apply Ein; exact Hin0 ].
               rewrite <- !env_args_app, <- !List.app_assoc.
               exact (mk_rel_mod_eval a1 a1 Eb Eb HRmd).
             + cbn [List.repeat List.app].
               replace (ups ++ ns ++ fa ++ ys ++ c0 :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c0 :: nil) by (rewrite <- !List.app_assoc; reflexivity).
               rewrite env_args_snoc; exact Ea2. }
           (** The type's relation is the shape's at its own argument on both
               sides; the shape's at the right argument is that one, moved
               along the domain ([ind_rel_pre_r]). *)
           assert (Hmv : forall c0 c1 c2 r r', canon_doms_rel ups k (ns ++ nv ++ ys) B c0 c1 -> canon_doms_rel ups k (ns ++ nv ++ ys) B c1 c2 ->
                      rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
                        k ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c1 :: nil) t' r r' ->
                      rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
                        k ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c2 :: nil) t' r r').
           { intros c0 c1 c2 r r' H01 H12 Hs0.
             assert (H00 : canon_doms_rel ups k (ns ++ nv ++ ys) B c0 c0) by (etransitivity; [ exact H01 | symmetry; exact H01 ]).
             rewrite <- !List.app_assoc in Hs0 |- *.
             eapply (Hprer _ _ _ _ _ _ _ _ Hs0 Mk ns ns ns c gs1 t gs2 nv nv nv (S kk)
                       (ys ++ c0 :: nil) (ys ++ c1 :: nil) (ys ++ c2 :: nil));
               [ reflexivity | exact HM | reflexivity | reflexivity | exact Hnsd | exact Hnsd | rewrite <- Heq; exact Hcon
               | exact INV | exact INV | reflexivity | lia | | ];
               (apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); assumption ]). }
           intros x x'; split; intro Hx.
           - constructor; intros c0 c0' Hcc.
             pose proof (proj1 (Edr _ _) Hcc) as Hin.
             pose proof (proj1 (HE x x') Hx) as Hx2; cbn beta in Hx2.
             destruct (Hx2 _ _ Hin) as [r r' Er Er' Hrr].
             destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
             assert (H00 : canon_doms_rel ups k (ns ++ nv ++ ys) B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
             econstructor; [ exact Er | exact Er' | exact (Hmv _ _ _ _ _ H00 Hcc (proj1 (Ecod _ _) Hrr)) ].
           - apply HE; intros c0 c0' Hin.
             pose proof (proj2 (Edr _ _) Hin) as Hcc.
             destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx _ _ Hcc) as (r & r' & Er & Er' & Hrr).
             destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
             assert (Hc'c : canon_doms_rel ups k (ns ++ nv ++ ys) B c0' c0) by (symmetry; exact Hcc).
             econstructor; [ exact Er | exact Er' | apply Ecod; exact (Hmv _ _ _ _ _ Hcc Hc'c Hrr) ]. }
      (** The end of the shape: an element of the member it ends in, at the
          parameters it evaluates to. *)
      assert (Hkd : kk = List.length (ptyp_doms t)) by lia.
      subst kk.
      rewrite (ptyp_skip_end t) in Ea |- *.
      cbn [ptyp_ty] in Ea.
      set (L := List.length (ptyp_doms t)) in *.
      pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
      destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
      pose proof (rec_prefix_gargs D HD Hc Hsu k Mk HM c gs gs1 t gs2 ups ups a0 ns ns nv nv ys ys Hcon Heq Hgu0 Hlu Ha0 Hnsd INV L (le_n _) Hy)
        as Hgall.
      assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
      rewrite Hft in Hgall.
      destruct (rec_closure D HD Hc k Mk HM c gs gs1 t gs2 Mj Hcon Heq HMj ups ups ns ns nv nv ys ys
                  Hlu Hlns Hlnv Hly Hlu Hlns Hlnv Hly Hgall)
        as (bs & bs0 & Ebs & _ & _ & Hil).
      set (pat' := List.repeat false L ++ pat) in *.
      pose proof (sh_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as Hw; fold pat pat' in Hw.
      rewrite Hft in Hw.
      assert (HTex : forall m, m < im_nn Mj ->
                 exists Tm, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) m = Some Tm).
      { intros m Hm; apply nth_error_lt_some'.
        rewrite length_tele_insts by exact (member_nparams_ass D Hc _ _ HMj); rewrite length_im_nparams; lia. }
      assert (Hlink : forall m P Tm, List.nth_error (ptyp_ps t) m = Some P ->
                 List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) m = Some Tm ->
                 exists b1 b, ⟦ P[wk_pat pat']ʷ ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ b1 /\ ⟦ P ⟧ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b /\
                   canon_nparams_rel D ups (ptyp_mem t) m (List.firstn m bs) b b1).
      { intros * HP HTm.
        pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HTm) as HPv.
        rewrite Heq, <- nonrec_args_prefix_cargs_strat in HPv.
        destruct (rel_exp_under_ctx_wk_simple Hw HPv) as (RΓ' & HΓ' & i1 & Hwk).
        pose proof (Henv L ys (le_n _) Hly Hgy RΓ') as Hρ.
        rewrite Hft in Hρ; specialize (Hρ HΓ').
        destruct (Hwk _ _ Hρ) as (u & u' & Ru & Eu & Eu' & HRu & b1 & b & Eb1 & Eb & Hbb).
        unfold pat' in Eu', Eb; rewrite <- Hly, HwkE in Eu', Eb.
        pose proof (Hil _ _ _ HP HTm) as Hcan.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        pose proof (per_head_iff Eu' Eu' HRuu) as Rel.
        assert (HPu : PER Ru) by (eapply per_elem_PER; exact HRu).
        exists b1, b; split; [ exact Eb1 | split; [ exact Eb | apply Hcan, Rel; symmetry; exact Hbb ] ]. }
      destruct (eval_exps_each (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t)) (env_args nil (ups ++ ns ++ fa ++ ys))) as [bs1 Ebs1].
      { intros m M HMm; rewrite List.nth_error_map in HMm.
        destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; cbn in HMm; [ injection HMm as <- | discriminate ].
        assert (Hm : m < im_nn Mj) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
        destruct (HTex _ Hm) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
      assert (Htf : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs bs1).
      { rewrite tele_rel_iff, List.length_rev, length_im_nparams.
        rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ Ebs1), List.length_map.
        split; [ exact HlPs | split; [ exact HlPs |] ].
        intros j y y' Hy1 Hy1'.
        assert (Hj : j < im_nn Mj) by (rewrite <- HlPs, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
        destruct (nth_error_lt_some' (ptyp_ps t) j ltac:(lia)) as [P HP].
        destruct (HTex _ Hj) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & b & Eb1 & Eb & Hr).
        destruct (eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
        destruct (eval_exps_nth _ _ _ _ _ Ebs1 ltac:(rewrite List.nth_error_map, HP; reflexivity)) as (b2 & Hb2 & Eb2).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
        rewrite Hy1 in Hb0; injection Hb0 as ->; rewrite Hy1' in Hb2; injection Hb2 as ->; exact Hr. }
      (** The relation of the end's type. *)
      assert (HZ : ⊨ (sh_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D).
      { pose proof (sh_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as H.
        rewrite Hft in H; unfold im_params in H; rewrite <- !List.app_assoc; exact H. }
      destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
      assert (HE : RZ (env_args nil (ups ++ ns ++ fa ++ ys)) (env_args nil (ups ++ ns ++ fa ++ ys))).
      { apply (Henv L ys (le_n _) Hly Hgy); rewrite Hft; unfold im_params; rewrite !List.app_assoc.
        rewrite !List.app_assoc in HRZ; exact HRZ. }
      assert (ERk : R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) (ptyp_mem t) ups ups bs1 bs1).
      { eapply (mty_end_rel (ptyp_mem t) Mj ups _ RZ (ns ++ fa ++ ys) (im_nn Mk) (List.length pat')); try eassumption.
        - rewrite !List.length_app, length_sh_ctx, length_cargs_ctx, length_im_nparams; lia.
        - unfold pat'; rewrite !List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat; lia. }
      pose proof (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMj _ _ Htf) as Hbb.
      pose proof (nparams_rel_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMj _ _ Htf) as Hb1b.
      assert (Hok : okr_at D ups (canon_nparams_rel D ups) (ptyp_mem t) (ns ++ nv ++ ys) (ptyp_ps t) bs).
      { exists bs; [ exact Ebs |]; unfold ntele_rel; rewrite HMj; exact Hbb. }
      intros x x'; split; intro Hx.
      - econstructor; [ exact Ebs | exact Ebs | exact Hok | exact Hok |].
        exact (ind_rel_idx p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ _ _ _ _ _ _ _ _ _ HMj (proj1 (ERk _ _) Hx) Hb1b Hb1b).
      - destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx) as (b1 & b2 & E1 & E2 & _ & _ & Hr).
        pose proof (functional_eval_exps' _ _ _ _ E1 Ebs) as ->.
        pose proof (functional_eval_exps' _ _ _ _ E2 Ebs) as ->.
        apply ERk; exact (ind_rel_idx p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ _ _ _ _ _ _ _ _ _ HMj Hr Htf Htf).
    Qed.
  End ShapeMember.
End ShapeChar.

End Fixed_GCtx.
