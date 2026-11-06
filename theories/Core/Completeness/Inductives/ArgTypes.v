(** * The Types of a Constructor's Arguments, in the PER Model

    The arguments of a constructor of a member of a group are typed over
    its parameters: a non-recursive one by a type over the non-recursive
    arguments before it, which [wk_pat] weakens past the recursive ones; a
    recursive one by the [Π] over its shape's domains of the member the
    shape ends in ([ptyp_ty]).  Given the context of the arguments
    semantically well formed, this file proves the weakenings valid
    ([cargs_wk], [shape_domains_ctx_wk]) and characterizes the relation of a recursive
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
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews.
From Mctt.Core.Semantic Require Import Realizability RecordPER.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
From Mctt.Core.Completeness.Records Require Model.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The type of a recursive argument: its end under the shape's
    domains. *)
Lemma ptyp_ty_ctx_pi : forall p D nn t pat,
    ptyp_ty p D nn pat t
    = ctx_pi (shape_domains_ctx pat (ptyp_doms t))
        (ptyp_ty p D nn (List.repeat false (List.length (ptyp_doms t)) ++ pat) (pt_self (ptyp_mem t) (ptyp_ps t))).
Proof.
  intros p0 D0 nn; induction t as [j Ps | B t IH]; intros pat; [ reflexivity |].
  cbn [ptyp_ty ptyp_doms shape_domains_ctx List.length ptyp_ps ptyp_mem].
  rewrite ctx_pi_app; cbn [ctx_pi].
  rewrite (IH (false :: pat)), repeat_false_cons; reflexivity.
Qed.

(** ** Semantically Equal Contexts

    Two semantically equal contexts have the same relation of
    environments, so the semantic judgments over one hold over the
    other. *)
Lemma per_ctx_env_eq_iff : forall Γ Γ' R R', ⊨ Γ ≈ Γ' -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * [Rx HRx] HR HR'.
  etransitivity; [ eapply per_ctx_env_right_irrel; [ exact HR | exact HRx ] |].
  destruct (per_ctx_env_sym _ _ _ HRx) as [HRx' _].
  eapply per_ctx_env_right_irrel; [ exact HRx' | exact HR' ].
Qed.

Lemma rel_chain_env_iff : forall (R R' : relation env) l, R <~> R' -> rel_chain R l -> rel_chain R' l.
Proof.
  intros R R' l E; induction l as [| a [| b l] IH]; cbn; [ tauto | tauto |].
  destruct l as [| c l]; [ apply E |].
  intros [Hab Hl]; split; [ apply E; exact Hab | exact (IH Hl) ].
Qed.

(** An evaluation of a substitution into one of two equal contexts is,
    retagged at the other, one into the other, at an environment of their
    relation: the two agree on which entries are propositions there. *)
#[local] Transparent eval_sub.
Lemma eval_sub_conv_tgt : forall Δ Δ' R σ ρ ρσ, EF Δ ≈ Δ' ∈ per_ctx_env ↘ R -> R ρσ ρσ ->
    ⟦ σ : Δ ⟧s ρ ↘ ρσ -> ⟦ σ : Δ' ⟧s ρ ↘ ctx_retag Δ' ρσ.
Proof.
  intros * HR Hρ Hσ; unfold eval_sub in *; intros x Hx.
  pose proof (per_ctx_env_length HR) as Hl.
  destruct (per_ctx_env_sym _ _ _ HR) as [HR' _].
  assert (HPR : PER R) by (eapply per_env_PER; exact HR).
  pose proof (per_ctx_env_retag_right HR' _ _ Hρ) as Hρr.
  rewrite (env_entry_ctx_retag Δ' ρσ x Hx).
  destruct (Hσ x ltac:(lia)) as [Hp Hn]; split.
  - intros Hp'; apply eval_sentry_proof_retag with (t := ctx_entry_tag Δ x ρσ) (U := ctx_entry_unit Δ x).
    apply Hp; exact (per_ctx_env_props_cross _ _ _ HR' _ _ (symmetry Hρr) _ Hp').
  - intros Hn'; apply eval_sentry_retag with (t := ctx_entry_tag Δ x ρσ) (U := ctx_entry_unit Δ x).
    apply Hn; intros Hp'; exact (Hn' (per_ctx_env_props_cross _ _ _ HR _ _ Hρr _ Hp')).
Qed.
#[local] Opaque eval_sub.

Lemma rel_sub_under_ctx_conv_tgt : forall Γ Δ Δ' R' σ σ', Γ ⊨ˢ σ ≈ σ' : Δ -> EF Δ' ≈ Δ' ∈ per_ctx_env ↘ R' -> ⊨ Δ ≈ Δ' ->
    Γ ⊨ˢ σ ≈ σ' : Δ'.
Proof.
  intros * [RΓ HRΓ Ro HRo Hb Hsc] HR' Heq.
  pose proof (per_ctx_env_eq_iff _ _ _ _ Heq HRo HR') as E.
  destruct Heq as [Rx HRx].
  pose proof (per_ctx_env_length HRx) as Hlx.
  assert (ERx : Ro <~> Rx) by (eapply per_ctx_env_right_irrel; [ exact HRo | exact HRx ]).
  assert (HPo : PER Ro) by (eapply per_env_PER; exact HRo).
  econstructor; [ exact HRΓ | exact HR' | | intros x Hx; apply Hsc; lia ].
  intros * HΓ'' φ Hw Hφ ρ ρ' Hρ.
  destruct (Hb _ _ HΓ'' φ Hw Hφ ρ ρ' Hρ) as [a b c d E1 E2 E3 E4 Hch].
  pose proof Hch as (Hab & Hbc & Hcd).
  (** Each of the four environments is related to itself. *)
  assert (Hself : forall e, Ro e e -> Rx e e) by (intros e He; apply ERx; exact He).
  (** Retagged at the second target, they evaluate into it and stay
      related. *)
  pose proof (rel_chain_env_iff _ _ _ E Hch) as (H'ab & H'bc & H'cd).
  econstructor;
    [ apply (eval_sub_conv_tgt _ _ _ _ _ _ HRx (Hself _ ltac:(etransitivity; [ exact Hab | symmetry; exact Hab ])) E1)
    | apply (eval_sub_conv_tgt _ _ _ _ _ _ HRx (Hself _ ltac:(etransitivity; [ symmetry; exact Hab | exact Hab ])) E2)
    | apply (eval_sub_conv_tgt _ _ _ _ _ _ HRx (Hself _ ltac:(etransitivity; [ exact Hcd | symmetry; exact Hcd ])) E3)
    | apply (eval_sub_conv_tgt _ _ _ _ _ _ HRx (Hself _ ltac:(etransitivity; [ symmetry; exact Hcd | exact Hcd ])) E4)
    | split; [| split ]; apply (per_ctx_env_retag HR'); assumption ].
Qed.

Lemma rel_sub_under_ctx_conv_src : forall Γ Γ' Δ σ σ', Γ ⊨ˢ σ ≈ σ' : Δ -> ⊨ Γ' -> ⊨ Γ ≈ Γ' -> Γ' ⊨ˢ σ ≈ σ' : Δ.
Proof.
  intros * [RΓ HRΓ Ro HRo Hb Hsc] HΓ' Heq.
  destruct (rel_ctx_wf_per_ctx_env HΓ') as [R' HR'].
  pose proof (per_ctx_env_eq_iff _ _ _ _ Heq HRΓ HR') as E.
  assert (Hlx : List.length Γ = List.length Γ') by (destruct Heq as [Rx HRx]; exact (per_ctx_env_length HRx)).
  econstructor; [ exact HR' | exact HRo | | intros x Hx; rewrite <- Hlx; exact (Hsc x Hx) ].
  intros * HΓ'' φ [Hm Hw] Hφ ρ ρ' Hρ.
  apply (Hb _ _ HΓ'' φ); [| intros x Hx; apply Hφ; lia | exact Hρ ].
  constructor; [ exact Hm |]; intros ? ? H; apply E, Hw, H.
Qed.

(** ** The Contexts of the Arguments and of the Domains *)

(** The kind of a non-recursive argument is its tag. *)
Lemma nonrec_kind_at : forall gs1 gs2 r A,
    List.nth_error (cargs_nonrec_kinds (gs1 ++ ca_arg r A :: gs2)) (List.length (cargs_nonrec gs1)) = Some r.
Proof. induction gs1 as [| [r0 B | Ps] gs1 IH]; intros; cbn; [ reflexivity | apply IH | apply IH ]. Qed.

Section ArgsCtx.
  Variables (D : ind_decl) (p : qname) (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HD : valid_ind_decl D) (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).

  (** The weakening of the context of a recursive argument's domains to
      that of their types, and the context, from those of the arguments
      before it. *)
  Lemma shape_domains_ctx_wk_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ->
      forall j, j <= List.length (ptyp_doms t) ->
        shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊨ʷ (wk_pat (List.repeat false j ++ cargs_pat gs1))
          : doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.
  Proof.
    intros * Heq Hw0; induction j as [| j IH]; intros Hj.
    - exact Hw0.
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, doms_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.repeat List.app wk_pat].
      destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
      exact (rel_wk_under_ctx_q (IH ltac:(lia)) (rel_type_of_typ HBv)).
  Qed.

  Lemma shape_domains_ctx_sem_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk ->
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ->
      forall j, j <= List.length (ptyp_doms t) ->
        ⊨ shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof.
    intros * Heq HC0 Hw0; induction j as [| j IH]; intros Hj.
    - exact HC0.
    - destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      pose proof (shape_domains_ctx_wk_gen _ _ _ Heq Hw0 j ltac:(lia)) as Hw.
      destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & i & HBv).
      rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
      pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
      rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      exact (rel_ctx_wf_ext_typ _ _ _ (IH ltac:(lia)) HBw).
  Qed.

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
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk.
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_nonrec_ctx cargs_pat List.rev List.map List.app].
      destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_params _ HD _ _ HM)) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R)
        | intros x Hx; cbn [wk_pat]; rewrite List.length_app; lia
        | intros ρ ρ' _ x _; cbn [wk_pat]; change (fun x0 : nat => x0) with wk_id; rewrite eval_wk_id; reflexivity ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [r A | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_nonrec_ctx_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
        destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as (_ & j & HAv).
        rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAv.
        exact (rel_wk_under_ctx_q IHw (rel_type_of_abs_kind_sort HAv)).
      + rewrite cargs_nonrec_ctx_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
  Qed.

  Lemma shape_domains_ctx_wk : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊨ʷ (wk_pat (List.repeat false j ++ cargs_pat gs1))
          : doms_ctx (List.firstn j (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk.
  Proof. intros * Heq; exact (shape_domains_ctx_wk_gen _ _ _ Heq (cargs_wk _ _ Heq)). Qed.

  Lemma shape_domains_ctx_sem : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall j, j <= List.length (ptyp_doms t) ->
        ⊨ shape_domains_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk.
  Proof. intros * Heq; exact (shape_domains_ctx_sem_gen _ _ _ Heq (cargs_prefix_sem _ _ Heq) (cargs_wk _ _ Heq)). Qed.
End ArgsCtx.

(** ** The Canonical Model of a Valid Group *)

Section GroupFacts.
  Variables (p : qname) (D : ind_decl).
  Hypothesis (Hg : valid_group p D).
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hl := valid_group_lookup _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.

  Lemma valid_group_canon : forall ups, per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      ind_canon_props D ups.
  Proof.
    intros ups Hgd Hu; destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    exact (canon_props_at D HD Hc Hsu ups a Hgd Hu Ha Hass).
  Qed.

  Lemma valid_group_adm : forall ups ups2, per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      per_tele_args (List.rev (ind_uparams D)) nil nil ups ups2 ->
      adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) ups2.
  Proof.
    intros ups ups2 Hgd Hu Hg2; destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    exact (canon_adm_at D HD Hc Hsu ups a Hu Ha ups2 Hg2).
  Qed.

  (** The domains of the shapes at related prefixes, at [ups] and at
      uniform parameters [ups2] related to it: their values related. *)
  Lemma valid_group_doms_related : forall ups ups2, per_tele_args (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      per_tele_args (List.rev (ind_uparams D)) nil nil ups ups2 -> exists u : universe_index, doms_related u D ups ups2.
  Proof.
    intros ups ups2 Hgd Hu Hg2; destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    exists (univ_idx a); exact (canon_hd D HD Hc Hsu ups a Hu Ha ups2 Hg2).
  Qed.

  Lemma valid_group_relate : forall k Mk pm ups ups' ns ns', ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_tele_args (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns' ->
      exists i, DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem i
        ↘ grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) k ups ups' ns ns'.
  Proof.
    intros * HM Hh Hgu Hu Hns.
    destruct (sort_value D HD ups (uparams_refl_l D HD Hc _ _ Hgu) Hu) as [a Ha].
    exists (univ_idx a); exact (ind_relate D HD Hc Hsu p Hl Hass k Mk pm ups ups' ns ns' a HM Hh Hgu Hu Ha Hns).
  Qed.

  (** A declared member at uniform parameters related to [cups] and
      [cups']: its relation is the canonical one at [cups] and [cups'],
      whatever the related bases. *)
  Lemma valid_group_type_rel_base : forall k Mk pm cups cups' cs cs' ns ns' i R, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_tele_args (List.rev (ind_uparams D)) nil nil cups cups' -> List.length cups = ind_nu D ->
      per_tele_args (List.rev (ind_uparams D)) nil nil cups cs -> per_tele_args (List.rev (ind_uparams D)) nil nil cups' cs' ->
      DF d_ind p k (cs ++ ns) ≈ d_ind p k (cs' ++ ns') ∈ per_univ_elem i ↘ R ->
      (R <~> grp_rel p D cups (canon_nparams_rel D cups) (canon_args_rel D cups) (canon_doms_rel D cups) k cups cups' ns ns') /\
      tele_rel (canon_nparams_rel D cups k) (List.rev (im_nparams Mk)) ns ns'.
  Proof.
    intros * HM Hh Hgu Hu Hcs Hcs' HR.
    pose proof (length_ups_tele_args D _ _ Hgu Hu) as Hu'.
    pose proof (length_ups_tele_args D _ _ Hcs Hu) as Hlc.
    pose proof (length_ups_tele_args D _ _ Hcs' Hu') as Hlc'.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HR Hl Hlc Hlc') as [_ _ Hcp _ _ _ Hns _].
    unfold member_nparams in Hns; rewrite HM in Hns.
    pose proof (uparams_sym D HD Hc _ _ Hcs Hu) as Hcsc.
    pose proof (canon_nparams_rel_refl_l' p D cs Hass Hcp k Mk ns ns' HM Hns) as Hnsns.
    destruct (valid_group_relate k Mk pm cs cups ns ns HM Hh Hcsc Hlc Hnsns) as [i1 W1].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ W1 Hl Hlc Hu) as [_ _ _ [Hn0 Ha0 Hd0] _ _ _ _].
    pose proof (tele_rel_nr_change p D cs _ _ _ _ _ _ Hn0 Ha0 Hd0 k Mk HM ns ns' Hns) as Hns2.
    destruct (valid_group_relate k Mk pm cups cups' ns ns' HM Hh Hgu Hu Hns2) as [i2 T].
    split; [| exact Hns2 ].
    etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR | exact W1 ] |].
    eapply per_univ_elem_right_irrel; [ exact (per_univ_sym _ _ _ _ W1) | exact T ].
  Qed.

  (** The canonical relation of a declared member's non-uniform
      parameters does not depend on which of two related uniform
      parameters it is read at. *)
  Lemma valid_group_nparams_base_change : forall k Mk pm cs xc a b, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_tele_args (List.rev (ind_uparams D)) nil nil cs xc -> List.length cs = ind_nu D ->
      tele_rel (canon_nparams_rel D cs k) (List.rev (im_nparams Mk)) a b ->
      tele_rel (canon_nparams_rel D xc k) (List.rev (im_nparams Mk)) a b.
  Proof.
    intros * HM Hh Hcx Hlc Hab.
    pose proof (length_ups_tele_args D _ _ Hcx Hlc) as Hlx.
    pose proof (valid_group_canon cs (uparams_refl_l D HD Hc _ _ Hcx) Hlc) as Hcp.
    pose proof (canon_nparams_rel_refl_l' p D cs Hass Hcp k Mk a b HM Hab) as Haa.
    destruct (valid_group_relate k Mk pm cs xc a a HM Hh Hcx Hlc Haa) as [i1 W1].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ W1 Hl Hlc Hlx) as [_ _ _ [Hn0 Ha0 Hd0] _ _ _ _].
    exact (tele_rel_nr_change p D cs _ _ _ _ _ _ Hn0 Ha0 Hd0 k Mk HM a b Hab).
  Qed.

  (** The canonical relations at two related uniform parameters agree, at
      every member. *)
  Lemma valid_group_fam_agree : forall ups ups2, per_tele_args (List.rev (ind_uparams D)) nil nil ups ups2 -> List.length ups = ind_nu D ->
      ind_fam_agree D (canon_nparams_rel D ups) (canon_nparams_rel D ups2) (canon_args_rel D ups) (canon_args_rel D ups2)
        (canon_doms_rel D ups) (canon_doms_rel D ups2).
  Proof.
    intros ups ups2 Hg2 Hu.
    pose proof (uparams_refl_l D HD Hc _ _ Hg2) as Hgd.
    destruct (sort_value D HD ups Hgd Hu) as [a Ha].
    destruct (valid_group_canon ups Hgd Hu) as [CnP CnI CaP CaI CdP CdI].
    constructor.
    - intros m Mm k vs vs1 vs2 HM Hk Hp _.
      destruct (nparams_lt_ass D m Mm k Hass HM Hk) as (κ & A & HA).
      pose proof (nparams_prefix_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM k vs vs1 ltac:(lia) Hp) as Hpp.
      destruct (canon_hn D HD Hc Hsu ups a Hu Ha ups2 Hg2 m Mm k κ A vs vs HM HA Hpp) as (b & b' & Eb & Eb' & [R HR] & _).
      unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ _ HM HA), (member_nparams_eq _ _ _ HM).
      etransitivity; [ symmetry; exact (per_head_left Eb Eb' HR) | exact (per_head_right Eb Eb' HR) ].
    - intros m Mm ms ms1 ms2 c gs k vs vs1 vs2 HM Hm _ Hcon Hk Hp _.
      destruct (nth_error_lt_some' _ _ Hk) as [A HA].
      pose proof (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM _ _ Hm) as Hmm.
      pose proof (args_rel_pre_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM ms c gs Hmm Hcon k vs vs1 ltac:(lia) Hp)
        as Hpp.
      destruct (canon_ha D HD Hc Hsu ups a Hu Ha ups2 Hg2 m Mm ms ms c gs k A vs vs HM Hmm Hcon HA Hpp) as (b & b' & Eb & Eb' & [R HR] & _).
      unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcon HA), (member_nparams_eq _ _ _ HM),
        (member_con_tele_eq _ _ _ _ _ HM Hcon).
      etransitivity; [ symmetry; exact (per_head_left Eb Eb' HR) | exact (per_head_right Eb Eb' HR) ].
    - intros m Mm ms ms1 ms2 c gs gs1 t gs2 ws ws1 ws2 k ys ys1 ys2 HM Hm _ Hcon Heq Hw _ Hk Hy _.
      destruct (nth_error_lt_some' _ _ Hk) as [B HB].
      pose proof (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM _ _ Hm) as Hmm.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (args_rel_pre_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM ms c gs Hmm Hcon _ ws ws1 HK Hw) as Hww.
      pose proof (doms_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI m Mm HM ms c gs gs1 t gs2 ws Hmm Hcon Heq Hww
                    k ys ys1 ltac:(lia) Hy) as Hyy.
      destruct (canon_hd D HD Hc Hsu ups a Hu Ha ups2 Hg2 m Mm ms ms c gs gs1 t gs2 ws ws k B ys ys HM Hmm Hcon Heq Hww HB Hyy)
        as (b & b' & Eb & Eb' & [[R HR] _ _]).
      unfold shape_doms_rel, canon_doms_rel; rewrite (List.nth_error_nth _ _ _ HB).
      (** The domain reads only as many components as there are values. *)
      pose proof Hmm as Hlm; rewrite tele_rel_iff in Hlm; destruct Hlm as (Hlm & _).
      pose proof Hww as Hlw; rewrite tele_prefix_rel_iff in Hlw; destruct Hlw as (Hlw & _).
      pose proof Hyy as Hly; rewrite tele_prefix_rel_iff in Hly; destruct Hly as (Hly & _).
      replace k with (List.length ys) by exact Hly.
      rewrite (List.app_assoc ms ws ys), (List.app_assoc (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1)).
      rewrite <- !components_env_app_firstn
        by (try (unfold shape_doms_tele; rewrite List.length_map; lia);
            rewrite !List.length_app, length_cargs_nonrec_tele; lia).
      rewrite <- (List.app_assoc ms ws ys), <- (List.app_assoc (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1)).
      etransitivity; [ symmetry; exact (per_head_left Eb Eb' HR) | exact (per_head_right Eb Eb' HR) ].
  Qed.

  (** A recursive argument at the canonical relations, its right side
      moved from the left base and prefix to related ones, and back
      ([ind_rel_base_r], [ind_rel_pre_r]). *)
  Lemma valid_group_rec_arg_move_right : forall k Mk c gs1 t gs2 ups ups' ms ms' ws ws' x y, ind_member D k = Some Mk ->
      ind_con Mk c = Some (gs1 ++ ca_rec t :: gs2) ->
      per_tele_args (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
      tele_prefix_rel (canon_args_rel D ups k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      (rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
         k ups ups (ms ++ ws) (ms ++ ws) (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t x y <->
       rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
         k ups ups' (ms ++ ws) (ms' ++ ws') (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) t x y).
  Proof.
    intros * HM Hcon Hgu Hu Hm Hw.
    pose proof (uparams_refl_l D HD Hc _ _ Hgu) as Hgd.
    destruct (valid_group_canon ups Hgd Hu) as [CnP CnI CaP CaI CdP CdI].
    pose proof (valid_group_adm ups ups Hgd Hu Hgd) as Add.
    pose proof (valid_group_adm ups ups' Hgd Hu Hgu) as Ad'.
    assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t :: gs2)))
      by (rewrite cargs_nonrec_app, List.length_app; lia).
    pose proof (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM _ _ Hm) as Hmm.
    pose proof (nparams_rel_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM _ _ Hm) as Hm'm.
    pose proof (args_rel_pre_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM ms c _ Hmm Hcon _ _ _ HK Hw) as Hww.
    assert (Hw'w : tele_prefix_rel (canon_args_rel D ups k ms' c) (List.length (cargs_nonrec gs1)) ws' ws).
    { pose proof (args_prefix_rel_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM ms c _ _ _ _ Hmm Hcon HK Hw) as H.
      exact (args_prefix_rel_inst p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM ms ms' c _ _ _ _ Hm Hcon HK H). }
    assert (Hy0 : forall ma wa, tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk))
                                                   (cargs_nonrec_tele gs1) ma wa t) 0 nil nil)
      by (intros; apply tele_prefix_rel_nil).
    assert (HTs : List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1
                  = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn 0 (shape_doms_tele t))
      by (cbn [List.firstn]; rewrite List.app_nil_r; reflexivity).
    split; intro H.
    - pose proof (proj1 (proj2 (proj2 (ind_rel_base_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups' Ad' ups Add)))
                    _ _ _ _ _ _ _ _ _ H Mk ms ms c gs1 t gs2 ws ws 0 nil nil eq_refl HM
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                    Hmm Hcon Hww eq_refl (Nat.le_0_l _) (Hy0 _ _) HTs) as H1.
      pose proof (proj1 (proj2 (proj2 (ind_rel_pre_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups' Ad' Add)))
                    _ _ _ _ _ _ _ _ _ H1 Mk ms ms ms' c gs1 t gs2 ws ws ws' 0 nil nil nil eq_refl HM
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                    Hmm Hm Hcon Hww Hw eq_refl (Nat.le_0_l _) (Hy0 _ _) (Hy0 _ _) HTs) as H2.
      rewrite List.app_nil_r in H2; exact H2.
    - pose proof (proj1 (proj2 (proj2 (ind_rel_pre_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups' Ad' Add)))
                    _ _ _ _ _ _ _ _ _ H Mk ms ms' ms c gs1 t gs2 ws ws' ws 0 nil nil nil eq_refl HM
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                    Hm Hm'm Hcon Hw Hw'w eq_refl (Nat.le_0_l _) (Hy0 _ _) (Hy0 _ _) HTs) as H1.
      rewrite List.app_nil_r in H1.
      exact (proj1 (proj2 (proj2 (ind_rel_base_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups Add ups' Ad')))
               _ _ _ _ _ _ _ _ _ H1 Mk ms ms c gs1 t gs2 ws ws 0 nil nil eq_refl HM
               ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
               Hmm Hcon Hww eq_refl (Nat.le_0_l _) (Hy0 _ _) HTs).
  Qed.
End GroupFacts.

(** ** Types in a Universe

    An element of a large universe, or of a small one at a level, is a
    type of a large universe. *)
(** A type of a universe, weakened: its two values are related relevant
    types. *)
Lemma rel_exp_of_typ_wk_relevant : forall {Γ Δ φ A} {i : nat},
    Γ ⊨ʷ φ : Δ -> Δ ⊨ A : Typeω@i ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ),
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A[φ]ʷ ⟧ ρ ↘ a /\ ⟦ A ⟧ ⟪φ⟫ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_universe_elements (per_univ i).
Proof.
  intros * Hw HA.
  destruct (rel_exp_under_ctx_wk_simple Hw HA) as (RΓ & HΓ & i0 & Hwk).
  exists RΓ, HΓ; intros ρ ρ' Hρ.
  destruct (Hwk _ _ Hρ) as (y & y' & Ry & Ey & Ey' & HRy & [Hp | (m & m' & Em & Em' & Hmm)]);
    cbn in Ey; inversion Ey; subst; [ discriminate |].
  destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
  apply ERy in Hmm; exists m, m'; split; [ exact Em | split; [ exact Em' | exact Hmm ] ].
Qed.

Lemma rel_subtyp_small_large_at : forall Γ M (n i : nat), Γ ⊨ M : Level@n -> Γ ⊨ Type⟨M⟩ ⊆ Typeω@i.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_subtyp_with (S i).
  intros Γ' env_rel' HΓ0 σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev') as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom m2 ≈ m2 ∈ per_lvl) by lvl_pw.
  exists 𝕌@m1 𝕌@m2 𝕌ω@i 𝕌ω@i; try (apply eval_exp_univ; eassumption); try apply eval_exp_typ.
  - eexists; apply per_univ_elem_core_suniv'; [ eassumption | exact I | reflexivity ].
  - eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ].
  - apply per_subtyp_small_large; [ assumption | solve_universe_index ].
Qed.

Lemma rel_exp_typ_at : forall Γ (i : nat), ⊨ Γ -> Γ ⊨ Typeω@i : Typeω@(S i).
Proof.
  intros * H.
  pose proof (rel_ctx_wf_per_ctx_env H) as [env_relΓ HΓ].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hu : per_universe_elements (per_univ (S i)) 𝕌ω@i 𝕌ω@i)
    by (constructor; [| reflexivity | reflexivity | discriminate | discriminate ];
        eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

Lemma typ_of_univ_elem : forall Ψ M S, ⊨ Ψ -> Ψ ⊨ M : S ->
    (exists i : nat, S = Typeω@i) \/ (exists t (n : nat), S = Type⟨t⟩ /\ Ψ ⊨ t : Level@n) ->
    exists j : nat, Ψ ⊨ M : Typeω@j.
Proof.
  intros * HΨ HM [[i ->] | (t & n & -> & Ht)]; [ eauto |].
  exists 0; eapply rel_exp_under_ctx_subtyp; [ exact HM | exact (rel_type_of_typ (rel_exp_typ_at _ 0 HΨ)) | exact (rel_subtyp_small_large_at _ _ n 0 Ht) ].
Qed.

Lemma rel_exp_conv_typ : forall Γ N T T' (i : nat), Γ ⊨ N : T -> Γ ⊨ T ≈ T' : Typeω@i -> Γ ⊨ N : T'.
Proof.
  intros * HN HT.
  eapply rel_exp_under_ctx_subtyp; [ exact HN | | exact (rel_subtyp_under_ctx_refl (rel_type_of_typ HT)) ].
  exact (rel_type_of_typ (rel_exp_under_ctx_trans (rel_exp_under_ctx_sym HT) HT)).
Qed.

(** Terms of the types of a telescope are terms of the types of an equal
    one. *)
Lemma tele_insts_rel_conv : forall Γ Δ Δ' Ms, Γ ⊨ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' ->
    List.length Δ' = List.length Δ -> List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Γ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Γ)) Ms ->
    forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ' Id Ms) k = Some T -> Γ ⊨ N : T.
Proof.
  induction Δ as [| e Δ IH]; intros Δ' Ms HX Ha Ha' Hll Hl HMs HMss k N T HN HT.
  - destruct Ms; [ destruct k; discriminate | discriminate ].
  - destruct Δ' as [| e' Δ']; [ discriminate |].
    inversion Ha as [| ? ? (κ & A & ->) HaΔ]; subst; inversion Ha' as [| ? ? (κ' & A' & ->) HaΔ']; subst.
    cbn [List.length] in Hll, Hl.
    (** Related contexts agree on their entries' kinds. *)
    assert (κ' = κ) as -> by (destruct HX as [_ _ [R HRR]]; cbn [List.app] in HRR; inversion HRR; subst; reflexivity).
    destruct (rel_ext_under_ctx_ass_inv _ _ _ _ _ _ HX) as [HX0 _ (S' & HS' & HA') i HAA'].
    destruct (List.exists_last (l := Ms) ltac:(intros ->; cbn in Hl; discriminate)) as (Ms0 & M & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    assert (Hl0 : List.length Ms0 = List.length Δ) by lia.
    apply List.Forall_app in HMss as [HMss0 _].
    assert (Hti : forall X Y, all_assumptions Y -> List.length Ms0 = List.length Y ->
               tele_insts (ce_ass κ X :: Y) Id (Ms0 ++ M :: nil) = tele_insts Y Id Ms0 ++ X[sb_of_list Id Ms0] :: nil).
    { intros X Y HY HlY; change (ce_ass κ X :: Y) with ((ce_ass κ X :: nil) ++ Y).
      rewrite tele_insts_app by (try exact HY; lia); reflexivity. }
    assert (HlT : forall Y, all_assumptions Y -> List.length Ms0 = List.length Y -> List.length (tele_insts Y Id Ms0) = List.length Y)
      by (intros Y HY HlY; rewrite length_tele_insts by exact HY; lia).
    pose proof (HlT _ HaΔ Hl0) as HlT0; pose proof (HlT _ HaΔ' ltac:(lia)) as HlT0'.
    rewrite (Hti _ _ HaΔ' ltac:(lia)) in HT.
    assert (HMs0 : forall k N T, List.nth_error Ms0 k = Some N -> List.nth_error (tele_insts Δ Id Ms0) k = Some T -> Γ ⊨ N : T).
    { intros k0 N0 T0 HN0 HT0.
      assert (Hk0 : k0 < List.length Δ) by (rewrite <- HlT0; apply List.nth_error_Some; congruence).
      apply (HMs k0); [ rewrite List.nth_error_app1 by lia; exact HN0 | rewrite (Hti _ _ HaΔ Hl0), List.nth_error_app1 by lia; exact HT0 ]. }
    destruct (Nat.lt_ge_cases k (List.length Δ')) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      exact (IH _ _ HX0 HaΔ HaΔ' ltac:(lia) Hl0 HMs0 HMss0 _ _ _ HN HT).
    + assert (k = List.length Δ') as ->.
      { assert (Hk' : k < List.length (Ms0 ++ M :: nil)) by (apply List.nth_error_Some; congruence).
        rewrite List.length_app in Hk'; cbn in Hk'; lia. }
      rewrite List.nth_error_app2, HlT0', Nat.sub_diag in HT by lia; injection HT as <-.
      rewrite List.nth_error_app2 in HN by lia.
      replace (List.length Δ' - List.length Ms0) with 0 in HN by lia; injection HN as <-.
      pose proof (HMs (List.length Δ) M (A[sb_of_list Id Ms0])) as HM.
      rewrite List.nth_error_app2 in HM by lia.
      rewrite (Hti _ _ HaΔ Hl0), List.nth_error_app2 in HM by lia.
      rewrite Hl0, HlT0, !Nat.sub_diag in HM.
      specialize (HM eq_refl eq_refl).
      pose proof (rel_ext_under_ctx_left _ _ _ HX0) as HW.
      pose proof (rel_ctx_wf_app_r _ _ HW) as HΓ.
      pose proof (gsub_of_list _ _ _ _ _ (gsub_id _ HΓ) HaΔ HW Hl0 HMs0 HMss0) as Hgs.
      pose proof (rel_type_under_ctx_gsub Hgs HAA') as HE.
      (** The right type's instance is a type, by the instance into the
          right telescope. *)
      assert (HMs0' : forall k N T, List.nth_error Ms0 k = Some N -> List.nth_error (tele_insts Δ' Id Ms0) k = Some T -> Γ ⊨ N : T)
        by exact (IH _ _ HX0 HaΔ HaΔ' ltac:(lia) Hl0 HMs0 HMss0).
      pose proof (rel_ext_under_ctx_right _ _ _ HX0) as HW'.
      assert (Hl0' : List.length Ms0 = List.length Δ') by lia.
      pose proof (gsub_of_list _ _ _ _ _ (gsub_id _ HΓ) HaΔ' HW' Hl0' HMs0' HMss0) as Hgs'.
      pose proof (rel_exp_under_ctx_gsub Hgs' HA') as HA's.
      rewrite (type_sort_sub _ _ (sort_kind_type_sort _ _ HS')) in HA's.
      destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS') HA's) as [j HA'j].
      exact (rel_exp_under_ctx_subtyp HM HA'j (rel_subtyp_under_ctx_refl HE)).
Qed.

(** ** The Members at Arguments

    A declared member's type former at terms of its parameters' types is a
    type; so is the type of any member at the group's uniform parameters
    as variables and terms of its non-uniform parameters' types, a view's
    being its container's at the view's instance. *)
Lemma valid_group_valid_ind_apps : forall p D, valid_group p D -> forall k Mk pm Ψ Ms, ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> ⊨ Ψ ->
    List.length Ms = im_np D Mk ->
    (forall m N T, List.nth_error Ms m = Some N -> List.nth_error (tele_insts (im_params D Mk) Id Ms) m = Some T -> Ψ ⊨ N : T) ->
    List.Forall (exp_scoped (List.length Ψ)) Ms ->
    exists j : nat, Ψ ⊨ apps (a_ind p k) Ms : Typeω@j.
Proof.
  intros p D Hg k Mk pm Ψ Ms HM Hh HΨ HMl HMs HMss.
  pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc; pose proof (valid_group_sort _ _ Hg) as Hsu.
  pose proof (member_params_ass D Hc k Mk HM) as Hpa.
  destruct (valid_ind_decl_sort D HD) as [i HS].
  pose proof (valid_ind_decl_params D HD k Mk HM) as HP.
  pose proof HP as HP'; unfold im_params in HP'.
  pose proof (rel_wk_under_ctx_shiftn _ _ HP') as Hw; rewrite length_im_nparams in Hw.
  assert (HB : im_params D Mk ⊨ (ind_sort D)[wk_shiftn (im_nn Mk)]ʷ : Typeω@i)
    by (pose proof (rel_exp_under_ctx_wk Hw HS) as H; cbn [exp_wk] in H; exact H).
  destruct (closed_app_sem _ _ Hpa HP HΨ) as [HPΨ _].
  pose proof (closed_app_valid _ _ _ _ _ Hpa HP HΨ HB) as HBΨ.
  pose proof (closed_weaken_valid _ _ _ _ HΨ (valid_exp_under_ctx_ind D HD Hc Hsu p (valid_group_lookup _ _ Hg) (valid_group_ass _ _ Hg) k Mk pm HM Hh))
    as HMv.
  unfold ind_ty in HMv.
  assert (HMl' : List.length Ms = List.length (im_params D Mk)) by (rewrite length_im_params; exact HMl).
  pose proof (rel_exp_apps_ctx_pi_n _ (im_params D Mk) Ψ _ i (a_ind p k) Ms eq_refl Hpa HPΨ HBΨ HMv HMl' HMs HMss) as HR.
  apply (typ_of_univ_elem _ _ _ HΨ HR).
  destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; cbn [exp_wk exp_sub]; [ left; eauto | right ].
  destruct (valid_ind_decl_sort_lvl D HD) as [n Hn]; rewrite Heq in Hn; cbn [ind_sort_lvl] in Hn.
  exists (t[wk_shiftn (im_nn Mk)]ʷ[sb_of_list Id Ms]), n; split; [ reflexivity |].
  pose proof (rel_exp_under_ctx_wk Hw Hn) as Hn1; cbn [exp_wk] in Hn1.
  pose proof (closed_app_valid _ _ _ _ _ Hpa HP HΨ Hn1) as Hn2.
  pose proof (gsub_of_list _ _ _ _ _ (gsub_id _ HΨ) Hpa HPΨ HMl' HMs HMss) as Hgs.
  pose proof (rel_exp_under_ctx_gsub Hgs Hn2) as Hn3; cbn [exp_sub] in Hn3; exact Hn3.
Qed.

Lemma tele_insts_agree_mvc : forall Δ k σ σ' Ms, all_assumptions Δ -> ctx_mvc Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> sentry_exp (σ x) = sentry_exp (σ' x)) -> tele_insts Δ σ Ms = tele_insts Δ σ' Ms.
Proof.
  intros * Ha Hm Hs H.
  pose proof (tele_insts_sub_mvc Δ k σ σ' Id Ms Ha Hm Hs ltac:(intros x Hx; rewrite sentry_sub_id; exact (H x Hx))) as E.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), (List.map_ext (fun M => M[Id]) (fun M => M) exp_sub_id), !List.map_id in E.
  exact E.
Qed.

Lemma valid_group_mty_valid : forall p D, valid_group p D -> containers_valid D ->
    forall j Mj Z nn L Ns, ind_member D j = Some Mj -> ⊨ Z ++ ind_uparams D -> List.length Z = L + nn ->
    List.length Ns = im_nn Mj ->
    (forall m N T, List.nth_error Ns m = Some N ->
       List.nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D nn L)) Ns) m = Some T -> Z ++ ind_uparams D ⊨ N : T) ->
    List.Forall (exp_scoped (List.length (Z ++ ind_uparams D))) Ns ->
    exists i : nat, Z ++ ind_uparams D ⊨ ind_mty p D j (ind_uvars D nn L) Ns : Typeω@i.
Proof.
  intros p D Hg Hcv j Mj Z nn L Ns HMj HΨ HlZ HlN HNs HNss.
  pose proof (valid_group_closed _ _ Hg) as Hc; pose proof (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)) as Hmv.
  pose proof (rel_ctx_wf_app_r _ _ HΨ) as HU.
  set (Us := ind_uvars D nn L) in *.
  assert (HUs : Us = vars_from (List.length Z) (List.length (ind_uparams D))) by (unfold Us, ind_uvars, ind_nu; rewrite HlZ; reflexivity).
  pose proof (valid_vars_tele Z (ind_uparams D) (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc) (decl_mvc_uparams _ Hmv) HΨ) as HUv.
  rewrite <- HUs in HUv.
  assert (HlU : List.length Us = ind_nu D) by (unfold Us, ind_uvars; apply length_vars_from).
  assert (HlTU : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in *; lia).
  (** The uniform parameters as variables are scoped. *)
  assert (HUss : List.Forall (exp_scoped (List.length (Z ++ ind_uparams D))) Us)
    by (rewrite HUs; apply vars_from_scoped; rewrite List.length_app; lia).
  unfold ind_mty; rewrite HMj; unfold im_ty_at, im_ref, im_pre.
  destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; cbn [fst snd].
  - apply (valid_group_valid_ind_apps p D Hg j Mj pm); [ exact HMj | exact Hh | exact HΨ | rewrite List.length_app; unfold im_np; lia |
      | apply List.Forall_app; split; assumption ].
    intros m N T HN HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (exact (decl_closed_ass _ Hc) || (unfold ind_nu in *; lia)).
    destruct (Nat.lt_ge_cases m (ind_nu D)) as [Hm | Hm].
    + rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      exact (HUv _ _ _ HN HT).
    + rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite HlU in HN; rewrite HlTU in HT.
      exact (HNs _ _ _ HN HT).
  - (** A view: the container's type former at the view's instance. *)
    destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & HMk' & Hkd & HIl & _ & Hvm & _).
    pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
    pose proof (valid_group_closed _ _ HgQ) as HcQ; pose proof (decl_typed_mvc _ _ _ (valid_group_typed _ _ HgQ)) as HmvQ.
    pose proof (decl_closed_ass _ HcQ) as HaQ.
    assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
    { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
      unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate .. ]. }
    destruct Hhd as [pm Hhd].
    destruct (decl_typed_view_wrap _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (D2 & Hq2 & Hvw).
    rewrite Hq in Hq2; injection Hq2 as <-.
    destruct (view_wrap_ok_members _ _ _ Hvw _ _ _ HMk' Hvm) as (Mv & HMv & Hnn & _).
    rewrite HMj in HMv; injection HMv as <-.
    pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ HMj Hh) as HsIs.
    pose proof (proj1 (proj2 (decl_mvc_members _ Hmv _ _ HMj))) as HmIs; rewrite Hh in HmIs; cbn in HmIs.
    set (IsU := List.map (fun I => I[sb_of_list Id Us]) Is).
    assert (HlIsU : List.length IsU = ind_nu Dq) by (unfold IsU; rewrite List.length_map; exact HIl).
    assert (HlTI : List.length (tele_insts (ind_uparams Dq) Id IsU) = ind_nu Dq)
      by (rewrite length_tele_insts by exact HaQ; unfold ind_nu in *; lia).
    (** The instance, at the uniform parameters as variables, is scoped. *)
    assert (HIsUs : List.Forall (exp_scoped (List.length (Z ++ ind_uparams D))) IsU).
    { unfold IsU; apply List.Forall_map, List.Forall_forall; intros I HIin.
      apply exp_scoped_sb_of_list; [| exact HUss ].
      eapply exp_scoped_mono; [| exact (proj1 (List.Forall_forall _ _) HsIs I HIin) ]; unfold ind_nu in *; lia. }
    apply (valid_group_valid_ind_apps qc Dq HgQ kc Mk' pm); [ exact HMk' | exact Hhd | exact HΨ | rewrite List.length_app; unfold im_np; lia |
      | apply List.Forall_app; split; assumption ].
    intros m N T HN HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (exact HaQ || (unfold ind_nu in *; lia)).
    destruct (Nat.lt_ge_cases m (ind_nu Dq)) as [Hm | Hm].
    + (** The instance, of the container's uniform parameters' types. *)
      rewrite List.nth_error_app1 in HN by lia; rewrite List.nth_error_app1 in HT by lia.
      unfold IsU in HN; rewrite List.nth_error_map in HN.
      destruct (List.nth_error Is m) as [I |] eqn:HI; cbn in HN; [ injection HN as <- | discriminate ].
      assert (Hm' : m < List.length (tele_insts (ind_uparams Dq) Id Is))
        by (rewrite length_tele_insts by exact HaQ; unfold ind_nu in *; lia).
      destruct (nth_error_lt_some' _ _ Hm') as [T0 HT0].
      pose proof (tele_insts_closed_sub _ _ (sb_of_list Id Us) _ _ HaQ (decl_closed_uparams _ HcQ) HT0) as HT1.
      fold IsU in HT1; rewrite HT in HT1; injection HT1 as ->.
      pose proof (valid_group_views_view_is p D Hg Hcv _ _ _ _ _ _ _ _ _ _ HMj Hh Hq HI HT0) as HIv.
      pose proof (closed_app_valid _ _ _ _ _ (decl_closed_ass _ Hc) HU HΨ HIv) as HIv'.
      pose proof (gsub_of_list (ind_uparams D) _ _ Id Us (gsub_id _ HΨ) (decl_closed_ass _ Hc)
                    (proj1 (closed_app_sem _ _ (decl_closed_ass _ Hc) HU HΨ)) ltac:(unfold ind_nu in HlU; lia) HUv HUss) as Hgs.
      exact (rel_exp_under_ctx_gsub Hgs HIv').
    + (** The non-uniform arguments, of the container's non-uniform
          parameters' types at the instance: those of the view's, by the
          view's equation. *)
      rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HT by lia.
      rewrite HlIsU in HN; rewrite HlTI in HT.
      set (τ := sb_of_wk (wk_shiftn (List.length Z))).
      pose proof (rel_wk_under_ctx_shiftn _ _ HΨ) as Hw.
      pose proof (gsub_wk _ _ _ Hw HΨ HU) as Hgτ.
      pose proof (valid_group_views_view_nparams p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ HMj Hh Hq HMk' Hvm HMj) as HX.
      pose proof (member_nparams_ass D Hc _ _ HMj) as HaX.
      pose proof (member_nparams_ass Dq HcQ _ _ HMk') as HaY.
      pose proof (rel_ext_under_ctx_gsub _ _ _ _ _ Hgτ HaX (all_assumptions_sub _ _ HaY) HX) as HXτ.
      assert (EX : tele_insts (im_nparams Mj) (sb_of_list Id Us) Ns = tele_insts (tele_sub (im_nparams Mj) τ) Id Ns).
      { rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ _ _ (sb_compose_id_right τ)).
        apply (tele_insts_agree_mvc _ (ind_nu D));
          [ exact HaX | exact (proj1 (decl_mvc_members _ Hmv _ _ HMj)) | exact (decl_closed_nparams_scoped _ Hc _ _ HMj) |].
        intros x Hx; rewrite HUs, sb_of_list_vars by (unfold ind_nu in Hx; exact Hx).
        unfold τ, sb_of_wk, wk_shiftn; cbn; f_equal; lia. }
      assert (EY : tele_insts (im_nparams Mk') (sb_of_list Id IsU) Ns
                   = tele_insts (tele_sub (tele_sub (im_nparams Mk') (sb_of_list Id Is)) τ) Id Ns).
      { rewrite !tele_insts_tele_sub.
        apply (tele_insts_agree_mvc _ (ind_nu Dq));
          [ exact HaY | exact (proj1 (decl_mvc_members _ HmvQ _ _ HMk')) | exact (decl_closed_nparams_scoped _ HcQ _ _ HMk') |].
        intros x Hx.
        assert (HxI : x < List.length Is) by (unfold ind_nu in *; lia).
        assert (HlIsU' : List.length IsU = List.length Is) by (unfold IsU; apply List.length_map).
        rewrite (sb_of_list_nth IsU _ x a_prop) by lia.
        unfold sb_compose; rewrite (sb_of_list_nth Is _ x a_prop HxI).
        rewrite HlIsU'.
        destruct (nth_error_lt_some' Is (List.length Is - 1 - x) ltac:(lia)) as [I HI'].
        assert (HIU : List.nth_error IsU (List.length Is - 1 - x) = Some I[sb_of_list Id Us])
          by (unfold IsU; rewrite List.nth_error_map, HI'; reflexivity).
        rewrite (List.nth_error_nth _ _ _ HI'), (List.nth_error_nth _ _ _ HIU); cbn [sentry_sub sentry_exp].
        pose proof (List.nth_error_In _ _ HI') as HIin.
        change (fun x0 : nat => sentry_sub (τ x0) Id) with (τ ⨟ Id).
        unfold τ; rewrite <- exp_sub_sub, exp_sub_id, exp_sub_of_wk, HUs.
        rewrite (exp_at_vars _ _ _ (proj1 (List.Forall_forall _ _) HsIs I HIin) (proj1 (List.Forall_forall _ _) HmIs I HIin)).
        reflexivity. }
      rewrite EY in HT.
      assert (HMsτ : forall m0 N0 T0, List.nth_error Ns m0 = Some N0 ->
                 List.nth_error (tele_insts (tele_sub (im_nparams Mj) τ) Id Ns) m0 = Some T0 -> Z ++ ind_uparams D ⊨ N0 : T0)
        by (intros m0 N0 T0 HN0 HT0; rewrite <- EX in HT0; exact (HNs _ _ _ HN0 HT0)).
      exact (tele_insts_rel_conv _ _ _ Ns HXτ (all_assumptions_sub _ _ HaX) (all_assumptions_sub _ _ (all_assumptions_sub _ _ HaY))
               ltac:(rewrite !length_tele_sub, !length_im_nparams; lia) ltac:(rewrite length_tele_sub, length_im_nparams; lia)
               HMsτ HNss _ _ _ HN HT).
  - (** A record view: the record at the view's instance, of no
        non-uniform parameter. *)
    pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as Hnp.
    destruct Ns; [| unfold im_nn in HlN; rewrite Hnp in HlN; discriminate HlN ].
    rewrite List.app_nil_r.
    pose proof (valid_group_views_rview_type p D Hg _ _ _ _ _ HMj Hh) as H0.
    pose proof (closed_app_valid _ _ _ _ _ (decl_closed_ass _ Hc) HU HΨ H0) as H1.
    pose proof (gsub_of_list (ind_uparams D) _ _ Id Us (gsub_id _ HΨ) (decl_closed_ass _ Hc)
                  (proj1 (closed_app_sem _ _ (decl_closed_ass _ Hc) HU HΨ)) ltac:(unfold ind_nu in HlU; lia) HUv HUss) as Hgs.
    pose proof (rel_exp_under_ctx_gsub Hgs H1) as H2.
    rewrite apps_exp_sub in H2; cbn [exp_sub] in H2.
    destruct (valid_group_sort _ _ Hg) as [[i Hi] | [t Ht]]; rewrite ?Hi, ?Ht in H2; cbn [exp_sub] in H2;
      [ exists i; exact H2 | exists 0; eapply rel_exp_suniv_tm_large; exact H2 ].
Qed.

(** ** The Contexts of the Arguments of a Valid Group's Members

    Each prefix of the arguments of a constructor of a member is a context
    over the member's parameters, weakened to its non-recursive arguments
    by [wk_pat]: a recursive argument's type is the [Π] over its shape's
    domains of the type of the member it ends in. *)
(** The domains of a shape, split after the first [kk]: the rest, past
    those, over the first. *)
Lemma shape_domains_ctx_split : forall Bs pat kk,
    shape_domains_ctx pat Bs
    = shape_domains_ctx (List.repeat false kk ++ pat) (List.skipn kk Bs) ++ shape_domains_ctx pat (List.firstn kk Bs).
Proof.
  induction Bs as [| B Bs IH]; intros pat [| kk]; cbn [shape_domains_ctx List.skipn List.firstn List.repeat List.app];
    rewrite ?List.app_nil_r; try reflexivity.
  rewrite (IH (false :: pat) kk), repeat_false_cons, <- List.app_assoc; reflexivity.
Qed.

(** The end of a recursive argument's type, under the shape's domains, is
    a type of a universe: the member's type at the uniform parameters as
    variables and the shape's parameters, weakened past the recursive
    arguments. *)
Lemma valid_group_shape_leaf : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk c gs gs1 t gs2, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk ->
    cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk ->
    exists j : nat, shape_domains_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
      ⊨ ptyp_ty p D (im_nn Mk) (List.repeat false (List.length (ptyp_doms t)) ++ cargs_pat gs1) (pt_self (ptyp_mem t) (ptyp_ps t))
      : Typeω@j.
Proof.
  intros p D Hg Hcv k Mk c gs gs1 t gs2 HM Hcon Heq HΨ IHw.
  pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
  pose proof (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)) as Hmv.
  set (pat := cargs_pat gs1).
  set (L := List.length (ptyp_doms t)).
  set (pat' := List.repeat false L ++ pat).
  set (Φ := shape_domains_ctx pat (ptyp_doms t)).
  assert (HlΦ : List.length Φ = L) by (unfold Φ; apply length_shape_domains_ctx).
  assert (HΦ : ⊨ Φ ++ cargs_ctx p D Mk gs1 ++ im_params D Mk).
  { pose proof (shape_domains_ctx_sem_gen D p k Mk c gs HD HM Hcon gs1 t gs2 Heq HΨ IHw L (le_n _)) as H.
    unfold L in H; rewrite List.firstn_all in H; exact H. }
  assert (HwΦ : Φ ++ cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat pat')
                  : doms_ctx (ptyp_doms t) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk).
  { pose proof (shape_domains_ctx_wk_gen D p k Mk c gs HD HM Hcon gs1 t gs2 Heq IHw L (le_n _)) as H.
    unfold L in H; rewrite List.firstn_all in H; exact H. }
        destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
        { cbn [ptyp_ty].
          assert (HE : ⊨ (Φ ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D)
            by (unfold im_params in HΦ; rewrite <- !List.app_assoc; exact HΦ).
          assert (Hpat : List.length pat = List.length gs1) by apply length_cargs_pat.
          assert (Hpat' : List.length pat' = L + List.length gs1) by (unfold pat'; rewrite List.length_app, List.repeat_length; lia).
          assert (Hnargs : pat_nargs pat' = L + List.length (cargs_nonrec_ctx gs1)).
          { unfold pat', pat; rewrite pat_nargs_app, pat_nargs_cargs_pat; f_equal.
            clear; induction L as [| L IH]; cbn; lia. }
          destruct (valid_group_mty_valid p D Hg Hcv (ptyp_mem t) Mj (Φ ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk) (im_nn Mk) (List.length pat')
                      (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t)) HMj HE) as [j0 Hv].
          - rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia.
          - rewrite List.length_map; exact HlPs.
          - intros m N T HN HT.
            apply nth_error_map_inv in HN as (P & HPm & ->).
            set (s := L + List.length (cargs_nonrec_ctx gs1) + im_nn Mk).
            assert (Hti : tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mk) (List.length pat')))
                            (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t))
                          = List.map (fun T => T[wk_pat pat']ʷ) (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn s)) (ptyp_ps t))).
            { rewrite <- !map_sub_of_wk; symmetry.
              eapply (tele_insts_sub_mvc _ (ind_nu D));
                [ exact (member_nparams_ass D Hc _ _ HMj) | exact (proj1 (decl_mvc_members _ Hmv _ _ HMj))
                | exact (decl_closed_nparams_scoped _ Hc _ _ HMj) |].
              intros x Hx; unfold ind_uvars; rewrite sb_of_list_vars by exact Hx; cbn.
              unfold s, wk_shiftn; rewrite <- Hnargs.
              replace (x + (pat_nargs pat' + im_nn Mk)) with (pat_nargs pat' + (im_nn Mk + x)) by lia.
              rewrite wk_pat_ge; f_equal; lia. }
            rewrite Hti in HT; apply nth_error_map_inv in HT as (T0 & HT0 & ->).
            assert (Hσ : s = ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk)
              by (unfold s, ptyp_depth; fold L; rewrite cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele; reflexivity).
            rewrite Hσ in HT0.
            pose proof (valid_ind_decl_rec_field _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HPm HT0) as HP0.
            rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HP0.
            pose proof (rel_exp_under_ctx_wk HwΦ HP0) as H.
            unfold im_params in H; rewrite <- !List.app_assoc; exact H.
          - (** The shape's parameters are scoped by the domains, the
                non-recursive arguments before and the parameters. *)
            pose proof (ptyp_scoped_ps _ _ (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HM) c gs gs1 t gs2
                                              (cons_lookup_in _ _ _ Hcon) Heq)) as HPs.
            apply List.Forall_map; eapply List.Forall_impl; [| exact HPs ]; intros P HP.
            eapply exp_scoped_wk; [ exact HP |]; intros x Hx.
            assert (Hb : wk_pat pat' x < List.length pat' + im_np D Mk)
              by (apply wk_pat_bound; rewrite Hnargs; unfold ptyp_depth in Hx; fold L in Hx; lia).
            rewrite !List.length_app, length_cargs_ctx, length_im_nparams, HlΦ.
            unfold im_np, ind_nu in *; lia.
          - exists j0; unfold im_params; rewrite <- !List.app_assoc in Hv; exact Hv. }
Qed.

Lemma valid_group_cargs_sem_all : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> forall gs1 gs2, gs = gs1 ++ gs2 ->
      ⊨ cargs_ctx p D Mk gs1 ++ im_params D Mk /\
      cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_nonrec_ctx gs1 ++ im_params D Mk.
Proof.
  intros p D Hg Hcv k Mk c gs HM Hcon.
  pose proof (valid_group_valid _ _ Hg) as HD.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
  - cbn [cargs_ctx cargs_ctx_aux cargs_nonrec_ctx cargs_pat List.rev List.map List.app].
    destruct (rel_ctx_wf_per_ctx_env (valid_ind_decl_params _ HD _ _ HM)) as [R HR].
    split; [ exact (valid_ind_decl_params _ HD _ _ HM) |].
    eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R)
      | intros x Hx; cbn [wk_pat]; rewrite List.length_app; lia
      | intros ρ ρ' _ x _; cbn [wk_pat]; change (fun x0 : nat => x0) with wk_id; rewrite eval_wk_id; reflexivity ].
  - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
    destruct (IH _ Heq) as [HΨ IHw].
    rewrite cargs_ctx_snoc, cargs_pat_snoc.
    destruct g as [r A | t]; cbn [cargs_ctx_aux List.app wk_pat].
    + rewrite cargs_nonrec_ctx_snoc_arg.
      assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
        by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
      destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as (_ & j & HAv).
      rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAv.
      pose proof (rel_exp_under_ctx_wk IHw HAv) as HAw; cbn [exp_wk] in HAw.
      rewrite abs_kind_sort_wk in HAw; cbn [exp_wk] in HAw.
      split; [ exact (rel_ctx_wf_ext_sort _ _ _ _ HΨ (sort_kind_abs_kind_sort r j) HAw)
             | exact (rel_wk_under_ctx_q IHw (rel_type_of_abs_kind_sort HAv)) ].
    + rewrite cargs_nonrec_ctx_snoc_rec.
      (** The recursive argument's type, the [Π] over its domains of the
          end ([valid_group_shape_leaf]). *)
      assert (Hj : exists j : nat, cargs_ctx p D Mk gs1 ++ im_params D Mk ⊨ ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t : Typeω@j).
      { rewrite (ptyp_ty_ctx_pi p D (im_nn Mk) t (cargs_pat gs1)).
        assert (HΦa : all_assumptions (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t))) by apply shape_domains_ctx_ass.
        assert (HΦ : ⊨ shape_domains_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk).
        { pose proof (shape_domains_ctx_sem_gen D p k Mk c gs HD HM Hcon gs1 t gs2 Heq HΨ IHw _ (le_n _)) as H.
          rewrite List.firstn_all in H; exact H. }
        destruct (valid_group_shape_leaf p D Hg Hcv k Mk c gs gs1 t gs2 HM Hcon Heq HΨ IHw) as [j0 Hleaf].
        exact (rel_exp_ctx_pi _ _ _ _ HΦa HΦ Hleaf). }
      destruct Hj as [j Hj].
      pose proof (rel_ctx_wf_ext_typ _ _ _ HΨ Hj) as HC.
      split; [ exact HC |].
      exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
Qed.

Corollary valid_group_cargs_sem : forall p D, valid_group p D -> containers_valid D ->
    forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> ⊨ cargs_ctx p D Mk gs ++ im_params D Mk.
Proof. intros * Hg Hcv * HM Hcon; exact (proj1 (valid_group_cargs_sem_all p D Hg Hcv k Mk c gs HM Hcon gs nil (eq_sym (List.app_nil_r gs)))). Qed.

(** ** The Arguments' Environments, Weakened to the Non-Recursive Ones *)

Lemma env_tele_extend_typed : forall ρ T vs, env_tele ρ T vs = env_extend_typed ρ (tele_entries ρ T vs).
Proof. reflexivity. Qed.

Lemma length_ctx_retag : forall Δ ρ, List.length Δ <= List.length ρ -> List.length (ctx_retag Δ ρ) = List.length ρ.
Proof.
  induction Δ as [| e Δ IH]; intros ρ Hl; [ reflexivity |].
  destruct ρ as [| d ρ]; cbn [List.length] in Hl; [ lia |].
  cbn [ctx_retag List.length List.tl]; rewrite IH by lia; reflexivity.
Qed.

(** The retagging, at a telescope over [Δ], of an environment extended by
    typed values over one of [Δ]'s length: the telescope's arguments over
    the retagged base. *)
Lemma ctx_retag_extend_typed : forall T Δ ρ vts, List.length ρ = List.length Δ -> List.length vts = List.length T ->
    ctx_retag (List.rev T ++ Δ) (env_extend_typed ρ vts) = env_tele (ctx_retag Δ ρ) T (List.map fst vts).
Proof.
  induction T as [| e T IH] using List.rev_ind; intros Δ ρ vts Hρ Hl.
  - destruct vts; [ reflexivity | discriminate ].
  - rewrite List.length_app in Hl; cbn [List.length] in Hl.
    destruct vts as [| [v t] vts _] using List.rev_ind; [ cbn in Hl; lia |].
    rewrite List.length_app in Hl; cbn [List.length] in Hl.
    rewrite List.rev_app_distr, List.map_app; cbn [List.rev List.app List.map fst].
    unfold env_tele; rewrite tele_entries_app by (rewrite List.length_map; lia); fold (env_tele (ctx_retag Δ ρ) T (List.map fst vts)).
    cbn [tele_entries tele_head_type List.tl]; rewrite !env_extend_typed_app; cbn [env_extend_typed List.fold_left fst snd].
    cbn [ctx_retag extend_env List.tl List.hd].
    rewrite (IH Δ ρ vts Hρ ltac:(lia)).
    assert (HlT : List.length (env_tele (ctx_retag Δ ρ) T (List.map fst vts)) = List.length (List.rev T ++ Δ)).
    { rewrite length_env_tele, length_ctx_retag, List.length_map, List.length_app, List.length_rev; lia. }
    unfold centry_tag; rewrite <- HlT, env_upto_exact.
    destruct e; reflexivity.
Qed.

Lemma length_nonrec_typed : forall gs vts, List.length vts = List.length gs ->
    List.length (nonrec_typed gs vts) = List.length (cargs_nonrec gs).
Proof. induction gs as [| [] gs IH]; intros [| vt vts] Hl; cbn in *; try discriminate; try reflexivity; rewrite ?IH by lia; reflexivity. Qed.

(** The arguments of a constructor after its parameters, weakened past
    the recursive ones and retagged at the context of the non-recursive
    ones: the closed environment of the non-recursive values. *)
Lemma ctx_retag_wk_cargs : forall pq G Mk gs1 ups vs, List.length ups = List.length (im_params G Mk) ->
    List.length vs = List.length gs1 ->
    ctx_retag (cargs_nonrec_ctx gs1 ++ im_params G Mk)
      (⟪wk_pat (cargs_pat gs1)⟫ (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (ups ++ vs)))
    = env_tele nil (List.rev (cargs_nonrec_ctx gs1 ++ im_params G Mk)) (ups ++ nonrec_arg_vals gs1 vs).
Proof.
  intros * Hu Hv.
  rewrite !env_tele_closed_app by exact Hu.
  set (base := env_tele nil (List.rev (im_params G Mk)) ups).
  rewrite (env_tele_extend_typed base (List.rev (cargs_ctx pq G Mk gs1)) vs).
  rewrite eval_wk_pat_args by (rewrite tele_entries_length, Hv; reflexivity).
  rewrite cargs_nonrec_ctx_rev_tele.
  assert (Hb : List.length base = List.length (im_params G Mk)) by (unfold base; rewrite length_env_tele; cbn; lia).
  rewrite (ctx_retag_extend_typed (cargs_nonrec_tele gs1) (im_params G Mk) base)
    by (first [ exact Hb | rewrite length_nonrec_typed, length_cargs_nonrec_tele by (rewrite tele_entries_length; exact Hv); reflexivity ]).
  rewrite nonrec_typed_values, tele_entries_values, List.rev_involutive.
  f_equal; unfold base.
  rewrite <- (List.rev_involutive (im_params G Mk)) at 1; rewrite <- (List.app_nil_r (List.rev (List.rev (im_params G Mk)))).
  apply ctx_retag_env_tele; [ reflexivity | reflexivity | rewrite List.length_rev; exact Hu ].
Qed.

(** The same after the first [d] domains of a recursive argument's shape:
    their values kept. *)
Lemma ctx_retag_wk_cargs_doms : forall pq G Mk gs1 pat Bs ups vs ys, pat = cargs_pat gs1 ->
    List.length ups = List.length (im_params G Mk) -> List.length vs = List.length gs1 -> List.length ys = List.length Bs ->
    ctx_retag (doms_ctx Bs ++ cargs_nonrec_ctx gs1 ++ im_params G Mk)
      (⟪wk_pat (List.repeat false (List.length Bs) ++ pat)⟫
         (env_tele nil (List.rev (shape_domains_ctx pat Bs ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (ups ++ vs ++ ys)))
    = env_tele nil (List.rev (doms_ctx Bs ++ cargs_nonrec_ctx gs1 ++ im_params G Mk)) (ups ++ nonrec_arg_vals gs1 vs ++ ys).
Proof.
  intros * -> Hu Hv Hy.
  assert (Hcu : List.length (ups ++ vs) = List.length (cargs_ctx pq G Mk gs1 ++ im_params G Mk))
    by (rewrite !List.length_app, length_cargs_ctx; lia).
  assert (Hsu : List.length (ups ++ nonrec_arg_vals gs1 vs) = List.length (cargs_nonrec_ctx gs1 ++ im_params G Mk))
    by (rewrite !List.length_app, length_nonrec_arg_vals, cargs_nonrec_ctx_rev_tele, List.length_rev, length_cargs_nonrec_tele by exact Hv; lia).
  rewrite (List.app_assoc ups vs ys), (env_tele_closed_app (cargs_ctx pq G Mk gs1 ++ im_params G Mk) _ _ _ Hcu).
  rewrite (List.app_assoc ups (nonrec_arg_vals gs1 vs) ys), (env_tele_closed_app (cargs_nonrec_ctx gs1 ++ im_params G Mk) _ _ _ Hsu).
  rewrite (env_tele_extend_typed _ (List.rev (shape_domains_ctx (cargs_pat gs1) Bs)) ys).
  rewrite eval_wk_pat_falses by (rewrite tele_entries_length; exact Hy).
  assert (Hrs := ctx_retag_wk_cargs pq G Mk gs1 ups vs Hu Hv).
  assert (Hl : List.length (⟪wk_pat (cargs_pat gs1)⟫ (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (ups ++ vs)))
               = List.length (cargs_nonrec_ctx gs1 ++ im_params G Mk)).
  { rewrite (env_tele_closed_app _ _ _ _ Hu), env_tele_extend_typed.
    rewrite eval_wk_pat_args by (rewrite tele_entries_length, Hv; reflexivity).
    rewrite length_env_extend_typed, length_nonrec_typed, length_env_tele by (rewrite tele_entries_length; exact Hv).
    rewrite cargs_nonrec_ctx_rev_tele, List.length_app, List.length_rev, length_cargs_nonrec_tele; cbn; lia. }
  rewrite <- (List.rev_involutive (doms_ctx Bs)) at 1.
  rewrite (ctx_retag_extend_typed (List.rev (doms_ctx Bs))) by
    (first [ exact Hl | rewrite List.length_rev, tele_entries_length; unfold doms_ctx; rewrite List.length_rev, List.length_map; exact Hy ]).
  rewrite Hrs, tele_entries_values; reflexivity.
Qed.

(** The same with the parameters split into the uniform and the
    non-uniform ones. *)
Corollary ctx_retag_wk_cargs_args : forall pq G Mk gs1 U ms vs, List.length U + List.length ms = List.length (im_params G Mk) ->
    List.length vs = List.length gs1 ->
    ctx_retag (cargs_nonrec_ctx gs1 ++ im_params G Mk)
      (⟪wk_pat (cargs_pat gs1)⟫ (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs)))
    = env_tele nil (List.rev (cargs_nonrec_ctx gs1 ++ im_params G Mk)) (U ++ ms ++ nonrec_arg_vals gs1 vs).
Proof.
  intros * Hu Hv; rewrite !List.app_assoc; apply ctx_retag_wk_cargs; [ rewrite List.length_app; exact Hu | exact Hv ].
Qed.

(** The closed environment of the non-recursive arguments after the
    parameters: the components after the uniform parameters. *)
Lemma closed_env_nonrec_args_components : forall G Mk gs1 U ms nv, List.length U = ind_nu G ->
    env_tele nil (List.rev (cargs_nonrec_ctx gs1 ++ im_params G Mk)) (U ++ ms ++ nv)
    = components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (ms ++ nv).
Proof.
  intros * HU; unfold components_env, decl_env, im_params.
  rewrite (List.app_assoc (cargs_nonrec_ctx gs1) (im_nparams Mk) (ind_uparams G)).
  rewrite (env_tele_closed_app (ind_uparams G) (cargs_nonrec_ctx gs1 ++ im_nparams Mk) U (ms ++ nv)) by (unfold ind_nu in HU; exact HU).
  rewrite List.rev_app_distr, cargs_nonrec_ctx_rev_tele, List.rev_involutive; reflexivity.
Qed.

(** The uniform parameters as variables, past [L + nn] components: the
    uniform parameters' values. *)
Lemma eval_uvars_components : forall D ups T zs nn L, List.length ups = ind_nu D -> List.length zs = L + nn ->
    ⟦ ind_uvars D nn L ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups T zs ↘ ups.
Proof.
  intros * Hu Hz.
  pose proof (eval_vars_from_args (tele_entries nil (List.rev (ind_uparams D)) ups) nil (tele_entries (decl_env D ups) T zs)) as H.
  rewrite tele_entries_values, !tele_entries_length, env_extend_typed_app in H.
  unfold ind_uvars; rewrite <- Hz, <- Hu; exact H.
Qed.

(** The same after the first domains of a recursive argument's shape. *)
Lemma closed_env_shape_doms_components : forall G Mk gs1 Bs U ms nv ys, List.length U = ind_nu G ->
    env_tele nil (List.rev (doms_ctx Bs ++ cargs_nonrec_ctx gs1 ++ im_params G Mk)) (U ++ ms ++ nv ++ ys)
    = components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.map (ce_ass ak_relevant) Bs) (ms ++ nv ++ ys).
Proof.
  intros * HU; unfold components_env, decl_env, im_params.
  rewrite (List.app_assoc (cargs_nonrec_ctx gs1) (im_nparams Mk) (ind_uparams G)).
  rewrite (List.app_assoc (doms_ctx Bs) (cargs_nonrec_ctx gs1 ++ im_nparams Mk) (ind_uparams G)).
  rewrite (env_tele_closed_app (ind_uparams G) (doms_ctx Bs ++ cargs_nonrec_ctx gs1 ++ im_nparams Mk) U (ms ++ nv ++ ys))
    by (unfold ind_nu in HU; exact HU).
  rewrite !List.rev_app_distr, cargs_nonrec_ctx_rev_tele, List.rev_involutive; unfold doms_ctx; rewrite List.rev_involutive.
  rewrite <- !List.app_assoc; reflexivity.
Qed.

(** The components read only as many non-recursive arguments of a
    constructor as there are values. *)
Lemma components_env_con_prefix : forall G U Tn gs gs1 gs2 ms nv, gs = gs1 ++ gs2 -> List.length ms = List.length Tn ->
    List.length nv = List.length (cargs_nonrec gs1) ->
    components_env G U (Tn ++ cargs_nonrec_tele gs) (ms ++ nv) = components_env G U (Tn ++ cargs_nonrec_tele gs1) (ms ++ nv).
Proof.
  intros * Heq Hm Hn.
  rewrite components_env_app_firstn
    by (try exact Hm; rewrite Heq, cargs_nonrec_tele_app, List.length_app, !length_cargs_nonrec_tele; lia).
  f_equal; f_equal; rewrite Heq, cargs_nonrec_tele_app, List.firstn_app, Hn, <- length_cargs_nonrec_tele, List.firstn_all, Nat.sub_diag.
  cbn [List.firstn]; rewrite List.app_nil_r; reflexivity.
Qed.

(** A type over [Δ] weakened into [Γ], at an environment [Γ] relates to
    itself, against the type at the weakened environment retagged at
    [Δ]: related values. *)
Lemma wk_type_retag_link : forall Γ Δ φ A (i : nat) RΓ ρ, Γ ⊨ʷ φ : Δ -> Δ ⊨ᵗ A ≈ A at i ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
    exists (j : nat) R a a', ⟦ A[φ]ʷ ⟧ ρ ↘ a /\ ⟦ A ⟧ ctx_retag Δ (⟪φ⟫ ρ) ↘ a' /\ DF a ≈ a' ∈ per_univ_elem j ↘ R.
Proof.
  intros * Hw HA HRΓ Hρ.
  destruct (rel_type_inversion_wk Hw HA) as (RΓ' & HRΓ' & Hwk).
  assert (E : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hwk _ _ (proj1 (E _ _) Hρ)) as (a & a1 & Ea & Ea1 & [R1 HR1]).
  pose proof Hw as [RΓw HRΓw RΔw HRΔw Hφ _ _].
  assert (Ew : RΓ <~> RΓw) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hφ _ _ (proj1 (Ew _ _) Hρ)) as Hφρ.
  pose proof (per_ctx_env_retag_right HRΔw _ _ Hφρ) as Hφr.
  destruct (rel_type_inversion_simple_at HRΔw HA _ _ Hφr) as (a2 & a3 & Ea2 & Ea3 & [R2 HR2]).
  assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R3 & HR3 & _).
  exists i, R3, a, a3; repeat split; assumption.
Qed.

(** A term over [Δ] weakened into [Γ], at an environment [Γ] relates to
    itself, against the term at the weakened environment retagged at
    [Δ]: related values at a relevant type. *)
Lemma wk_term_retag_link : forall Γ Δ φ A M RΓ ρ, Γ ⊨ʷ φ : Δ -> Δ ⊨ M : A ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
    exists (i : nat) R a a', ⟦ A[φ]ʷ ⟧ ρ ↘ a /\ ⟦ A ⟧ ctx_retag Δ (⟪φ⟫ ρ) ↘ a' /\ DF a ≈ a' ∈ per_univ_elem i ↘ R /\
      (domain_kind a = ak_propositional \/
       exists m m', ⟦ M[φ]ʷ ⟧ ρ ↘ m /\ ⟦ M ⟧ ctx_retag Δ (⟪φ⟫ ρ) ↘ m' /\ R m m').
Proof.
  intros * Hw HM HRΓ Hρ.
  destruct (rel_exp_under_ctx_wk_simple Hw HM) as (RΓ' & HRΓ' & i & Hwk).
  assert (E : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hwk _ _ (proj1 (E _ _) Hρ)) as (a & a1 & R1 & Ea & Ea1 & HR1 & Hm).
  pose proof Hw as [RΓw HRΓw RΔw HRΔw Hφ _ _].
  assert (Ew : RΓ <~> RΓw) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hφ _ _ (proj1 (Ew _ _) Hρ)) as Hφρ.
  pose proof (per_ctx_env_retag_right HRΔw _ _ Hφρ) as Hφr.
  destruct (presup_rel_exp_under_ctx_simple_at HRΔw HM) as [iA HA].
  destruct (HA _ _ Hφr) as (a2 & a3 & Ea2 & Ea3 & [R2 HR2]).
  assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R3 & HR3 & E13).
  exists i, R3, a, a3; split; [ exact Ea | split; [ exact Ea3 | split; [ exact HR3 |] ] ].
  destruct (rel_exp_under_ctx_simple_at HRΔw HM _ _ Hφr) as [(a0 & Ea0 & Hp0) | (m2 & m3 & Em2 & Em3 & Hm23)].
  - left; assert (a0 = a1) as -> by (eapply functional_eval_exp; eassumption).
    rewrite (per_univ_elem_kind _ _ _ _ HR1); exact Hp0.
  - destruct Hm as [Hp | (m & m1 & Em & Em1 & Hmm)]; [ left; exact Hp | right ].
    assert (m2 = m1) as -> by (eapply functional_eval_exp; eassumption).
    apply (per_head_iff Ea1 Ea3 HR2) in Hm23.
    assert (E12 : R1 <~> R2) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR1) HR2).
    assert (HP1 : PER R1) by (eapply per_elem_PER; exact HR1).
    exists m, m3; split; [ exact Em | split; [ exact Em3 |] ].
    apply E13; etransitivity; [ exact Hmm | apply E12; exact Hm23 ].
Qed.

(** The type of a non-recursive argument, at arguments related at the
    context of those before it: its relation is the canonical one of the
    argument at their non-recursive values. *)
Lemma valid_group_arg_head : forall pq G, valid_group pq G -> containers_valid G ->
    forall k Mk c gs gs1 r A gs2 U ms vs, ind_member G k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_arg r A :: gs2 ->
    List.length U = ind_nu G -> List.length ms = im_nn Mk -> List.length vs = List.length gs1 ->
    per_tele_args (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) nil nil (U ++ ms ++ vs) (U ++ ms ++ vs) ->
    exists (i : nat) R a, ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs) ↘ a /\
      DF a ≈ a ∈ per_univ_elem i ↘ R /\
      (R <~> canon_args_rel G U k ms c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 vs)).
Proof.
  intros pq G Hg Hcv k Mk c gs gs1 r A gs2 U ms vs HM Hcon Heq HlU Hlm Hlv Hgp.
  pose proof (valid_group_valid _ _ Hg) as HD.
  destruct (valid_group_cargs_sem_all pq G Hg Hcv k Mk c gs HM Hcon gs1 (ca_arg r A :: gs2) Heq) as [HW Hw].
  assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
    by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
  pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
  destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as (_ & j & HAv).
  rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAv.
  destruct (rel_ctx_wf_per_ctx_env HW) as [RΓ HΓ].
  assert (Hρ : RΓ (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs))
                  (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs))).
  { apply (tele_args_env_rel _ _ _ _ _ _ HΓ HW); [| exact Hgp ].
    rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
  destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_abs_kind_sort HAv) HΓ Hρ) as (i0 & Rm & m & m' & Em & Em' & HRm).
  rewrite (ctx_retag_wk_cargs_args pq G Mk gs1 U ms vs) in Em' by (try exact Hlv; rewrite length_im_params; unfold im_np, ind_nu in *; lia).
  rewrite (closed_env_nonrec_args_components G Mk gs1 U ms) in Em' by assumption.
  rewrite <- (components_env_con_prefix G U (List.rev (im_nparams Mk)) gs gs1 (ca_arg r A :: gs2) ms) in Em'
    by (first [ exact Heq | rewrite List.length_rev, Hlm; reflexivity | apply length_nonrec_arg_vals; exact Hlv ]).
  pose proof (per_univ_trans _ _ _ _ _ _ HRm (per_univ_sym _ _ _ _ HRm)) as HRmm.
  exists i0, Rm, m; split; [ exact Em | split; [ exact HRmm |] ].
  unfold canon_args_rel, nth_atyp; rewrite HM, Hcon, (List.nth_error_nth _ _ _ HA), (member_nparams_eq _ _ _ HM),
    (member_con_tele_eq _ _ _ _ _ HM Hcon).
  exact (per_head_right Em Em' HRm).
Qed.

(** The type of a non-recursive argument in the constructor's context and
    at the non-recursive values alone (readback's fresh variables'):
    related types. *)
Lemma valid_group_arg_types : forall pq G, valid_group pq G -> containers_valid G ->
    forall k Mk c gs gs1 r A gs2 U ms vs, ind_member G k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_arg r A :: gs2 ->
    List.length U = ind_nu G -> List.length ms = im_nn Mk -> List.length vs = List.length gs1 ->
    per_tele_args (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) nil nil (U ++ ms ++ vs) (U ++ ms ++ vs) ->
    exists (i : nat) R a a', ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs) ↘ a /\
      ⟦ A ⟧ components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (ms ++ nonrec_arg_vals gs1 vs) ↘ a' /\
      DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  intros pq G Hg Hcv k Mk c gs gs1 r A gs2 U ms vs HM Hcon Heq HlU Hlm Hlv Hgp.
  pose proof (valid_group_valid _ _ Hg) as HD.
  destruct (valid_group_cargs_sem_all pq G Hg Hcv k Mk c gs HM Hcon gs1 (ca_arg r A :: gs2) Heq) as [HW Hw].
  assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
    by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
  pose proof (nonrec_kind_at gs1 gs2 r A) as Hr; rewrite <- Heq in Hr.
  destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ _ HM Hcon HA Hr) as (_ & j & HAv).
  rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HAv.
  destruct (rel_ctx_wf_per_ctx_env HW) as [RΓ HΓ].
  assert (Hρ : RΓ (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs))
                  (env_tele nil (List.rev (cargs_ctx pq G Mk gs1 ++ im_params G Mk)) (U ++ ms ++ vs))).
  { apply (tele_args_env_rel _ _ _ _ _ _ HΓ HW); [| exact Hgp ].
    rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
  destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_abs_kind_sort HAv) HΓ Hρ) as (i0 & Rm & m & m' & Em & Em' & HRm).
  rewrite (ctx_retag_wk_cargs_args pq G Mk gs1 U ms vs) in Em' by (try exact Hlv; rewrite length_im_params; unfold im_np, ind_nu in *; lia).
  rewrite (closed_env_nonrec_args_components G Mk gs1 U ms) in Em' by assumption.
  exists i0, Rm, m, m'; split; [ exact Em | split; [ exact Em' | exact HRm ] ].
Qed.

(** The type of a domain of a recursive argument's shape, after [d] of
    them, at arguments related at the context of those before: its relation
    is the canonical one of the domain at the non-recursive values. *)
Lemma valid_group_dom_head : forall pq G, valid_group pq G -> containers_valid G ->
    forall k Mk c gs gs1 t gs2 d B U ms vs ys, ind_member G k = Some Mk -> ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (ptyp_doms t) d = Some B ->
    List.length U = ind_nu G -> List.length ms = im_nn Mk -> List.length vs = List.length gs1 -> List.length ys = d ->
    per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk)) nil nil
      (U ++ ms ++ vs ++ ys) (U ++ ms ++ vs ++ ys) ->
    exists (i : nat) R b, ⟦ B[wk_pat (List.repeat false d ++ cargs_pat gs1)]ʷ ⟧
        env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk))
          (U ++ ms ++ vs ++ ys) ↘ b /\
      DF b ≈ b ∈ per_univ_elem i ↘ R /\
      (R <~> canon_doms_rel G U k (ms ++ nonrec_arg_vals gs1 vs ++ ys)
               (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t)) B).
Proof.
  intros pq G Hg Hcv k Mk c gs gs1 t gs2 d B U ms vs ys HM Hcon Heq HB HlU Hlm Hlv Hly Hgp.
  pose proof (valid_group_valid _ _ Hg) as HD.
  assert (Hd : d <= List.length (ptyp_doms t)) by (assert (d < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
  destruct (valid_group_cargs_sem_all pq G Hg Hcv k Mk c gs HM Hcon gs1 (ca_rec t :: gs2) Heq) as [HW0 Hw0].
  pose proof (shape_domains_ctx_wk_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq Hw0 d Hd) as Hw.
  pose proof (shape_domains_ctx_sem_gen G pq k Mk c gs HD HM Hcon gs1 t gs2 Heq HW0 Hw0 d Hd) as HW.
  destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
  rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
  destruct (rel_ctx_wf_per_ctx_env HW) as [RΓ HΓ].
  set (E := env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t)) ++ cargs_ctx pq G Mk gs1 ++ im_params G Mk))
              (U ++ ms ++ vs ++ ys)).
  assert (Hρ : RΓ E E).
  { apply (tele_args_env_rel _ _ _ _ _ _ HΓ HW); [| exact Hgp ].
    rewrite !List.length_app, length_shape_domains_ctx, List.length_firstn, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia. }
  destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_typ HBv) HΓ Hρ) as (i0 & Rm & m & m' & Em & Em' & HRm).
  (** The weakened environment, retagged: the components. *)
  assert (Hlf : List.length (List.firstn d (ptyp_doms t)) = d) by (rewrite List.length_firstn; lia).
  assert (HE : ctx_retag (doms_ctx (List.firstn d (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params G Mk)
                 (⟪wk_pat (List.repeat false d ++ cargs_pat gs1)⟫ E)
               = components_env G U (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn d (shape_doms_tele t))
                   (ms ++ nonrec_arg_vals gs1 vs ++ ys)).
  { unfold E; replace (List.repeat false d) with (List.repeat false (List.length (List.firstn d (ptyp_doms t)))) by (rewrite Hlf; reflexivity).
    rewrite (List.app_assoc U ms (vs ++ ys)).
    rewrite (ctx_retag_wk_cargs_doms pq G Mk gs1 (cargs_pat gs1) (List.firstn d (ptyp_doms t)) (U ++ ms) vs ys eq_refl)
      by (first [ rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | exact Hlv | lia ]).
    rewrite <- (List.app_assoc U ms), closed_env_shape_doms_components by exact HlU.
    unfold shape_doms_tele; rewrite List.firstn_map; reflexivity. }
  rewrite HE in Em'.
  pose proof (per_univ_trans _ _ _ _ _ _ HRm (per_univ_sym _ _ _ _ HRm)) as HRmm.
  exists i0, Rm, m; split; [ exact Em | split; [ exact HRmm |] ].
  unfold canon_doms_rel.
  exact (per_head_right Em Em' HRm).
Qed.

(** ** Coherence of a View, and the Relation of its Type

    [view_agreement_canonical p D ups ups' j]: the elements of the view [j] of [D] at
    the canonical relations at [ups] and [ups'] cohere with those of its
    container's member at the view's instance there ([view_agreement]).
    [view_end_rel]: the relation of the view's type, the container's at
    any uniform parameters related to the instance, is the group's at the
    view. *)
(** A family [P] of filed groups, each valid, closed under the containers
    of their views (e.g. the groups filed in the source of a sound
    embedding); then the containers of each are valid. *)
Record valid_groups (P : qname -> ind_decl -> Prop) : Prop := mk_valid_groups
  { (** Each group of [P] is valid *)
    valid_groups_valid : forall qn G, P qn G -> valid_group qn G
    (** The containers of its views are in [P] *)
  ; valid_groups_containers : forall qn G k Mk qc kc Is vm Dq, P qn G -> ind_member G k = Some Mk ->
      im_head Mk = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq -> P qc Dq }.

Lemma containers_valid_of_groups : forall P, valid_groups P -> forall qn D, P qn D -> containers_valid D.
Proof.
  intros P HP qn D HD k Mk qc k' Is vm Dq HM Hh Hq.
  exact (valid_groups_valid _ HP _ _ (valid_groups_containers _ HP _ _ _ _ _ _ _ _ _ HD HM Hh Hq)).
Qed.

(** The elements of the view [j] at the canonical relations at [ups] and
    [ups'] cohere with those of its container's member at the view's
    instance there ([view_agreement]). *)
Definition view_agreement_canonical (p : qname) (D : ind_decl) (ups ups' : list domain) (j : nat) : Prop :=
  forall Mj qc kc Is vm Dq cups cups', ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups' ↘ cups' ->
    view_agreement p D ups ups' (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
      qc Dq cups cups' (canon_nparams_rel Dq cups) (canon_args_rel Dq cups) (canon_doms_rel Dq cups) vm.

(** The relation of the view [j]'s type, the container's member at any
    uniform parameters related to the instance, is the group's at the
    view. *)
Definition view_end_rel (p : qname) (D : ind_decl) (ups ups' : list domain) (j : nat) : Prop :=
  forall Mj qc kc Is vm Dq cups cups', ind_member D j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups' ↘ cups' ->
    forall cs cs' ns ns' (i : universe_index) R,
      per_tele_args (List.rev (ind_uparams Dq)) nil nil cups cs -> per_tele_args (List.rev (ind_uparams Dq)) nil nil cups' cs' ->
      DF d_ind qc kc (cs ++ ns) ≈ d_ind qc kc (cs' ++ ns') ∈ per_univ_elem i ↘ R ->
      (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups' ns ns').

(** The relation of the record view [j]'s type, the record at any
    arguments related to the view's instance, is the group's at the record
    view (which has no non-uniform parameter). *)
Definition rview_end_rel (p : qname) (D : ind_decl) (ups ups' : list domain) (j : nat) : Prop :=
  forall Mj qr Is fl R cups cups', ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    record_lookup gc_deps gc_stack qr = Some R ->
    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups' ↘ cups' ->
    forall cs cs' (i : universe_index) Rel,
      per_tele_args (List.rev (record_params R)) nil nil cups cs -> per_tele_args (List.rev (record_params R)) nil nil cups' cs' ->
      DF d_record qr cs ≈ d_record qr cs' ∈ per_univ_elem i ↘ Rel ->
      (Rel <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups' nil nil).

Lemma view_end_rel_of_agreement : forall p D, valid_group p D -> containers_valid D ->
    forall ups ups', per_tele_args (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
    forall j, view_agreement_canonical p D ups ups' j -> view_end_rel p D ups ups' j.
Proof.
  intros p D Hg Hcv ups ups' Hgu Hu j Hcoh Mj qc kc Is vm Dq cups cups' HMj Hh Hq Ec Ec' cs cs' ns ns' i R Hcs Hcs' HR.
  pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
  pose proof (valid_group_typed _ _ Hg) as Hdt.
  destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMj Hh) as (D2 & Mk' & Hl2 & HMk' & Hkd & HIl & _ & Hvm & _).
  rewrite Hq in Hl2; injection Hl2 as <-.
  assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
  { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
    unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate .. ]. }
  destruct Hhd as [pm Hhd].
  destruct (valid_group_views_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hcu).
  pose proof (functional_eval_exps' _ _ _ _ E0 Ec) as <-; pose proof (functional_eval_exps' _ _ _ _ E0' Ec') as <-.
  assert (Hlc : List.length c0 = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ E0); exact HIl).
  destruct (valid_group_type_rel_base qc Dq HgQ _ _ _ _ _ _ _ _ _ _ _ HMk' Hhd Hcu Hlc Hcs Hcs' HR) as [Hbase _].
  pose proof (Hcoh _ _ _ _ _ _ _ _ HMj Hh Hq E0 E0') as Hvc.
  destruct (agree_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc _ _ HMk') as (v & Mv & Hvmb).
  assert (v = j) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mj) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HMj in HMv; congruence).
  pose proof (valid_group_canon p D Hg ups (uparams_refl_l D (valid_group_valid _ _ Hg) (valid_group_closed _ _ Hg) _ _ Hgu) Hu) as Hcp.
  pose proof (valid_group_canon qc Dq HgQ c0 (uparams_refl_l Dq (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hcu) Hlc) as HcpQ.
  destruct Hcp as [HnP HnI HaP HaI HdP HdI]; destruct HcpQ as [HnP' HnI' HaP' HaI' HdP' HdI'].
  intros x y; split; intro Hxy.
  - apply Hbase in Hxy.
    exact (view_container_to_group p D ups ups' _ _ _ (valid_group_ass _ _ Hg) HnP HnI HaP HaI HdP HdI qc Dq c0 c0' _ _ _ (valid_group_ass _ _ HgQ)
             HnP' HnI' HaP' HaI' HdP' HdI' vm Hvc kc Mk' j Mj ns ns' x y HMk' Hvmb Hxy).
  - apply Hbase.
    exact (view_group_to_container p D ups ups' _ _ _ (valid_group_ass _ _ Hg) HnP HnI HaP HaI HdP HdI qc Dq c0 c0' _ _ _ (valid_group_ass _ _ HgQ)
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

Lemma eval_mty_inv : forall (pq : qname) D j Mj Us Ns ρ a, ind_member D j = Some Mj -> im_is_rview Mj = false ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ a ->
    exists cs bs, ⟦ im_pre Mj Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ cs /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs /\
      a = d_ind (fst (im_ref pq j Mj)) (snd (im_ref pq j Mj)) (cs ++ bs).
Proof.
  intros * HM Hrv Ea; unfold ind_mty, im_ty_at in Ea; rewrite HM in Ea.
  unfold im_is_rview in Hrv; destruct (im_head Mj) eqn:Hh; try discriminate Hrv;
    apply eval_apps_exp_ind in Ea as (ls & Els & Eap);
    apply eval_exps_app_inv in Els as (cs & bs & -> & Ecs & Ebs);
    exists cs, bs; (split; [ exact Ecs | split; [ exact Ebs |] ]);
    exact (apps_ind_val _ _ _ _ _ Eap).
Qed.

(** The type of a record view at uniform arguments: the record at the
    values of the instance; a record view has no non-uniform
    parameter. *)
Lemma apps_record_val : forall (qn : qname) ys xs r,
    $*| d_record qn xs & ys | gc_deps ⍮ gc_stack ↘ r -> r = d_record qn (xs ++ ys).
Proof.
  induction ys as [| y ys IH]; intros xs r H; inversion H; subst; [ rewrite List.app_nil_r; reflexivity |].
  match goal with Ha : $| d_record _ _ & _ | _ ⍮ _ ↘ _ |- _ => inversion Ha; subst end.
  match goal with Hr : $*| d_record _ (xs ++ y :: nil) & ys | _ ⍮ _ ↘ _ |- _ => rewrite (IH _ _ Hr), <- List.app_assoc; reflexivity end.
Qed.

Lemma eval_mty_inv_rview : forall (pq : qname) D j Mj qr Is fl Us Ns ρ a, ind_member D j = Some Mj ->
    im_head Mj = mh_record qr Is fl ->
    ⟦ ind_mty pq D j Us Ns ⟧ ρ ↘ a ->
    exists cs bs, ⟦ im_pre Mj Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ cs /\ ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs /\
      a = d_record qr (cs ++ bs).
Proof.
  intros * HM Hh Ea; unfold ind_mty, im_ty_at in Ea; rewrite HM, Hh in Ea.
  apply eval_apps_exp_record in Ea as (ls & Els & Eap).
  apply eval_exps_app_inv in Els as (cs & bs & -> & Ecs & Ebs).
  exists cs, bs; split; [ exact Ecs | split; [ exact Ebs |] ].
  exact (apps_record_val _ _ _ _ Eap).
Qed.

(** The record of a record view at related parameters: related types, of
    the canonical record relation at the left parameters. *)
Lemma vrr_type_rel : forall qr R cups cs, valid_rview_record qr R ->
    per_tele_args (List.rev (record_params R)) nil nil cups cs -> List.length cups = List.length (record_params R) ->
    exists (i : universe_index), DF d_record qr cups ≈ d_record qr cs ∈ per_univ_elem i ↘ record_rel R (canon_fields_rel R cups).
Proof.
  intros * [Hl Hv Hc Ht] Hg Hu.
  destruct Hv as [HP HPr [i HS] HF HT HFk].
  pose proof (typed_params_ass _ _ _ Ht) as Hass.
  destruct (Records.Model.sort_tele_value (record_params R) (record_sort R) HP (ex_intro _ i HS) cups
              (Records.Model.record_params_args_refl_l (record_params R) HP Hass _ _ Hg) Hu) as [a Ha].
  exists (univ_idx a).
  exact (Records.Model.record_relate qr R Hl (typed_nodup _ _ _ Ht) (record_typed_sort_univ _ _ _ Ht) HF
           (ex_intro _ i HS) HT HFk _ _ _ Hg Hu Ha).
Qed.

Section ShapeChar.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.

  (** At a declared member there is no view to cohere. *)
  Lemma view_end_rel_decl : forall ups ups' j Mj pm, ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      view_end_rel p D ups ups' j.
  Proof.
    intros * HM Hh Mj' qc kc Is vm Dq cups cups' HM' Hh'.
    rewrite HM in HM'; injection HM' as <-; rewrite Hh in Hh'; discriminate.
  Qed.

  (** At a member that is not a record view there is no record to
      cohere. *)
  Lemma rview_end_rel_not_rview : forall ups ups' j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false ->
      rview_end_rel p D ups ups' j.
  Proof.
    intros * HM Hrv Mj' qr Is fl R cups cups' HM' Hh'.
    rewrite HM in HM'; injection HM' as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv Hh').
  Qed.

  (** The instance of a record view [j] at the group's uniform parameters
      as variables, after more variables [zs] related to themselves:
      related to its instance at [ups]. *)
  Lemma rview_pre_values : forall j Mj qr Is fl R ups Z RZ zs nn L cs, ind_member D j = Some Mj ->
      im_head Mj = mh_record qr Is fl -> valid_rview_record qr R ->
      List.length ups = ind_nu D -> per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
      ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
      List.length zs = List.length Z -> L + nn = List.length zs ->
      RZ (components_env D ups (List.rev Z) zs) (components_env D ups (List.rev Z) zs) ->
      ⟦ im_pre Mj (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ cs ->
      exists cups, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups /\ per_tele_args (List.rev (record_params R)) nil nil cups cs.
  Proof.
    intros * HMj Hh HR Hu Hgu HZ HRZ Hlz HL HE Ecs.
    unfold im_pre in Ecs; rewrite Hh in Ecs.
    assert (HIs : List.map (fun I => I[sb_of_list Id (ind_uvars D nn L)]) Is = List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is).
    { pose proof (decl_closed_rhead_scoped _ Hc _ _ _ _ _ HMj Hh) as Hs.
      pose proof (proj1 (proj2 (decl_mvc_members _ (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)) _ _ HMj))) as Hm.
      rewrite Hh in Hm; cbn in Hm.
      apply List.map_ext_in; intros I HI; unfold ind_uvars.
      rewrite (exp_at_vars _ _ _ (proj1 (List.Forall_forall _ _) Hs I HI) (proj1 (List.Forall_forall _ _) Hm I HI)), HL, Hlz.
      reflexivity. }
    rewrite HIs in Ecs.
    destruct (valid_group_views_rview_args_wk p D Hg _ _ _ _ _ _ HMj Hh HR Z RZ ups zs HZ HRZ Hlz Hu Hgu HE)
      as (cups & cs0 & Ecups & Ecs0 & Hgc).
    pose proof (functional_eval_exps' _ _ _ _ Ecs0 Ecs) as ->.
    exists cups; split; [ exact Ecups | exact Hgc ].
  Qed.

  (** The uniform arguments of a view [j] at the group's uniform parameters
      as variables, after more variables [zs] related to themselves: related
      to its instance at [ups]. *)
  Lemma view_pre_values : forall j Mj qc kc Is vm Dq ups Z RZ zs nn L cs, ind_member D j = Some Mj ->
      im_head Mj = mh_view qc kc Is vm -> ind_lookup gc_deps gc_stack qc = Some Dq ->
      List.length ups = ind_nu D -> per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
      ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
      List.length zs = List.length Z -> L + nn = List.length zs ->
      RZ (components_env D ups (List.rev Z) zs) (components_env D ups (List.rev Z) zs) ->
      ⟦ im_pre Mj (ind_uvars D nn L) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ cs ->
      exists cups, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups /\ per_tele_args (List.rev (ind_uparams Dq)) nil nil cups cs.
  Proof.
    intros * HMj Hh Hq Hu Hgu HZ HRZ Hlz HL HE Ecs.
    unfold im_pre in Ecs; rewrite Hh in Ecs.
    assert (HIs : List.map (fun I => I[sb_of_list Id (ind_uvars D nn L)]) Is = List.map (fun I => I[wk_shiftn (List.length Z)]ʷ) Is).
    { pose proof (decl_closed_head_scoped _ Hc _ _ _ _ _ _ HMj Hh) as Hs.
      pose proof (proj1 (proj2 (decl_mvc_members _ (decl_typed_mvc _ _ _ (valid_group_typed _ _ Hg)) _ _ HMj))) as Hm.
      rewrite Hh in Hm; cbn in Hm.
      apply List.map_ext_in; intros I HI; unfold ind_uvars.
      rewrite (exp_at_vars _ _ _ (proj1 (List.Forall_forall _ _) Hs I HI) (proj1 (List.Forall_forall _ _) Hm I HI)), HL, Hlz.
      reflexivity. }
    rewrite HIs in Ecs.
    destruct (valid_group_views_view_args_wk p D Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq Z RZ ups zs HZ HRZ Hlz Hu Hgu HE)
      as (cups & cs0 & Ecups & Ecs0 & Hgc).
    pose proof (functional_eval_exps' _ _ _ _ Ecs0 Ecs) as ->.
    exists cups; split; [ exact Ecups | exact Hgc ].
  Qed.

  (** The type of the member [j] at the group's uniform parameters as
      variables, after more variables [zs] related to themselves, and at
      non-uniform arguments of values [bs]: its relation is the group's at
      [j], at a view by [view_end_rel]. *)
  Lemma mty_end_rel : forall j Mj ups Z RZ zs nn L Ns bs a i R, ind_member D j = Some Mj ->
      List.length ups = ind_nu D -> per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
      ⊨ Z ++ ind_uparams D -> EF Z ++ ind_uparams D ≈ Z ++ ind_uparams D ∈ per_ctx_env ↘ RZ ->
      List.length zs = List.length Z -> L + nn = List.length zs ->
      RZ (components_env D ups (List.rev Z) zs) (components_env D ups (List.rev Z) zs) ->
      List.length Ns = im_nn Mj ->
      ⟦ Ns ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ bs ->
      ⟦ ind_mty p D j (ind_uvars D nn L) Ns ⟧ components_env D ups (List.rev Z) zs ↘ a ->
      DF a ≈ a ∈ per_univ_elem i ↘ R -> view_end_rel p D ups ups j -> rview_end_rel p D ups ups j ->
      (R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) j ups ups bs bs).
  Proof.
    intros * HMj Hu Hgu HZ HRZ Hlz HL HE HlN Ebs Ea HR Hend Hrend.
    destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
    - destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Ea) as (cs & bs' & Ecs & Ebs' & ->).
      pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
      unfold im_pre, im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
      assert (HU : ⟦ ind_uvars D nn L ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) zs ↘ ups)
        by (apply eval_uvars_components; lia).
      pose proof (functional_eval_exps' _ _ _ _ Ecs HU) as ->.
      exact (proj1 (valid_group_type_rel_base p D Hg j Mj pm ups ups ups ups bs bs i R HMj Hh Hgu Hu Hgu Hgu HR)).
    - destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Ea) as (cs & bs' & Ecs & Ebs' & ->).
      pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
      unfold im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
      destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & _).
      destruct (view_pre_values _ _ _ _ _ _ _ _ _ _ _ _ _ cs HMj Hh Hq Hu Hgu HZ HRZ Hlz HL HE Ecs) as (cups & Ecups & Hgc).
      exact (Hend _ _ _ _ _ _ _ _ HMj Hh Hq Ecups Ecups cs cs bs bs i R Hgc Hgc HR).
    - (** A record view: the record at the instance, of no non-uniform
          parameter, by [rview_end_rel]. *)
      destruct (eval_mty_inv_rview _ _ _ _ _ _ _ _ _ _ _ HMj Hh Ea) as (cs & bs' & Ecs & Ebs' & ->).
      pose proof (functional_eval_exps' _ _ _ _ Ebs' Ebs) as ->.
      pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as Hnp.
      unfold im_nn in HlN; rewrite Hnp in HlN; destruct Ns; [| discriminate HlN ].
      inversion Ebs; subst; rewrite List.app_nil_r in HR.
      destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R0 HR0].
      destruct (rview_pre_values _ _ _ _ _ _ _ _ _ _ _ _ cs HMj Hh HR0 Hu Hgu HZ HRZ Hlz HL HE Ecs) as (cups & Ecups & Hgc).
      exact (Hrend _ _ _ _ _ _ _ HMj Hh (valid_rview_record_lookup _ _ HR0) Ecups Ecups cs cs i R Hgc Hgc HR).
  Qed.

  Section ShapeMember.
    Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
    Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
    Hypothesis (HΨ : ⊨ cargs_ctx p D Mk gs ++ im_params D Mk).

    (** ** The Rest of a Shape is a Type

        After the first [kk] domains of a recursive argument's shape, the
        type of the rest of the shape is a type of a universe. *)
    Lemma shape_prefix_valid : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall kk, kk <= List.length (ptyp_doms t) ->
        exists j : nat, shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
          ⊨ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) : Typeω@j.
    Proof.
      intros gs1 t gs2 Heq kk Hk.
      destruct (valid_group_cargs_sem_all p D Hg Hcv k Mk c gs HM Hcon gs1 (ca_rec t :: gs2) Heq) as [HC Hw].
      destruct (valid_group_shape_leaf p D Hg Hcv k Mk c gs gs1 t gs2 HM Hcon Heq HC Hw) as [j Hleaf].
      pose proof (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq _ (le_n _)) as HΦ.
      rewrite List.firstn_all in HΦ.
      rewrite (shape_domains_ctx_split _ _ kk), <- List.app_assoc in Hleaf, HΦ.
      rewrite ptyp_ty_ctx_pi, ptyp_doms_skip, ptyp_mem_skip, ptyp_ps_skip.
      rewrite (List.app_assoc (List.repeat false _) (List.repeat false kk) (cargs_pat gs1)), <- List.repeat_app, List.length_skipn,
        Nat.sub_add by exact Hk.
      exact (rel_exp_ctx_pi _ _ _ _ (shape_domains_ctx_ass _ _) HΦ Hleaf).
    Qed.

    (** ** One Step Through a Shape's Domains

        The rest of a shape after [kk + 1] domains, at the extension by an
        argument of the closure of the [kk]-th domain (stored at the
        domain's value, as a [Π]'s codomain is), against it at the
        telescope's extension (stored at the domain's type): related
        types. *)
    Lemma shape_codomain_tele : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall zs ys kk B, List.length zs = List.length (cargs_ctx p D Mk gs1 ++ im_params D Mk) -> List.length ys = kk ->
        List.nth_error (ptyp_doms t) kk = Some B ->
        per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
          nil nil (zs ++ ys) (zs ++ ys) ->
        forall (i : nat) a1 R1,
          ⟦ B[wk_pat (List.repeat false kk ++ cargs_pat gs1)]ʷ ⟧
            env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
              (zs ++ ys) ↘ a1 ->
          DF a1 ≈ a1 ∈ per_univ_elem i ↘ R1 ->
          forall x b, R1 x x ->
          ⟦ ptyp_ty p D (im_nn Mk) (false :: List.repeat false kk ++ cargs_pat gs1) (ptyp_skip (S kk) t) ⟧
            env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
              (zs ++ ys) ↦ x ⦂ entry_type_value a1 ↘ b ->
          exists (j : nat) Rb b',
            ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false (S kk) ++ cargs_pat gs1) (ptyp_skip (S kk) t) ⟧
              env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn (S kk) (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
                (zs ++ ys ++ x :: nil) ↘ b' /\
            DF b ≈ b' ∈ per_univ_elem j ↘ Rb.
    Proof.
      intros gs1 t gs2 Heq zs ys kk B Hlz Hly HB Hgz i a1 R1 Eb HR1 x b Hx Eb2.
      assert (Hk : kk < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      set (pat' := List.repeat false kk ++ cargs_pat gs1).
      set (Γk := shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk) in *.
      set (Et := env_tele nil (List.rev Γk) (zs ++ ys)) in *.
      pose proof (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia)) as HWk; fold Γk in HWk.
      destruct (rel_ctx_wf_per_ctx_env HWk) as [RΓ HΓ].
      assert (HlΓ : List.length (zs ++ ys) = List.length Γk)
        by (unfold Γk; rewrite !List.length_app, length_shape_domains_ctx, List.length_firstn in *; lia).
      assert (Hρ : RΓ Et Et) by exact (tele_args_env_rel _ _ _ _ _ _ HΓ HWk HlΓ Hgz).
      (** The domain, weakened, is a type there. *)
      pose proof (shape_domains_ctx_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia)) as Hw; fold Γk pat' in Hw.
      destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & jB & HBv).
      rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
      pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
      pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HBw)) as HΓB.
      (** The two extensions are related. *)
      pose proof (per_head_of Eb Eb HR1 Hx) as Hh.
      destruct (per_head_closure_readable HΓB HΓ Hρ Hh) as [Rt _].
      pose proof (entry_readable_of_elem HR1 Hx) as [Rv _].
      assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
      assert (Htag : per_env_extend B[wk_pat pat']ʷ B[wk_pat pat']ʷ RΓ (Et ↦ x ⦂ entry_type_value a1)
                       (Et ↦ x ⦂ entry_type_closure B[wk_pat pat']ʷ Et)).
      { apply per_env_extend_intro'; [ exact Hρ | exact Hh | exact Rv |].
        assert (HlEt : List.length Et = List.length Γk) by (unfold Et; rewrite length_env_tele; cbn; lia).
        unfold centry_tag in Rt; cbn [centry_type] in Rt.
        rewrite <- HlEt, env_upto_exact in Rt; exact Rt. }
      (** The rest of the shape is a type after one more domain. *)
      assert (HSk : shape_domains_ctx (cargs_pat gs1) (List.firstn (S kk) (ptyp_doms t)) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk
                    = Γk ▹{ak_relevant} B[wk_pat pat']ʷ)
        by (rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia; reflexivity).
      destruct (shape_prefix_valid gs1 t gs2 Heq (S kk) ltac:(lia)) as [jT HT'].
      rewrite HSk in HT'; cbn [List.repeat List.app] in HT'.
      destruct (rel_exp_of_typ_inversion_simple_at HΓB HT' _ _ Htag) as (b0 & b' & Eb0 & Eb' & [Rb HRb]).
      assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
      exists jT, Rb, b'; split; [| exact HRb ].
      rewrite HSk, List.app_assoc; cbn [List.rev].
      rewrite env_tele_snoc by (rewrite List.length_rev; exact HlΓ).
      exact Eb'.
    Qed.

    (** ** The Parameters a Shape Ends In

        After all the domains [ys] of a recursive argument's shape, related
        to themselves canonically, the parameters of the end evaluate, at
        the non-recursive arguments and at all the arguments (the end's
        type has them weakened past the recursive ones), to values related
        canonically at the member the shape ends in. *)
    Lemma shape_end_params_link : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall ups ns fa ys, List.length ups = ind_nu D -> List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
        per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
        tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
        per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
          nil nil (ups ++ ns ++ fa ++ ys) (ups ++ ns ++ fa ++ ys) ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns (nonrec_arg_vals gs1 fa) t)
          (List.length (ptyp_doms t)) ys ys ->
        ps_link D (canon_nparams_rel D ups) (ptyp_ps t)
          (List.map (fun P => P[wk_pat (List.repeat false (List.length (ptyp_doms t)) ++ cargs_pat gs1)]ʷ) (ptyp_ps t))
          (ptyp_mem t)
          (components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nonrec_arg_vals gs1 fa ++ ys))
          (env_tele nil (List.rev (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
             (ups ++ ns ++ fa ++ ys)).
    Proof.
      intros gs1 t gs2 Heq ups ns fa ys Hlu Hlns Hlk Hgu0 Hnsd INV Hctx Hy.
      destruct (sort_value D HD ups Hgu0 Hlu) as [a0 Ha0].
      set (nv := nonrec_arg_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (pat := cargs_pat gs1) in *.
      set (L := List.length (ptyp_doms t)) in *.
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlk).
      pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
      set (E := env_tele nil (List.rev (shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa ++ ys)).
      set (Ec := components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ns ++ nv ++ ys)).
      (** The arguments weakened past the recursive ones, retagged: the
          components. *)
      assert (HwkE : ctx_retag (doms_ctx (ptyp_doms t) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) (⟪wk_pat (List.repeat false L ++ pat)⟫ E) = Ec).
      { unfold E, Ec, L.
        rewrite (List.app_assoc ups ns (fa ++ ys)).
        rewrite (ctx_retag_wk_cargs_doms p D Mk gs1 pat (ptyp_doms t) (ups ++ ns) fa ys eq_refl)
          by (first [ rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | exact Hlk | exact Hly ]).
        rewrite <- (List.app_assoc ups ns), closed_env_shape_doms_components by exact Hlu; reflexivity. }
      destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
      pose proof (rec_prefix_tele_args D HD Hc Hsu k Mk HM c gs gs1 t gs2 ups ups a0 ns ns nv nv ys ys Hcon Heq Hgu0 Hlu Ha0 Hnsd INV L (le_n _) Hy)
        as Hgall.
      assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
      rewrite Hft in Hgall.
      destruct (rec_closure D HD Hc k Mk HM c gs gs1 t gs2 Mj Hcon Heq HMj ups ups ns ns nv nv ys ys
                  Hlu Hlns Hlnv Hly Hlu Hlns Hlnv Hly Hgall)
        as (bs & bs0 & Ebs & _ & _ & Hil).
      set (pat' := List.repeat false L ++ pat) in *.
      pose proof (shape_domains_ctx_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as Hw; fold pat pat' in Hw.
      rewrite Hft in Hw.
      pose proof (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as HWs; fold pat in HWs.
      rewrite Hft in HWs.
      assert (Hlctx : List.length (ups ++ ns ++ fa ++ ys) = List.length (shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_params D Mk))
        by (rewrite !List.length_app, length_shape_domains_ctx, length_cargs_ctx, length_im_params; unfold im_np; lia).
      assert (HTex : forall m, m < im_nn Mj ->
                 exists Tm, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) m = Some Tm).
      { intros m Hm; apply nth_error_lt_some'.
        rewrite length_tele_insts by exact (member_nparams_ass D Hc _ _ HMj); rewrite length_im_nparams; lia. }
      assert (Hlink : forall m P Tm, List.nth_error (ptyp_ps t) m = Some P ->
                 List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn (ptyp_depth t + K + im_nn Mk))) (ptyp_ps t)) m = Some Tm ->
                 exists b1 b, ⟦ P[wk_pat pat']ʷ ⟧ E ↘ b1 /\ ⟦ P ⟧ Ec ↘ b /\
                   canon_nparams_rel D ups (ptyp_mem t) m (List.firstn m bs) b b1).
      { intros * HP HTm.
        pose proof (valid_ind_decl_rec_field _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HTm) as HPv.
        rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HPv; unfold ptyp_tele in HPv.
        destruct (rel_ctx_wf_per_ctx_env HWs) as [RΓ' HΓ'].
        assert (Hρ : RΓ' E E) by exact (tele_args_env_rel _ _ _ _ _ _ HΓ' HWs Hlctx Hctx).
        destruct (wk_term_retag_link _ _ _ _ _ _ _ Hw HPv HΓ' Hρ)
          as (i1 & Ru & u & u' & Eu & Eu' & HRu & [Hpu | (b1 & b & Eb1 & Eb & Hbb)]);
          rewrite HwkE in Eu'; pose proof (Hil _ _ _ HP HTm) as [Hcan (u0 & Eu0 & Hu0)].
        (** The parameter's type is relevant. *)
        { exfalso; assert (u0 = u') as -> by (eapply functional_eval_exp; eassumption).
          rewrite <- (per_univ_elem_kind _ _ _ _ HRu), Hpu in Hu0; discriminate. }
        rewrite HwkE in Eb.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        pose proof (per_head_iff Eu' Eu' HRuu) as Rel.
        assert (HPu : PER Ru) by (eapply per_elem_PER; exact HRu).
        exists b1, b; split; [ exact Eb1 | split; [ exact Eb | apply Hcan, Rel; symmetry; exact Hbb ] ]. }
      destruct (eval_exps_each (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t)) E) as [bs1 Ebs1].
      { intros m M HMm; rewrite List.nth_error_map in HMm.
        destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; cbn in HMm; [ injection HMm as <- | discriminate ].
        assert (Hm : m < im_nn Mj) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
        destruct (HTex _ Hm) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
      apply (mk_ps_link _ _ _ _ _ _ _ bs bs1 Ebs Ebs1).
      unfold nparams_tele_rel; rewrite HMj.
      rewrite tele_rel_iff, List.length_rev, length_im_nparams.
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
      rewrite Hy1 in Hb0; injection Hb0 as ->; rewrite Hy1' in Hb2; injection Hb2 as ->; exact Hr.
    Qed.

    (** ** A Recursive Argument of a Function Shape

        After [kk] domains [ys] of a recursive argument's shape, related to
        themselves canonically, the relation of the type of the rest of the
        shape is the shape's relation ([rec_arg_rel]) of its rest, given the
        relation of the type of the member the shape ends in
        ([view_end_rel], nothing at a declared member). *)
    Lemma shape_char : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall ups ns fa, List.length ups = ind_nu D -> List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
        per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
        tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
        (forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
           R (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
             (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))) ->
        view_end_rel p D ups ups (ptyp_mem t) -> rview_end_rel p D ups ups (ptyp_mem t) ->
        forall n kk ys a i R, kk + n = List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns (nonrec_arg_vals gs1 fa) t)
            kk ys ys ->
          per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
            (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
            (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) ys ys ->
          ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) ⟧
            env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
              (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)))) ys ↘ a ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          (R <~> rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
                   k ups ups (ns ++ nonrec_arg_vals gs1 fa ++ ys) (ns ++ nonrec_arg_vals gs1 fa ++ ys)
                   (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) (ptyp_skip kk t)).
    Proof.
      intros gs1 t gs2 Heq ups ns fa Hlu Hlns Hlk Hgu0 Hnsd INV Hpre Hend Hrend.
      destruct (valid_group_canon p D Hg ups Hgu0 Hlu) as [CnP CnI CaP CaI CdP CdI].
      pose proof (valid_group_adm p D Hg ups ups Hgu0 Hlu Hgu0) as Cad.
      destruct (sort_value D HD ups Hgu0 Hlu) as [a0 Ha0].
      destruct (ind_rel_pre_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI ups Cad Cad) as (_ & _ & Hprer & _).
      set (nv := nonrec_arg_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (pat := cargs_pat gs1) in *.
      set (C := cargs_ctx p D Mk gs1 ++ im_params D Mk) in *.
      set (Ef := env_tele nil (List.rev C) (ups ++ ns ++ fa)) in *.
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlk).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (HlC : List.length (ups ++ ns ++ fa) = List.length C)
        by (unfold C; rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      pose proof (cargs_prefix_sem D p Mk gs HΨ gs1 (ca_rec t :: gs2) Heq) as HCs; fold C in HCs.
      (** The environment of the arguments and [kk] domains, closed. *)
      assert (HEcl : forall kk ys, env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
                                   = env_tele nil (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C)) (ups ++ ns ++ fa ++ ys)).
      { intros kk ys; unfold Ef.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite (env_tele_closed_app C _ (ups ++ ns ++ fa) ys) by exact HlC; reflexivity. }
      (** Weakened past the recursive arguments and retagged: the
          components. *)
      assert (HwkE : forall kk ys, kk <= List.length (ptyp_doms t) -> List.length ys = kk ->
                 ctx_retag (doms_ctx (List.firstn kk (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)
                   (⟪wk_pat (List.repeat false kk ++ pat)⟫ (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys))
                 = components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) (ns ++ nv ++ ys)).
      { intros kk ys Hk Hly.
        assert (Hlf : List.length (List.firstn kk (ptyp_doms t)) = kk) by (rewrite List.length_firstn; lia).
        rewrite HEcl; unfold C.
        replace (List.repeat false kk) with (List.repeat false (List.length (List.firstn kk (ptyp_doms t)))) by (rewrite Hlf; reflexivity).
        rewrite (List.app_assoc ups ns (fa ++ ys)).
        rewrite (ctx_retag_wk_cargs_doms p D Mk gs1 pat (List.firstn kk (ptyp_doms t)) (ups ++ ns) fa ys eq_refl)
          by (first [ rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | exact Hlk | lia ]).
        rewrite <- (List.app_assoc ups ns), closed_env_shape_doms_components by exact Hlu.
        unfold shape_doms_tele; rewrite List.firstn_map; reflexivity. }
      (** The arguments before, as arguments of their telescope. *)
      assert (Hgpf : per_tele_args (List.rev C) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
      { destruct (rel_ctx_wf_per_ctx_env HCs) as [R0 HR0].
        assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HCs).
        assert (HR0' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ R0)
          by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
        assert (Hl0 : List.length (tele_entries nil (List.rev C) (ups ++ ns ++ fa)) = List.length (List.rev C))
          by (rewrite tele_entries_length, List.length_rev; exact HlC).
        assert (Hta : all_assumptions (List.rev C))
          by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HM) ]).
        pose proof (proj2 (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (Hpre _ HR0))) as H.
        rewrite tele_entries_values in H; exact H. }
      (** The environment of the arguments and [kk] domains, in the context
          of their types. *)
      assert (Henv : forall kk ys, kk <= List.length (ptyp_doms t) -> List.length ys = kk ->
                 per_tele_args (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) Ef Ef ys ys ->
                 forall R0, EF shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C
                              ≈ shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C ∈ per_ctx_env ↘ R0 ->
                   R0 (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys)
                      (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys)).
      { intros kk ys Hk Hly Hgy R0 HR0.
        destruct (rel_ctx_wf_per_ctx_env HCs) as [RC HRC].
        apply (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRC HR0 (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk Hk)
                 (Hpre _ HRC)); [ rewrite length_shape_domains_ctx, List.length_firstn; lia | exact Hgy ]. }
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
           match goal with Hx : eval_exp _ _ (B[wk_pat pat']ʷ) _ _ |- _ => rename Hx into Eb end.
           match goal with Hx : _ <~> pi_elements _ _ _ _ |- _ => rename Hx into HE end.
           match goal with Hx : forall c0 c' (_ : _ c0 c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename Hx into Hcod end.
           match goal with Hx : PER _ |- _ => rename Hx into HPin end.
           match goal with Hx : forall c0 c', _ c0 c' -> rel_typ_kind _ _ _ |- _ => rename Hx into HcodS end.
           pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
           pose proof (shape_domains_ctx_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia)) as Hw; fold pat C in Hw.
           destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
           rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
           set (Et := env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys) in *.
           destruct (rel_exp_of_typ_wk_relevant Hw HBv) as (RΓ & HΓ & Hwk).
           pose proof (Henv kk ys ltac:(lia) Hly Hgy RΓ HΓ) as Hρ.
           destruct (Hwk _ _ Hρ) as (m & m' & Em & Em' & [[Rm HRm] Hrm _]).
           assert (m = a1) as -> by (eapply functional_eval_exp; eassumption).
           (** The domain's type at the components. *)
           destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_typ HBv) HΓ Hρ) as (j3 & R3 & a1' & a3 & Ea1' & Ea3 & HR3).
           assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
           rewrite (HwkE kk ys ltac:(lia) Hly) in Ea3.
           set (Ts := List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) in *.
           assert (Ein : in_rel <~> R3) by (eapply per_univ_elem_right_irrel; [ exact equiv_a_a' | exact HR3 ]).
           pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR3) HR3) as HR3'.
           (** The domain's relation is the one of its type, weakened. *)
           assert (Edr : canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B <~> in_rel).
           { unfold canon_doms_rel.
             pose proof (per_head_iff Ea3 Ea3 HR3') as Q.
             intros u v; split; intro Huv.
             - apply Ein; apply Q in Huv; exact Huv.
             - apply Q; apply Ein; exact Huv. }
           assert (HdrP : PER (canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B)).
           { split; intros u v; [ intro Huv | intros w Huv Hvw ]; apply Edr; apply Edr in Huv;
               [ symmetry; exact Huv | apply Edr in Hvw; etransitivity; eassumption ]. }
           (** The telescope after one more domain. *)
           assert (HTs : List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn (S kk) (shape_doms_tele t) = Ts ++ ce_ass ak_relevant B :: nil).
           { unfold Ts; rewrite (firstn_S_snoc _ _ _ (ltac:(unfold shape_doms_tele; rewrite List.nth_error_map, HB; reflexivity)
                                                    : List.nth_error (shape_doms_tele t) kk = Some (ce_ass ak_relevant B))).
             rewrite <- !List.app_assoc; reflexivity. }
           (** The context after one more domain, and its environments: the
               closure's extension at the domain's value and the
               telescope's at the domain's type are related. *)
           pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
           pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HBw)) as HΓB.
           assert (HSk : shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)) ++ C = (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C) ▹{ak_relevant} B[wk_pat pat']ʷ)
             by (rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia; reflexivity).
           assert (HEt : forall c0, env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)))) (ys ++ c0 :: nil)
                                    = Et ↦ c0 ⦂ entry_type_closure B[wk_pat pat']ʷ Et).
           { intros c0; rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
             cbn [List.rev]; rewrite env_tele_snoc by (rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia).
             reflexivity. }
           pose proof (per_univ_trans _ _ _ _ _ _ HRm (per_univ_sym _ _ _ _ HRm)) as HRmd.
           change (per_univ_elem j Rm a1 a1) in HRmd.
           assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
           assert (Htag : forall c0, in_rel c0 c0 ->
                     per_env_extend B[wk_pat pat']ʷ B[wk_pat pat']ʷ RΓ (Et ↦ c0 ⦂ entry_type_value a1) (Et ↦ c0 ⦂ entry_type_closure B[wk_pat pat']ʷ Et)).
           { intros c0 Hc0.
             pose proof (proj1 (Ein _ _) Hc0) as Hc0'.
             assert (HRm3 : Rm <~> R3) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRm HR3).
             pose proof (proj2 (HRm3 _ _) Hc0') as Hcm.
             pose proof (per_head_of Eb Eb HRmd Hcm) as Hh.
             destruct (per_head_closure_readable HΓB HΓ Hρ Hh) as [Rt _].
             pose proof (entry_readable_of_elem HRmd Hcm) as [Rv _].
             apply per_env_extend_intro'; [ exact Hρ | exact Hh | exact Rv |].
             assert (HlEt : List.length Et = List.length (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C)).
             { unfold Et, Ef; rewrite !length_env_tele; cbn [List.length].
               rewrite (List.length_app (shape_domains_ctx _ _) C), length_shape_domains_ctx, List.length_firstn; lia. }
             unfold centry_tag in Rt; cbn [centry_type] in Rt.
             rewrite <- HlEt, env_upto_exact in Rt; exact Rt. }
           (** The codomain at related arguments, by the induction. *)
           assert (Hcodr : forall c0 c0' (Hin : in_rel c0 c0'), exists a2,
                      ⟦ ptyp_ty p D (im_nn Mk) (false :: pat') t' ⟧ Et ↦ c0 ⦂ entry_type_value a1 ↘ a2 /\
                      (out_rel c0 c0' Hin <~> rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups))
                                                (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) k ups ups
                                                ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c0 :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t')).
           { intros c0 c0' Hin.
             assert (Hin0 : in_rel c0 c0) by (etransitivity; [ exact Hin | symmetry; exact Hin ]).
             destruct (Hcod _ _ Hin) as [a2 a2' Ea2 Ea2' HR2].
             exists a2; split; [ exact Ea2 |].
             (** The rest of the shape at the closure's extension and at
                 the telescope's: related types. *)
             destruct (shape_prefix_valid gs1 t gs2 Heq (S kk) ltac:(lia)) as [jT HT'].
             fold pat C in HT'; rewrite HSk in HT'.
             change (ptyp_skip (S kk) t) with t' in HT'; cbn [List.repeat List.app] in HT'.
             destruct (rel_exp_of_typ_inversion_simple_at HΓB HT' _ _ (Htag _ Hin0)) as (b & b' & Eb2 & Eb2' & [Rb HRb]).
             assert (b = a2) as -> by (eapply functional_eval_exp; eassumption).
             assert (Eob : out_rel c0 c0' Hin <~> Rb) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR2 HRb).
             pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRb) HRb) as HRbb.
             etransitivity; [ exact Eob |].
             rewrite <- HTs.
             replace ((ns ++ nv ++ ys) ++ c0 :: nil) with (ns ++ nv ++ (ys ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
             change t' with (ptyp_skip (S kk) t).
             eapply (IH (S kk) (ys ++ c0 :: nil) b' jT Rb); [ lia | | | | exact HRbb ].
             + apply tele_prefix_rel_snoc; [ exact Hy |].
               unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB).
               apply Edr; exact Hin0.
             + rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
               cbn [List.rev].
               apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ j Rm);
                 [ rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia | exact Hgy |
                 | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRm HR3), Ein; exact Hin0 ].
               exact (mk_rel_mod_eval a1 a1 Eb Eb HRmd).
             + rewrite HEt; exact Eb2'. }
           (** The type's relation is the shape's at its own argument on both
               sides; the shape's at the right argument is that one, moved
               along the domain ([ind_rel_pre_r]). *)
           assert (Hmv : forall c0 c1 c2 r r', canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c0 c1 -> canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c1 c2 ->
                      rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
                        k ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c1 :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t' r r' ->
                      rec_arg_rel p D (admissible_index_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups)
                        k ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c2 :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t' r r').
           { intros c0 c1 c2 r r' H01 H12d Hs0.
             assert (H00 : canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c0 c0) by (etransitivity; [ exact H01 | symmetry; exact H01 ]).
             rewrite <- !List.app_assoc in Hs0 |- *.
             eapply (Hprer _ _ _ _ _ _ _ _ _ Hs0 Mk ns ns ns c gs1 t gs2 nv nv nv (S kk)
                       (ys ++ c0 :: nil) (ys ++ c1 :: nil) (ys ++ c2 :: nil));
               [ reflexivity | exact HM | reflexivity | reflexivity | exact Hnsd | exact Hnsd | rewrite <- Heq; exact Hcon
               | exact INV | exact INV | reflexivity | lia | | | first [ exact (eq_sym HTs) | exact HTs ] ];
               (apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); assumption ]). }
           intros fx fx'; split; intro Hx.
           - pose proof (proj1 (HE fx fx') Hx) as [Hxl Hxr Hx2]; cbn beta in Hx2.
             constructor; [| rewrite Hxl; exact Hrm | rewrite Hxr; exact Hrm ]; intros c0 c0' Hcc.
             pose proof (proj1 (Edr _ _) Hcc) as Hin.
             destruct (Hx2 _ _ Hin) as [r r' Er Er' Hrr].
             destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
             assert (H00 : canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
             econstructor; [ exact Er | exact Er' | exact (Hmv _ _ _ _ _ H00 Hcc (proj1 (Ecod _ _) Hrr)) ].
           - destruct (rec_arg_pi_kind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx) as [Hxl Hxr].
             apply HE; constructor; [ rewrite Hxl; symmetry; exact Hrm | rewrite Hxr; symmetry; exact Hrm |]; intros c0 c0' Hin.
             pose proof (proj2 (Edr _ _) Hin) as Hcc.
             destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx _ _ Hcc) as (r & r' & Er & Er' & Hrr).
             destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
             assert (Hc'c : canon_doms_rel D ups k (ns ++ nv ++ ys) Ts B c0' c0) by (symmetry; exact Hcc).
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
      assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
      set (pat' := List.repeat false L ++ pat) in *.
      (** The parameters of the end, at the non-recursive arguments and at
          all of them. *)
      assert (Hctx : per_tele_args (List.rev (shape_domains_ctx pat (ptyp_doms t) ++ C)) nil nil (ups ++ ns ++ fa ++ ys) (ups ++ ns ++ fa ++ ys)).
      { rewrite List.rev_app_distr.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        apply per_tele_args_app_intro; [ rewrite List.length_rev; exact HlC | exact Hgpf | rewrite <- Hft; exact Hgy ]. }
      destruct (shape_end_params_link gs1 t gs2 Heq ups ns fa ys Hlu Hlns Hlk Hgu0 Hnsd INV Hctx Hy) as [bs bs1 Ebs Ebs1 Htf].
      unfold nparams_tele_rel in Htf; rewrite HMj in Htf.
      (** The relation of the end's type. *)
      set (Z := shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk).
      assert (HZ : ⊨ Z ++ ind_uparams D).
      { pose proof (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as H.
        rewrite Hft in H; unfold Z, im_params in H |- *; rewrite <- !List.app_assoc; exact H. }
      destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
      (** The environment of all the arguments, as the components after the
          uniform parameters. *)
      assert (HEZ : env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn L (ptyp_doms t)))) ys = components_env D ups (List.rev Z) (ns ++ fa ++ ys)).
      { rewrite HEcl, Hft; unfold components_env, decl_env, C, Z, im_params.
        rewrite <- (env_tele_closed_app (ind_uparams D) (shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk)
                      ups (ns ++ fa ++ ys)) by (unfold ind_nu in Hlu; exact Hlu).
        rewrite <- !List.app_assoc; reflexivity. }
      assert (HE : RZ (components_env D ups (List.rev Z) (ns ++ fa ++ ys)) (components_env D ups (List.rev Z) (ns ++ fa ++ ys))).
      { rewrite <- HEZ; apply (Henv L ys (le_n _) Hly Hgy); rewrite Hft; unfold C, Z, im_params in *; rewrite !List.app_assoc.
        rewrite !List.app_assoc in HRZ; exact HRZ. }
      assert (Ebs1' : ⟦ List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) (ns ++ fa ++ ys) ↘ bs1).
      { rewrite <- HEZ, HEcl, Hft; exact Ebs1. }
      rewrite HEZ in Ea.
      assert (ERk : R <~> grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel D ups) (ptyp_mem t) ups ups bs1 bs1).
      { eapply (mty_end_rel (ptyp_mem t) Mj ups _ RZ (ns ++ fa ++ ys) (im_nn Mk) (List.length pat')
                  (List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t))); try eassumption.
        - unfold Z; rewrite !List.length_app, length_shape_domains_ctx, length_cargs_ctx, length_im_nparams; lia.
        - unfold pat'; rewrite !List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat; lia.
        - rewrite List.length_map; exact HlPs. }
      pose proof (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMj _ _ Htf) as Hbb.
      pose proof (nparams_rel_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMj _ _ Htf) as Hb1b.
      assert (HTsL : List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn L (shape_doms_tele t)
                     = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
        by (rewrite List.firstn_all2 by (unfold shape_doms_tele; rewrite List.length_map; lia); reflexivity).
      rewrite HTsL.
      assert (Hok : admissible_index_at D ups (canon_nparams_rel D ups) (ptyp_mem t) (ns ++ nv ++ ys)
                      (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ptyp_ps t) bs).
      { exists bs; [ exact Ebs |]; unfold nparams_tele_rel; rewrite HMj; exact Hbb. }
      intros x x'; split; intro Hx.
      - econstructor; [ exact Ebs | exact Ebs | exact Hok | exact Hok |].
        exact (ind_rel_idx p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ _ _ _ _ _ _ _ _ _ HMj (proj1 (ERk _ _) Hx) Hb1b Hb1b).
      - destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx) as (b1 & b2 & E1 & E2 & _ & _ & Hr).
        pose proof (functional_eval_exps' _ _ _ _ E1 Ebs) as ->.
        pose proof (functional_eval_exps' _ _ _ _ E2 Ebs) as ->.
        apply ERk; exact (ind_rel_idx p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ _ _ _ _ _ _ _ _ _ HMj Hr Htf Htf).
    Qed.

    (** ** The Type of a Recursive Argument, Evaluated by its Shape

        After [kk] domains [ys] of a recursive argument's shape, related to
        themselves canonically, the type of the rest of the shape and its
        value by the shape at the non-recursive arguments ([eval_shape_type], the
        type of the fresh variables readback takes) are related types,
        given that, at a view, the container's type at the view's instance
        and at uniform parameters related to it are related at related
        non-uniform parameters. *)
    Lemma shape_type_link : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        forall ups ns fa, List.length ups = ind_nu D -> List.length ns = im_nn Mk -> List.length fa = List.length gs1 ->
        per_tele_args (List.rev (ind_uparams D)) nil nil ups ups ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns ->
        tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa) ->
        (forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
           R (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
             (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))) ->
        (forall Mj qc kc Is vm Dq cups cs bs bs', ind_member D (ptyp_mem t) = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
           ind_lookup gc_deps gc_stack qc = Some Dq -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ups ↘ cups ->
           per_tele_args (List.rev (ind_uparams Dq)) nil nil cups cs ->
           nparams_tele_rel D (canon_nparams_rel D ups) (ptyp_mem t) bs bs' ->
           exists (i : universe_index) R, DF d_ind qc kc (cups ++ bs) ≈ d_ind qc kc (cs ++ bs') ∈ per_univ_elem i ↘ R) ->
        forall n kk ys a (i : nat) R, kk + n = List.length (ptyp_doms t) ->
          tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns (nonrec_arg_vals gs1 fa) t)
            kk ys ys ->
          per_tele_args (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t))))
            (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
            (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa)) ys ys ->
          ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false kk ++ cargs_pat gs1) (ptyp_skip kk t) ⟧
            env_tele (env_tele nil (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) (ups ++ ns ++ fa))
              (List.rev (shape_domains_ctx (cargs_pat gs1) (List.firstn kk (ptyp_doms t)))) ys ↘ a ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          exists b, ⟦shty ptyp_skip kk t of p ups ⟧ gc_deps ⍮ gc_stack
                      ⍮ components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t)
                          (ns ++ nonrec_arg_vals gs1 fa ++ ys) ↘ b /\
            Dom a ≈ b ∈ per_univ i.
    Proof.
      intros gs1 t gs2 Heq ups ns fa Hlu Hlns Hlk Hgu0 Hnsd INV Hpre Hend.
      destruct (valid_group_canon p D Hg ups Hgu0 Hlu) as [CnP CnI CaP CaI CdP CdI].
      set (nv := nonrec_arg_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (pat := cargs_pat gs1) in *.
      set (C := cargs_ctx p D Mk gs1 ++ im_params D Mk) in *.
      set (Ef := env_tele nil (List.rev C) (ups ++ ns ++ fa)) in *.
      set (TsF := List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) in *.
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_arg_vals; exact Hlk).
      assert (HlC : List.length (ups ++ ns ++ fa) = List.length C)
        by (unfold C; rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      pose proof (cargs_prefix_sem D p Mk gs HΨ gs1 (ca_rec t :: gs2) Heq) as HCs; fold C in HCs.
      assert (HEcl : forall kk ys, env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys
                                   = env_tele nil (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C)) (ups ++ ns ++ fa ++ ys)).
      { intros kk ys; unfold Ef.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite (env_tele_closed_app C _ (ups ++ ns ++ fa) ys) by exact HlC; reflexivity. }
      (** Weakened past the recursive arguments and retagged: the
          components. *)
      assert (HwkE : forall kk ys, kk <= List.length (ptyp_doms t) -> List.length ys = kk ->
                 ctx_retag (doms_ctx (List.firstn kk (ptyp_doms t)) ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)
                   (⟪wk_pat (List.repeat false kk ++ pat)⟫ (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys))
                 = components_env D ups TsF (ns ++ nv ++ ys)).
      { intros kk ys Hk Hly.
        assert (Hlf : List.length (List.firstn kk (ptyp_doms t)) = kk) by (rewrite List.length_firstn; lia).
        rewrite HEcl; unfold C.
        replace (List.repeat false kk) with (List.repeat false (List.length (List.firstn kk (ptyp_doms t)))) by (rewrite Hlf; reflexivity).
        rewrite (List.app_assoc ups ns (fa ++ ys)).
        rewrite (ctx_retag_wk_cargs_doms p D Mk gs1 pat (List.firstn kk (ptyp_doms t)) (ups ++ ns) fa ys eq_refl)
          by (first [ rewrite List.length_app, length_im_params; unfold im_np, ind_nu in *; lia | exact Hlk | lia ]).
        rewrite <- (List.app_assoc ups ns), closed_env_shape_doms_components by exact Hlu.
        unfold TsF, shape_doms_tele; rewrite <- List.firstn_map.
        apply eq_sym; rewrite (List.app_assoc ns nv ys).
        rewrite (List.app_assoc (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) (List.map (ce_ass ak_relevant) (ptyp_doms t))).
        rewrite (components_env_app_firstn D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (List.map (ce_ass ak_relevant) (ptyp_doms t)) (ns ++ nv) ys)
          by (first [ rewrite !List.length_app, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; lia
                    | rewrite List.length_map; lia ]).
        rewrite <- !List.app_assoc, Hly; reflexivity. }
      assert (Hgpf : per_tele_args (List.rev C) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
      { destruct (rel_ctx_wf_per_ctx_env HCs) as [R0 HR0].
        assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HCs).
        assert (HR0' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ R0)
          by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
        assert (Hl0 : List.length (tele_entries nil (List.rev C) (ups ++ ns ++ fa)) = List.length (List.rev C))
          by (rewrite tele_entries_length, List.length_rev; exact HlC).
        assert (Hta : all_assumptions (List.rev C))
          by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D Hc k Mk HM) ]).
        pose proof (proj2 (per_tele_args_of_env_extend _ _ _ _ per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (Hpre _ HR0))) as H.
        rewrite tele_entries_values in H; exact H. }
      assert (Henv : forall kk ys, kk <= List.length (ptyp_doms t) -> List.length ys = kk ->
                 per_tele_args (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) Ef Ef ys ys ->
                 forall R0, EF shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C
                              ≈ shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C ∈ per_ctx_env ↘ R0 ->
                   R0 (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys)
                      (env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys)).
      { intros kk ys Hk Hly Hgy R0 HR0.
        destruct (rel_ctx_wf_per_ctx_env HCs) as [RC HRC].
        apply (tele_args_env_rel_gen _ _ _ _ _ _ _ _ HRC HR0 (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk Hk)
                 (Hpre _ HRC)); [ rewrite length_shape_domains_ctx, List.length_firstn; lia | exact Hgy ]. }
      induction n as [| n IH]; intros kk ys a i R Hkn Hy Hgy Ea HR.
      2: { (** A domain: the codomains at related arguments, by the induction
               at the right one. *)
           assert (Hk : kk < List.length (ptyp_doms t)) by lia.
           destruct (ptyp_skip_lt kk t Hk) as (B & HB & Hs).
           rewrite Hs in Ea |- *.
           set (t' := ptyp_skip (S kk) t) in *.
           set (pat' := List.repeat false kk ++ pat) in *.
           cbn [ptyp_ty] in Ea.
           inversion Ea; subst a.
           basic_invert_per_univ_elem HR.
           match goal with Hx : eval_exp _ _ (B[wk_pat pat']ʷ) _ _ |- _ => rename Hx into Eb end.
           match goal with Hx : _ <~> pi_elements _ _ _ _ |- _ => rename Hx into HE end.
           match goal with Hx : forall c0 c' (_ : _ c0 c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename Hx into Hcod end.
           match goal with Hx : PER _ |- _ => rename Hx into HPin end.
           match goal with Hx : forall c0 c', _ c0 c' -> rel_typ_kind _ _ _ |- _ => rename Hx into HcodS end.
           pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
           pose proof (shape_domains_ctx_wk D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia)) as Hw; fold pat in Hw.
           destruct (valid_ind_decl_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as (_ & j & HBv).
           rewrite Heq, <- cargs_nonrec_ctx_nonrec_args_prefix in HBv.
           set (Et := env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)))) ys) in *.
           destruct (rel_ctx_wf_per_ctx_env (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq kk ltac:(lia))) as [RΓ HΓ].
           fold pat C in HΓ.
           pose proof (Henv kk ys ltac:(lia) Hly Hgy RΓ HΓ) as Hρ; fold Et in Hρ.
           (** The domain's type at the components. *)
           destruct (wk_type_retag_link _ _ _ _ _ _ _ Hw (rel_type_of_typ HBv) HΓ Hρ) as (j3 & R3 & a0' & m' & Ea0' & Em' & HR3).
           assert (a0' = a0) as -> by (eapply functional_eval_exp; eassumption).
           unfold Et in Em'; rewrite (HwkE kk ys ltac:(lia) Hly) in Em'.
           set (EcF := components_env D ups TsF (ns ++ nv ++ ys)) in *.
           assert (Ein : in_rel <~> R3) by (eapply per_univ_elem_right_irrel; [ exact equiv_a_a' | exact HR3 ]).
           pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HR3) HR3) as HR3'.
           (** The domain's relation, at the components of the prefix. *)
           assert (HEc : components_env D ups (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) (ns ++ nv ++ ys)
                         = EcF).
           { unfold EcF, TsF; rewrite (List.app_assoc ns nv ys), !List.app_assoc.
             rewrite <- Hly, <- components_env_app_firstn
               by (first [ rewrite !List.length_app, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; lia
                         | unfold shape_doms_tele; rewrite List.length_map; lia ]).
             reflexivity. }
           assert (Edr : canon_doms_rel D ups k (ns ++ nv ++ ys) (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t)) B
                         <~> in_rel).
           { unfold canon_doms_rel; rewrite HEc.
             pose proof (per_head_iff Em' Em' HR3') as Q.
             intros u v; split; intro Huv.
             - apply Ein; apply Q in Huv; exact Huv.
             - apply Q; apply Ein; exact Huv. }
           (** The context after one more domain, and its environments. *)
           pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
           pose proof (per_ctx_env_of_typ (κ := ak_relevant) HΓ (rel_type_of_typ HBw)) as HΓB.
           assert (HSk : shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)) ++ C = (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C) ▹{ak_relevant} B[wk_pat pat']ʷ)
             by (rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia; reflexivity).
           assert (HEt : forall c0, env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)))) (ys ++ c0 :: nil)
                                    = Et ↦ c0 ⦂ entry_type_closure B[wk_pat pat']ʷ Et).
           { intros c0; rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
             cbn [List.rev]; rewrite env_tele_snoc by (rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia).
             reflexivity. }
           assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
           assert (Htag : forall c0, in_rel c0 c0 ->
                     per_env_extend B[wk_pat pat']ʷ B[wk_pat pat']ʷ RΓ (Et ↦ c0 ⦂ entry_type_value a0) (Et ↦ c0 ⦂ entry_type_closure B[wk_pat pat']ʷ Et)).
           { intros c0 Hc0.
             pose proof (per_head_of Eb Eb equiv_a_a' Hc0) as Hh.
             destruct (per_head_closure_readable HΓB HΓ Hρ Hh) as [Rt _].
             pose proof (entry_readable_of_elem equiv_a_a' Hc0) as [Rv _].
             apply per_env_extend_intro'; [ exact Hρ | exact Hh | exact Rv |].
             assert (HlEt : List.length Et = List.length (shape_domains_ctx pat (List.firstn kk (ptyp_doms t)) ++ C)).
             { unfold Et, Ef; rewrite !length_env_tele; cbn [List.length].
               rewrite (List.length_app (shape_domains_ctx _ _) C), length_shape_domains_ctx, List.length_firstn; lia. }
             unfold centry_tag in Rt; cbn [centry_type] in Rt.
             rewrite <- HlEt, env_upto_exact in Rt; exact Rt. }
           (** The components after one more domain. *)
           assert (HEcS : forall c0, components_env D ups TsF ((ns ++ nv ++ ys) ++ c0 :: nil) = EcF ↦ c0 ⦂ entry_type_closure B EcF).
           { intros c0; unfold EcF, components_env; apply (env_tele_snoc_at _ _ _ ak_relevant).
             assert (Hlen : List.length (ns ++ nv ++ ys) = List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) + kk)
               by (rewrite !List.length_app, List.length_rev, length_cargs_nonrec_tele, length_im_nparams; lia).
             unfold TsF; rewrite List.app_assoc, Hlen, List.nth_error_app2 by lia.
             replace (List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) + kk
                      - List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1)) with kk by lia.
             unfold shape_doms_tele; rewrite List.nth_error_map, HB; reflexivity. }
           destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ equiv_a_a' HR3) as (Rd & HRd & ERd).
           exists (Πᵈ{ak_relevant} m' (nil ↦ d_shfam p ups EcF B t' ⦂ entry_type_none) fam_cod); split.
           { econstructor; exact Em'. }
           (** The domain is a type of a universe: relevant. *)
           assert (Hd0 : domain_kind a0 = ak_relevant).
           { destruct (rel_exp_of_typ_relevant_at HΓ HBw _ _ Hρ) as (b0 & Eb0 & Hr0).
             assert (b0 = a0) as -> by (eapply functional_eval_exp; eassumption); exact Hr0. }
           eexists; apply (per_univ_elem_pi_canonical HRd);
             [| intros c0 c0' Hcc; apply (HcodS c0 c0'); apply ERd; exact Hcc
              | exact Hd0 | rewrite <- (per_univ_elem_kind _ _ _ _ HRd); exact Hd0 | constructor | constructor
              | assumption
              | intros c0 c0' Hcc;
                match goal with HN : forall c c', in_rel c c' -> value_not_level_sort _ _ |- _ => apply (HN c0 c0') end;
                apply ERd; exact Hcc ].
           intros c0 c0' Hcc.
           assert (Hin : in_rel c0 c0') by (apply ERd; exact Hcc).
           assert (Hin0 : in_rel c0' c0') by (etransitivity; [ symmetry; exact Hin | exact Hin ]).
           destruct (Hcod _ _ Hin) as [a2 a2' Ea2 Ea2' HR2].
           (** The rest of the shape at the closure's extension and at the
               telescope's. *)
           destruct (shape_prefix_valid gs1 t gs2 Heq (S kk) ltac:(lia)) as [jT HT'].
           fold pat C in HT'; rewrite HSk in HT'.
           change (ptyp_skip (S kk) t) with t' in HT'; cbn [List.repeat List.app] in HT'.
           destruct (rel_exp_of_typ_inversion_simple_at HΓB HT' _ _ (Htag _ Hin0)) as (bb & bb' & Ebb & Ebb' & [Rb HRb]).
           assert (bb = a2') as -> by (eapply functional_eval_exp; eassumption).
           pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRb) HRb) as HRbb.
           assert (Hy' : tele_prefix_rel (shape_doms_rel (canon_doms_rel D ups k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ns nv t)
                           (S kk) (ys ++ c0' :: nil) (ys ++ c0' :: nil)).
           { apply tele_prefix_rel_snoc; [ exact Hy |].
             unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); apply Edr; exact Hin0. }
           assert (Hgy' : per_tele_args (List.rev (shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)))) Ef Ef (ys ++ c0' :: nil) (ys ++ c0' :: nil)).
           { rewrite (firstn_S_snoc _ _ _ HB), shape_domains_ctx_snoc, List.length_firstn, Nat.min_l by lia.
             cbn [List.rev].
             apply (per_tele_args_snoc _ _ _ _ _ _ _ _ _ i in_rel);
               [ rewrite List.length_rev, length_shape_domains_ctx, List.length_firstn; lia | exact Hgy | | exact Hin0 ].
             exact (mk_rel_mod_eval a0 a0 Eb Eb equiv_a_a'). }
           assert (Ea2'' : ⟦ ptyp_ty p D (im_nn Mk) (List.repeat false (S kk) ++ pat) (ptyp_skip (S kk) t) ⟧
                             env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn (S kk) (ptyp_doms t)))) (ys ++ c0' :: nil) ↘ bb').
           { rewrite HEt; exact Ebb'. }
           destruct (IH (S kk) (ys ++ c0' :: nil) bb' jT _ ltac:(lia) Hy' Hgy' Ea2'' HRbb) as (b3 & Eb3 & Hab3).
           destruct (per_univ_trans' _ _ _ _ _ ltac:(eexists; exact HR2) ltac:(eexists; exact HRb)) as [R4 HR4].
           destruct (per_univ_trans' _ _ _ _ _ ltac:(eexists; exact HR4) Hab3) as [R5 HR5].
           exists a2, b3, R5; split; [ exact Ea2 | split; [| exact HR5 ] ].
           apply eval_fam_cod_shfam.
           rewrite (List.app_assoc nv ys (c0' :: nil)), (List.app_assoc ns (nv ++ ys) (c0' :: nil)), HEcS in Eb3.
           exact Eb3. }
      (** The end of the shape. *)
      assert (Hkd : kk = List.length (ptyp_doms t)) by lia.
      subst kk.
      rewrite (ptyp_skip_end t) in Ea |- *.
      cbn [ptyp_ty] in Ea.
      set (L := List.length (ptyp_doms t)) in *.
      pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & _ & _).
      destruct (length_rec_ps D HD k Mk HM c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HlPs).
      assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
      set (pat' := List.repeat false L ++ pat) in *.
      assert (Hctx : per_tele_args (List.rev (shape_domains_ctx pat (ptyp_doms t) ++ C)) nil nil (ups ++ ns ++ fa ++ ys) (ups ++ ns ++ fa ++ ys)).
      { rewrite List.rev_app_distr.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        apply per_tele_args_app_intro; [ rewrite List.length_rev; exact HlC | exact Hgpf | rewrite <- Hft; exact Hgy ]. }
      destruct (shape_end_params_link gs1 t gs2 Heq ups ns fa ys Hlu Hlns Hlk Hgu0 Hnsd INV Hctx Hy) as [bs bs1 Ebs Ebs1 Htf].
      assert (Htf' : tele_rel (canon_nparams_rel D ups (ptyp_mem t)) (List.rev (im_nparams Mj)) bs1 bs).
      { unfold nparams_tele_rel in Htf; rewrite HMj in Htf.
        exact (nparams_rel_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMj _ _ Htf). }
      (** The environment of all the arguments, as the components after the
          uniform parameters. *)
      set (Z := shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk).
      assert (HZ : ⊨ Z ++ ind_uparams D).
      { pose proof (shape_domains_ctx_sem D p k Mk c gs HD HM Hcon HΨ _ _ _ Heq L (le_n _)) as H.
        rewrite Hft in H; unfold Z, im_params in H |- *; rewrite <- !List.app_assoc; exact H. }
      destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
      assert (HEZ : env_tele Ef (List.rev (shape_domains_ctx pat (List.firstn L (ptyp_doms t)))) ys = components_env D ups (List.rev Z) (ns ++ fa ++ ys)).
      { rewrite HEcl, Hft; unfold components_env, decl_env, C, Z, im_params.
        rewrite <- (env_tele_closed_app (ind_uparams D) (shape_domains_ctx pat (ptyp_doms t) ++ cargs_ctx p D Mk gs1 ++ im_nparams Mk)
                      ups (ns ++ fa ++ ys)) by (unfold ind_nu in Hlu; exact Hlu).
        rewrite <- !List.app_assoc; reflexivity. }
      assert (HE : RZ (components_env D ups (List.rev Z) (ns ++ fa ++ ys)) (components_env D ups (List.rev Z) (ns ++ fa ++ ys))).
      { rewrite <- HEZ; apply (Henv L ys (le_n _) Hly Hgy); rewrite Hft; unfold C, Z, im_params in *; rewrite !List.app_assoc.
        rewrite !List.app_assoc in HRZ; exact HRZ. }
      assert (Ebs1' : ⟦ List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ components_env D ups (List.rev Z) (ns ++ fa ++ ys) ↘ bs1).
      { rewrite <- HEZ, HEcl, Hft; exact Ebs1. }
      rewrite HEZ in Ea; clear Ebs1; rename Ebs1' into Ebs1.
      destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
      1,2: destruct (eval_mty_inv _ _ _ _ _ _ _ _ HMj ltac:(unfold im_is_rview; rewrite Hh; reflexivity) Ea) as (cs & bs2 & Ecs & Ebs2 & ->);
           pose proof (functional_eval_exps' _ _ _ _ Ebs2 Ebs1) as ->;
           unfold im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
      3: { (** A record view: the record at the view's instance. *)
           destruct (eval_mty_inv_rview _ _ _ _ _ _ _ _ _ _ _ HMj Hh Ea) as (cs & bs2 & Ecs & Ebs2 & ->).
           pose proof (functional_eval_exps' _ _ _ _ Ebs2 Ebs1) as ->.
           pose proof (rview_struct_nparams _ _ _ (decl_typed_record_struct _ _ _ (valid_group_typed _ _ Hg)) _ _ _ _ _ HMj Hh) as Hnp.
           assert (Hps0 : ptyp_ps t = nil)
             by (unfold im_nn in HlPs; rewrite Hnp in HlPs; destruct (ptyp_ps t); [ reflexivity | discriminate HlPs ]).
           rewrite Hps0 in Ebs1; assert (bs1 = nil) as -> by (inversion Ebs1; reflexivity).
           rewrite List.app_nil_r in HR.
           destruct (valid_group_records _ _ Hg _ _ _ _ _ HMj Hh) as [R0 HR0].
           destruct (rview_pre_values (ptyp_mem t) Mj qr Is fl R0 ups _ RZ (ns ++ fa ++ ys) (im_nn Mk) (List.length pat') cs
                       HMj Hh HR0 Hlu Hgu0 HZ HRZ ltac:(unfold Z; rewrite !List.length_app, length_shape_domains_ctx, length_cargs_ctx, length_im_nparams; lia)
                       ltac:(unfold pat'; rewrite !List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat; lia) HE Ecs)
             as (cups & Ecups & Hgc).
           assert (Hlc : List.length cups = List.length (record_params R0))
             by (rewrite (eval_exps_length _ _ _ Ecups); exact (rview_record_len p D Hg _ _ _ _ _ _ HMj Hh HR0)).
           destruct (vrr_type_rel _ _ _ _ HR0 Hgc Hlc) as [i1 W].
           exists (d_record qr cups); split.
           + eapply eval_shape_type_rview; [ exact (valid_group_lookup _ _ Hg) | exact HMj | exact Hh | exact Ecups ].
           + rewrite List.app_nil_r.
             exact (per_univ_trans' _ _ _ _ _ ltac:(eexists; exact HR) ltac:(eexists; exact (per_univ_sym _ _ _ _ W))). }
      - (** A declared member: its own uniform parameters. *)
        assert (HU : ⟦ im_pre Mj (ind_uvars D (im_nn Mk) (List.length pat')) ⟧* gc_deps ⍮ gc_stack
                       ⍮ components_env D ups (List.rev Z) (ns ++ fa ++ ys) ↘ ups).
        { unfold im_pre; rewrite Hh; apply eval_uvars_components; [ exact Hlu |].
          unfold pat'; rewrite !List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat; lia. }
        pose proof (functional_eval_exps' _ _ _ _ Ecs HU) as ->.
        destruct (valid_group_relate p D Hg (ptyp_mem t) Mj pm ups ups bs1 bs HMj Hh Hgu0 Hlu Htf') as [i1 W].
        exists (d_ind p (ptyp_mem t) (ups ++ bs)); split.
        + eapply eval_shape_type_self; [ exact Ebs | eapply eval_mref_decl; [ exact (valid_group_lookup _ _ Hg) | exact HMj | exact Hh ] ].
        + exact (per_univ_trans' _ _ _ _ _ ltac:(eexists; exact HR) ltac:(eexists; exact W)).
      - (** A view: the container's type at the view's instance. *)
        destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (Dq & Mk' & Hq & _).
        destruct (view_pre_values (ptyp_mem t) Mj qc kc Is vm Dq ups _ RZ (ns ++ fa ++ ys) (im_nn Mk) (List.length pat') cs
                    HMj Hh Hq Hlu Hgu0 HZ HRZ ltac:(unfold Z; rewrite !List.length_app, length_shape_domains_ctx, length_cargs_ctx, length_im_nparams; lia)
                    ltac:(unfold pat'; rewrite !List.length_app, List.repeat_length; unfold pat; rewrite length_cargs_pat; lia) HE Ecs)
          as (cups & Ecups & Hgc).
        destruct (Hend Mj qc kc Is vm Dq cups cs bs bs1 HMj Hh Hq Ecups Hgc Htf) as (i1 & R1 & W).
        exists (d_ind qc kc (cups ++ bs)); split.
        + eapply eval_shape_type_self; [ exact Ebs | eapply eval_mref_view; [ exact (valid_group_lookup _ _ Hg) | exact HMj | exact Hh | exact Ecups ] ].
        + exact (per_univ_trans' _ _ _ _ _ ltac:(eexists; exact HR) ltac:(eexists; exact (per_univ_sym _ _ _ _ W))).
    Qed.
  End ShapeMember.
End ShapeChar.

End Fixed_GCtx.
