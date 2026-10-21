(** * Valid Groups: the Canonical Model and the Type Formers

    A group is semantically valid ([valid_ind_decl]) when its telescopes and
    types are: these are the judgments of its typing, read in the PER model.
    From them, each declared member at related parameters is a type of the
    universe its sort denotes ([ind_relate]), with the canonical relations
    of [Core.Semantic.Inductives.IndPER]: the group's canonical model.  The
    type formers are then elements of their [Π]-types
    ([valid_exp_under_ctx_ind]), and the values of the declared members at
    the group's uniform parameters make an environment of the context of
    the group's members as variables ([selfs_env_rel]), at which the view
    equations are read ([Inductives/ViewEquations.v]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas DescTyping.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases VariableCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance Telescope.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Lists *)

Lemma length_nparams_prefix : forall M k, k <= im_nn M -> List.length (nparams_prefix M k) = k.
Proof. intros; unfold nparams_prefix; rewrite List.length_rev, List.length_firstn, List.length_rev, length_im_nparams; lia. Qed.

Lemma length_nonrec_args_prefix : forall gs k, k <= List.length (cargs_nonrec gs) -> List.length (nonrec_args_prefix gs k) = k.
Proof. intros; unfold nonrec_args_prefix; rewrite List.length_rev, List.length_firstn, List.length_map; lia. Qed.

Lemma nparams_prefix_suffix : forall D M k, exists Δ, im_params D M = Δ ++ nparams_prefix M k ++ ind_uparams D.
Proof.
  intros; exists (List.rev (List.skipn k (List.rev (im_nparams M)))).
  unfold im_params; rewrite List.app_assoc; f_equal.
  unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
Qed.

Lemma rev_nparams_prefix : forall (D : ind_decl) M k,
    List.rev (nparams_prefix M k ++ ind_uparams D) = List.rev (ind_uparams D) ++ List.firstn k (List.rev (im_nparams M)).
Proof. intros; unfold nparams_prefix; rewrite List.rev_app_distr, List.rev_involutive; reflexivity. Qed.

Lemma rev_im_params : forall D M, List.rev (im_params D M) = List.rev (ind_uparams D) ++ List.rev (im_nparams M).
Proof. intros; unfold im_params; apply List.rev_app_distr. Qed.

Lemma length_im_params : forall D M, List.length (im_params D M) = im_np D M.
Proof. intros; unfold im_params, im_np, ind_nu; rewrite List.length_app, length_im_nparams; lia. Qed.

Lemma doms_ctx_snoc : forall Bs B, doms_ctx (Bs ++ B :: nil) = ce_ass B :: doms_ctx Bs.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

Lemma eval_wk_pat_falses : forall ys k pat E, List.length ys = k ->
    ⟪wk_pat (List.repeat false k ++ pat)⟫ (env_args E ys) = env_args (⟪wk_pat pat⟫ E) ys.
Proof.
  intros ys; induction ys as [| y ys IH] using List.rev_ind; intros k pat E Hl.
  - cbn in Hl; subst k; reflexivity.
  - rewrite List.length_app in Hl; cbn in Hl.
    replace k with (S (List.length ys)) by lia.
    cbn [List.repeat List.app wk_pat].
    rewrite !env_args_snoc, eval_wk_q_cons by typeclasses eauto.
    rewrite IH by reflexivity; reflexivity.
Qed.

Lemma tele_ass_map_ass : forall As, tele_ass (List.map ce_ass As).
Proof. induction As; constructor; eauto. Qed.

Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
Proof. induction 1; cbn; congruence. Qed.

Lemma eval_exps_each : forall Ms ρ, (forall m M, List.nth_error Ms m = Some M -> exists v, ⟦ M ⟧ ρ ↘ v) ->
    exists vs, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs.
Proof.
  induction Ms as [| M Ms IH]; intros ρ H; [ exists nil; constructor |].
  destruct (H 0 M eq_refl) as [v Hv].
  destruct (IH ρ ltac:(intros m N HN; exact (H (S m) N HN))) as [vs Hvs].
  exists (v :: vs); econstructor; eassumption.
Qed.

Lemma eval_exps_nth : forall Ms ρ vs m M, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> List.nth_error Ms m = Some M ->
    exists v, List.nth_error vs m = Some v /\ ⟦ M ⟧ ρ ↘ v.
Proof.
  induction Ms as [| M0 Ms IH]; intros * H Hm; inversion H; subst; [ destruct m; discriminate |].
  destruct m as [| m]; cbn in Hm |- *; [ injection Hm as <-; eauto | eapply IH; eassumption ].
Qed.

(** ** The Declaration's Judgments, Positionwise

    The typing of a declaration states its judgments at decompositions of
    its lists; the semantic validity states them at positions. *)

Lemma cargs_strat_nonrec : forall gs, cargs_strat gs = List.rev (List.map ce_ass (cargs_nonrec gs)).
Proof. induction gs as [| [A | Ps] gs IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma nonrec_args_prefix_cargs_strat : forall gs1 gs2, cargs_strat gs1 = nonrec_args_prefix (gs1 ++ gs2) (List.length (cargs_nonrec gs1)).
Proof.
  intros; unfold nonrec_args_prefix; rewrite cargs_strat_nonrec, cargs_nonrec_app, List.map_app, List.firstn_app.
  rewrite List.firstn_all2 by (rewrite List.length_map; lia).
  rewrite List.length_map, Nat.sub_diag; cbn; rewrite List.app_nil_r; reflexivity.
Qed.

Lemma nonrec_nth_split : forall gs k A, List.nth_error (cargs_nonrec gs) k = Some A ->
    exists gs1 gs2, gs = gs1 ++ ca_arg A :: gs2 /\ List.length (cargs_nonrec gs1) = k.
Proof.
  induction gs as [| [B | Ps] gs IH]; intros k A H; cbn in H; [ destruct k; discriminate | |].
  - destruct k as [| k]; cbn in H.
    + injection H as ->; exists nil, gs; split; reflexivity.
    + destruct (IH _ _ H) as (gs1 & gs2 & -> & Hl); exists (ca_arg B :: gs1), gs2; split; [ reflexivity | cbn; lia ].
  - destruct (IH _ _ H) as (gs1 & gs2 & -> & Hl); exists (ca_rec Ps :: gs1), gs2; split; [ reflexivity | cbn; lia ].
Qed.

Lemma nparams_nth_split : forall M k A, List.nth_error (List.rev (im_nparams M)) k = Some (ce_ass A) ->
    exists Δ1, im_nparams M = Δ1 ++ ce_ass A :: nparams_prefix M k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & Hl & Hlen).
  exists (List.rev l2).
  assert (Hf : List.firstn k (List.rev (im_nparams M)) = l1)
    by (rewrite Hl, <- Hlen, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  unfold nparams_prefix; rewrite Hf, <- (List.rev_involutive (im_nparams M)), Hl, List.rev_app_distr; cbn.
  rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma nparams_prefix_S : forall M k A, List.nth_error (List.rev (im_nparams M)) k = Some (ce_ass A) ->
    nparams_prefix M (S k) = ce_ass A :: nparams_prefix M k.
Proof. intros * H; unfold nparams_prefix; rewrite (firstn_S_snoc _ _ _ H), List.rev_app_distr; reflexivity. Qed.

Lemma nparams_prefix_full : forall M, nparams_prefix M (im_nn M) = im_nparams M.
Proof. intros; unfold nparams_prefix; rewrite List.firstn_all2 by (rewrite List.length_rev, length_im_nparams; lia); apply List.rev_involutive. Qed.

(** Related arguments at a closed telescope make related environments of
    it. *)
Lemma gargs_env_rel : forall Ctx R zs zs' ρ ρ', EF Ctx ≈ Ctx ∈ per_ctx_env ↘ R -> ⊨ Ctx ->
    List.length zs = List.length Ctx ->
    per_gargs (List.rev Ctx) ρ ρ' zs zs' -> R (env_args ρ zs) (env_args ρ' zs').
Proof.
  intros * HR HC Hl Hg.
  assert (HC' : ⊨ List.rev (List.rev Ctx) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  destruct (gargs_rel _ _ _ _ _ Hg _ _ per_ctx_env_nil_true I HC') as (R' & HR' & Hρ).
  rewrite List.firstn_all2 in HR' by (rewrite List.length_rev; lia).
  rewrite List.rev_involutive, List.app_nil_r in HR'.
  assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E; exact Hρ.
Qed.

(** Arguments related at a telescope are related by the canonical
    relations. *)
Lemma gargs_tele_canon : forall ts (tr : nat -> list domain -> relation domain) E,
    (forall j A pre, List.nth_error ts j = Some (ce_ass A) ->
       (tr j pre <~> per_head A A (env_args E pre) (env_args E pre))) ->
    forall E' vs vs', per_gargs ts E E' vs vs' -> List.length vs = List.length ts -> tele_rel tr ts vs vs'.
Proof.
  intros * Htr * Hg Hl.
  assert (Hgen : forall ts' ρ ρ' xs xs', per_gargs ts' ρ ρ' xs xs' ->
             forall k pre, ρ = env_args E pre -> List.length pre = k -> ts' = List.skipn k ts ->
             tele_rel_from tr k pre xs xs').
  { induction 1 as [ts' ρ ρ' | i A ρ ρ' x x' ts' ys ys' R HA Hx Hg' IH]; intros k pre Hρ Hk Hts'; [ exact I |].
    split.
    - assert (Hnth : List.nth_error ts k = Some (ce_ass A)).
      { assert (H0 : List.nth_error (List.skipn k ts) 0 = Some (ce_ass A)) by (rewrite <- Hts'; reflexivity).
        rewrite List.nth_error_skipn, Nat.add_0_r in H0; exact H0. }
      apply (Htr _ _ _ Hnth).
      destruct HA as [b b' Eb Eb' HR].
      subst ρ.
      eapply per_head_of; [ exact Eb | exact Eb | | exact Hx ].
      eapply per_univ_trans; [ exact HR | apply per_univ_sym; exact HR ].
    - apply (IH (S k) (pre ++ x :: nil)); [ rewrite env_args_snoc, Hρ; reflexivity | rewrite List.length_app; cbn; lia |].
      assert (Hsk : List.skipn (S k) ts = List.tl (List.skipn k ts))
        by (change (S k) with (1 + k); rewrite <- List.skipn_skipn; destruct (List.skipn k ts); reflexivity).
      rewrite Hsk, <- Hts'; reflexivity. }
  split; [ exact Hl |].
  exact (Hgen _ _ _ _ _ Hg 0 nil eq_refl eq_refl eq_refl).
Qed.

(** ** Equal Extensions, Entry by Entry

    Two extensions equal in the PER model are equal entry by entry: the
    outer parts are, and the two last entries are types related over the
    first's outer part.  A substitution built from valid parts moves such
    an equation along it ([rel_ext_under_ctx_gsub]). *)

Lemma rel_ext_under_ctx_ass_inv : forall Γ Ψ Ψ' A A', Γ ⊨ˣ Ψ ▹ A ≈ Ψ' ▹ A' ->
    Γ ⊨ˣ Ψ ≈ Ψ' /\
    exists i : nat, Ψ ++ Γ ⊨ A : Typeω@i /\ Ψ ++ Γ ⊨ A ≈ A' : Typeω@i /\ Ψ' ++ Γ ⊨ A' : Typeω@i.
Proof.
  intros * [HL HR [R HRR]]; cbn [List.app] in HL, HR, HRR.
  inversion HRR as [| ? ? i0 ? ? tail_rel head_rel ? HT _ Hhead _ | |]; subst.
  pose proof (rel_ctx_wf_tail HL) as HL0; pose proof (rel_ctx_wf_tail HR) as HR0.
  destruct (rel_ctx_wf_ass_inv HL) as [i1 HA]; destruct (rel_ctx_wf_ass_inv HR) as [i2 HA'].
  split; [ constructor; [ exact HL0 | exact HR0 | exists tail_rel; exact HT ] |].
  destruct (rel_ctx_wf_per_ctx_env HL0) as [RL HRL]; destruct (rel_ctx_wf_per_ctx_env HR0) as [RR HRR0].
  assert (EL : tail_rel <~> RL) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (ER : tail_rel <~> RR) by (eapply per_ctx_env_left_irrel; eassumption).
  set (i := max (max i1 i2) i0).
  assert (HAi : Ψ ++ Γ ⊨ A : Typeω@i) by (eapply rel_exp_cumu_ge; [| exact HA ]; lia).
  assert (HA'i : Ψ' ++ Γ ⊨ A' : Typeω@i) by (eapply rel_exp_cumu_ge; [| exact HA' ]; lia).
  assert (HA'L : Ψ ++ Γ ⊨ A' : Typeω@i).
  { eapply (rel_exp_under_ctx_restrict HRL HRR0); [| exact HA'i ].
    intros ρ ρ' Hρ; apply ER, EL; exact Hρ. }
  exists i; split; [ exact HAi | split; [| exact HA'i ] ].
  apply (rel_exp_under_ctx_of_simple HRL HAi HA'L).
  intros ρ ρ' Hρ.
  destruct (Hhead _ _ (proj2 (EL _ _) Hρ)) as [a a' Ea Ea' Haa].
  exists a, a'; split; [ exact Ea | split; [ exact Ea' |] ].
  intros j R0 b b' Eb Eb' HRb.
  inversion Eb; subst; inversion Eb'; subst.
  destruct (per_univ_elem_univ _ _ _ _ HRb (or_introl (ex_intro _ _ eq_refl))) as [_ ER0].
  apply ER0; cbn [univ_idx].
  eexists; eapply per_univ_elem_cumu_ge; [| exact Haa ]; lia.
Qed.

Lemma rel_ext_under_ctx_gsub : forall Γ τ Δ Ψ Ψ', gsub Γ τ Δ -> tele_ass Ψ -> tele_ass Ψ' ->
    Δ ⊨ˣ Ψ ≈ Ψ' -> Γ ⊨ˣ tele_sub Ψ τ ≈ tele_sub Ψ' τ.
Proof.
  intros Γ τ Δ Ψ; induction Ψ as [| e Ψ IH]; intros Ψ' Hg Ha Ha' HΨ.
  - pose proof (per_ctx_respects_length (rxu_eq _ _ _ HΨ)) as Hl; rewrite !List.length_app in Hl.
    destruct Ψ' as [| e' Ψ']; cbn in Hl; [| lia ].
    destruct (gsub_sem Hg) as [HΓ _].
    constructor; [ exact HΓ | exact HΓ | exact (rel_ctx_wf_per_ctx HΓ) ].
  - pose proof (per_ctx_respects_length (rxu_eq _ _ _ HΨ)) as Hl; rewrite !List.length_app in Hl.
    destruct Ψ' as [| e' Ψ']; cbn in Hl; [ lia |].
    assert (He : exists A, e = ce_ass A) by (inversion Ha as [| ? ? He _]; exact He).
    assert (He' : exists A', e' = ce_ass A') by (inversion Ha' as [| ? ? He' _]; exact He').
    destruct He as [A ->]; destruct He' as [A' ->].
    assert (Hsa : tele_ass Ψ) by (inversion Ha; assumption).
    assert (Hsa' : tele_ass Ψ') by (inversion Ha'; assumption).
    destruct (rel_ext_under_ctx_ass_inv _ _ _ _ _ HΨ) as [HΨ0 (i & HA & HAA & HA')].
    pose proof (IH _ Hg Hsa Hsa' HΨ0) as IH0.
    assert (Hl0 : List.length Ψ = List.length Ψ') by lia.
    pose proof (gsub_qn _ _ _ _ Hg Hsa (rxu_left _ _ _ HΨ0)) as Hq.
    pose proof (gsub_qn _ _ _ _ Hg Hsa' (rxu_right _ _ _ HΨ0)) as Hq'.
    pose proof (rel_exp_under_ctx_gsub Hq HA) as HAτ.
    pose proof (rel_exp_under_ctx_gsub Hq HAA) as HAAτ.
    pose proof (rel_exp_under_ctx_gsub Hq' HA') as HA'τ.
    cbn [exp_sub] in HAτ, HAAτ, HA'τ; rewrite <- Hl0 in HA'τ.
    cbn [tele_sub centry_sub]; rewrite <- Hl0.
    destruct IH0 as [H1 H2 H3].
    constructor; cbn [List.app].
    + exact (rel_ctx_wf_extend H1 HAτ).
    + exact (rel_ctx_wf_extend H2 HA'τ).
    + exact (per_ctx_extend H3 HAAτ).
Qed.

(** The variables of a closed telescope, each of the type its telescope
    gives it at the variables before. *)
Lemma valid_vars_tele : forall Φ Δ,
    tele_ass Δ -> ctx_scoped 0 Δ -> ctx_mvc Δ -> ⊨ Φ ++ Δ ->
    forall k N T, List.nth_error (vars_from (List.length Φ) (List.length Δ)) k = Some N ->
      List.nth_error (tele_insts Δ Id (vars_from (List.length Φ) (List.length Δ))) k = Some T ->
      Φ ++ Δ ⊨ N : T.
Proof.
  intros * Hass Hs Hmv HΔ k N T HN HT.
  apply vars_from_nth_error in HN as [Hk ->].
  apply tele_insts_nth in HT as (A & HA & ->).
  destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
  assert (HΔeq : Δ = List.rev l2 ++ ce_ass A :: List.rev l1)
    by (rewrite <- (List.rev_involutive Δ), Hrev, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; reflexivity).
  assert (Hlen : List.length Δ = List.length l2 + S k)
    by (rewrite HΔeq, List.length_app; cbn [List.length]; rewrite !List.length_rev; lia).
  assert (HsA : exp_scoped k A).
  { rewrite HΔeq in Hs; apply ctx_scoped_app in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HsA _].
    rewrite List.length_rev, Nat.add_0_r in HsA; congruence. }
  assert (HmA : exp_mvc 0 A).
  { unfold ctx_mvc in Hmv; rewrite HΔeq in Hmv; apply List.Forall_app in Hmv as [_ Hmv].
    apply List.Forall_cons_iff in Hmv as [HmA _]; exact HmA. }
  replace (A[sb_of_list Id (List.firstn k (vars_from (List.length Φ) (List.length Δ)))])
    with (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ).
  - apply valid_exp_under_ctx_vlookup; [| exact HΔ ].
    replace (List.length Φ + (List.length Δ - 1 - k)) with (0 + List.length (Φ ++ List.rev l2))
      by (rewrite List.length_app, List.length_rev; lia).
    replace (A[wk_shiftn (List.length Φ + List.length l2 + 1)]ʷ)
      with (A[wk_shift]ʷ[wk_shiftn (List.length (Φ ++ List.rev l2))]ʷ)
      by (rewrite exp_wk_wk; apply exp_wk_wk_eq; intros x; cbn; rewrite List.length_app, List.length_rev; lia).
    rewrite HΔeq, List.app_assoc.
    apply ctx_lookup_app_r; constructor.
  - rewrite <- exp_sub_of_wk; eapply exp_scoped_mvc_agree; [ exact HsA | exact HmA |].
    intros x Hx; rewrite sb_of_list_firstn_vars by lia; cbn; f_equal; lia.
Qed.

(** ** The Group's Conditions, from its Typing

    The conditions the universe clause asks of a group ([grp_tele_ass]) are
    syntactic, and its typing gives them, with the typing of its views'
    containers. *)
Lemma grp_tele_ass_of_typed : forall D, decl_typed gc_deps gc_stack D ->
    (forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup gc_deps gc_stack qc = Some Dq -> decl_typed gc_deps gc_stack Dq) ->
    grp_tele_ass D.
Proof.
  intros D HD Hcont; constructor.
  - exact (dt_ass _ _ _ HD).
  - exact (dt_nparams_ass _ _ _ HD).
  - intros v Mv qc kc Is vm HMv Hh.
    destruct (dt_view _ _ _ HD _ _ _ _ _ _ HMv Hh) as (Dq & Mc & HDq & HMc & _ & HlIs & _ & Hvm & _).
    destruct (dt_vwrap _ _ _ HD _ _ _ _ _ _ HMv Hh) as (D' & HD' & Hvw).
    rewrite HDq in HD'; injection HD' as <-.
    destruct (vwo_members _ _ _ Hvw _ _ _ HMc Hvm) as (Mv' & HMv' & Hnn & _).
    rewrite HMv in HMv'; injection HMv' as <-.
    exists Dq, Mc; repeat split; [ exact HDq | exact HMc | exact (eq_sym Hnn) | exact HlIs ].
  - exact (dt_rank _ _ _ HD).
  - exact (dt_vwrap _ _ _ HD).
  - exact (dt_view_maps_coherent _ _ _ HD).
  - intros v Mv qc kc Is vm Dq i' Mi' HMv Hh HDq HMi'.
    destruct (dt_vwrap _ _ _ HD _ _ _ _ _ _ HMv Hh) as (D' & HD' & Hvw).
    rewrite HDq in HD'; injection HD' as <-.
    assert (Hi' : i' < List.length vm)
      by (rewrite (vwo_length _ _ _ Hvw); apply List.nth_error_Some; unfold ind_member in HMi'; congruence).
    destruct (nth_error_lt_some' _ _ Hi') as [w Hw].
    destruct (vwo_members _ _ _ Hvw _ _ _ HMi' Hw) as (Mw & HMw & Hnn & _).
    refine (mk_view_member_image _ _ _ _ _ _ w Mw Hw HMw Hnn _).
    destruct (im_head Mi') as [pm' | q'' k'' Is'' vm''] eqn:Hh'.
    + destruct (dt_view_decl _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ HMv Hh HDq HMi' Hh' Hw) as (Mw' & vm' & HMw' & Hhw).
      rewrite HMw in HMw'; injection HMw' as <-; exists vm'; exact Hhw.
    + destruct (dt_view_view _ _ _ HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMv Hh HDq HMi' Hh' Hw) as (Mw' & X & vm' & HMw' & Hhw & HlX).
      rewrite HMw in HMw'; injection HMw' as <-; exists X, vm'; split; [ exact Hhw | exact HlX ].
  - exact (dt_plen _ _ _ HD).
  - intros v Mv qc kc Is vm Dq i' Mi' c gs' HMv Hh HDq HMi' Hin.
    exact (dt_plen _ _ _ (Hcont _ _ _ _ _ _ _ HMv Hh HDq) _ _ _ _ HMi' Hin).
Qed.

(** The values of the declared members of the group at [p] at the uniform
    parameters [ups], in order: the values of the members as variables
    ([grp_selfs]) the substitution [grp_sb p D] gives at [ups]. *)
Definition selfs_vals (p : qname) (D : ind_decl) (ups : list domain) : list domain :=
  List.map (fun j => d_ind p j ups) (List.seq 0 (ind_ndecl D)).

(** ** A Telescope at the Sort

    A type of a declaration in the context [Pre] over the uniform
    parameters, of the sort shifted past [Pre], evaluates at related
    arguments to types of the universe the sort denotes at the uniform
    parameters. *)
Section Sort.
  Variable (D : ind_decl).
  Hypothesis (HD : valid_ind_decl D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).

  Lemma sort_univ : forall ρ b, ⟦ ind_sort D ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; inversion Hb; subst; unfold is_univ; eauto.
  Qed.

  Lemma sort_wk_univ : forall φ ρ b, ⟦ (ind_sort D)[φ]ʷ ⟧ ρ ↘ b -> is_univ b.
  Proof.
    intros * Hb; destruct Hsu as [[i Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; subst;
      unfold is_univ; eauto.
  Qed.

  Lemma uparams_ass : tele_ass (ind_uparams D).
  Proof. exact (dc_ass _ Hc). Qed.

  Lemma rev_uparams_ass : tele_ass (List.rev (ind_uparams D)).
  Proof. apply List.Forall_rev, uparams_ass. Qed.

  Lemma sort_typ_rel : forall Pre T, ⊨ Pre ++ ind_uparams D ->
      Pre ++ ind_uparams D ⊨ T : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      forall ups ups' zs zs', List.length zs = List.length Pre -> List.length zs' = List.length Pre ->
        List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
        per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
        forall a, ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        exists t t', ⟦ T ⟧ env_args nil (ups ++ zs) ↘ t /\ ⟦ T ⟧ env_args nil (ups' ++ zs') ↘ t' /\
          Dom t ≈ t' ∈ per_univ (univ_idx a).
  Proof.
    intros * HC HT * Hz Hz' Hu Hu' Hg a Ha.
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_args nil (ups ++ zs)) (env_args nil (ups' ++ zs'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR HC); [ unfold ind_nu in *; rewrite !List.length_app; lia | exact Hg ]. }
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (HRee : R (env_args nil (ups ++ zs)) (env_args nil (ups ++ zs)))
      by (etransitivity; [ exact HRe | symmetry; exact HRe ]).
    destruct (rel_exp_under_ctx_simple_full_at HR HT) as [i0 Hsimp].
    destruct (Hsimp _ _ HRe) as (b & b' & R0 & Eb & Eb' & HR0 & t & t' & Et & Et' & Htt).
    destruct (per_univ_elem_univ _ _ _ _ HR0 (sort_wk_univ _ _ _ Eb)) as [_ ER0].
    (** The sort shifted past [Pre] is the sort at the uniform parameters. *)
    destruct (vid_sort _ HD) as [i HS].
    destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) HS) as (RΓ & HΓ & j & Hwk).
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hwk _ _ (proj1 (E _ _) HRee)) as (x & x' & Rx & Ex & Ex' & HRx & m & m' & Em & Em' & Hmm).
    rewrite env_args_app, <- Hz, eval_wk_shiftn_args in Em'.
    assert (m' = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (m = b) as -> by (eapply functional_eval_exp; eassumption).
    cbn in Ex; inversion Ex; subst.
    basic_invert_per_univ_elem HRx.
    match goal with Hm : ?r b a, H : ?r <~> _ |- _ => apply H in Hm; destruct Hm as [Rm HRm] end.
    destruct (per_univ_elem_univ _ _ _ _ HRm (sort_wk_univ _ _ _ Eb)) as [Hidx _].
    exists t, t'; split; [ exact Et | split; [ exact Et' |] ].
    rewrite Hidx; apply ER0; exact Htt.
  Qed.

  (** Arguments related at a telescope of types at the sort, by the
      canonical relations, are arguments related at it. *)
  Lemma tele_canon_gargs : forall (ts : list centry) (Pre0 : ctx) (tr : nat -> list domain -> relation domain)
      ups ups' zs zs' a,
      tele_ass ts ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      List.length zs = List.length Pre0 -> List.length zs' = List.length Pre0 ->
      per_gargs (List.rev (Pre0 ++ ind_uparams D)) nil nil (ups ++ zs) (ups' ++ zs') ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      (forall j A, List.nth_error ts j = Some (ce_ass A) ->
         ⊨ List.rev (List.firstn j ts) ++ Pre0 ++ ind_uparams D /\
         List.rev (List.firstn j ts) ++ Pre0 ++ ind_uparams D
           ⊨ A : (ind_sort D)[wk_shiftn (j + List.length Pre0)]ʷ) ->
      (forall j A pre, List.nth_error ts j = Some (ce_ass A) ->
         (tr j pre <~> per_head A A (env_args nil (ups ++ zs ++ pre)) (env_args nil (ups ++ zs ++ pre)))) ->
      forall k vs vs', k <= List.length ts -> tele_prefix_rel tr k vs vs' ->
        per_gargs (List.firstn k ts) (env_args nil (ups ++ zs)) (env_args nil (ups' ++ zs')) vs vs'.
  Proof.
    intros * Hts Hu Hu' Hz Hz' Hg Ha Hv Htr k.
    induction k as [| k IH]; intros vs vs' Hk Hp.
    - rewrite tele_prefix_rel_iff in Hp; destruct Hp as (Hl & Hl' & _).
      destruct vs, vs'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hl & Hl' & Hr).
      destruct (nth_error_lt_some' ts k ltac:(lia)) as [e He].
      assert (HA : exists A, e = ce_ass A)
        by (unfold tele_ass in Hts; rewrite List.Forall_forall in Hts; apply Hts; eapply List.nth_error_In; exact He).
      destruct HA as [A ->].
      destruct (nth_error_lt_some' vs k ltac:(lia)) as [v Hv0].
      destruct (nth_error_lt_some' vs' k ltac:(lia)) as [v' Hv0'].
      rewrite (firstn_S_snoc _ _ _ He).
      assert (Hvs : vs = List.firstn k vs ++ v :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0), List.firstn_all2 by lia; reflexivity).
      assert (Hvs' : vs' = List.firstn k vs' ++ v' :: nil)
        by (rewrite <- (firstn_S_snoc _ _ _ Hv0'), List.firstn_all2 by lia; reflexivity).
      pose proof (IH _ _ ltac:(lia) (tele_prefix_rel_of_pre _ _ _ _ k Hp ltac:(lia))) as IHk.
      rewrite Hvs, Hvs'.
      destruct (Hv _ _ He) as [HC HT].
      assert (Hlf : List.length (List.firstn k ts) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv : List.length (List.firstn k vs) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv' : List.length (List.firstn k vs') = k) by (rewrite List.length_firstn; lia).
      assert (Hg' : per_gargs (List.rev (List.rev (List.firstn k ts) ++ Pre0 ++ ind_uparams D)) nil nil
                      (ups ++ zs ++ List.firstn k vs) (ups' ++ zs' ++ List.firstn k vs')).
      { rewrite List.rev_app_distr, List.rev_involutive, !List.app_assoc.
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, List.length_app; unfold ind_nu in *; lia | exact Hg |].
        exact IHk. }
      set (Pre := List.rev (List.firstn k ts) ++ Pre0).
      assert (HC' : ⊨ Pre ++ ind_uparams D) by (unfold Pre; rewrite <- List.app_assoc; exact HC).
      assert (HT' : Pre ++ ind_uparams D ⊨ A : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ)
        by (unfold Pre; rewrite <- List.app_assoc, List.length_app, List.length_rev, Hlf; exact HT).
      assert (Hg'' : per_gargs (List.rev (Pre ++ ind_uparams D)) nil nil
                       (ups ++ (zs ++ List.firstn k vs)) (ups' ++ (zs' ++ List.firstn k vs')))
        by (unfold Pre; rewrite <- List.app_assoc; exact Hg').
      destruct (sort_typ_rel Pre A HC' HT' ups ups' (zs ++ List.firstn k vs) (zs' ++ List.firstn k vs')
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  ltac:(unfold Pre; rewrite !List.length_app, List.length_rev; lia)
                  Hu Hu' Hg'' a Ha)
        as (t & t' & Et & Et' & [R0 HR0]).
      destruct (per_univ_elem_to_nat _ _ _ _ HR0) as [n Hn].
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R0); [ lia | exact IHk | |].
      + rewrite <- !env_args_app, <- !List.app_assoc; exact (mk_rel_mod_eval t t' Et Et' Hn).
      + pose proof (Hr _ _ _ Hv0 Hv0') as Hrv.
        apply (Htr _ _ _ He) in Hrv.
        assert (HRtt : DF t ≈ t ∈ per_univ_elem n ↘ R0)
          by (eapply per_univ_trans; [ exact Hn | apply per_univ_sym; exact Hn ]).
        exact (Hrv _ _ _ _ Et Et HRtt).
  Qed.

  Lemma uparams_sem : ⊨ ind_uparams D.
  Proof. exact (vid_uparams _ HD). Qed.

  Lemma rev_uparams_sem : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact uparams_sem. Qed.

  Lemma uparams_refl_l : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof.
    intros * Hg; eapply (per_gargs_refl_l _ _ _ per_ctx_env_nil_true rev_uparams_sem); [ exact rev_uparams_ass | exact I | exact Hg ].
  Qed.

  Lemma length_ups_gargs : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D.
  Proof. intros * Hg Hu; destruct (per_gargs_length _ _ _ _ _ Hg) as [Hl _]; lia. Qed.

  (** ** The Telescopes of a Member *)
  Section Member.
    Variables (k : nat) (Mk : imember).
    Hypothesis (HM : ind_member D k = Some Mk).

    Lemma member_nparams_ass : tele_ass (im_nparams Mk).
    Proof. exact (mc_ass _ _ (dc_members _ Hc _ _ HM)). Qed.

    Lemma member_params_ass : tele_ass (im_params D Mk).
    Proof. exact (decl_closed_params_ass _ _ _ Hc HM). Qed.

    Lemma rev_params_ass : tele_ass (List.rev (im_params D Mk)).
    Proof. apply List.Forall_rev, member_params_ass. Qed.

    Lemma rev_params_sem : ⊨ List.rev (List.rev (im_params D Mk)) ++ ⋅.
    Proof. rewrite List.rev_involutive, List.app_nil_r; exact (vid_params _ HD _ _ HM). Qed.

    Lemma nparams_prefix_sem : forall j, ⊨ nparams_prefix Mk j ++ ind_uparams D.
    Proof.
      intros; destruct (nparams_prefix_suffix D Mk j) as [Δ HΔ]; pose proof (vid_params _ HD _ _ HM) as H; rewrite HΔ in H.
      exact (rel_ctx_wf_app_r _ _ H).
    Qed.

    Lemma length_rec_ps : forall c gs gs1 t gs2, ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj.
    Proof. intros * Hcon Heq; exact (vid_plen _ HD _ _ _ _ HM Hcon _ _ _ Heq). Qed.

    (** The parameters of a recursive argument, at related arguments before
        it, are related at the non-uniform parameters of the member its
        shape ends in. *)
    Lemma rec_closure : forall c gs gs1 t gs2 Mj, ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        ind_member D (ptyp_mem t) = Some Mj ->
        forall ups ups' ms ms' ws ws' ys ys',
          List.length ups = ind_nu D -> List.length ms = im_nn Mk -> List.length ws = List.length (cargs_nonrec gs1) ->
          List.length ys = ptyp_depth t ->
          List.length ups' = ind_nu D -> List.length ms' = im_nn Mk -> List.length ws' = List.length (cargs_nonrec gs1) ->
          List.length ys' = ptyp_depth t ->
          per_gargs (List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)) nil nil
            (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') ->
          exists bs bs', ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ms ++ ws ++ ys) ↘ bs /\
            ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ bs' /\
            per_gargs (List.rev (im_nparams Mj)) (env_args nil ups) (env_args nil ups') bs bs' /\
            (forall m P T, List.nth_error (ptyp_ps t) m = Some P ->
               List.nth_error (tele_insts (im_nparams Mj)
                                 (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + im_nn Mk))) (ptyp_ps t)) m
                 = Some T ->
               (per_head T T (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups' ++ ms' ++ ws' ++ ys'))
                  <~> canon_nparams_rel D ups (ptyp_mem t) m (List.firstn m bs))).
    Proof.
      intros * Hcon Heq HMj * Hu Hm Hw Hy Hu' Hm' Hw' Hy' Hg.
      rename t into Ps.
      set (K := List.length (cargs_nonrec gs1)) in *.
      set (L := ptyp_depth Ps + K + im_nn Mk).
      set (Ξ0 := ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_params D Mk).
      set (E := env_args nil (ups ++ ms ++ ws ++ ys)); set (E' := env_args nil (ups' ++ ms' ++ ws' ++ ys')).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (HΞ0 : ⊨ Ξ0).
      { pose proof (vid_dctx _ HD _ _ _ _ _ _ _ (List.length (ptyp_doms Ps)) HM Hcon Heq (le_n _)) as H.
        rewrite List.firstn_all in H; exact H. }
      destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (HEE : R0 E E').
      { apply (gargs_env_rel Ξ0 R0 (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') nil nil); [ exact HR0 | exact HΞ0 | | exact Hg ].
        unfold Ξ0, ptyp_tele; rewrite !List.length_app, length_nonrec_args_prefix, doms_ctx_length by exact HK.
        rewrite length_im_params; unfold ptyp_depth, im_np in *; lia. }
      destruct (length_rec_ps _ _ _ _ _ Hcon Heq) as (Mj' & HMj' & HPl).
      rewrite HMj in HMj'; injection HMj' as <-.
      assert (HwkE : ⟪wk_shiftn L⟫ E = env_args nil ups).
      { unfold E, L; rewrite env_args_app; replace (ptyp_depth Ps + K + im_nn Mk) with (List.length (ms ++ ws ++ ys))
          by (rewrite !List.length_app; lia); apply eval_wk_shiftn_args. }
      assert (HwkE' : ⟪wk_shiftn L⟫ E' = env_args nil ups').
      { unfold E', L; rewrite env_args_app; replace (ptyp_depth Ps + K + im_nn Mk) with (List.length (ms' ++ ws' ++ ys'))
          by (rewrite !List.length_app; lia); apply eval_wk_shiftn_args. }
      (** The substitution of the uniform parameters: a shift past the
          arguments and the non-uniform parameters. *)
      assert (Hwk : Ξ0 ⊨ˢ sb_of_wk (wk_shiftn L) ≈ sb_of_wk (wk_shiftn L) : ind_uparams D).
      { apply rel_sub_of_wk.
        assert (HL : L = List.length (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_nparams Mk))
          by (unfold L, ptyp_tele, ptyp_depth; rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams, doms_ctx_length
                by exact HK; lia).
        assert (HΞe : Ξ0 = (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ im_nparams Mk) ++ ind_uparams D)
          by (unfold Ξ0, im_params; rewrite <- !List.app_assoc; reflexivity).
        rewrite HΞe, HL; apply rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0. }
      (** The induction over the parameters of the recursive argument. *)
      assert (Hall : forall m, m <= im_nn Mj ->
                 Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps))
                   ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps)) : nparams_prefix Mj m ++ ind_uparams D /\
                 exists bs bs', ⟦ List.firstn m (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ bs /\
                   ⟦ List.firstn m (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ bs' /\
                   per_gargs (List.firstn m (List.rev (im_nparams Mj))) (env_args nil ups) (env_args nil ups') bs bs' /\
                   (forall m' P T, m' < m -> List.nth_error (ptyp_ps Ps) m' = Some P ->
                      List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps Ps)) m' = Some T ->
                      (per_head T T E E' <~> canon_nparams_rel D ups (ptyp_mem Ps) m' (List.firstn m' bs)))).
      { induction m as [| m IH]; intros Hmn.
        - cbn [List.firstn sb_of_list]; unfold nparams_prefix; cbn [List.firstn List.rev List.app].
          split; [ exact Hwk |]; exists nil, nil; split; [ constructor | split; [ constructor | split; [ constructor | intros; lia ] ] ].
        - destruct (IH ltac:(lia)) as (Hτ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
          destruct (nth_error_lt_some' (ptyp_ps Ps) m ltac:(lia)) as [P HP].
          assert (HT : exists T, List.nth_error (tele_insts (im_nparams Mj) (sb_of_wk (wk_shiftn L)) (ptyp_ps Ps)) m = Some T).
          { apply nth_error_lt_some'.
            rewrite length_tele_insts by exact (mc_ass _ _ (dc_members _ Hc _ _ HMj)).
            rewrite length_im_nparams; lia. }
          destruct HT as [T HT].
          destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
          pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ _ _ _ HM Hcon Heq HMj HP HT) as HPv.
          destruct (vid_npar _ HD _ _ _ _ HMj HA) as (_ & j & HAv).
          set (τ := sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m (ptyp_ps Ps))) in *.
          (** The new entry, and the substitution extended by it. *)
          assert (Hτ' : Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) (ptyp_ps Ps))
                          ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) (ptyp_ps Ps)) : nparams_prefix Mj (S m) ++ ind_uparams D).
          { rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (nparams_prefix_S _ _ _ HA); cbn [sb_of_list List.app].
            eapply rel_sub_under_ctx_extend; [ exact Hτ | exact HAv | exact HPv ]. }
          split; [ exact Hτ' |].
          (** The values of the new parameter, and its type's. *)
          destruct (rel_exp_under_ctx_simple_at HR0 HPv _ _ HEE) as (b & b' & Eb & Eb' & Hbb).
          assert (Hτev : ⟦ τ ⟧s E ↘ env_args nil (ups ++ bs)).
          { unfold τ; rewrite env_args_app, <- HwkE; apply eval_sb_of_list; [ apply eval_sub_of_wk; typeclasses eauto | exact Ebs ]. }
          assert (Hτev' : ⟦ τ ⟧s E' ↘ env_args nil (ups' ++ bs')).
          { unfold τ; rewrite env_args_app, <- HwkE'; apply eval_sb_of_list; [ apply eval_sub_of_wk; typeclasses eauto | exact Ebs' ]. }
          destruct (rel_exp_of_typ_inversion HAv) as (RA & HRA & HAgen).
          destruct (HAgen _ _ HR0 _ _ Hτ _ _ _ _ HEE Hτev Hτev') as [t1 t2 t3 t4 Et1 Et2 Et3 Et4 Hch].
          destruct Hch as ([R12 HR12] & [R23 HR23] & [R34 HR34]).
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR12 HR23) as (R13 & HR13 & E13).
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR13 HR34) as (R14 & HR14 & E14).
          pose proof (Hbb _ _ _ _ Et1 Et4 HR14) as Hb14.
          assert (E23 : R23 <~> R14)
            by (etransitivity; [ symmetry; eapply per_univ_elem_left_irrel; [ exact HR13 | exact HR23 ]
                               | eapply per_univ_elem_right_irrel; [ exact HR13 | exact HR14 ] ]).
          assert (Hlbs : List.length bs = m) by (rewrite (eval_exps_length _ _ _ Ebs), List.length_firstn; lia).
          exists (bs ++ b :: nil), (bs' ++ b' :: nil); split; [| split; [| split ] ].
          + rewrite (firstn_S_snoc _ _ _ HP); apply eval_exps_app; [ exact Ebs | econstructor; [ exact Eb | constructor ] ].
          + rewrite (firstn_S_snoc _ _ _ HP); apply eval_exps_app; [ exact Ebs' | econstructor; [ exact Eb' | constructor ] ].
          + rewrite (firstn_S_snoc _ _ _ HA).
            destruct (per_univ_elem_to_nat _ _ _ _ HR23) as [n Hn].
            apply (per_gargs_snoc _ _ _ _ _ _ _ _ n R23);
              [ rewrite List.length_firstn, List.length_rev, length_im_nparams, (eval_exps_length _ _ _ Ebs), List.length_firstn; lia
              | exact Hgb | rewrite <- !env_args_app; exact (mk_rel_mod_eval t2 t3 Et2 Et3 Hn) | apply E23, Hb14 ].
          + intros m' P' T' Hmm' HP' HT'.
            destruct (Nat.lt_ge_cases m' m) as [Hlt | Hge].
            * rewrite List.firstn_app, Hlbs, (proj2 (Nat.sub_0_le m' m)) by lia; cbn; rewrite List.app_nil_r.
              exact (Hil _ _ _ Hlt HP' HT').
            * assert (m' = m) as -> by lia.
              rewrite HT in HT'; injection HT' as <-.
              rewrite List.firstn_app, Hlbs, Nat.sub_diag, List.firstn_all2 by lia; cbn; rewrite List.app_nil_r.
              unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMj HA).
              assert (HR22 : DF t2 ≈ t2 ∈ per_univ_elem j ↘ R23)
                by (eapply per_univ_trans; [ exact HR23 | apply per_univ_sym; exact HR23 ]).
              pose proof (per_head_iff Et1 Et4 HR14) as Q1.
              pose proof (per_head_iff Et2 Et2 HR22) as Q2.
              intros x y; rewrite <- (Q1 x y), <- (Q2 x y), <- (E23 x y); reflexivity. }
      destruct (Hall (im_nn Mj) (le_n _)) as (_ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
      rewrite List.firstn_all2 in Ebs, Ebs' by lia.
      rewrite List.firstn_all2 in Hgb by (rewrite List.length_rev, length_im_nparams; lia).
      exists bs, bs'; split; [ exact Ebs | split; [ exact Ebs' | split; [ exact Hgb |] ] ].
      intros m P T HP HT.
      assert (Hm0 : m < im_nn Mj) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
      exact (Hil _ _ _ Hm0 HP HT).
    Qed.

    (** The canonical relations of the non-uniform parameters are those of
        the telescope. *)
    Lemma nr_gargs : forall ups ups' a, per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        forall j vs vs', j <= im_nn Mk -> tele_prefix_rel (canon_nparams_rel D ups k) j vs vs' ->
          per_gargs (List.firstn j (List.rev (im_nparams Mk))) (env_args nil ups) (env_args nil ups') vs vs'.
    Proof.
      intros * Hg Hu Ha * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof (tele_canon_gargs (List.rev (im_nparams Mk)) nil (canon_nparams_rel D ups k) ups ups' nil nil a
                    ltac:(apply List.Forall_rev, member_nparams_ass) Hu Hu' eq_refl eq_refl
                    ltac:(rewrite !List.app_nil_r; exact Hg) Ha) as Hcan.
      rewrite !List.app_nil_r in Hcan; apply Hcan; [ | | rewrite List.length_rev, length_im_nparams; exact Hj | exact Hp ].
      - intros j0 A HA; cbn [List.app List.length]; rewrite Nat.add_0_r.
        split; [ exact (nparams_prefix_sem j0) | exact (proj1 (vid_npar _ HD _ _ _ _ HM HA)) ].
      - intros j0 A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA); reflexivity.
    Qed.

    Lemma params_gargs : forall ups ups' a ms ms', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        per_gargs (List.rev (im_params D Mk)) nil nil (ups ++ ms) (ups' ++ ms').
    Proof.
      intros * Hg Hu Ha Hm.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      rewrite rev_im_params; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg |].
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite <- (List.firstn_all2 (n := im_nn Mk) (List.rev (im_nparams Mk))) by (rewrite List.length_rev, length_im_nparams; lia).
      eapply nr_gargs; [ exact Hg | exact Hu | exact Ha | lia |].
      rewrite <- (List.firstn_all2 (n := im_nn Mk) ms), <- (List.firstn_all2 (n := im_nn Mk) ms')
        by (rewrite List.length_rev, length_im_nparams in *; lia).
      apply tele_prefix_rel_of_full with (T := List.rev (im_nparams Mk)); [ exact Hm | rewrite List.length_rev, length_im_nparams; lia ].
    Qed.

    (** The canonical relations of a constructor's non-recursive arguments
        are those of its telescope. *)
    Lemma ar_gargs : forall c gs ups ups' a ms ms', ind_con Mk c = Some gs ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        forall j vs vs', j <= List.length (cargs_nonrec gs) -> tele_prefix_rel (canon_args_rel D ups k ms c) j vs vs' ->
          per_gargs (List.firstn j (List.map ce_ass (cargs_nonrec gs))) (env_args nil (ups ++ ms)) (env_args nil (ups' ++ ms')) vs vs'.
    Proof.
      intros * Hcon Hg Hu Ha Hm * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite List.length_rev in Hl, Hl'.
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      eapply (tele_canon_gargs (List.map ce_ass (cargs_nonrec gs)) (im_nparams Mk) (canon_args_rel D ups k ms c) ups ups' ms ms' a);
        [ apply tele_ass_map_ass | exact Hu | exact Hu' | exact Hl | exact Hl'
        | exact Hpg | exact Ha | | | rewrite List.length_map; exact Hj | exact Hp ].
      - intros j0 A HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (cargs_nonrec gs) j0) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
        assert (Hj0 : j0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
        destruct (vid_arg _ HD _ _ _ _ _ _ HM Hcon HA0) as [HAv _].
        split; [ exact (vid_strat _ HD _ _ _ _ j0 HM Hcon ltac:(lia)) | exact HAv ].
      - intros j0 A pre HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (cargs_nonrec gs) j0) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
        unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcon HA0); reflexivity.
    Qed.

    (** The canonical relations of the domains of a recursive argument's
        shape are those of their telescope. *)
    Lemma dom_gargs : forall c gs gs1 t gs2 ups ups' a ms ms' ws ws', ind_con Mk c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        tele_prefix_rel (canon_args_rel D ups k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        forall j ys ys', j <= List.length (ptyp_doms t) -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups k) ms ws (ptyp_doms t)) j ys ys' ->
          per_gargs (List.firstn j (List.map ce_ass (ptyp_doms t)))
            (env_args nil (ups ++ ms ++ ws)) (env_args nil (ups' ++ ms' ++ ws')) ys ys'.
    Proof.
      intros * Hcon Heq Hg Hu Ha Hm Hw * Hj Hp.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
      rewrite List.length_rev, length_im_nparams in Hl, Hl'.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg Hu Ha Hm _ ws ws' HK Hw) as Hgw.
      eapply (tele_canon_gargs (List.map ce_ass (ptyp_doms t)) (nonrec_args_prefix gs K ++ im_nparams Mk)
                (shape_doms_rel (canon_doms_rel ups k) ms ws (ptyp_doms t)) ups ups' (ms ++ ws) (ms' ++ ws') a);
        [ apply tele_ass_map_ass | exact Hu | exact Hu'
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK; lia
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK; lia
        | | exact Ha | | | rewrite List.length_map; exact Hj | exact Hp ].
      - rewrite <- List.app_assoc; fold (im_params D Mk); rewrite List.rev_app_distr, (List.app_assoc ups), (List.app_assoc ups').
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np in *; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgw.
      - intros j0 A HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (ptyp_doms t) j0) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
        assert (Hj0 : j0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as [HBv _].
        rewrite List.firstn_map; fold (doms_ctx (List.firstn j0 (ptyp_doms t))).
        rewrite <- !List.app_assoc; fold (im_params D Mk); rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by exact HK.
        split; [ exact (vid_dctx _ HD _ _ _ _ _ _ _ j0 HM Hcon Heq ltac:(lia)) |].
        replace (j0 + (K + im_nn Mk)) with (j0 + K + im_nn Mk) by lia; exact HBv.
      - intros j0 A pre HA.
        rewrite List.nth_error_map in HA.
        destruct (List.nth_error (ptyp_doms t) j0) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
        unfold shape_doms_rel, canon_doms_rel; rewrite (List.nth_error_nth _ _ _ HB), <- !List.app_assoc; reflexivity.
    Qed.

    (** The arguments of a constructor before a recursive one, with the
        domains of its shape, as arguments of their telescope. *)
    Lemma rec_prefix_gargs : forall c gs gs1 t gs2 ups ups' a ms ms' ws ws' ys ys', ind_con Mk c = Some gs ->
        gs = gs1 ++ ca_rec t :: gs2 ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
        List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
        tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ms ms' ->
        tele_prefix_rel (canon_args_rel D ups k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
        forall j, j <= List.length (ptyp_doms t) -> tele_prefix_rel (shape_doms_rel (canon_doms_rel ups k) ms ws (ptyp_doms t)) j ys ys' ->
          per_gargs (List.rev (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk))
            nil nil (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys').
    Proof.
      intros * Hcon Heq Hg Hu Ha Hm Hw j Hj Hy.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg Hu Ha Hm _ ws ws' HK Hw) as Hgv.
      pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
      pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg Hu Ha Hm Hw j ys ys' Hj Hy) as Hgy.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      assert (Hrv : List.rev (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
                    = (List.rev (im_params D Mk) ++ List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1))))
                        ++ List.rev (doms_ctx (List.firstn j (ptyp_doms t))))
        by (rewrite !List.rev_app_distr; reflexivity).
      rewrite Hrv.
      replace (ups ++ ms ++ ws ++ ys) with (((ups ++ ms) ++ ws) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      replace (ups' ++ ms' ++ ws' ++ ys') with (((ups' ++ ms') ++ ws') ++ ys') by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro;
        [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, length_im_params by exact HK; unfold im_np in *; lia | |].
      - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np in *; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
      - unfold doms_ctx; rewrite List.rev_involutive, <- List.firstn_map, <- !List.app_assoc; exact Hgy.
    Qed.
  End Member.

  (** ** The Group at Related Uniform Parameters *)

  Section Canon.
    Variable (ups : list domain) (a : domain).
    Hypothesis (Hgd : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
      (Ha : ⟦ ind_sort D ⟧ env_args nil ups ↘ a).

    Lemma canon_hn : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        nparams_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm k0 A vs vs' HM Hk Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk0 : k0 < im_nn Mm)
        by (rewrite <- length_im_nparams, <- List.length_rev; apply List.nth_error_Some; congruence).
      pose proof (nr_gargs _ _ HM _ _ _ Hg2 Hu Ha k0 vs vs' ltac:(lia) Hp) as Hgv.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof (proj1 (vid_npar _ HD _ _ _ _ HM Hk)) as HAv; rewrite <- (length_nparams_prefix Mm k0) in HAv at 2 by lia.
      eapply (sort_typ_rel (nparams_prefix Mm k0) A (nparams_prefix_sem _ _ HM k0) HAv ups ups2 vs vs');
        [ rewrite length_nparams_prefix; lia | rewrite length_nparams_prefix; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite rev_nparams_prefix; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg2 | exact Hgv ].
    Qed.

    Lemma canon_ha : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        args_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs k0 A vs vs' HM Hm Hcon HA Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk : k0 < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      pose proof (ar_gargs _ _ HM _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm k0 vs vs' ltac:(lia) Hp) as Hgv.
      pose proof (params_gargs _ _ HM _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (vid_arg _ HD _ _ _ _ _ _ HM Hcon HA) as [HAv _].
      assert (HC : ⊨ (nonrec_args_prefix gs k0 ++ im_nparams Mm) ++ ind_uparams D)
        by (rewrite <- List.app_assoc; exact (vid_strat _ HD _ _ _ _ k0 HM Hcon ltac:(lia))).
      assert (HT : (nonrec_args_prefix gs k0 ++ im_nparams Mm) ++ ind_uparams D
                     ⊨ A : (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k0 ++ im_nparams Mm))]ʷ)
        by (rewrite <- List.app_assoc, List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; exact HAv).
      eapply (sort_typ_rel (nonrec_args_prefix gs k0 ++ im_nparams Mm) A HC HT ups ups2 (ms ++ vs) (ms' ++ vs'));
        [ rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; lia
        | rewrite !List.length_app, length_nonrec_args_prefix, length_im_nparams by lia; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite <- List.app_assoc; fold (im_params D Mm); rewrite List.rev_app_distr, !List.app_assoc.
      apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, length_im_params; unfold im_np; lia | exact Hpg |].
      unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
    Qed.

    Lemma canon_hd : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        doms_related (univ_idx a) D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs gs1 t gs2 ws ws' k0 B ys ys' HM Hm Hcon Heq Hw HB Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hkl : k0 < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      pose proof (rec_prefix_gargs _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hw k0 ltac:(lia) Hy) as Hgall.
      pose proof Hw as Hw0; rewrite tele_prefix_rel_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_prefix_rel_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ _ _ HM Hcon Heq HB) as [HBv _].
      set (Pre := doms_ctx (List.firstn k0 (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ im_nparams Mm).
      fold K in HBv.
      assert (HLP : List.length Pre = k0 + K + im_nn Mm)
        by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix, length_im_nparams by exact HK; lia).
      assert (HC : ⊨ Pre ++ ind_uparams D)
        by (unfold Pre; rewrite <- !List.app_assoc; exact (vid_dctx _ HD _ _ _ _ _ _ _ k0 HM Hcon Heq ltac:(lia))).
      assert (HT : Pre ++ ind_uparams D ⊨ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ)
        by (rewrite HLP; unfold Pre; rewrite <- !List.app_assoc; exact HBv).
      eapply (sort_typ_rel Pre B HC HT ups ups2 (ms ++ ws ++ ys) (ms' ++ ws' ++ ys'));
        [ rewrite HLP, !List.length_app; lia | rewrite HLP, !List.length_app; lia | exact Hu | exact Hu2 | | exact Ha ].
      unfold Pre; rewrite <- !List.app_assoc; exact Hgall.
    Qed.

    Lemma canon_hc : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        recs_related D ups ups2.
    Proof.
      intros ups2 Hg2 m Mm ms ms' c gs gs1 t gs2 ws ws' ys ys' HM Hm Hcon Heq Hp Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      pose proof (rec_prefix_gargs _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hp _ (le_n _)
                    (tele_rel_pre _ _ _ _ Hy)) as Hgall.
      rewrite List.firstn_all in Hgall; fold (ptyp_tele t) in Hgall.
      pose proof Hp as Hp0; rewrite tele_prefix_rel_iff in Hp0; destruct Hp0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_rel_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_rel_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_im_nparams in Hlm, Hlm'.
      destruct (length_rec_ps _ _ HM _ _ _ _ _ Hcon Heq) as (Mj & HMj & HPl).
      destruct (rec_closure _ _ HM _ _ _ _ _ _ Hcon Heq HMj ups ups2 ms ms' ws ws' ys ys' Hu Hlm Hlw Hly Hu2 Hlm' Hlw' Hly' Hgall)
        as (bs & bs' & Ebs & Ebs' & Hgb & _).
      apply (mk_rel_evals _ _ _ _ bs bs' Ebs Ebs').
      unfold ntele_rel; rewrite HMj.
      eapply (gargs_tele_canon _ (canon_nparams_rel D ups (ptyp_mem t)) (env_args nil ups)); [ | exact Hgb |].
      - intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMj HA), env_args_app; reflexivity.
      - rewrite (eval_exps_length _ _ _ Ebs), List.length_rev, length_im_nparams; exact HPl.
    Qed.

    (** The conditions of the clause at the canonical relations at [ups],
        and the bases admissible beside [ups]. *)
    Lemma canon_props_at : grp_tele_ass D -> ind_canon_props D ups.
    Proof.
      intros Hass0; constructor;
        [ exact (canon_nparams_per _ D ups ups (canon_hn ups Hgd))
        | exact (canon_nparams_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd))
        | exact (canon_args_per _ D ups ups (canon_ha ups Hgd))
        | exact (canon_args_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd) (canon_ha ups Hgd))
        | exact (canon_doms_per _ D ups ups (canon_hd ups Hgd))
        | exact (canon_doms_invariant _ D ups ups Hass0 Hu Hu (canon_hn ups Hgd) (canon_ha ups Hgd) (canon_hd ups Hgd)) ].
    Qed.

    Lemma canon_adm_at : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        adm_uparams D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) ups2.
    Proof.
      intros ups2 Hg2; exact (canon_adm (univ_idx a) D ups ups2 (canon_hn _ Hg2) (canon_ha _ Hg2) (canon_hc _ Hg2) (canon_hd _ Hg2)).
    Qed.
  End Canon.

  (** The sort at uniform parameters related to themselves has a value. *)
  Lemma sort_value : forall ups, per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> List.length ups = ind_nu D ->
      exists a, ⟦ ind_sort D ⟧ env_args nil ups ↘ a.
  Proof.
    intros ups Hg Hu.
    destruct (vid_sort _ HD) as [i HS].
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HRU0 : RU (env_args nil ups) (env_args nil ups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]).
    destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRU0) as (a & _ & Ea & _ & _); eauto.
  Qed.

  (** Uniform parameters related at their telescope: a PER. *)
  Lemma uparams_rel_env : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      forall RU, EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU -> RU (env_args nil ups) (env_args nil ups').
  Proof. intros * Hg Hu RU HRU; apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]. Qed.

  Lemma uparams_of_env : forall ups ups' RU, EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
      RU (env_args nil ups) (env_args nil ups') -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups'.
  Proof.
    intros * HRU Hu Hu' H.
    assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
    exact (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass HRU' nil nil ups ups'
                    ltac:(rewrite List.length_rev; exact Hu) ltac:(rewrite List.length_rev; exact Hu') H)).
  Qed.

  Lemma uparams_sym : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups' ups.
  Proof.
    intros * Hg Hu.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    apply (uparams_of_env _ _ RU HRU Hu' Hu); symmetry; exact (uparams_rel_env _ _ Hg Hu _ HRU).
  Qed.

  Lemma uparams_trans : forall ups ups' ups'', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups' ups'' -> per_gargs (List.rev (ind_uparams D)) nil nil ups ups''.
  Proof.
    intros * Hg Hu Hg'.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'; pose proof (length_ups_gargs _ _ Hg' Hu') as Hu''.
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
    apply (uparams_of_env _ _ RU HRU Hu Hu'').
    etransitivity; [ exact (uparams_rel_env _ _ Hg Hu _ HRU) | exact (uparams_rel_env _ _ Hg' Hu' _ HRU) ].
  Qed.

  (** ** The Canonical Model

      A declared member of the group at related parameters is a type of the
      universe the sort denotes, its elements those of the group's
      canonical relations. *)

  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : grp_tele_ass D).

  Lemma ind_relate : forall k Mk pm ups ups' ns ns' a, ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns' ->
      DF d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_univ_elem (univ_idx a)
        ↘ grp_rel p D ups (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups) k ups ups' ns ns'.
  Proof.
    intros * HM Hh Hg Hu Ha Hns.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof (uparams_refl_l _ _ Hg) as Hgd.
    eapply per_univ_elem_indty_canon;
      [ exact Hl | exact Hass | exact Hu | exact Hu' | | (eapply canon_hn; eassumption) | (eapply canon_hn; eassumption)
      | (eapply canon_ha; eassumption) | (eapply canon_ha; eassumption)
      | (eapply canon_hd; eassumption) | (eapply canon_hd; eassumption)
      | (eapply canon_hc; eassumption) | (eapply canon_hc; eassumption) | exact HM | exact Hh | exact Hns ].
    intros s; exact (per_gargs_top _ _ _ _ _ Hg ltac:(rewrite List.length_rev; exact Hu) s).
  Qed.

  Section DeclMember.
    Variables (k : nat) (Mk : imember) (pm : qname).
    Hypotheses (HM : ind_member D k = Some Mk) (Hh : im_head Mk = mh_decl pm).

    (** Parameters related over any bases are related over the empty one,
        and split into the uniform and the non-uniform ones. *)
    Lemma params_split_rel : forall ρ ρ' ys ys', per_gargs (List.rev (im_params D Mk)) ρ ρ' ys ys' ->
        List.length ys = im_np D Mk ->
        per_gargs (List.rev (ind_uparams D)) nil nil (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') /\
        per_gargs (List.rev (im_nparams Mk)) (env_args nil (List.firstn (ind_nu D) ys)) (env_args nil (List.firstn (ind_nu D) ys'))
          (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys') /\
        List.length (List.firstn (ind_nu D) ys) = ind_nu D /\ List.length ys' = im_np D Mk.
    Proof.
      intros * Hg Hlen.
      pose proof (per_gargs_length _ _ _ _ _ Hg) as [Hl' _].
      pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true (rev_params_sem _ _ HM) (rev_params_ass _ _ HM) ρ ρ' nil nil _ _ I I I Hg) as Hg0.
      rewrite <- (List.firstn_skipn (ind_nu D) ys), <- (List.firstn_skipn (ind_nu D) ys') in Hg0.
      rewrite rev_im_params in Hg0.
      assert (H1l : List.length (List.firstn (ind_nu D) ys) = List.length (List.rev (ind_uparams D)))
        by (rewrite List.length_firstn, List.length_rev; unfold im_np, ind_nu in *; lia).
      assert (H1l' : List.length (List.firstn (ind_nu D) ys') = List.length (List.rev (ind_uparams D)))
        by (rewrite List.length_firstn, List.length_rev; unfold im_np, ind_nu in *; lia).
      destruct (per_gargs_app (List.rev (ind_uparams D)) (List.rev (im_nparams Mk)) nil nil
                  (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys')
                  H1l Hg0 H1l') as [H1 H2].
      repeat split; [ exact H1 | exact H2 | rewrite List.length_firstn; unfold im_np in *; lia | lia ].
    Qed.

    (** The type former at related parameters, at the sort's universe. *)
    Lemma ind_at_params : forall ρ ρ' ys ys', per_gargs (List.rev (im_params D Mk)) ρ ρ' ys ys' ->
        List.length ys = im_np D Mk ->
        Dom d_ind p k ys ≈ d_ind p k ys' ∈ per_head ((ind_sort D)[wk_shiftn (im_nn Mk)]ʷ) ((ind_sort D)[wk_shiftn (im_nn Mk)]ʷ)
          (env_args ρ ys) (env_args ρ' ys').
    Proof.
      intros * Hg Hlen i0 R0 b b' Eb Eb' HR0.
      destruct (params_split_rel _ _ _ _ Hg Hlen) as (Hgu & Hgn & Hlu & Hl').
      set (ups := List.firstn (ind_nu D) ys) in *; set (ups' := List.firstn (ind_nu D) ys') in *.
      set (ns := List.skipn (ind_nu D) ys) in *; set (ns' := List.skipn (ind_nu D) ys') in *.
      assert (Hys : ys = ups ++ ns) by (symmetry; apply List.firstn_skipn).
      assert (Hys' : ys' = ups' ++ ns') by (symmetry; apply List.firstn_skipn).
      assert (Hlns : List.length ns = im_nn Mk) by (unfold ns; rewrite List.length_skipn; unfold im_np in *; lia).
      destruct (vid_sort _ HD) as [i HS].
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      pose proof (uparams_refl_l _ _ Hgu) as Hgu0.
      pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass nil nil ρ nil _ _ I I I Hgu0) as Hgρ.
      assert (HRUρ : RU (env_args ρ ups) (env_args nil ups)) by exact (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem Hlu Hgρ).
      destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRUρ) as (a0 & a & Ea0 & Ea & _).
      (** The index of the sort's universe, at the parameters' values and at
          the uniform ones. *)
      assert (Hub : is_univ b) by exact (sort_wk_univ _ _ _ Eb).
      destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
      destruct (rel_ctx_wf_per_ctx_env (vid_params _ HD _ _ HM)) as [RP HRP].
      assert (HPP : PER RP) by (eapply per_env_PER; exact HRP).
      assert (HRP0 : RP (env_args ρ ys) (env_args ρ' ys'))
        by (apply (gargs_env_rel _ _ _ _ _ _ HRP (vid_params _ HD _ _ HM)); [ rewrite length_im_params; exact Hlen | exact Hg ]).
      assert (HRPd : RP (env_args ρ ys) (env_args ρ ys)) by (etransitivity; [ exact HRP0 | symmetry; exact HRP0 ]).
      assert (Hwk : ⟪wk_shiftn (List.length (im_nparams Mk))⟫ (env_args ρ ys) = env_args ρ ups)
        by (rewrite Hys, env_args_app, length_im_nparams, <- Hlns; apply eval_wk_shiftn_args).
      rewrite <- length_im_nparams in Eb.
      pose proof (univ_idx_wk _ _ _ _ _ _ _ _ _ (vid_params _ HD _ _ HM) HS HRP HRPd Eb ltac:(rewrite Hwk; exact Ea0) Hub) as Hi1.
      pose proof (univ_idx_rel _ _ _ _ _ _ _ _ HRU HS HRUρ Ea0 Ea (sort_univ _ _ Ea0)) as Hi2.
      apply ER0; rewrite <- Hi1, <- Hi2.
      (** The type former at the parameters. *)
      assert (Hns : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns').
      { eapply (gargs_tele_canon _ (canon_nparams_rel D ups k) (env_args nil ups)); [ | exact Hgn | rewrite List.length_rev, length_im_nparams; exact Hlns ].
        intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA), env_args_app; reflexivity. }
      rewrite Hys, Hys'.
      eexists; exact (ind_relate _ _ _ _ _ _ _ _ HM Hh Hgu Hlu Ea Hns).
    Qed.

    (** ** The Type Former *)
    Lemma valid_exp_under_ctx_ind : ⋅ ⊨ a_ind p k : ind_ty D Mk.
    Proof.
      destruct (vid_ty _ HD _ _ HM) as [i HT].
      destruct (rel_exp_of_typ_inversion_simple HT) as (R & HR & Hsimp).
      apply (rel_exp_closed_intro _ _ i); [ intros; apply (ind_ty_sub _ _ _ _ Hc HM) | intros; reflexivity |].
      intros ρ ρ'.
      assert (Hρ : R ρ ρ') by (inversion HR; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Hsimp ρ ρ' Hρ) as (a & a' & Ea & Ea' & [R0 HR0]).
      exists a, a', R0, (d_ind p k nil), (d_ind p k nil).
      split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ constructor | split; [ constructor |] ] ] ] ].
      unfold ind_ty in Ea, Ea'; rewrite <- (List.rev_involutive (im_params D Mk)) in Ea, Ea'.
      eapply (ctx_pi_rel_elem (im_np D Mk) (d_ind p k) _ ltac:(intros xs x Hx; eapply eval_app_indty; eassumption)
                (List.rev (im_params D Mk)) (rev_params_ass _ _ HM) ρ ρ' nil nil);
        [ rewrite List.length_rev, length_im_params; reflexivity | reflexivity | exact Ea | exact Ea' | exact HR0 | ].
      intros ys ys' Hg Hlen; cbn [List.app]; apply ind_at_params; [ exact Hg | rewrite Hlen, List.length_rev, length_im_params; reflexivity ].
    Qed.
  End DeclMember.

  Lemma eval_apps_ind : forall k Mk ys xs, ind_member D k = Some Mk -> List.length xs + List.length ys <= im_np D Mk ->
      $*| d_ind p k xs & ys | gc_deps ⍮ gc_stack ↘ d_ind p k (xs ++ ys).
  Proof.
    intros k Mk; induction ys as [| y ys IH]; intros xs HM Hlen; [ rewrite List.app_nil_r; constructor |].
    econstructor; [ eapply eval_app_indty; [ exact Hl | exact HM | cbn in *; lia ] |].
    replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
    apply IH; [ exact HM | rewrite List.length_app; cbn in *; lia ].
  Qed.

  (** ** The Members as Values of the Context of the Members as Variables

      The type of [Self_j], the declared member [j] with the members as
      variables, is a type over the uniform parameters, and the type former
      [j] at uniform parameters is of it there.  So the values of the
      declared members at related uniform parameters, after them, are
      related environments of [grp_sctx D]. *)
  Section Selfs.
    Hypothesis (Hord : ind_order_ok D).

    Lemma self_ty_sem : forall j Mj, ind_member D j = Some Mj -> exists i : nat, ind_uparams D ⊨ self_ty D Mj : Typeω@i.
    Proof.
      intros * HMj.
      destruct (vid_sort _ HD) as [i HS].
      pose proof (vid_params _ HD _ _ HMj) as HP; unfold im_params in HP.
      pose proof (rel_exp_under_ctx_wk (rel_wk_under_ctx_shiftn _ _ HP) HS) as HSw; cbn [exp_wk] in HSw.
      unfold self_ty, im_nn; eapply rel_exp_ctx_pi; [ exact (member_nparams_ass _ _ HMj) | exact HP | exact HSw ].
    Qed.

    Lemma self_val_rel : forall j Mj, ind_member D j = Some Mj -> j < ind_ndecl D ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        forall i R a a', ⟦ self_ty D Mj ⟧ env_args nil ups ↘ a -> ⟦ self_ty D Mj ⟧ env_args nil ups' ↘ a' ->
          DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom d_ind p j ups ≈ d_ind p j ups' ∈ R.
    Proof.
      intros * HMj Hj * Hg Hu * Ea Ea' HR.
      assert (Hd : im_is_decl Mj = true) by (apply (proj2 (Hord _ _ HMj)); exact Hj).
      assert (Hh : exists pm, im_head Mj = mh_decl pm)
        by (unfold im_is_decl in Hd; destruct (im_head Mj); [ eauto | discriminate ]).
      destruct Hh as [pm Hh].
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      unfold self_ty in Ea, Ea'; rewrite <- (List.rev_involutive (im_nparams Mj)) in Ea, Ea'.
      eapply (ctx_pi_rel_elem (im_np D Mj) (d_ind p j) _ ltac:(intros xs x Hx; eapply eval_app_indty; eassumption)
                (List.rev (im_nparams Mj)) ltac:(apply List.Forall_rev, (member_nparams_ass _ _ HMj)) nil nil ups ups');
        [ rewrite List.length_rev, length_im_nparams; unfold im_np in *; lia | lia | exact Ea | exact Ea' | exact HR | ].
      intros ys ys' Hgy Hly.
      apply (ind_at_params _ _ _ HMj Hh); [| rewrite List.length_app, Hly, List.length_rev, length_im_nparams; unfold im_np in *; lia ].
      rewrite rev_im_params; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg | exact Hgy ].
    Qed.

    Lemma grp_selfs_prefix_sem : forall n, n <= ind_ndecl D ->
        ⊨ grp_selfs_from D 0 (List.firstn n (ind_members D)) ++ ind_uparams D.
    Proof.
      induction n as [| n IH]; intros Hn; [ exact uparams_sem |].
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; cbn [Nat.add List.app].
      pose proof (IH ltac:(lia)) as HC.
      destruct (self_ty_sem _ _ HMn) as [i Hi].
      pose proof (rel_exp_under_ctx_wk (rel_wk_under_ctx_shiftn _ _ HC) Hi) as Hw; cbn [exp_wk] in Hw.
      rewrite length_grp_selfs_from in Hw.
      exact (rel_ctx_wf_ext_typ _ _ _ HC Hw).
    Qed.

    Lemma grp_sctx_sem : ⊨ grp_sctx D.
    Proof. unfold grp_sctx, grp_selfs; exact (grp_selfs_prefix_sem _ (le_n _)). Qed.

    Lemma uparams_refl_r : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        per_gargs (List.rev (ind_uparams D)) nil nil ups' ups'.
    Proof.
      intros * Hg Hu.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      assert (HPU : PER RU) by (eapply per_env_PER; exact HRU).
      assert (H12 : RU (env_args nil ups) (env_args nil ups'))
        by (apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]).
      assert (H22 : RU (env_args nil ups') (env_args nil ups')) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
      assert (HRU' : EF List.rev (List.rev (ind_uparams D)) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D)) ++ ⋅ ∈ per_ctx_env ↘ RU)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HRU).
      destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true rev_uparams_sem rev_uparams_ass HRU' nil nil ups' ups'
                  ltac:(rewrite List.length_rev; exact Hu') ltac:(rewrite List.length_rev; exact Hu') H22) as [_ H].
      exact H.
    Qed.

    Lemma selfs_gargs : forall n, n <= ind_ndecl D ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        per_gargs (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) (env_args nil ups) (env_args nil ups')
          (List.map (fun j => d_ind p j ups) (List.seq 0 n)) (List.map (fun j => d_ind p j ups') (List.seq 0 n)).
    Proof.
      induction n as [| n IH]; intros Hn ups ups' Hg Hu; [ constructor |].
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      pose proof (uparams_refl_r _ _ Hg Hu) as Hgr.
      pose proof (uparams_refl_l _ _ Hg) as Hgl.
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      pose proof (IH ltac:(lia) _ _ Hg Hu) as IHn.
      pose proof (IH ltac:(lia) _ _ Hgr Hu') as IHr.
      set (Ψ := grp_selfs_from D 0 (List.firstn n (ind_members D))) in *.
      assert (HlΨ : List.length Ψ = n) by (unfold Ψ; rewrite length_grp_selfs_from, List.length_firstn; lia).
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; fold Ψ; cbn [Nat.add List.rev].
      rewrite List.seq_S, !List.map_app; cbn [List.map Nat.add].
      rewrite List.length_firstn; replace (Nat.min n (List.length (ind_members D))) with n by lia.
      (** The prefix environments are related at the prefix context. *)
      pose proof (grp_selfs_prefix_sem n ltac:(lia)) as HC; fold Ψ in HC.
      destruct (rel_ctx_wf_per_ctx_env HC) as [RΓ0 HRΓ0].
      assert (Henv : forall ys ys', per_gargs (List.rev (ind_uparams D)) nil nil ys ys' -> List.length ys = ind_nu D ->
                 per_gargs (List.rev Ψ) (env_args nil ys) (env_args nil ys')
                   (List.map (fun j => d_ind p j ys) (List.seq 0 n)) (List.map (fun j => d_ind p j ys') (List.seq 0 n)) ->
                 RΓ0 (env_args (env_args nil ys) (List.map (fun j => d_ind p j ys) (List.seq 0 n)))
                     (env_args (env_args nil ys') (List.map (fun j => d_ind p j ys') (List.seq 0 n)))).
      { intros ys ys' Hgy Hly Hgs; rewrite <- !env_args_app.
        apply (gargs_env_rel _ _ _ _ _ _ HRΓ0 HC); [ rewrite !List.length_app, List.length_map, List.length_seq; unfold ind_nu in *; lia |].
        rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hly | exact Hgy | exact Hgs ]. }
      destruct (self_ty_sem _ _ HMn) as [i Hi].
      destruct (rel_exp_under_ctx_wk_simple (rel_wk_under_ctx_shiftn _ _ HC) Hi) as (RΓ & HΓ & i0 & Hwk).
      assert (E0 : RΓ0 <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
      rewrite HlΨ in Hwk.
      assert (Hval : forall ys ys', per_gargs (List.rev (ind_uparams D)) nil nil ys ys' -> List.length ys = ind_nu D ->
                 per_gargs (List.rev Ψ) (env_args nil ys) (env_args nil ys')
                   (List.map (fun j => d_ind p j ys) (List.seq 0 n)) (List.map (fun j => d_ind p j ys') (List.seq 0 n)) ->
                 exists m m', ⟦ (self_ty D Mn)[wk_shiftn n]ʷ ⟧ env_args (env_args nil ys) (List.map (fun j => d_ind p j ys) (List.seq 0 n)) ↘ m /\
                   ⟦ self_ty D Mn ⟧ env_args nil ys' ↘ m' /\ Dom m ≈ m' ∈ per_univ i).
      { intros ys ys' Hgy Hly Hgs.
        destruct (Hwk _ _ (proj1 (E0 _ _) (Henv _ _ Hgy Hly Hgs))) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
        replace n with (List.length (List.map (fun j => d_ind p j ys') (List.seq 0 n))) in Em' at 1
          by (rewrite List.length_map, List.length_seq; reflexivity).
        rewrite eval_wk_shiftn_args in Em'.
        assert (Hy1 : y = d_univ i) by (cbn in Ey; inversion Ey; reflexivity).
        rewrite Hy1 in HRy.
        destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
        apply ERy in Hmm.
        exists m, m'; split; [ exact Em | split; [ exact Em' | exact Hmm ] ]. }
      destruct (Hval _ _ Hg Hu IHn) as (m & m' & Em & Em' & [R1 HR1]).
      destruct (Hval _ _ Hgr Hu' IHr) as (m2 & m2' & Em2 & Em2' & [R2 HR2]).
      assert (m2' = m') as -> by (eapply functional_eval_exp; eassumption).
      (** The type of [Self_n] at the left prefix, related to the one at the
          right prefix through the member's type at the right uniform
          parameters. *)
      pose proof (per_univ_sym _ _ _ _ HR2) as HR2'.
      pose proof (per_univ_trans _ _ _ _ _ _ HR1 (per_univ_elem_resp_iff HR2'
                    ltac:(eapply per_univ_elem_right_irrel; [ exact HR2' | exact (per_univ_sym _ _ _ _ HR1) ]))) as HR12.
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ i R1); [ rewrite List.length_rev, HlΨ, List.length_map, List.length_seq; reflexivity | exact IHn | |].
      - econstructor; [ exact Em | exact Em2 | exact HR12 ].
      - (** The value: the type former at the uniform parameters, of the
            member's type there. *)
        assert (Hn' : n < ind_ndecl D) by lia.
        destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
        assert (HRu : RU (env_args nil ups) (env_args nil ups'))
          by (apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ exact Hu | exact Hg ]).
        destruct (rel_exp_of_typ_inversion_simple_at HRU Hi _ _ HRu) as (b & b' & Eb & Eb' & [Rb HRb]).
        assert (b' = m') as -> by (eapply functional_eval_exp; eassumption).
        pose proof (self_val_rel _ _ HMn Hn' _ _ Hg Hu _ _ _ _ Eb Eb' HRb) as Hx.
        destruct (Hval _ _ Hgl Hu (IH ltac:(lia) _ _ Hgl Hu)) as (m3 & m3' & Em3 & Em3' & [R3 HR3]).
        assert (m3 = m) as -> by (eapply functional_eval_exp; eassumption).
        assert (m3' = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (E1 : R1 <~> R3) by (eapply per_univ_elem_right_irrel; eassumption).
        assert (E3 : R3 <~> Rb) by (eapply per_univ_elem_right_irrel; [ exact (per_univ_sym _ _ _ _ HR3) | exact HRb ]).
        apply E1, E3; exact Hx.
    Qed.

    (** The values of the declared members at the uniform parameters [ups],
        after them: an environment of [grp_sctx D]. *)
    Lemma selfs_env_rel : forall RS, EF grp_sctx D ≈ grp_sctx D ∈ per_ctx_env ↘ RS ->
        forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' -> List.length ups = ind_nu D ->
        RS (env_args (env_args nil ups) (selfs_vals p D ups)) (env_args (env_args nil ups') (selfs_vals p D ups')).
    Proof.
      intros RS HRS ups ups' Hg Hu.
      pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
      rewrite <- !env_args_app.
      apply (gargs_env_rel _ _ _ _ _ _ HRS grp_sctx_sem).
      - rewrite length_grp_sctx, List.length_app; unfold selfs_vals; rewrite List.length_map, List.length_seq; lia.
      - unfold grp_sctx, grp_selfs; rewrite List.rev_app_distr.
        apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hg |].
        exact (selfs_gargs _ (le_n _) _ _ Hg Hu).
    Qed.

    (** ** The Substitution of the Members for their Variables

        [grp_sb p D] is a substitution from the uniform parameters into
        the members as variables, built from valid parts: each declared
        member's type former at the uniform parameters is of its type with
        the members as variables. *)
    Hypothesis (Hmv : decl_mvc D).

    Lemma valid_self_apps : forall j Mj, ind_member D j = Some Mj -> j < ind_ndecl D ->
        ind_uparams D ⊨ apps (a_ind p j) (vars_from 0 (ind_nu D)) : self_ty D Mj.
    Proof.
      intros * HMj Hj.
      assert (Hd : im_is_decl Mj = true) by (apply (proj2 (Hord _ _ HMj)); exact Hj).
      assert (Hh : exists pm, im_head Mj = mh_decl pm)
        by (unfold im_is_decl in Hd; destruct (im_head Mj); [ eauto | discriminate ]).
      destruct Hh as [pm Hh].
      pose proof (closed_weaken_valid _ _ _ _ uparams_sem (valid_exp_under_ctx_ind _ _ _ HMj Hh)) as HI.
      unfold ind_ty, im_params in HI; rewrite ctx_pi_app in HI; fold (self_ty D Mj) in HI.
      destruct (self_ty_sem _ _ HMj) as [i Hi].
      destruct (closed_app_sem _ _ uparams_ass uparams_sem uparams_sem) as [HUU _].
      pose proof (closed_app_valid _ _ _ _ _ uparams_ass uparams_sem uparams_sem Hi) as HiU.
      pose proof (rel_exp_apps_ctx_pi_n _ (ind_uparams D) (ind_uparams D) _ i (a_ind p j) (vars_from 0 (ind_nu D)) eq_refl
                    uparams_ass HUU HiU HI ltac:(rewrite length_vars_from; reflexivity)) as H.
      rewrite (exp_at_vars _ _ _ (self_ty_scoped _ _ _ Hc HMj) (self_ty_mvc _ _ _ Hc Hmv HMj)) in H.
      rewrite (exp_wk_id_ext (self_ty D Mj) _ wk_shiftn_zero) in H.
      apply H.
      intros k N T HN HT.
      pose proof (valid_vars_tele nil (ind_uparams D) uparams_ass (dc_uparams _ Hc) (dmv_uparams _ Hmv) uparams_sem k N T) as Hv.
      cbn [List.length List.app] in Hv; exact (Hv HN HT).
    Qed.

    Lemma nth_rev_grp_selfs : forall n k, n <= ind_ndecl D -> k < n ->
        exists Mk, ind_member D k = Some Mk /\
          List.nth_error (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) k
            = Some (ce_ass (self_ty D Mk)[wk_shiftn k]ʷ).
    Proof.
      induction n as [| n IH]; intros k Hn Hk; [ lia |].
      pose proof (ind_ndecl_le D) as Hle.
      destruct (List.nth_error (ind_members D) n) as [Mn |] eqn:HMn; [| apply List.nth_error_None in HMn; lia ].
      rewrite (firstn_S_nth_error _ _ _ HMn), grp_selfs_from_snoc; cbn [Nat.add List.rev].
      assert (HlΨ : List.length (List.rev (grp_selfs_from D 0 (List.firstn n (ind_members D)))) = n)
        by (rewrite List.length_rev, length_grp_selfs_from, List.length_firstn; lia).
      destruct (Nat.lt_ge_cases k n) as [Hkn | Hkn].
      - rewrite List.nth_error_app1 by lia; exact (IH _ ltac:(lia) Hkn).
      - assert (k = n) as -> by lia.
        exists Mn; split; [ exact HMn |].
        rewrite List.nth_error_app2, HlΨ, Nat.sub_diag by lia; cbn.
        rewrite List.length_firstn, Nat.min_l by lia; reflexivity.
    Qed.

    Lemma grp_sb_gsub : gsub (ind_uparams D) (grp_sb p D) (grp_sctx D).
    Proof.
      unfold grp_sb, grp_sctx.
      apply gsub_of_list; [ exact (gsub_id _ uparams_sem) | | exact grp_sctx_sem | |].
      - unfold grp_selfs; generalize 0; induction (List.firstn (ind_ndecl D) (ind_members D)) as [| M ms IH]; intros j;
          cbn [grp_selfs_from]; [ constructor |].
        apply List.Forall_app; split; [ apply IH | constructor; [ eexists; reflexivity | constructor ] ].
      - unfold grp_selfs; rewrite length_grp_sb_list, length_grp_selfs_from, List.length_firstn.
        pose proof (ind_ndecl_le D); lia.
      - intros k N T HN HT.
        rewrite List.nth_error_map in HN.
        destruct (List.nth_error (List.seq 0 (ind_ndecl D)) k) as [j |] eqn:Hj; cbn in HN; [| discriminate ].
        injection HN as <-.
        assert (Hk : k < ind_ndecl D)
          by (rewrite <- (List.length_seq (ind_ndecl D) 0); apply List.nth_error_Some; congruence).
        assert (j = k) as -> by (rewrite (List.nth_error_nth' _ 0 (n := k)) in Hj by (rewrite List.length_seq; exact Hk);
                                 injection Hj as <-; rewrite List.seq_nth by exact Hk; reflexivity).
        apply tele_insts_nth in HT as (A & HA & ->).
        destruct (nth_rev_grp_selfs (ind_ndecl D) k (le_n _) Hk) as (Mk & HMk & HAk).
        unfold grp_selfs in HA; rewrite HAk in HA; injection HA as <-.
        rewrite exp_sub_wk, (exp_sub_sb_eq _ _ Id), exp_sub_id; [ exact (valid_self_apps _ _ HMk Hk) |].
        intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
        set (L := List.firstn k (List.map (fun j => apps (a_ind p j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D)))).
        assert (HL : List.length L = k)
          by (unfold L; rewrite List.length_firstn, length_grp_sb_list; lia).
        replace (x + k) with (List.length L + x) by lia.
        apply sb_of_list_ge.
    Qed.
  End Selfs.
End Sort.

(** ** Valid Filed Groups

    What the semantic lemmas about a group filed at [p] ask of it: it is
    found there, valid, closed, of a universe as its sort, with the
    conditions of the universe clause, typed, and filed at the path of its
    first member. *)
Record valid_group (p : qname) (D : ind_decl) : Prop := mk_valid_group
  { (** It is found at [p] *)
    vgr_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** It is semantically valid *)
  ; vgr_valid : valid_ind_decl D
    (** It is closed *)
  ; vgr_closed : decl_closed D
    (** Its sort is a universe *)
  ; vgr_sort : ind_sort_univ (ind_sort D)
    (** The structural conditions of the universe clause *)
  ; vgr_ass : grp_tele_ass D
    (** It is typed *)
  ; vgr_typed : decl_typed gc_deps gc_stack D
    (** It is filed at its first member's path *)
  ; vgr_mpath : ind_mpath D 0 = Some p }.

(** The groups the views of a group nest through are valid. *)
Definition containers_valid (D : ind_decl) : Prop :=
  forall k Mk qc k' Is vm Dq, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
    ind_lookup gc_deps gc_stack qc = Some Dq -> valid_group qc Dq.

End Fixed_GCtx.
