(** * Valid Declarations: the Type Former and the Constructors

    A declaration is semantically valid ([valid_ind_decl_cons]) when its telescopes and
    types are: these are the judgments of its typing, read in the PER model.
    From them, the inductive type at related parameters is a type of the
    universe its sort denotes ([ind_relate]), with the canonical relations of
    [Core.Semantic.Inductives.IndPER]; the type former and the constructors are then
    elements of their [Π]-types. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Decl.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Semantic Validity of a Declaration

    The core of a declaration's validity ([valid_ind_decl], with [nparams_prefix] and
    [nonrec_args_prefix]) is defined in [LogicalRelation/Definitions.v].  The judgments
    of the declaration's constructors: their contexts of arguments and their
    types, which mention the type former, so that they are read once the
    type former is known to be valid. *)
Record valid_ind_decl_cons (D : ind_decl) : Prop := mk_valid_ind_decl_cons
{ vic_core :> valid_ind_decl D
; vic_cargs : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    ⊨ cargs_ctx p D gs ++ ind_params D
; vic_cod : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    exists j, cargs_ctx p D gs ++ ind_params D ⊨ apps (a_ind p) (ind_pvars D (List.length gs)) : Typeω@j
; vic_conty : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    exists j, ⋅ ⊨ con_ty p D gs : Typeω@j
}.

(** ** Lists *)

Lemma length_nparams_prefix : forall D k, k <= ind_nn D -> List.length (nparams_prefix D k) = k.
Proof. intros; unfold nparams_prefix; rewrite List.length_rev, List.length_firstn, List.length_rev, length_nparams; lia. Qed.

Lemma length_nonrec_args_prefix : forall gs k, k <= List.length (cargs_nonrec gs) -> List.length (nonrec_args_prefix gs k) = k.
Proof. intros; unfold nonrec_args_prefix; rewrite List.length_rev, List.length_firstn, List.length_map; lia. Qed.

Lemma nparams_prefix_suffix : forall D k, exists Δ, ind_params D = Δ ++ nparams_prefix D k ++ ind_uparams D.
Proof.
  intros; exists (List.rev (List.skipn k (List.rev (ind_nparams D)))).
  rewrite params_split, List.app_assoc; f_equal.
  unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
Qed.

Lemma rev_nparams_prefix : forall D k, List.rev (nparams_prefix D k ++ ind_uparams D) = List.rev (ind_uparams D) ++ List.firstn k (List.rev (ind_nparams D)).
Proof. intros; unfold nparams_prefix; rewrite List.rev_app_distr, List.rev_involutive; reflexivity. Qed.

Lemma doms_ctx_snoc : forall Bs B, doms_ctx (Bs ++ B :: nil) = ce_ass B :: doms_ctx Bs.
Proof. intros; unfold doms_ctx; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.





(** The type of a recursive argument of a simple shape: its end under the
    shape's domains. *)
Lemma ptyp_ty_ctx_pi : forall p D t pat, ptyp_simple t = true ->
    ptyp_ty p D pat t = ctx_pi (sh_ctx pat (ptyp_doms t)) (ptyp_ty p D (List.repeat false (List.length (ptyp_doms t)) ++ pat) (pt_self 0 (ptyp_ps t))).
Proof.
  intros p0 D0; induction t as [[| k] Ps | k Ps | B t IH]; intros pat Hs; cbn in Hs; try discriminate; [ reflexivity |].
  cbn [ptyp_ty ptyp_doms sh_ctx List.length ptyp_ps].
  rewrite ctx_pi_app; cbn [ctx_pi].
  rewrite (IH _ Hs), repeat_false_cons; reflexivity.
Qed.


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

Lemma nparams_nth_split : forall D k A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
    exists Δ1, ind_nparams D = Δ1 ++ ce_ass A :: nparams_prefix D k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & Hl & Hlen).
  exists (List.rev l2).
  assert (Hf : List.firstn k (List.rev (ind_nparams D)) = l1)
    by (rewrite Hl, <- Hlen, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  unfold nparams_prefix; rewrite Hf, <- (List.rev_involutive (ind_nparams D)), Hl, List.rev_app_distr; cbn.
  rewrite <- List.app_assoc; reflexivity.
Qed.

(** ** A Telescope at the Sort

    A type of a declaration in the context [Pre] over the uniform parameters,
    of the sort shifted past [Pre], evaluates at related arguments to types
    of the universe the sort denotes at the uniform parameters. *)
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
    pose proof (decl_closed_nu D Hc) as Hle.
    destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
    assert (HRe : R (env_args nil (ups ++ zs)) (env_args nil (ups' ++ zs'))).
    { assert (HC' : ⊨ List.rev (List.rev (Pre ++ ind_uparams D)) ++ ⋅)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
      destruct (gargs_rel _ _ _ _ _ Hg _ _ per_ctx_env_nil_true I HC') as (R' & HR' & Hρ).
      rewrite List.firstn_all2 in HR'
        by (rewrite !List.length_app, List.length_rev, List.length_app, length_ind_uparams by exact Hle; lia).
      rewrite List.rev_involutive, List.app_nil_r in HR'.
      assert (E : R' <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
      apply E; exact Hρ. }
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

  (** Arguments related at a telescope of types at the sort, by the canonical
      relations, are arguments related at it. *)
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
      forall k vs vs', k <= List.length ts -> tele_pre tr k vs vs' ->
        per_gargs (List.firstn k ts) (env_args nil (ups ++ zs)) (env_args nil (ups' ++ zs')) vs vs'.
  Proof.
    intros * Hts Hu Hu' Hz Hz' Hg Ha Hv Htr k.
    induction k as [| k IH]; intros vs vs' Hk Hp.
    - rewrite tele_pre_iff in Hp; destruct Hp as (Hl & Hl' & _).
      destruct vs, vs'; cbn in *; try discriminate; constructor.
    - pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hl & Hl' & Hr).
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
      pose proof (IH _ _ ltac:(lia) (tele_pre_of_pre _ _ _ _ k Hp ltac:(lia))) as IHk.
      rewrite Hvs, Hvs'.
      destruct (Hv _ _ He) as [HC HT].
      assert (Hlf : List.length (List.firstn k ts) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv : List.length (List.firstn k vs) = k) by (rewrite List.length_firstn; lia).
      assert (Hlv' : List.length (List.firstn k vs') = k) by (rewrite List.length_firstn; lia).
      assert (Hg' : per_gargs (List.rev (List.rev (List.firstn k ts) ++ Pre0 ++ ind_uparams D)) nil nil
                      (ups ++ zs ++ List.firstn k vs) (ups' ++ zs' ++ List.firstn k vs')).
      { rewrite List.rev_app_distr, List.rev_involutive, !List.app_assoc.
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, List.length_app, length_ind_uparams
                                      by exact (decl_closed_nu D Hc); lia | exact Hg |].
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

  (** Conversely, arguments related at a telescope are related by the
      canonical relations. *)
  Lemma gargs_tele_canon : forall ts (tr : nat -> list domain -> relation domain) E,
      (forall j A pre, List.nth_error ts j = Some (ce_ass A) ->
         (tr j pre <~> per_head A A (env_args E pre) (env_args E pre))) ->
      forall E' vs vs', per_gargs ts E E' vs vs' -> List.length vs = List.length ts -> tele_full tr ts vs vs'.
  Proof.
    intros * Htr * Hg Hl.
    assert (Hgen : forall ts' ρ ρ' xs xs', per_gargs ts' ρ ρ' xs xs' ->
               forall k pre, ρ = env_args E pre -> List.length pre = k -> ts' = List.skipn k ts ->
               tele_rel_aux tr k pre xs xs').
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
    pose proof (per_gargs_length _ _ _ _ _ Hg) as [Hl' _].
    split; [ exact Hl |].
    exact (Hgen _ _ _ _ _ Hg 0 nil eq_refl eq_refl eq_refl).
  Qed.
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

  Lemma eval_exps_length : forall Ms ρ ms, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms -> List.length ms = List.length Ms.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma nparams_prefix_S : forall k A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
      nparams_prefix D (S k) = ce_ass A :: nparams_prefix D k.
  Proof. intros * H; unfold nparams_prefix; rewrite (firstn_S_snoc _ _ _ H), List.rev_app_distr; reflexivity. Qed.

  Lemma nparams_prefix_full : nparams_prefix D (ind_nn D) = ind_nparams D.
  Proof. unfold nparams_prefix; rewrite List.firstn_all2 by (rewrite List.length_rev, length_nparams; lia); apply List.rev_involutive. Qed.

  Lemma length_rec_ps : forall c gs gs1 Ps gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      List.length (ptyp_ps Ps) = ind_nn D.
  Proof.
    intros * Hcon Heq; pose proof (dc_rec_len _ Hc) as HPl.
    exact (HPl _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq).
  Qed.

  (** The parameters of a recursive argument, at related arguments before it,
      are related at the non-uniform parameters. *)
  Lemma rec_closure : forall c gs gs1 t gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      forall ups ups' ms ms' ws ws' ys ys',
        List.length ups = ind_nu D -> List.length ms = ind_nn D -> List.length ws = List.length (cargs_nonrec gs1) ->
        List.length ys = ptyp_depth t ->
        List.length ups' = ind_nu D -> List.length ms' = ind_nn D -> List.length ws' = List.length (cargs_nonrec gs1) ->
        List.length ys' = ptyp_depth t ->
        per_gargs (List.rev (ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D)) nil nil
          (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') ->
        exists bs bs', ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ms ++ ws ++ ys) ↘ bs /\
          ⟦ (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ bs' /\
          per_gargs (List.rev (ind_nparams D)) (env_args nil ups) (env_args nil ups') bs bs' /\
          (forall m P T, List.nth_error (ptyp_ps t) m = Some P ->
             List.nth_error (tele_insts (ind_nparams D)
                               (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + ind_nn D))) (ptyp_ps t)) m
               = Some T ->
             (per_head T T (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups' ++ ms' ++ ws' ++ ys'))
                <~> ind_nr D ups m (List.firstn m bs))).
  Proof.
    intros * Hcon Heq * Hu Hm Hw Hy Hu' Hm' Hw' Hy' Hg.
    rename t into Ps.
    pose proof (decl_closed_nu D Hc) as Hle.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (L := ptyp_depth Ps + K + ind_nn D).
    set (Ξ0 := ptyp_tele Ps ++ nonrec_args_prefix gs K ++ ind_params D).
    set (E := env_args nil (ups ++ ms ++ ws ++ ys)); set (E' := env_args nil (ups' ++ ms' ++ ws' ++ ys')).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (HΞ0 : ⊨ Ξ0).
    { pose proof (vid_dctx _ HD _ _ _ _ _ (List.length (ptyp_doms Ps)) Hcon Heq (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
    assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
    assert (HEE : R0 E E').
    { apply (gargs_env_rel Ξ0 R0 (ups ++ ms ++ ws ++ ys) (ups' ++ ms' ++ ws' ++ ys') nil nil); [ exact HR0 | exact HΞ0 | | exact Hg ].
      unfold Ξ0, ptyp_tele; rewrite !List.length_app, length_nonrec_args_prefix, doms_ctx_length by exact HK.
      rewrite params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; unfold ptyp_depth in Hy; lia. }
    pose proof (length_rec_ps _ _ _ _ _ Hcon Heq) as HPl.
    assert (HwkE : ⟪wk_shiftn L⟫ E = env_args nil ups).
    { unfold E, L; rewrite env_args_app; replace (ptyp_depth Ps + K + ind_nn D) with (List.length (ms ++ ws ++ ys))
        by (rewrite !List.length_app; lia); apply eval_wk_shiftn_args. }
    assert (HwkE' : ⟪wk_shiftn L⟫ E' = env_args nil ups').
    { unfold E', L; rewrite env_args_app; replace (ptyp_depth Ps + K + ind_nn D) with (List.length (ms' ++ ws' ++ ys'))
        by (rewrite !List.length_app; lia); apply eval_wk_shiftn_args. }
    (** The substitution of the uniform parameters: a shift past the
        arguments and the non-uniform parameters. *)
    assert (Hwk : Ξ0 ⊨ˢ sb_of_wk (wk_shiftn L) ≈ sb_of_wk (wk_shiftn L) : ind_uparams D).
    { apply rel_sub_of_wk.
      assert (HL : L = List.length (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ ind_nparams D))
        by (unfold L, ptyp_tele, ptyp_depth; rewrite !List.length_app, length_nonrec_args_prefix, length_nparams, doms_ctx_length by exact HK; lia).
      assert (HΞe : Ξ0 = (ptyp_tele Ps ++ nonrec_args_prefix gs K ++ ind_nparams D) ++ ind_uparams D)
        by (unfold Ξ0; rewrite params_split, <- !List.app_assoc; reflexivity).
      rewrite HΞe, HL; apply rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0. }
    (** The induction over the parameters of the recursive argument. *)
    assert (Hall : forall m, m <= ind_nn D ->
               Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps) ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps)
                 : nparams_prefix D m ++ ind_uparams D /\
               exists bs bs', ⟦ List.firstn m Ps ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ bs /\
                 ⟦ List.firstn m Ps ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ bs' /\
                 per_gargs (List.firstn m (List.rev (ind_nparams D))) (env_args nil ups) (env_args nil ups') bs bs' /\
                 (forall m' P T, m' < m -> List.nth_error Ps m' = Some P ->
                    List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) Ps) m' = Some T ->
                    (per_head T T E E' <~> ind_nr D ups m' (List.firstn m' bs)))).
    { induction m as [| m IH]; intros Hmn.
      - cbn [List.firstn sb_of_list]; unfold nparams_prefix; cbn [List.firstn List.rev List.app].
        split; [ exact Hwk |]; exists nil, nil; split; [ constructor | split; [ constructor | split; [ constructor | intros; lia ] ] ].
      - destruct (IH ltac:(lia)) as (Hτ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
        destruct (nth_error_lt_some' Ps m ltac:(lia)) as [P HP].
        assert (HT : exists T, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) Ps) m = Some T).
        { apply nth_error_lt_some'.
          rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc).
          rewrite length_nparams; lia. }
        destruct HT as [T HT].
        destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
        pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HT) as HPv.
        destruct (vid_npar _ HD _ _ HA) as (_ & j & HAv).
        set (τ := sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps)) in *.
        (** The new entry, and the substitution extended by it. *)
        assert (Hτ' : Ξ0 ⊨ˢ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) Ps)
                        ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) Ps) : nparams_prefix D (S m) ++ ind_uparams D).
        { rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (nparams_prefix_S _ _ HA); cbn [sb_of_list List.app].
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
            [ rewrite List.length_firstn, List.length_rev, length_nparams, (eval_exps_length _ _ _ Ebs), List.length_firstn; lia
            | exact Hgb | rewrite <- !env_args_app; exact (mk_rel_mod_eval t2 t3 Et2 Et3 Hn) | apply E23, Hb14 ].
        + intros m' P' T' Hmm' HP' HT'.
          destruct (Nat.lt_ge_cases m' m) as [Hlt | Hge].
          * rewrite List.firstn_app, Hlbs, (proj2 (Nat.sub_0_le m' m)) by lia; cbn; rewrite List.app_nil_r.
            exact (Hil _ _ _ Hlt HP' HT').
          * assert (m' = m) as -> by lia.
            rewrite HT in HT'; injection HT' as <-.
            rewrite List.firstn_app, Hlbs, Nat.sub_diag, List.firstn_all2 by lia; cbn; rewrite List.app_nil_r.
            unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA).
            assert (HR22 : DF t2 ≈ t2 ∈ per_univ_elem j ↘ R23)
              by (eapply per_univ_trans; [ exact HR23 | apply per_univ_sym; exact HR23 ]).
            pose proof (per_head_iff Et1 Et4 HR14) as Q1.
            pose proof (per_head_iff Et2 Et2 HR22) as Q2.
            intros x y; rewrite <- (Q1 x y), <- (Q2 x y), <- (E23 x y); reflexivity. }
    destruct (Hall (ind_nn D) (le_n _)) as (_ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
    rewrite List.firstn_all2 in Ebs, Ebs' by lia.
    rewrite List.firstn_all2 in Hgb by (rewrite List.length_rev, length_nparams; lia).
    exists bs, bs'; split; [ exact Ebs | split; [ exact Ebs' | split; [ exact Hgb |] ] ].
    intros m P T HP HT.
    assert (Hm0 : m < ind_nn D) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    exact (Hil _ _ _ Hm0 HP HT).
  Qed.

  Lemma uparams_sem : ⊨ ind_uparams D.
  Proof.
    destruct (nparams_prefix_suffix D 0) as [Δ HΔ]; unfold nparams_prefix in HΔ; cbn [List.firstn List.rev List.app] in HΔ.
    pose proof (vid_params _ HD) as H; rewrite HΔ in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  Lemma nparams_prefix_sem : forall k, ⊨ nparams_prefix D k ++ ind_uparams D.
  Proof. intros; destruct (nparams_prefix_suffix D k) as [Δ HΔ]; pose proof (vid_params _ HD) as H; rewrite HΔ in H; exact (rel_ctx_wf_app_r _ _ H). Qed.

  Lemma rev_uparams_sem : ⊨ List.rev (List.rev (ind_uparams D)) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact uparams_sem. Qed.

  Lemma uparams_refl_l : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof.
    intros * Hg; eapply (per_gargs_refl_l _ _ _ per_ctx_env_nil_true rev_uparams_sem); [ | exact I | exact Hg ].
    apply List.Forall_rev, (decl_uparams_ass D Hc).
  Qed.

  Lemma length_ups_gargs : forall ups ups', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> List.length ups' = ind_nu D.
  Proof. intros * Hg Hu; destruct (per_gargs_length _ _ _ _ _ Hg) as [Hl _]; lia. Qed.

  (** The canonical relations of the non-uniform parameters are those of the
      telescope. *)
  Lemma nr_gargs : forall ups ups' a, per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      forall k vs vs', k <= ind_nn D -> tele_pre (ind_nr D ups) k vs vs' ->
        per_gargs (List.firstn k (List.rev (ind_nparams D))) (env_args nil ups) (env_args nil ups') vs vs'.
  Proof.
    intros * Hg Hu Ha * Hk Hp.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof (tele_canon_gargs (List.rev (ind_nparams D)) nil (ind_nr D ups) ups ups' nil nil a
                  ltac:(apply List.Forall_rev, (decl_closed_nparams_ass D Hc)) Hu Hu' eq_refl eq_refl
                  ltac:(rewrite !List.app_nil_r; exact Hg) Ha) as Hcan.
    rewrite !List.app_nil_r in Hcan; apply Hcan; [ | | rewrite List.length_rev, length_nparams; exact Hk | exact Hp ].
    - intros j A HA; cbn [List.app List.length]; rewrite Nat.add_0_r.
      split; [ exact (nparams_prefix_sem j) | exact (proj1 (vid_npar _ HD _ _ HA)) ].
    - intros j A pre HA; unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA); reflexivity.
  Qed.

  Lemma params_gargs : forall ups ups' a ms ms', per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
      per_gargs (List.rev (ind_params D)) nil nil (ups ++ ms) (ups' ++ ms').
  Proof.
    intros * Hg Hu Ha Hm.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    rewrite rev_params_split; apply per_gargs_app_intro;
      [ rewrite List.length_rev, length_ind_uparams by exact (decl_closed_nu D Hc); exact Hu | exact Hg |].
    pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
    rewrite <- (List.firstn_all2 (n := ind_nn D) (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams; lia).
    eapply nr_gargs; [ exact Hg | exact Hu | exact Ha | lia |].
    rewrite <- (List.firstn_all2 (n := ind_nn D) ms), <- (List.firstn_all2 (n := ind_nn D) ms')
      by (rewrite List.length_rev, length_nparams in *; lia).
    apply tele_pre_of_full with (T := List.rev (ind_nparams D)); [ exact Hm | rewrite List.length_rev, length_nparams; lia ].
  Qed.

  (** The canonical relations of a constructor's non-recursive arguments are
      those of its telescope. *)
  Lemma ar_gargs : forall c gs ups ups' a ms ms', ind_con D c = Some gs ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
      forall k vs vs', k <= List.length (cargs_nonrec gs) -> tele_pre (ind_ar D ups ms c) k vs vs' ->
        per_gargs (List.firstn k (List.map ce_ass (cargs_nonrec gs))) (env_args nil (ups ++ ms)) (env_args nil (ups' ++ ms')) vs vs'.
  Proof.
    intros * Hcon Hg Hu Ha Hm * Hk Hp.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
    rewrite List.length_rev, length_nparams in Hl, Hl'.
    pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
    eapply (tele_canon_gargs (List.map ce_ass (cargs_nonrec gs)) (ind_nparams D) (ind_ar D ups ms c) ups ups' ms ms' a);
      [ apply tele_ass_map_ass | exact Hu | exact Hu' | rewrite length_nparams; exact Hl | rewrite length_nparams; exact Hl'
      | rewrite <- params_split; exact Hpg | exact Ha | | | rewrite List.length_map; exact Hk | exact Hp ].
    - intros j A HA.
      rewrite List.nth_error_map in HA.
      destruct (List.nth_error (cargs_nonrec gs) j) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
      assert (Hj : j < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      destruct (vid_arg _ HD _ _ _ _ Hcon HA0) as [HAv _].
      rewrite length_nparams, <- params_split.
      split; [ exact (vid_strat _ HD _ _ j Hcon ltac:(lia)) | exact HAv ].
    - intros j A pre HA.
      rewrite List.nth_error_map in HA.
      destruct (List.nth_error (cargs_nonrec gs) j) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
      unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hcon HA0); reflexivity.
  Qed.

  (** The canonical relations of the domains of a recursive argument's shape
      are those of their telescope. *)
  Lemma dom_gargs : forall c gs gs1 t gs2 ups ups' a ms ms' ws ws', ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
      tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      forall k ys ys', k <= List.length (ptyp_doms t) -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
        per_gargs (List.firstn k (List.map ce_ass (ptyp_doms t)))
          (env_args nil (ups ++ ms ++ ws)) (env_args nil (ups' ++ ms' ++ ws')) ys ys'.
  Proof.
    intros * Hcon Heq Hg Hu Ha Hm Hw * Hk Hp.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    set (K := List.length (cargs_nonrec gs1)) in *.
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hl & Hl' & _).
    rewrite List.length_rev, length_nparams in Hl, Hl'.
    pose proof Hw as Hw0; rewrite tele_pre_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
    pose proof (params_gargs _ _ _ _ _ Hg Hu Ha Hm) as Hpg.
    pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg Hu Ha Hm _ ws ws' HK Hw) as Hgw.
    eapply (tele_canon_gargs (List.map ce_ass (ptyp_doms t)) (nonrec_args_prefix gs K ++ ind_nparams D)
              (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) ups ups' (ms ++ ws) (ms' ++ ws') a);
      [ apply tele_ass_map_ass | exact Hu | exact Hu'
      | rewrite !List.length_app, length_nonrec_args_prefix, length_nparams by exact HK; lia
      | rewrite !List.length_app, length_nonrec_args_prefix, length_nparams by exact HK; lia
      | | exact Ha | | | rewrite List.length_map; exact Hk | exact Hp ].
    - rewrite <- List.app_assoc, <- params_split, List.rev_app_distr, (List.app_assoc ups), (List.app_assoc ups').
      apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                     by exact (decl_closed_nu D Hc); lia | exact Hpg |].
      unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgw.
    - intros j A HA.
      rewrite List.nth_error_map in HA.
      destruct (List.nth_error (ptyp_doms t) j) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
      assert (Hj : j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as [HBv _].
      rewrite List.firstn_map; fold (doms_ctx (List.firstn j (ptyp_doms t))).
      rewrite <- !List.app_assoc, <- params_split, !List.length_app, length_nonrec_args_prefix, length_nparams by exact HK.
      split; [ exact (vid_dctx _ HD _ _ _ _ _ j Hcon Heq ltac:(lia)) |].
      replace (j + (K + ind_nn D)) with (j + K + ind_nn D) by lia; exact HBv.
    - intros j A pre HA.
      rewrite List.nth_error_map in HA.
      destruct (List.nth_error (ptyp_doms t) j) as [B |] eqn:HB; cbn in HA; [ injection HA as -> | discriminate ].
      unfold shape_tr, ind_dr; rewrite (List.nth_error_nth _ _ _ HB), <- !List.app_assoc; reflexivity.
  Qed.

  (** ** The Inductive Type at Related Parameters *)

  Variable (p : qname).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D).

  Section Canon.
    Variable (ups : list domain) (a : domain).
    Hypothesis (Hgd : per_gargs (List.rev (ind_uparams D)) nil nil ups ups) (Hu : List.length ups = ind_nu D)
      (Ha : ⟦ ind_sort D ⟧ env_args nil ups ↘ a).
    Let Hle := decl_closed_nu D Hc.
    Let Hlu : List.length (List.rev (ind_uparams D)) = ind_nu D.
    Proof. rewrite List.length_rev; apply length_ind_uparams; exact Hle. Qed.

    Lemma canon_hn : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
               forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
               tele_pre (ind_nr D ups) k vs vs' ->
               exists t t', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ t /\ ⟦ A ⟧ env_args nil (ups2 ++ vs') ↘ t' /\
                 Dom t ≈ t' ∈ per_univ (univ_idx a).
    Proof.
      intros ups2 Hg2 * HA Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk : k < ind_nn D)
        by (rewrite <- length_nparams, <- List.length_rev; apply List.nth_error_Some; congruence).
      pose proof (nr_gargs _ _ _ Hg2 Hu Ha k vs vs' ltac:(lia) Hp) as Hgv.
      pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof (proj1 (vid_npar _ HD _ _ HA)) as HAv; rewrite <- (length_nparams_prefix D k) in HAv at 2 by lia.
      eapply (sort_typ_rel (nparams_prefix D k) A (nparams_prefix_sem k) HAv ups ups2 vs vs');
        [ rewrite length_nparams_prefix; lia | rewrite length_nparams_prefix; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite rev_nparams_prefix; apply per_gargs_app_intro; [ rewrite Hlu; exact Hu | exact Hg2 | exact Hgv ].
    Qed.

    Lemma canon_ha : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
               forall ms ms' c gs k A vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
               ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
               tele_pre (ind_ar D ups ms c) k vs vs' ->
               exists t t', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ t /\ ⟦ A ⟧ env_args nil (ups2 ++ ms' ++ vs') ↘ t' /\
                 Dom t ≈ t' ∈ per_univ (univ_idx a).
    Proof.
      intros ups2 Hg2 * Hm Hcon HA Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (Hk : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm k vs vs' ltac:(lia) Hp) as Hgv.
      pose proof (params_gargs _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hlv & Hlv' & _).
      pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_nparams in Hlm, Hlm'.
      destruct (vid_arg _ HD _ _ _ _ Hcon HA) as [HAv _].
      assert (HC : ⊨ (nonrec_args_prefix gs k ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact (vid_strat _ HD _ _ k Hcon ltac:(lia))).
      assert (HT : (nonrec_args_prefix gs k ++ ind_nparams D) ++ ind_uparams D
                     ⊨ A : (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k ++ ind_nparams D))]ʷ)
        by (rewrite <- List.app_assoc, <- params_split, List.length_app, length_nonrec_args_prefix, length_nparams by lia; exact HAv).
      eapply (sort_typ_rel (nonrec_args_prefix gs k ++ ind_nparams D) A HC HT ups ups2 (ms ++ vs) (ms' ++ vs'));
        [ rewrite !List.length_app, length_nonrec_args_prefix, length_nparams by lia; lia
        | rewrite !List.length_app, length_nonrec_args_prefix, length_nparams by lia; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite <- List.app_assoc, <- params_split, List.rev_app_distr, !List.app_assoc.
      apply per_gargs_app_intro; [ rewrite List.length_app; rewrite List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; lia
                                 | exact Hpg |].
      unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
    Qed.

    Lemma canon_hd : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
               forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
               ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               List.nth_error (ptyp_doms t) k = Some B ->
               tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
               exists b b', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b /\
                 ⟦ B ⟧ env_args nil (ups2 ++ ms' ++ ws' ++ ys') ↘ b' /\
                 Dom b ≈ b' ∈ per_univ (univ_idx a).
    Proof.
      intros ups2 Hg2 * Hm Hcon Heq Hw HB Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm _ ws ws' HK Hw) as Hgw.
      pose proof (params_gargs _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hw k ys ys' ltac:(lia) Hy) as Hgy.
      pose proof Hw as Hw0; rewrite tele_pre_iff in Hw0; destruct Hw0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_nparams in Hlm, Hlm'.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as [HBv _].
      set (Pre := doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ ind_nparams D).
      fold K in HBv.
      assert (HLP : List.length Pre = k + K + ind_nn D)
        by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, length_nonrec_args_prefix, length_nparams by exact HK; lia).
      assert (HC : ⊨ Pre ++ ind_uparams D)
        by (unfold Pre; rewrite <- !List.app_assoc, <- params_split; exact (vid_dctx _ HD _ _ _ _ _ k Hcon Heq ltac:(lia))).
      assert (HT : Pre ++ ind_uparams D ⊨ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ)
        by (rewrite HLP; unfold Pre; rewrite <- !List.app_assoc, <- params_split; exact HBv).
      eapply (sort_typ_rel Pre B HC HT ups ups2 (ms ++ ws ++ ys) (ms' ++ ws' ++ ys'));
        [ rewrite HLP, !List.length_app; lia | rewrite HLP, !List.length_app; lia | exact Hu | exact Hu2 | | exact Ha ].
      unfold Pre; rewrite <- !List.app_assoc, <- params_split.
      assert (Hrv : List.rev (doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ ind_params D)
                    = (List.rev (ind_params D) ++ List.rev (nonrec_args_prefix gs K)) ++ List.rev (doms_ctx (List.firstn k (ptyp_doms t))))
        by (rewrite !List.rev_app_distr; reflexivity).
      rewrite Hrv.
      replace (ups ++ ms ++ ws ++ ys) with (((ups ++ ms) ++ ws) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      replace (ups2 ++ ms' ++ ws' ++ ys') with (((ups2 ++ ms') ++ ws') ++ ys') by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro;
        [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, params_split, List.length_app,
            length_nparams, length_ind_uparams by (exact HK || exact Hle); lia | |].
      - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                       by exact Hle; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgw.
      - unfold doms_ctx; rewrite List.rev_involutive, <- List.firstn_map, <- !List.app_assoc; exact Hgy.
    Qed.

    Lemma canon_hc : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
               forall ms ms' c gs gs1 t gs2 ws ws' ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
               ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
               tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               tele_full (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
               exps_rel (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) (env_args nil (ups2 ++ ms' ++ ws' ++ ys'))
                 (tele_full (ind_nr D ups) (List.rev (ind_nparams D))).
    Proof.
      intros ups2 Hg2 * Hm Hcon Heq Hp Hy.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm _ ws ws' HK Hp) as Hgv.
      pose proof (params_gargs _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hg2 Hu Ha Hm Hp _ ys ys' (le_n _) (tele_full_pre _ _ _ _ Hy)) as Hgy.
      rewrite List.firstn_all2 in Hgy by (rewrite List.length_map; lia).
      pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hlw & Hlw' & _).
      pose proof Hy as Hy0; rewrite tele_full_iff in Hy0; destruct Hy0 as (Hly & Hly' & _).
      pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_nparams in Hlm, Hlm'.
      destruct (rec_closure _ _ _ _ _ Hcon Heq ups ups2 ms ms' ws ws' ys ys' Hu Hlm Hlw Hly Hu2 Hlm' Hlw' Hly')
        as (bs & bs' & Ebs & Ebs' & Hgb & _).
      { unfold ptyp_tele.
        assert (Hrv : List.rev (doms_ctx (ptyp_doms t) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D)
                      = (List.rev (ind_params D) ++ List.rev (nonrec_args_prefix gs (List.length (cargs_nonrec gs1)))) ++ List.rev (doms_ctx (ptyp_doms t)))
          by (rewrite !List.rev_app_distr; reflexivity).
        rewrite Hrv.
        replace (ups ++ ms ++ ws ++ ys) with (((ups ++ ms) ++ ws) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        replace (ups2 ++ ms' ++ ws' ++ ys') with (((ups2 ++ ms') ++ ws') ++ ys') by (rewrite <- !List.app_assoc; reflexivity).
        apply per_gargs_app_intro;
          [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, params_split, List.length_app,
              length_nparams, length_ind_uparams by (exact HK || exact Hle); lia | |].
        - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                         by exact Hle; lia | exact Hpg |].
          unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
        - unfold doms_ctx; rewrite List.rev_involutive, <- !List.app_assoc; exact Hgy. }
      apply (mk_exps_rel _ _ _ _ bs bs' Ebs Ebs').
      eapply (gargs_tele_canon _ (ind_nr D ups) (env_args nil ups)); [ | exact Hgb |].
      - intros j A pre HA; unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA), env_args_app; reflexivity.
      - rewrite (eval_exps_length _ _ _ Ebs), List.length_rev, length_nparams; exact (length_rec_ps _ _ _ _ _ Hcon Heq).
    Qed.

    (** The conditions of the clause, at the canonical relations. *)
    Lemma ind_canon :
      (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups) k vs vs' -> PER (ind_nr D ups k vs)) /\
      (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups) k vs vs' -> (ind_nr D ups k vs <~> ind_nr D ups k vs')) /\
      (forall ms ms' c gs k A vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ind_ar D ups ms c) k vs vs' -> PER (ind_ar D ups ms c k vs)) /\
      (forall ms ms' c gs k A vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
         List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ind_ar D ups ms c) k vs vs' ->
         (ind_ar D ups ms c k vs <~> ind_ar D ups ms' c k vs')) /\
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
         PER (ind_dr ups (ms ++ ws ++ ys) B)) /\
      (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
         (ind_dr ups (ms ++ ws ++ ys) B <~> ind_dr ups (ms' ++ ws' ++ ys') B)) /\
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ups.
    Proof.
      assert (Hn : forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
                 tele_pre (ind_nr D ups) k vs vs' ->
                 exists t t', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ t /\ ⟦ A ⟧ env_args nil (ups ++ vs') ↘ t' /\
                   Dom t ≈ t' ∈ per_univ (univ_idx a)) by (intros; eapply canon_hn; eassumption).
      assert (Hv : forall ms ms' c gs k A vs vs', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
                 ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
                 tele_pre (ind_ar D ups ms c) k vs vs' ->
                 exists t t', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ t /\ ⟦ A ⟧ env_args nil (ups ++ ms' ++ vs') ↘ t' /\
                   Dom t ≈ t' ∈ per_univ (univ_idx a)) by (intros; eapply canon_ha; eassumption).
      assert (Hd : forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
                 ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
                 tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
                 List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys' ->
                 exists b b', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b /\
                   ⟦ B ⟧ env_args nil (ups ++ ms' ++ ws' ++ ys') ↘ b' /\ Dom b ≈ b' ∈ per_univ (univ_idx a))
        by (intros; eapply canon_hd; eassumption).
      split; [| split; [| split; [| split; [| split; [| split ] ] ] ] ].
      - exact (canon_n_P _ D ups ups Hn).
      - exact (canon_n_I _ D ups ups (decl_closed_params D Hc) Hu Hu Hn).
      - exact (canon_a_P _ D ups ups Hv).
      - exact (canon_a_I _ D ups ups (decl_closed_params D Hc) Hu Hu Hn Hv).
      - exact (canon_d_P _ D ups ups Hd).
      - exact (canon_d_I _ D ups ups (decl_closed_params D Hc) Hu Hu Hn Hv Hd).
      - apply (canon_adm (univ_idx a) D ups ups Hn Hv); intros; [ eapply canon_hc | eapply canon_hd ]; eassumption.
    Qed.

    (** A base related to [ups] is admissible beside it. *)
    Lemma canon_adm_beside : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
        ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ups2.
    Proof.
      intros ups2 Hg2.
      apply (canon_adm (univ_idx a) D ups ups2); intros;
        [ eapply (canon_hn ups2 Hg2) | eapply (canon_ha ups2 Hg2) | eapply (canon_hc ups2 Hg2) | eapply (canon_hd ups2 Hg2) ];
        eassumption.
    Qed.
  End Canon.

  Lemma ind_relate : forall ups ups' ns ns' a,
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns' ->
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem (univ_idx a)
        ↘ (ind_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns ns').
  Proof.
    intros * Hg Hu Ha Hns.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof (uparams_refl_l _ _ Hg) as Hgd.
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (Hlu : List.length (List.rev (ind_uparams D)) = ind_nu D)
      by (rewrite List.length_rev; apply length_ind_uparams; exact Hle).
    eapply per_univ_elem_indty_canon;
      [ exact Hl | exact (decl_closed_params D Hc) | exact Hu | exact Hu' | | (eapply canon_hn; eassumption) | (eapply canon_ha; eassumption)
      | (eapply canon_hn; eassumption) | (eapply canon_ha; eassumption) | (eapply canon_hd; eassumption) | (eapply canon_hd; eassumption)
      | (eapply canon_hc; eassumption) | (eapply canon_hc; eassumption) | exact Hns ].
    intros s; exact (per_gargs_top _ _ _ _ _ Hg ltac:(rewrite Hlu; exact Hu) s).
  Qed.

  Lemma rev_params_sem : ⊨ List.rev (List.rev (ind_params D)) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact (vid_params _ HD). Qed.

  Lemma rev_params_ass : tele_ass (List.rev (ind_params D)).
  Proof. apply List.Forall_rev, (decl_closed_params D Hc). Qed.

  (** Parameters related over any bases are related over the empty one, and
      split into the uniform and the non-uniform ones. *)
  Lemma params_split_rel : forall ρ ρ' ys ys', per_gargs (List.rev (ind_params D)) ρ ρ' ys ys' ->
      List.length ys = ind_np D ->
      per_gargs (List.rev (ind_uparams D)) nil nil (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') /\
      per_gargs (List.rev (ind_nparams D)) (env_args nil (List.firstn (ind_nu D) ys)) (env_args nil (List.firstn (ind_nu D) ys'))
        (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys') /\
      List.length (List.firstn (ind_nu D) ys) = ind_nu D /\ List.length ys' = ind_np D.
  Proof.
    intros * Hg Hlen.
    pose proof (decl_closed_nu D Hc) as Hle.
    pose proof (per_gargs_length _ _ _ _ _ Hg) as [Hl' _].
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true rev_params_sem rev_params_ass ρ ρ' nil nil _ _ I I I Hg) as Hg0.
    rewrite <- (List.firstn_skipn (ind_nu D) ys), <- (List.firstn_skipn (ind_nu D) ys') in Hg0.
    rewrite rev_params_split in Hg0.
    assert (H1l : List.length (List.firstn (ind_nu D) ys) = List.length (List.rev (ind_uparams D)))
      by (rewrite List.length_firstn, List.length_rev, length_ind_uparams by exact Hle; unfold ind_np in *; lia).
    assert (H1l' : List.length (List.firstn (ind_nu D) ys') = List.length (List.rev (ind_uparams D)))
      by (rewrite List.length_firstn, List.length_rev, length_ind_uparams by exact Hle; unfold ind_np in *; lia).
    destruct (per_gargs_app (List.rev (ind_uparams D)) (List.rev (ind_nparams D)) nil nil
                (List.firstn (ind_nu D) ys) (List.firstn (ind_nu D) ys') (List.skipn (ind_nu D) ys) (List.skipn (ind_nu D) ys')
                H1l Hg0 H1l') as [H1 H2].
    repeat split; [ exact H1 | exact H2 | rewrite List.length_firstn; unfold ind_np in *; lia | lia ].
  Qed.

  (** The type former at related parameters, at the sort's universe. *)
  Lemma ind_at_params : forall ρ ρ' ys ys', per_gargs (List.rev (ind_params D)) ρ ρ' ys ys' ->
      List.length ys = ind_np D ->
      Dom d_ind p ys ≈ d_ind p ys' ∈ per_head ((ind_sort D)[wk_shiftn (ind_nn D)]ʷ) ((ind_sort D)[wk_shiftn (ind_nn D)]ʷ)
        (env_args ρ ys) (env_args ρ' ys').
  Proof.
    intros * Hg Hlen i0 R0 b b' Eb Eb' HR0.
    pose proof (decl_closed_nu D Hc) as Hle.
    destruct (params_split_rel _ _ _ _ Hg Hlen) as (Hgu & Hgn & Hlu & Hl').
    set (ups := List.firstn (ind_nu D) ys) in *; set (ups' := List.firstn (ind_nu D) ys') in *.
    set (ns := List.skipn (ind_nu D) ys) in *; set (ns' := List.skipn (ind_nu D) ys') in *.
    assert (Hys : ys = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (Hys' : ys' = ups' ++ ns') by (symmetry; apply List.firstn_skipn).
    assert (Hlns : List.length ns = ind_nn D) by (unfold ns; rewrite List.length_skipn; unfold ind_nn; lia).
    assert (Hlur : List.length ups = List.length (ind_uparams D)) by (rewrite length_ind_uparams by exact Hle; exact Hlu).
    destruct (vid_sort _ HD) as [i HS].
    destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
    pose proof (uparams_refl_l _ _ Hgu) as Hgu0.
    assert (Huass : tele_ass (List.rev (ind_uparams D))) by (apply List.Forall_rev, (decl_uparams_ass D Hc)).
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true rev_uparams_sem Huass nil nil ρ nil _ _ I I I Hgu0) as Hgρ.
    assert (HRUρ : RU (env_args ρ ups) (env_args nil ups)) by exact (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem Hlur Hgρ).
    destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRUρ) as (a0 & a & Ea0 & Ea & _).
    (** The index of the sort's universe, at the parameters' values and at the
        uniform ones. *)
    assert (Hub : is_univ b) by exact (sort_wk_univ _ _ _ Eb).
    destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
    destruct (rel_ctx_wf_per_ctx_env (vid_params _ HD)) as [RP HRP].
    assert (HPP : PER RP) by (eapply per_env_PER; exact HRP).
    assert (HRP0 : RP (env_args ρ ys) (env_args ρ' ys'))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRP (vid_params _ HD)); [ unfold ind_np in Hlen; exact Hlen | exact Hg ]).
    assert (HRPd : RP (env_args ρ ys) (env_args ρ ys)) by (etransitivity; [ exact HRP0 | symmetry; exact HRP0 ]).
    assert (HCp : ⊨ ind_nparams D ++ ind_uparams D) by (rewrite <- params_split; exact (vid_params _ HD)).
    assert (HRP' : EF ind_nparams D ++ ind_uparams D ≈ ind_nparams D ++ ind_uparams D ∈ per_ctx_env ↘ RP)
      by (rewrite <- params_split; exact HRP).
    assert (Hwk : ⟪wk_shiftn (List.length (ind_nparams D))⟫ (env_args ρ ys) = env_args ρ ups)
      by (rewrite Hys, env_args_app, length_nparams, <- Hlns; apply eval_wk_shiftn_args).
    rewrite <- length_nparams in Eb.
    pose proof (univ_idx_wk _ _ _ _ _ _ _ _ _ HCp HS HRP' HRPd Eb ltac:(rewrite Hwk; exact Ea0) Hub) as Hi1.
    pose proof (univ_idx_rel _ _ _ _ _ _ _ _ HRU HS HRUρ Ea0 Ea (sort_univ _ _ Ea0)) as Hi2.
    apply ER0; rewrite <- Hi1, <- Hi2.
    (** The type former at the parameters. *)
    assert (Hns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns').
    { eapply (gargs_tele_canon _ (ind_nr D ups) (env_args nil ups)); [ | exact Hgn | rewrite List.length_rev, length_nparams; exact Hlns ].
      intros j A pre HA; unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA), env_args_app; reflexivity. }
    rewrite Hys, Hys'.
    eexists; exact (ind_relate _ _ _ _ _ Hgu Hlu Ea Hns).
  Qed.

  (** ** The Type Former *)
  Lemma valid_exp_under_ctx_ind : ⋅ ⊨ a_ind p : ind_ty D.
  Proof.
    destruct (vid_ty _ HD) as [i HT].
    destruct (rel_exp_of_typ_inversion_simple HT) as (R & HR & Hsimp).
    apply (rel_exp_closed_intro _ _ i); [ intros; apply ind_ty_sub, Hc | intros; reflexivity |].
    intros ρ ρ'.
    assert (Hρ : R ρ ρ') by (inversion HR; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    destruct (Hsimp ρ ρ' Hρ) as (a & a' & Ea & Ea' & [R0 HR0]).
    exists a, a', R0, (d_ind p nil), (d_ind p nil).
    split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ constructor | split; [ constructor |] ] ] ] ].
    unfold ind_ty in Ea, Ea'; rewrite <- (List.rev_involutive (ind_params D)) in Ea, Ea'.
    eapply (ctx_pi_rel_elem (ind_np D) (d_ind p) _ (fun xs x Hx => eval_app_indty _ _ _ _ _ _ Hl Hx)
              (List.rev (ind_params D)) rev_params_ass ρ ρ' nil nil);
      [ rewrite List.length_rev; reflexivity | reflexivity | exact Ea | exact Ea' | exact HR0 | ].
    intros ys ys' Hg Hlen; cbn [List.app]; apply ind_at_params; [ exact Hg | rewrite Hlen, List.length_rev; reflexivity ].
  Qed.

  Lemma eval_apps_ind : forall ys xs, List.length xs + List.length ys <= ind_np D ->
      $*| d_ind p xs & ys | gc_deps ⍮ gc_stack ↘ d_ind p (xs ++ ys).
  Proof.
    induction ys as [| y ys IH]; intros xs Hlen; [ rewrite List.app_nil_r; constructor |].
    econstructor; [ eapply (eval_app_indty _ _ _ D); [ exact Hl | cbn in *; lia ] |].
    replace (xs ++ y :: ys) with ((xs ++ y :: nil) ++ ys) by (rewrite <- List.app_assoc; reflexivity).
    apply IH; rewrite List.length_app; cbn in *; lia.
  Qed.

  (** ** The Constructors *)

  Variable (c : String.string) (gs : list carg).
  Hypothesis (Hcon : ind_con D c = Some gs) (HΨ : ⊨ cargs_ctx p D gs ++ ind_params D).

  Lemma cargs_prefix_sem : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊨ cargs_ctx p D gs1 ++ ind_params D.
  Proof.
    intros * Heq; pose proof HΨ as H.
    rewrite Heq in H; unfold cargs_ctx in H; rewrite cargs_ctx_aux_app, <- List.app_assoc in H.
    exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  (** The weakening of a prefix of the arguments to its non-recursive ones. *)
  Lemma cargs_wk : forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D gs1 ++ ind_params D ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D.
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (rel_ctx_wf_per_ctx_env (vid_params _ HD)) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (vid_arg _ HD _ _ _ _ Hcon HA) as (_ & j & HAv).
        rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
        exact (rel_wk_under_ctx_q IHw HAv).
      + rewrite cargs_strat_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
  Qed.

  (** The weakening of the context of a recursive argument's domains to that
      of their types, from the one of the arguments before it. *)
  Lemma sh_wk_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      cargs_ctx p D gs1 ++ ind_params D ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D ->
      forall k, k <= List.length (ptyp_doms t) ->
        sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
          ⊨ʷ (wk_pat (List.repeat false k ++ cargs_pat gs1))
          : doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
  Proof.
    intros * Heq Hw0; induction k as [| k IH]; intros Hk.
    - exact Hw0.
    - destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, doms_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.repeat List.app wk_pat].
      destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      exact (rel_wk_under_ctx_q (IH ltac:(lia)) HBv).
  Qed.

  Lemma sh_sem_gen : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      ⊨ cargs_ctx p D gs1 ++ ind_params D ->
      cargs_ctx p D gs1 ++ ind_params D ⊨ʷ (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D ->
      forall k, k <= List.length (ptyp_doms t) ->
        ⊨ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D.
  Proof.
    intros * Heq HC0 Hw0; induction k as [| k IH]; intros Hk.
    - exact HC0.
    - destruct (nth_error_lt_some' (ptyp_doms t) k ltac:(lia)) as [B HB].
      pose proof (sh_wk_gen _ _ _ Heq Hw0 k ltac:(lia)) as Hw.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      pose proof (rel_exp_under_ctx_wk Hw HBv) as HBw; cbn [exp_wk] in HBw.
      pose proof (IH ltac:(lia)) as HC.
      destruct (rel_ctx_wf_per_ctx_env HC) as [R HR].
      rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
      cbn [List.app].
      econstructor; [ exact HC | exact (per_ctx_env_of_typ HR HBw) | exact HBw ].
  Qed.

  Lemma sh_wk : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall k, k <= List.length (ptyp_doms t) ->
        sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
          ⊨ʷ (wk_pat (List.repeat false k ++ cargs_pat gs1))
          : doms_ctx (List.firstn k (ptyp_doms t)) ++ cargs_strat gs1 ++ ind_params D.
  Proof. intros * Heq; exact (sh_wk_gen _ _ _ Heq (cargs_wk gs1 (ca_rec t :: gs2) Heq)). Qed.

  Lemma sh_sem : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall k, k <= List.length (ptyp_doms t) ->
        ⊨ sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D.
  Proof.
    intros * Heq; exact (sh_sem_gen _ _ _ Heq (cargs_prefix_sem gs1 (ca_rec t :: gs2) Heq) (cargs_wk gs1 (ca_rec t :: gs2) Heq)).
  Qed.

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

  (** ** A Recursive Argument of a Function Shape

      After [k] domains [ys] of a recursive argument's shape, related to
      themselves canonically, the relation of the type of the rest of the
      shape is the shape's relation ([ind_shape_rel]) of its rest. *)
  Lemma shape_char : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall ups ns fa a0, List.length ups = ind_nu D -> List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a0 ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
      (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      forall n k ys a (i : nat) R, k + n = List.length (ptyp_doms t) ->
        tele_pre (shape_tr (ind_dr ups) ns (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
        per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t))))
          (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
        ⟦ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t) ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a ->
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        (R <~> ind_shape_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
                 ups ups (ns ++ nonrec_vals gs1 fa ++ ys) (ns ++ nonrec_vals gs1 fa ++ ys) (ptyp_skip k t)).
  Proof.
    intros gs1 t gs2 Heq ups ns fa a0 Hlu Hlns Hlk Hgu0 Ha0 Hnsd INV Hpre.
    pose proof (decl_closed_nu D Hc) as Hle.
    destruct (ind_canon ups a0 Hgu0 Hlu Ha0) as (CnP & CnI & CaP & CaI & CdP & CdI & Cad).
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (proj1 (ind_shape_rel_rebase p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI
                         (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)))) as Hreb.
    pose proof (ind_rel_idx p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI
                  (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups))) as Hidx.
    pose proof (tnr_sym p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI) as Hsym.
    set (nv := nonrec_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hlnv : List.length nv = K) by (apply length_nonrec_vals; exact Hlk).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hlpat : List.length pat = List.length gs1) by (unfold pat; apply length_cargs_pat).
    assert (HwkE : forall ys, ⟪wk_pat (List.repeat false (List.length ys) ++ pat)⟫ (env_args nil (ups ++ ns ++ fa ++ ys))
                              = env_args nil (ups ++ ns ++ nv ++ ys)).
    { intros ys.
      replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_app, eval_wk_pat_falses by reflexivity.
      unfold pat; replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_app, eval_wk_pat_args by exact Hlk.
      rewrite <- !env_args_app, <- !List.app_assoc; reflexivity. }
    (** The arguments before, as arguments of their telescope. *)
    assert (Hgpf : per_gargs (List.rev (cargs_ctx p D gs1 ++ ind_params D)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
    { pose proof (cargs_prefix_sem gs1 (ca_rec t :: gs2) Heq) as HC.
      destruct (rel_ctx_wf_per_ctx_env HC) as [R0 HR0].
      assert (HC' : ⊨ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
      assert (HR0' : EF List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅
                       ≈ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅ ∈ per_ctx_env ↘ R0)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
      assert (Hl0 : List.length (ups ++ ns ++ fa) = List.length (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
        by (rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx; unfold ind_nn, ind_np in *; lia).
      assert (Hta : tele_ass (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
        by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params D Hc) ]).
      exact (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (Hpre _ HR0))). }
    assert (Hsimp : ptyp_simple t = true) by exact (vid_simple _ HD _ _ _ _ _ Hcon Heq).
    (** The environment of the arguments and [k] domains, in the context of
        their types. *)
    assert (Henv : forall k ys, k <= List.length (ptyp_doms t) -> List.length ys = k ->
               per_gargs (List.rev (sh_ctx pat (List.firstn k (ptyp_doms t)))) (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
               forall R0, EF sh_ctx pat (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
                            ≈ sh_ctx pat (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R0 ->
                 R0 (env_args nil (ups ++ ns ++ fa ++ ys)) (env_args nil (ups ++ ns ++ fa ++ ys))).
    { intros k ys Hk Hly Hg R0 HR0.
      apply (gargs_env_rel _ _ _ _ _ _ HR0 (sh_sem _ _ _ Heq k Hk)).
      - rewrite !List.length_app, length_sh_ctx, List.length_firstn, length_cargs_ctx; unfold ind_nn, ind_np in *; lia.
      - rewrite List.rev_app_distr.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        apply per_gargs_app_intro; [ rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx; unfold ind_nn, ind_np in *; lia
                                   | exact Hgpf |].
        exact Hg. }
    induction n as [| n IH]; intros k ys a i R Hkn Hy Hgy Ea HR.
    2: { (** A domain: related arguments of it give related results. *)
         assert (Hk : k < List.length (ptyp_doms t)) by lia.
         destruct (ptyp_skip_lt k t Hk) as (B & HB & Hs).
         rewrite Hs in Ea |- *.
         set (t' := ptyp_skip (S k) t) in *.
         set (pat' := List.repeat false k ++ pat) in *.
         cbn [ptyp_ty] in Ea.
         inversion Ea; subst a.
         basic_invert_per_univ_elem HR.
         rename H3 into Eb, H1 into HE, H0 into Hcod, H into HPin.
         pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
         pose proof (sh_wk _ _ _ Heq k ltac:(lia)) as Hw; fold pat in Hw.
         destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & HBv).
         rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
         destruct (rel_exp_under_ctx_wk_simple Hw HBv) as (RΓ & HΓ & i0 & Hwk).
         pose proof (Henv k ys ltac:(lia) Hly Hgy RΓ HΓ) as Hρ.
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
         assert (Edr : ind_dr ups (ns ++ nv ++ ys) B <~> in_rel).
         { unfold ind_dr.
           pose proof (per_head_iff Em' Em' HRm') as Q.
           intros u v; split; intro Huv.
           - apply Ein; apply Q in Huv; exact Huv.
           - apply Q; apply Ein; exact Huv. }
         assert (HdrP : PER (ind_dr ups (ns ++ nv ++ ys) B)).
         { split; intros u v; [ intro Huv | intros w Huv Hvw ]; apply Edr; apply Edr in Huv;
             [ symmetry; exact Huv | apply Edr in Hvw; etransitivity; eassumption ]. }
         (** The codomain at related arguments, by the induction. *)
         assert (Hcodr : forall c0 c0' (Hin : in_rel c0 c0'), exists a2,
                    ⟦ ptyp_ty p D (false :: pat') t' ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↦ c0 ↘ a2 /\
                    (out_rel c0 c0' Hin <~> ind_shape_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups))
                                              (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ups ups
                                              ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c0 :: nil) t')).
         { intros c0 c0' Hin.
           assert (Hin0 : in_rel c0 c0) by (etransitivity; [ exact Hin | symmetry; exact Hin ]).
           destruct (Hcod _ _ Hin) as [a2 a2' Ea2 Ea2' HR2].
           pose proof (per_univ_trans _ _ _ _ _ _ HR2 (per_univ_sym _ _ _ _ HR2)) as HR2d.
           exists a2; split; [ exact Ea2 |].
           replace ((ns ++ nv ++ ys) ++ c0 :: nil) with (ns ++ nv ++ (ys ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
           change t' with (ptyp_skip (S k) t).
           eapply (IH (S k) (ys ++ c0 :: nil) a2 i (out_rel _ _ Hin)); [ lia | | | | exact HR2d ].
           + apply tele_pre_snoc; [ exact Hy |].
             unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB).
             apply Edr; exact Hin0.
           + rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
             cbn [List.rev].
             apply (per_gargs_snoc _ _ _ _ _ _ _ _ i in_rel);
               [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgy | | exact Hin0 ].
             rewrite <- !env_args_app, <- !List.app_assoc.
             exact (mk_rel_mod_eval a1 a1 Eb Eb equiv_a_a').
           + cbn [List.repeat List.app].
             replace (ups ++ ns ++ fa ++ ys ++ c0 :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c0 :: nil) by (rewrite <- !List.app_assoc; reflexivity).
             rewrite env_args_snoc; exact Ea2. }
         (** The type's relation is the shape's at its own argument on both
             sides; the shape's at the right argument is that one, moved
             along the domain ([ind_shape_rel_rebase]). *)
         assert (Hmv : forall c0 c1 c2 r r', ind_dr ups (ns ++ nv ++ ys) B c0 c1 -> ind_dr ups (ns ++ nv ++ ys) B c1 c2 ->
                    ind_shape_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
                      ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c1 :: nil) t' r r' ->
                    ind_shape_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
                      ups ups ((ns ++ nv ++ ys) ++ c0 :: nil) ((ns ++ nv ++ ys) ++ c2 :: nil) t' r r').
         { intros c0 c1 c2 r r' H01 H12 Hs0.
           assert (H00 : ind_dr ups (ns ++ nv ++ ys) B c0 c0) by (etransitivity; [ exact H01 | symmetry; exact H01 ]).
           rewrite <- !List.app_assoc in Hs0 |- *.
           eapply (Hreb _ _ _ _ _ _ _ Hs0 ups ups ns ns ns ns c gs1 t gs2 nv nv nv nv (S k)
                     (ys ++ c0 :: nil) (ys ++ c1 :: nil) (ys ++ c0 :: nil) (ys ++ c2 :: nil));
             [ reflexivity | reflexivity | exact Cad | exact Cad | rewrite <- Heq; exact Hcon
             | exact Hnsd | exact Hnsd | exact Hnsd | exact INV | exact INV | exact INV | reflexivity | lia | | | ];
             (apply tele_pre_snoc; [ exact Hy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); assumption ]). }
         intros x x'; split; intro Hx.
         - constructor; intros c0 c0' Hcc.
           pose proof (proj1 (Edr _ _) Hcc) as Hin.
           pose proof (proj1 (HE x x') Hx) as Hx2; cbn beta in Hx2.
           destruct (Hx2 _ _ Hin) as [r r' Er Er' Hrr].
           destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
           assert (H00 : ind_dr ups (ns ++ nv ++ ys) B c0 c0) by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
           econstructor; [ exact Er | exact Er' | exact (Hmv _ _ _ _ _ H00 Hcc (proj1 (Ecod _ _) Hrr)) ].
         - apply HE; intros c0 c0' Hin.
           pose proof (proj2 (Edr _ _) Hin) as Hcc.
           destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx _ _ Hcc) as (r & r' & Er & Er' & Hrr).
           destruct (Hcodr _ _ Hin) as (a2 & _ & Ecod).
           assert (Hc'c : ind_dr ups (ns ++ nv ++ ys) B c0' c0) by (symmetry; exact Hcc).
           econstructor; [ exact Er | exact Er' | apply Ecod; exact (Hmv _ _ _ _ _ Hcc Hc'c Hrr) ]. }
    (** The end of the shape: an element of the inductive type at the
        parameters it evaluates to. *)
    assert (Hkd : k = List.length (ptyp_doms t)) by lia.
    subst k.
    rewrite (ptyp_skip_end t Hsimp) in Ea |- *.
    cbn [ptyp_ty ptyp_ps] in Ea.
    set (L := List.length (ptyp_doms t)) in *.
    pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
    assert (Hgall : per_gargs (List.rev (ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_params D)) nil nil
                      (ups ++ ns ++ nv ++ ys) (ups ++ ns ++ nv ++ ys)).
    { pose proof (params_gargs _ _ _ _ _ Hgu0 Hlu Ha0 Hnsd) as Hpg.
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hgu0 Hlu Ha0 Hnsd _ nv nv HK INV) as Hgv.
      pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hgu0 Hlu Ha0 Hnsd INV L ys ys (le_n _) Hy) as Hgd.
      rewrite List.firstn_all2 in Hgd by (rewrite List.length_map; lia).
      unfold ptyp_tele.
      assert (Hrv : List.rev (doms_ctx (ptyp_doms t) ++ nonrec_args_prefix gs K ++ ind_params D)
                    = (List.rev (ind_params D) ++ List.rev (nonrec_args_prefix gs K)) ++ List.rev (doms_ctx (ptyp_doms t)))
        by (rewrite !List.rev_app_distr; reflexivity).
      rewrite Hrv.
      replace (ups ++ ns ++ nv ++ ys) with (((ups ++ ns) ++ nv) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      apply per_gargs_app_intro;
        [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, params_split, List.length_app,
            length_nparams, length_ind_uparams by (exact HK || exact Hle); lia | |].
      - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                       by exact Hle; lia | exact Hpg |].
        unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
      - unfold doms_ctx; rewrite List.rev_involutive, <- !List.app_assoc; exact Hgd. }
    destruct (rec_closure _ _ _ _ _ Hcon Heq ups ups ns ns nv nv ys ys Hlu Hlns Hlnv Hly Hlu Hlns Hlnv Hly Hgall)
      as (bs & bs0 & Ebs & _ & _ & Hil).
    set (pat' := List.repeat false L ++ pat) in *.
    assert (HlPs : List.length (ptyp_ps t) = ind_nn D) by exact (length_rec_ps _ _ _ _ _ Hcon Heq).
    pose proof (sh_wk _ _ _ Heq L (le_n _)) as Hw; fold pat pat' in Hw.
    assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
    rewrite Hft in Hw.
    assert (HTex : forall m, m < ind_nn D ->
               exists Tm, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) m = Some Tm).
    { intros m Hm; apply nth_error_lt_some'.
      rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
    assert (Hlink : forall m P Tm, List.nth_error (ptyp_ps t) m = Some P ->
               List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) m = Some Tm ->
               exists b1 b, ⟦ P[wk_pat pat']ʷ ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ b1 /\ ⟦ P ⟧ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b /\
                 ind_nr D ups m (List.firstn m bs) b b1).
    { intros * HP HTm.
      pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HTm) as HPv.
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
    { intros m M HM; rewrite List.nth_error_map in HM.
      destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; cbn in HM; [ injection HM as <- | discriminate ].
      assert (Hm : m < ind_nn D) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
      destruct (HTex _ Hm) as [Tm HTm].
      destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
    assert (Htf : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs1).
    { rewrite tele_full_iff, List.length_rev, length_nparams.
      rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ Ebs1), List.length_map.
      split; [ exact HlPs | split; [ exact HlPs |] ].
      intros j y y' Hy1 Hy1'.
      assert (Hj : j < ind_nn D) by (rewrite <- HlPs, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' (ptyp_ps t) j ltac:(lia)) as [P HP].
      destruct (HTex _ Hj) as [Tm HTm].
      destruct (Hlink _ _ _ HP HTm) as (b1 & b & Eb1 & Eb & Hr).
      destruct (eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
      destruct (eval_exps_nth _ _ _ _ _ Ebs1 ltac:(rewrite List.nth_error_map, HP; reflexivity)) as (b2 & Hb2 & Eb2).
      assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
      rewrite Hy1 in Hb0; injection Hb0 as ->; rewrite Hy1' in Hb2; injection Hb2 as ->; exact Hr. }
    pose proof (ind_relate _ _ _ _ _ Hgu0 Hlu Ha0 Htf) as Hind.
    pose proof (per_univ_sym _ _ _ _ Hind) as Hind'.
    assert (Et0 : ⟦ apps (a_ind p) (ind_uvars D (List.length pat') ++ List.map (fun P => P[wk_pat pat']ʷ) (ptyp_ps t)) ⟧
                    env_args nil (ups ++ ns ++ fa ++ ys) ↘ d_ind p (ups ++ bs1)).
    { apply eval_apps_exp; exists (d_ind p nil), (ups ++ bs1); split; [ constructor | split ].
      - apply eval_exps_app; [| exact Ebs1 ].
        unfold ind_uvars.
        replace (List.length pat' + ind_nn D) with (List.length (ns ++ fa ++ ys))
          by (unfold pat'; rewrite !List.length_app, List.repeat_length; lia).
        replace (ind_nu D) with (List.length ups) by exact Hlu.
        apply eval_vars_from_args.
      - change (d_ind p (ups ++ bs1)) with (d_ind p (nil ++ (ups ++ bs1))).
        apply eval_apps_ind; rewrite List.length_app, (eval_exps_length _ _ _ Ebs1), List.length_map; cbn; unfold ind_nn in *; lia. }
    assert (a = d_ind p (ups ++ bs1)) as -> by (eapply functional_eval_exp; eassumption).
    assert (ERk : R <~> ind_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups) bs bs1)
      by (eapply per_univ_elem_right_irrel; [ exact HR | exact Hind' ]).
    pose proof (tnr_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ Htf) as Hbb.
    intros x x'; split; intro Hx.
    - econstructor; [ exact Ebs | exact Ebs | exact (Hidx _ _ _ _ _ _ (proj1 (ERk _ _) Hx) Hbb (Hsym _ _ Htf)) ].
    - destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx) as (b1 & b2 & E1 & E2 & Hr).
      pose proof (functional_eval_exps' _ _ _ _ E1 Ebs) as ->.
      pose proof (functional_eval_exps' _ _ _ _ E2 Ebs) as ->.
      apply ERk; exact (Hidx _ _ _ _ _ _ Hr Hbb Htf).
  Qed.

  (** The links of a recursive argument's type to its shape after [k]
      domains [ys]: the value of the next domain, weakened past the
      recursive arguments before, is related to the domain's value; at the
      end, the values of the parameters of the leaf, weakened, are related to
      the parameters' values. *)
  Lemma shape_links : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall ups ns fa a0, List.length ups = ind_nu D -> List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a0 ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
      (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      forall k ys, k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr (ind_dr ups) ns (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
        per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t))))
          (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
        (forall B, List.nth_error (ptyp_doms t) k = Some B ->
           exists (j : nat) a1 b, ⟦ B[wk_pat (List.repeat false k ++ cargs_pat gs1)]ʷ ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a1 /\
             ⟦ B ⟧ env_args nil (ups ++ ns ++ nonrec_vals gs1 fa ++ ys) ↘ b /\ Dom a1 ≈ b ∈ per_univ j) /\
        (k = List.length (ptyp_doms t) ->
           exists bs bs1, ⟦ ptyp_ps t ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nonrec_vals gs1 fa ++ ys) ↘ bs /\
             ⟦ List.map (fun P => P[wk_pat (List.repeat false k ++ cargs_pat gs1)]ʷ) (ptyp_ps t) ⟧* gc_deps ⍮ gc_stack
               ⍮ env_args nil (ups ++ ns ++ fa ++ ys) ↘ bs1 /\
             tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs1).
  Proof.
    intros gs1 t gs2 Heq ups ns fa a0 Hlu Hlns Hlk Hgu0 Ha0 Hnsd INV Hpre.
    pose proof (decl_closed_nu D Hc) as Hle.
    set (nv := nonrec_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hlnv : List.length nv = K) by (apply length_nonrec_vals; exact Hlk).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hlpat : List.length pat = List.length gs1) by (unfold pat; apply length_cargs_pat).
    assert (HwkE : forall ys, ⟪wk_pat (List.repeat false (List.length ys) ++ pat)⟫ (env_args nil (ups ++ ns ++ fa ++ ys))
                              = env_args nil (ups ++ ns ++ nv ++ ys)).
    { intros ys.
      replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_app, eval_wk_pat_falses by reflexivity.
      unfold pat; replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_app, eval_wk_pat_args by exact Hlk.
      rewrite <- !env_args_app, <- !List.app_assoc; reflexivity. }
    (** The arguments before, as arguments of their telescope. *)
    assert (Hgpf : per_gargs (List.rev (cargs_ctx p D gs1 ++ ind_params D)) nil nil (ups ++ ns ++ fa) (ups ++ ns ++ fa)).
    { pose proof (cargs_prefix_sem gs1 (ca_rec t :: gs2) Heq) as HC.
      destruct (rel_ctx_wf_per_ctx_env HC) as [R0 HR0].
      assert (HC' : ⊨ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
      assert (HR0' : EF List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅
                       ≈ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅ ∈ per_ctx_env ↘ R0)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
      assert (Hl0 : List.length (ups ++ ns ++ fa) = List.length (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
        by (rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx; unfold ind_nn, ind_np in *; lia).
      assert (Hta : tele_ass (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
        by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params D Hc) ]).
      exact (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (Hpre _ HR0))). }
    assert (Hsimp : ptyp_simple t = true) by exact (vid_simple _ HD _ _ _ _ _ Hcon Heq).
    (** The environment of the arguments and [k] domains, in the context of
        their types. *)
    assert (Henv : forall k ys, k <= List.length (ptyp_doms t) -> List.length ys = k ->
               per_gargs (List.rev (sh_ctx pat (List.firstn k (ptyp_doms t)))) (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
               forall R0, EF sh_ctx pat (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
                            ≈ sh_ctx pat (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R0 ->
                 R0 (env_args nil (ups ++ ns ++ fa ++ ys)) (env_args nil (ups ++ ns ++ fa ++ ys))).
    { intros k ys Hk Hly Hg R0 HR0.
      apply (gargs_env_rel _ _ _ _ _ _ HR0 (sh_sem _ _ _ Heq k Hk)).
      - rewrite !List.length_app, length_sh_ctx, List.length_firstn, length_cargs_ctx; unfold ind_nn, ind_np in *; lia.
      - rewrite List.rev_app_distr.
        replace (ups ++ ns ++ fa ++ ys) with ((ups ++ ns ++ fa) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        apply per_gargs_app_intro; [ rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx; unfold ind_nn, ind_np in *; lia
                                   | exact Hgpf |].
        exact Hg. }
    intros k ys Hk Hy Hgy.
    pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
    split.
    - intros B HB.
      pose proof (sh_wk _ _ _ Heq k ltac:(lia)) as Hw; fold pat in Hw.
      destruct (vid_dom _ HD _ _ _ _ _ _ _ Hcon Heq HB) as (_ & j & HBv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HBv.
      destruct (rel_exp_under_ctx_wk_simple Hw HBv) as (RΓ & HΓ & i0 & Hwk).
      pose proof (Henv k ys ltac:(lia) Hly Hgy RΓ HΓ) as Hρ.
      destruct (Hwk _ _ Hρ) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
      assert (Hy1 : y = d_univ j) by (cbn in Ey; inversion Ey; reflexivity).
      rewrite Hy1 in HRy; clear Hy1 Ey Ey'.
      destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
      apply ERy in Hmm.
      rewrite <- Hly, HwkE in Em'.
      exists j, m, m'; split; [ exact Em | split; [ exact Em' | exact Hmm ] ].
    - intros Hkd; rewrite Hkd in Hly, Hy, Hgy |- *; clear Hkd Hk.
      set (L := List.length (ptyp_doms t)) in *.
      assert (Hgall : per_gargs (List.rev (ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_params D)) nil nil
                        (ups ++ ns ++ nv ++ ys) (ups ++ ns ++ nv ++ ys)).
      { pose proof (params_gargs _ _ _ _ _ Hgu0 Hlu Ha0 Hnsd) as Hpg.
        pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hgu0 Hlu Ha0 Hnsd _ nv nv HK INV) as Hgv.
        pose proof (dom_gargs _ _ _ _ _ _ _ _ _ _ _ _ Hcon Heq Hgu0 Hlu Ha0 Hnsd INV L ys ys (le_n _) Hy) as Hgd.
        rewrite List.firstn_all2 in Hgd by (rewrite List.length_map; lia).
        unfold ptyp_tele.
        assert (Hrv : List.rev (doms_ctx (ptyp_doms t) ++ nonrec_args_prefix gs K ++ ind_params D)
                      = (List.rev (ind_params D) ++ List.rev (nonrec_args_prefix gs K)) ++ List.rev (doms_ctx (ptyp_doms t)))
          by (rewrite !List.rev_app_distr; reflexivity).
        rewrite Hrv.
        replace (ups ++ ns ++ nv ++ ys) with (((ups ++ ns) ++ nv) ++ ys) by (rewrite <- !List.app_assoc; reflexivity).
        apply per_gargs_app_intro;
          [ rewrite !List.length_app, !List.length_rev, length_nonrec_args_prefix, params_split, List.length_app,
              length_nparams, length_ind_uparams by (exact HK || exact Hle); lia | |].
        - apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams
                                         by exact Hle; lia | exact Hpg |].
          unfold nonrec_args_prefix; rewrite List.rev_involutive; exact Hgv.
        - unfold doms_ctx; rewrite List.rev_involutive, <- !List.app_assoc; exact Hgd. }
      destruct (rec_closure _ _ _ _ _ Hcon Heq ups ups ns ns nv nv ys ys Hlu Hlns Hlnv Hly Hlu Hlns Hlnv Hly Hgall)
        as (bs & bs0 & Ebs & _ & _ & Hil).
      set (pat' := List.repeat false L ++ pat) in *.
      assert (HlPs : List.length (ptyp_ps t) = ind_nn D) by exact (length_rec_ps _ _ _ _ _ Hcon Heq).
      pose proof (sh_wk _ _ _ Heq L (le_n _)) as Hw; fold pat pat' in Hw.
      assert (Hft : List.firstn L (ptyp_doms t) = ptyp_doms t) by (apply List.firstn_all).
      rewrite Hft in Hw.
      assert (HTex : forall m, m < ind_nn D ->
                 exists Tm, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) m = Some Tm).
      { intros m Hm; apply nth_error_lt_some'.
        rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
      assert (Hlink : forall m P Tm, List.nth_error (ptyp_ps t) m = Some P ->
                 List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (ptyp_depth t + K + ind_nn D))) (ptyp_ps t)) m = Some Tm ->
                 exists b1 b, ⟦ P[wk_pat pat']ʷ ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ b1 /\ ⟦ P ⟧ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b /\
                   ind_nr D ups m (List.firstn m bs) b b1).
      { intros * HP HTm.
        pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HTm) as HPv.
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
      { intros m M HM; rewrite List.nth_error_map in HM.
        destruct (List.nth_error (ptyp_ps t) m) as [P |] eqn:HP; cbn in HM; [ injection HM as <- | discriminate ].
        assert (Hm : m < ind_nn D) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
        destruct (HTex _ Hm) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
      exists bs, bs1; split; [ exact Ebs | split; [ exact Ebs1 |] ].
      rewrite tele_full_iff, List.length_rev, length_nparams.
      rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ Ebs1), List.length_map.
      split; [ exact HlPs | split; [ exact HlPs |] ].
      intros j y y' Hy1 Hy1'.
      assert (Hj : j < ind_nn D) by (rewrite <- HlPs, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' (ptyp_ps t) j ltac:(lia)) as [P HP].
      destruct (HTex _ Hj) as [Tm HTm].
      destruct (Hlink _ _ _ HP HTm) as (b1 & b & Eb1 & Eb & Hr).
      destruct (eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
      destruct (eval_exps_nth _ _ _ _ _ Ebs1 ltac:(rewrite List.nth_error_map, HP; reflexivity)) as (b2 & Hb2 & Eb2).
      assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
      rewrite Hy1 in Hb0; injection Hb0 as ->; rewrite Hy1' in Hb2; injection Hb2 as ->; exact Hr.
  Qed.

  (** The type of a recursive argument after [k] domains, on the side of
      all the arguments, against the type of the rest of its shape on the
      side of the non-recursive ones. *)
  Lemma shty_link : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      forall ups ns fa a0, List.length ups = ind_nu D -> List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups -> ⟦ ind_sort D ⟧ env_args nil ups ↘ a0 ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
      (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      forall n k ys a (i : nat) R b, k + n = List.length (ptyp_doms t) ->
        tele_pre (shape_tr (ind_dr ups) ns (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
        per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t))))
          (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
        ⟦ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t) ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a ->
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        ⟦shty ptyp_skip k t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nonrec_vals gs1 fa ++ ys) ↘ b ->
        Dom a ≈ b ∈ per_univ i.
  Proof.
    intros gs1 t gs2 Heq ups ns fa a0 Hlu Hlns Hlk Hgu0 Ha0 Hnsd INV Hpre.
    pose proof (shape_links gs1 t gs2 Heq ups ns fa a0 Hlu Hlns Hlk Hgu0 Ha0 Hnsd INV Hpre) as Hlinks.
    pose proof (decl_closed_nu D Hc) as Hle.
    set (nv := nonrec_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hsimp : ptyp_simple t = true) by exact (vid_simple _ HD _ _ _ _ _ Hcon Heq).
    (** The type of the rest of the shape exists. *)
    assert (Hex : forall k ys, k <= List.length (ptyp_doms t) ->
               tele_pre (shape_tr (ind_dr ups) ns nv (ptyp_doms t)) k ys ys ->
               per_gargs (List.rev (sh_ctx pat (List.firstn k (ptyp_doms t)))) (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
               exists b, ⟦shty ptyp_skip k t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b).
    { intros k ys Hk Hy Hgy.
      destruct (Nat.lt_ge_cases k (List.length (ptyp_doms t))) as [Hlt | Hge].
      - destruct (ptyp_skip_lt k t Hlt) as (B & HB & Hs); rewrite Hs.
        destruct (proj1 (Hlinks k ys Hk Hy Hgy) B HB) as (j0 & a1 & b1 & _ & Eb1 & _).
        eexists; econstructor; exact Eb1.
      - assert (Hkd : k = List.length (ptyp_doms t)) by lia.
        destruct (proj2 (Hlinks k ys Hk Hy Hgy) Hkd) as (bs & _ & Ebs & _ & _).
        rewrite Hkd, (ptyp_skip_end t Hsimp); eexists; econstructor; exact Ebs. }
    induction n as [| n IH]; intros k ys a i R b Hkn Hy Hgy Ea HR Eb.
    - assert (Hkd : k = List.length (ptyp_doms t)) by lia.
      destruct (proj2 (Hlinks k ys ltac:(lia) Hy Hgy) Hkd) as (bs & bs1 & Ebs & Ebs1 & Htf).
      pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
      rewrite Hkd, (ptyp_skip_end t Hsimp) in Ea, Eb.
      rewrite Hkd in Ebs1.
      cbn [ptyp_ty ptyp_ps] in Ea.
      inversion Eb; subst b.
      match goal with E : ⟦ ptyp_ps t ⟧* _ ⍮ _ ⍮ _ ↘ ?b0 |- _ => pose proof (functional_eval_exps' _ _ _ _ E Ebs) as -> end.
      assert (HlPs : List.length (ptyp_ps t) = ind_nn D) by exact (length_rec_ps _ _ _ _ _ Hcon Heq).
      assert (Et0 : ⟦ apps (a_ind p) (ind_uvars D (List.length (List.repeat false (List.length (ptyp_doms t)) ++ pat))
                                       ++ List.map (fun P => P[wk_pat (List.repeat false (List.length (ptyp_doms t)) ++ pat)]ʷ) (ptyp_ps t)) ⟧
                      env_args nil (ups ++ ns ++ fa ++ ys) ↘ d_ind p (ups ++ bs1)).
      { apply eval_apps_exp; exists (d_ind p nil), (ups ++ bs1); split; [ constructor | split ].
        - apply eval_exps_app; [| exact Ebs1 ].
          unfold ind_uvars.
          replace (List.length (List.repeat false (List.length (ptyp_doms t)) ++ pat) + ind_nn D) with (List.length (ns ++ fa ++ ys))
            by (unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia).
          replace (ind_nu D) with (List.length ups) by exact Hlu.
          apply eval_vars_from_args.
        - change (d_ind p (ups ++ bs1)) with (d_ind p (nil ++ (ups ++ bs1))).
          apply eval_apps_ind; rewrite List.length_app, (eval_exps_length _ _ _ Ebs1), List.length_map, HlPs; cbn; unfold ind_nn; lia. }
      assert (a = d_ind p (ups ++ bs1)) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (ind_relate ups ups bs bs1 a0 Hgu0 Hlu Ha0 Htf) as Hrel.
      exact (per_univ_trans' _ _ _ _ _ (ltac:(eexists; exact HR)) (per_univ_sym' _ _ _ (ltac:(eexists; exact Hrel)))).
    - assert (Hk : k < List.length (ptyp_doms t)) by lia.
      destruct (ptyp_skip_lt k t Hk) as (B & HB & Hs).
      rewrite Hs in Ea, Eb.
      set (t' := ptyp_skip (S k) t) in *.
      set (pat' := List.repeat false k ++ pat) in *.
      cbn [ptyp_ty] in Ea.
      inversion Ea; subst a.
      basic_invert_per_univ_elem HR.
      rename H3 into Ea1, H0 into Hcod, H into HPin.
      inversion Eb; subst b.
      match goal with E : ⟦ B ⟧ _ ↘ ?x |- _ => rename x into b1; rename E into Eb1 end.
      pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
      destruct (proj1 (Hlinks k ys ltac:(lia) Hy Hgy) B HB) as (jd & a1' & b1' & Ea1' & Eb1' & Hab).
      assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
      assert (b1' = b1) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_trans' _ _ _ _ _ (ltac:(eexists; exact equiv_a_a')) Hab) as [Rab HRab].
      assert (Ein : in_rel <~> Rab) by (eapply per_univ_elem_right_irrel; [ exact equiv_a_a' | exact HRab ]).
      eexists; eapply per_univ_elem_pi_canonical; [ exact HRab |].
      intros c0 c0' Hcc.
      assert (Hcc0 : in_rel c0 c0') by (apply Ein; exact Hcc).
      assert (Hc'c' : in_rel c0' c0') by (etransitivity; [ symmetry; exact Hcc0 | exact Hcc0 ]).
      (** The domain's relation is the one of [B]'s value. *)
      assert (Hdr : ind_dr ups (ns ++ nv ++ ys) B c0' c0').
      { unfold ind_dr; intros i1 R1 b2 b2' Eb2 Eb2' HR1.
        assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2' = b1) as -> by (eapply functional_eval_exp; eassumption).
        pose proof (per_univ_sym _ _ _ _ HRab) as HRba.
        assert (E1 : Rab <~> R1) by (eapply per_univ_elem_right_irrel; [ exact HRba | exact HR1 ]).
        apply E1, Ein; exact Hc'c'. }
      assert (Hy' : tele_pre (shape_tr (ind_dr ups) ns nv (ptyp_doms t)) (S k) (ys ++ c0' :: nil) (ys ++ c0' :: nil)).
      { apply tele_pre_snoc; [ exact Hy |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hdr. }
      assert (Hgy' : per_gargs (List.rev (sh_ctx pat (List.firstn (S k) (ptyp_doms t)))) (env_args nil (ups ++ ns ++ fa))
                       (env_args nil (ups ++ ns ++ fa)) (ys ++ c0' :: nil) (ys ++ c0' :: nil)).
      { rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
        cbn [List.rev].
        apply (per_gargs_snoc _ _ _ _ _ _ _ _ i in_rel);
          [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgy | | exact Hc'c' ].
        rewrite <- !env_args_app, <- !List.app_assoc.
        exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 equiv_a_a'). }
      destruct (Hex (S k) (ys ++ c0' :: nil) ltac:(lia) Hy' Hgy') as [b2 Eb2]; fold t' in Eb2.
      destruct (Hcod _ _ Hcc0) as [a2 a2' Ea2 Ea2' Ha22].
      destruct (Hcod _ _ Hc'c') as [a3 a3' Ea3 Ea3' Ha33].
      assert (a3 = a2') as -> by (eapply functional_eval_exp; eassumption).
      assert (a3' = a2') as -> by (eapply functional_eval_exp; eassumption).
      assert (Ha2b : Dom a2' ≈ b2 ∈ per_univ i).
      { eapply (IH (S k) (ys ++ c0' :: nil) a2' i _ b2); [ lia | exact Hy' | exact Hgy' | | exact Ha33 | ].
        - cbn [List.repeat List.app]; fold pat'.
          replace (ups ++ ns ++ fa ++ ys ++ c0' :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c0' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite env_args_snoc; exact Ea2'.
        - exact Eb2. }
      destruct (per_univ_trans' _ _ _ _ _ (ltac:(eexists; exact Ha22)) Ha2b) as [R2 HR2].
      exists a2, b2, R2; split; [ exact Ea2 | split; [| exact HR2 ] ].
      apply eval_fam_cod_shfam.
      replace (ups ++ ns ++ nv ++ ys ++ c0' :: nil) with ((ups ++ ns ++ nv ++ ys) ++ c0' :: nil) in Eb2 by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_snoc in Eb2; exact Eb2.
  Qed.

  Section ConArgs.
    #[local] Set Default Proof Using "All".
    Variable (ps ps' as1 as1' : list domain).
    Hypothesis (Hgp : per_gargs (List.rev (ind_params D)) nil nil ps ps') (Hlp : List.length ps = ind_np D).
    Hypothesis (Hga : per_gargs (List.rev (cargs_ctx p D gs)) (env_args nil ps) (env_args nil ps') as1 as1')
      (Hla : List.length as1 = List.length gs).
    Let ups := List.firstn (ind_nu D) ps.
    Let ns := List.skipn (ind_nu D) ps.

    Lemma con_ps : ps = ups ++ ns.
    Proof. symmetry; apply List.firstn_skipn. Qed.

    Lemma con_ups : per_gargs (List.rev (ind_uparams D)) nil nil ups (List.firstn (ind_nu D) ps') /\
        per_gargs (List.rev (ind_uparams D)) nil nil ups ups /\ List.length ups = ind_nu D /\ List.length ps' = ind_np D.
    Proof.
      destruct (params_split_rel _ _ _ _ Hgp Hlp) as (H1 & _ & H3 & H4).
      split; [ exact H1 | split; [ exact (uparams_refl_l _ _ H1) | split; assumption ] ].
    Qed.

    Lemma con_sort : exists a, ⟦ ind_sort D ⟧ env_args nil ups ↘ a.
    Proof.
      destruct con_ups as (_ & Hgu0 & Hlu & _).
      destruct (vid_sort _ HD) as [i HS].
      destruct (rel_ctx_wf_per_ctx_env uparams_sem) as [RU HRU].
      assert (HRU0 : RU (env_args nil ups) (env_args nil ups)).
      { apply (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem); [ rewrite length_ind_uparams by exact (decl_closed_nu D Hc); exact Hlu | exact Hgu0 ]. }
      destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRU0) as (a & _ & Ea & _ & _); eauto.
    Qed.

    Lemma con_ns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns (List.skipn (ind_nu D) ps') /\
        tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns.
    Proof.
      destruct (params_split_rel _ _ _ _ Hgp Hlp) as (_ & H2 & H3 & _).
      pose proof (per_gargs_refl_l _ _ _ per_ctx_env_nil_true rev_params_sem rev_params_ass _ _ _ _ I Hgp) as Hgd.
      destruct (params_split_rel _ _ _ _ Hgd Hlp) as (_ & H2d & _ & _).
      assert (Hlns : List.length ns = ind_nn D) by (unfold ns; rewrite List.length_skipn; unfold ind_nn; lia).
      assert (Htr : forall j A pre, List.nth_error (List.rev (ind_nparams D)) j = Some (ce_ass A) ->
                 (ind_nr D ups j pre <~> per_head A A (env_args (env_args nil ups) pre) (env_args (env_args nil ups) pre)))
        by (intros j A pre HA; unfold ind_nr; rewrite (nth_ctyp_eq _ _ _ HA), env_args_app; reflexivity).
      split; eapply (gargs_tele_canon _ _ _ Htr); try eassumption; rewrite List.length_rev, length_nparams; exact Hlns.
    Qed.

    Lemma con_las' : List.length as1' = List.length gs.
    Proof. destruct (per_gargs_length _ _ _ _ _ Hga) as [H _]; lia. Qed.

    Lemma con_args_split : forall gs1 gs2, gs = gs1 ++ gs2 ->
        let k := List.length gs1 in
        per_gargs (List.rev (cargs_ctx p D gs1)) (env_args nil ps) (env_args nil ps') (List.firstn k as1) (List.firstn k as1') /\
        per_gargs (List.rev (cargs_ctx_aux p D (cargs_pat gs1) gs2)) (env_args nil (ps ++ List.firstn k as1))
          (env_args nil (ps' ++ List.firstn k as1')) (List.skipn k as1) (List.skipn k as1').
    Proof.
      intros * Heq k.
      pose proof con_las' as Hla'.
      assert (Hk : k <= List.length gs) by (unfold k; rewrite Heq, List.length_app; lia).
      pose proof Hga as H.
      unfold cargs_ctx in H; rewrite Heq, cargs_ctx_aux_app, List.app_nil_r, List.rev_app_distr in H.
      rewrite <- (List.firstn_skipn k as1), <- (List.firstn_skipn k as1') in H.
      assert (L1 : List.length (List.firstn k as1) = List.length (List.rev (cargs_ctx_aux p D nil gs1)))
        by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold k; lia).
      assert (L2 : List.length (List.firstn k as1') = List.length (List.rev (cargs_ctx_aux p D nil gs1)))
        by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold k; lia).
      destruct (per_gargs_app (List.rev (cargs_ctx_aux p D nil gs1)) (List.rev (cargs_ctx_aux p D (cargs_pat gs1) gs2))
                  _ _ (List.firstn k as1) (List.firstn k as1') (List.skipn k as1) (List.skipn k as1') L1 H L2) as [H1 H2].
      split; [ exact H1 | rewrite !env_args_app; exact H2 ].
    Qed.

    (** The environment of the parameters and the first [k] arguments is one
        of the context of their types. *)
    Lemma con_prefix_env : forall gs1 gs2, gs = gs1 ++ gs2 ->
        let k := List.length gs1 in
        forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
          R (env_args nil (ps ++ List.firstn k as1)) (env_args nil (ps ++ List.firstn k as1)).
    Proof.
      intros * Heq k R HR.
      pose proof (cargs_prefix_sem _ _ Heq) as HC.
      pose proof con_las' as Hla'.
      assert (HP : PER R) by (eapply per_env_PER; exact HR).
      assert (Hk : k <= List.length gs) by (unfold k; rewrite Heq, List.length_app; lia).
      assert (Hcross : R (env_args nil (ps ++ List.firstn k as1)) (env_args nil (ps' ++ List.firstn k as1'))).
      { apply (gargs_env_rel _ _ _ _ _ _ HR HC).
        - rewrite !List.length_app, length_cargs_ctx, List.length_firstn; unfold k, ind_np in *; lia.
        - rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev; unfold ind_np in *; lia | exact Hgp |].
          exact (proj1 (con_args_split _ _ Heq)). }
      etransitivity; [ exact Hcross | symmetry; exact Hcross ].
    Qed.

    Lemma con_entry : forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
        let k := List.length gs1 in
        exists T x x' (i : nat) Rk, cargs_ctx_aux p D (cargs_pat gs1) (g :: nil) = ce_ass T :: nil /\
          List.nth_error as1 k = Some x /\ List.nth_error as1' k = Some x' /\
          rel_typ i T (env_args nil (ps ++ List.firstn k as1)) T (env_args nil (ps' ++ List.firstn k as1')) Rk /\ Rk x x'.
    Proof.
      intros * Heq k; unfold k in *; clear k.
      destruct (con_args_split _ _ Heq) as [_ H2].
      pose proof con_las' as Hla'.
      assert (Hk : List.length gs1 < List.length as1) by (rewrite Hla, Heq, List.length_app; cbn; lia).
      assert (Hk' : List.length gs1 < List.length as1') by (rewrite Hla', Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some' as1 _ Hk) as [x Hx].
      destruct (nth_error_lt_some' as1' _ Hk') as [x' Hx'].
      rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx') in H2.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app] in H2 |- *; rewrite List.rev_app_distr in H2; cbn [List.rev List.app] in H2;
        inversion H2 as [| i T ? ? ? ? ? ? ? R HT Hxx]; subst;
        do 5 eexists; (split; [ reflexivity | split; [ exact Hx | split; [ exact Hx' | split; [ exact HT | exact Hxx ] ] ] ]).
    Qed.

    Lemma con_arg_step : forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 ->
        let k := List.length gs1 in
        exists x x', List.nth_error as1 k = Some x /\ List.nth_error as1' k = Some x' /\
          ind_ar D ups ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 (List.firstn k as1)) x x' /\
          ind_ar D ups ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 (List.firstn k as1)) x x.
    Proof.
      intros * Heq k; unfold k in *; clear k.
      assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
        by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
      destruct (con_entry _ _ _ Heq) as (T & x & x' & i & Rk & HT & Hx & Hx' & [t t' Et Et' HRk] & Hxx).
      cbn [cargs_ctx_aux List.app] in HT; injection HT as <-.
      assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
        by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      destruct (vid_arg _ HD _ _ _ _ Hcon HA) as (_ & jA & HAv).
      rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
      destruct (rel_exp_under_ctx_wk_simple (cargs_wk _ _ ltac:(exact Heq)) HAv) as (RΓ & HΓ & i0 & Hwk).
      pose proof (con_prefix_env _ _ Heq _ HΓ) as HE1.
      destruct (Hwk _ _ HE1) as (y & y' & Ry & Ey & Ey' & HRy & m & m' & Em & Em' & Hmm).
      assert (Hy : y = d_univ jA) by (cbn in Ey; inversion Ey; reflexivity).
      rewrite Hy in HRy; clear Hy Ey Ey'.
      destruct (per_univ_elem_univ _ _ _ _ HRy (or_introl (ex_intro _ _ eq_refl))) as [_ ERy].
      apply ERy in Hmm; destruct Hmm as [Rm HRm].
      assert (m = t) as -> by (eapply functional_eval_exp; eassumption).
      rewrite env_args_app, eval_wk_pat_args, <- env_args_app in Em' by exact Hlk.
      assert (ERk : Rk <~> Rm) by (eapply per_univ_elem_right_irrel; [ exact HRk | exact HRm ]).
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRm) HRm) as HRd.
      assert (Hcan : ind_ar D ups ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 (List.firstn (List.length gs1) as1))
                       <~> Rm).
      { unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hcon HA).
        rewrite List.app_assoc, <- con_ps.
        symmetry; exact (per_head_iff Em' Em' HRd). }
      assert (HPk : PER Rk) by (eapply per_elem_PER; exact HRk).
      exists x, x'; split; [ exact Hx | split; [ exact Hx' | split ] ].
      - apply Hcan, ERk, Hxx.
      - apply Hcan, ERk; etransitivity; [ exact Hxx | symmetry; exact Hxx ].
    Qed.

    Lemma con_rec_step : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1))
          (nonrec_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_vals gs1 (List.firstn (List.length gs1) as1)) ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1))
          (nonrec_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_vals gs1 (List.firstn (List.length gs1) as1')) ->
        exists x x', List.nth_error as1 (List.length gs1) = Some x /\ List.nth_error as1' (List.length gs1) = Some x' /\
          ind_shape_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
            ups (List.firstn (ind_nu D) ps')
            (ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1))
            (List.skipn (ind_nu D) ps' ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1')) t x x'.
    Proof.
      intros * Heq INV INVc.
      destruct (con_entry _ _ _ Heq) as (T & x & x' & i & Rk & HT & Hx & Hx' & [a a' Ea Ea' HRk] & Hxx).
      cbn [cargs_ctx_aux List.app] in HT; injection HT as <-.
      exists x, x'; split; [ exact Hx | split; [ exact Hx' |] ].
      pose proof (per_univ_trans _ _ _ _ _ _ HRk (per_univ_sym _ _ _ _ HRk)) as HRd.
      destruct con_ups as (_ & Hgu0 & Hlu & _).
      destruct con_sort as [a0 Ha0].
      destruct con_ns as (_ & Hnsd).
      assert (Hlns : List.length ns = ind_nn D) by (unfold ns; rewrite List.length_skipn; unfold ind_nn; lia).
      assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
        by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
      assert (Hpre : forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
                 R (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1)) (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1))).
      { intros R HR; rewrite List.app_assoc, <- con_ps; exact (con_prefix_env _ _ Heq R HR). }
      rewrite con_ps, <- List.app_assoc in Ea.
      pose proof (shape_char _ _ _ Heq ups ns _ a0 Hlu Hlns Hlk Hgu0 Ha0 Hnsd INV Hpre (List.length (ptyp_doms t)) 0 nil a i Rk
                    eq_refl (tele_pre_nil _) ltac:(cbn; constructor) ltac:(rewrite List.app_nil_r; exact Ea) HRd) as H.
      rewrite List.app_nil_r in H; apply H in Hxx.
      (** The right argument at the right constructor's own parameters. *)
      destruct con_ups as (Hgu & _ & _ & _).
      destruct con_ns as (Hns & _).
      destruct (ind_canon ups a0 Hgu0 Hlu Ha0) as (CnP & CnI & CaP & CaI & CdP & CdI & Cad).
      assert (Cad' : ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) (List.firstn (ind_nu D) ps'))
        by (eapply canon_adm_beside; eassumption).
      pose proof (proj1 (ind_shape_rel_rebase p D ups _ _ _ (decl_closed_params D Hc) CnP CnI CaP CaI CdP CdI _)
                    _ _ _ _ _ _ _ Hxx ups (List.firstn (ind_nu D) ps') ns ns ns (List.skipn (ind_nu D) ps') c gs1 t gs2
                    _ _ _ _ 0 nil nil nil nil
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) Cad Cad'
                    ltac:(rewrite <- Heq; exact Hcon) Hnsd Hnsd Hns INV INV INVc eq_refl ltac:(lia)
                    (tele_pre_nil _) (tele_pre_nil _) (tele_pre_nil _)) as Hg.
      repeat rewrite List.app_nil_r in Hg; exact Hg.
    Qed.

    Lemma con_split_at : forall k g, List.nth_error gs k = Some g ->
        gs = List.firstn k gs ++ g :: List.skipn (S k) gs /\ List.length (List.firstn k gs) = k.
    Proof.
      intros * Hg; split; [ rewrite <- (skipn_nth_cons' _ _ _ Hg), List.firstn_skipn; reflexivity |].
      rewrite List.length_firstn; assert (k < List.length gs) by (apply List.nth_error_Some; congruence); lia.
    Qed.

    Lemma con_prefix : forall k, k <= List.length gs ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec (List.firstn k gs)))
          (nonrec_vals (List.firstn k gs) (List.firstn k as1)) (nonrec_vals (List.firstn k gs) (List.firstn k as1')) /\
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec (List.firstn k gs)))
          (nonrec_vals (List.firstn k gs) (List.firstn k as1)) (nonrec_vals (List.firstn k gs) (List.firstn k as1)).
    Proof.
      pose proof con_las' as Hla'.
      induction k as [| k IH]; intros Hk; [ cbn; split; apply tele_pre_nil |].
      destruct (IH ltac:(lia)) as [IHc IHd].
      destruct (nth_error_lt_some' gs k ltac:(lia)) as [g Hg].
      destruct (nth_error_lt_some' as1 k ltac:(lia)) as [x Hx].
      destruct (nth_error_lt_some' as1' k ltac:(lia)) as [x' Hx'].
      destruct (con_split_at _ _ Hg) as [Heq Hlf].
      rewrite (firstn_S_snoc _ _ _ Hg), (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
      rewrite !nonrec_vals_app by (rewrite !List.length_firstn; lia).
      rewrite cargs_nonrec_app.
      destruct g as [A | Ps]; cbn [nonrec_vals cargs_nonrec].
      - destruct (con_arg_step _ _ _ Heq) as (y & y' & Hy & Hy' & Hr & Hrd).
        rewrite Hlf in Hy, Hy', Hr, Hrd.
        rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
        rewrite List.length_app, Nat.add_1_r.
        split; apply tele_pre_snoc; assumption.
      - rewrite !List.app_nil_r; split; assumption.
    Qed.

    Lemma con_args_rel : forall gs2 gs1, gs = gs1 ++ gs2 ->
        ind_args_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
          ups (List.firstn (ind_nu D) ps')
          (ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1))
          (List.skipn (ind_nu D) ps' ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1')) gs2
          (List.skipn (List.length gs1) as1) (List.skipn (List.length gs1) as1').
    Proof.
      pose proof con_las' as Hla'.
      induction gs2 as [| g gs2 IH]; intros gs1 Heq.
      - rewrite List.app_nil_r in Heq.
        rewrite (List.skipn_all2 as1), (List.skipn_all2 as1') by (rewrite <- Heq; lia); constructor.
      - assert (Hk : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' as1 (List.length gs1) ltac:(lia)) as [x Hx].
        destruct (nth_error_lt_some' as1' (List.length gs1) ltac:(lia)) as [x' Hx'].
        rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx').
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ gs2) by (rewrite <- List.app_assoc; exact Heq).
        pose proof (IH _ Heq') as IHg.
        rewrite List.length_app in IHg; cbn [List.length] in IHg; rewrite Nat.add_1_r in IHg.
        rewrite (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx'), !nonrec_vals_app in IHg by (rewrite List.length_firstn; lia).
        destruct g as [A | Ps]; cbn [nonrec_vals] in IHg.
        + constructor.
          rewrite <- !List.app_assoc; exact IHg.
        + assert (Hpre : List.firstn (List.length gs1) gs = gs1)
            by (rewrite Heq, firstn_app_exact by reflexivity; reflexivity).
          destruct (con_prefix (List.length gs1) ltac:(lia)) as [INVc INVd].
          rewrite Hpre in INVc, INVd.
          destruct (con_rec_step _ _ _ Heq INVd INVc) as (y & y' & Hy & Hy' & Hrel).
          rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
          constructor; [ exact Hrel |].
          repeat rewrite List.app_nil_r in IHg; exact IHg.
    Qed.

    Lemma con_rel : ind_rel p D (ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups)) (ind_nr D ups) (ind_ar D ups) (ind_dr ups)
        ns (List.skipn (ind_nu D) ps') (d_con p c (ps ++ as1)) (d_con p c (ps' ++ as1')).
    Proof.
      pose proof con_las' as Hla'.
      destruct con_ups as (Hgu & Hgu0 & Hlu & Hlp').
      destruct con_sort as [a0 Ha0].
      destruct con_ns as (Hns & Hnsd).
      destruct (ind_canon ups a0 Hgu0 Hlu Ha0) as (CnP & CnI & CaP & CaI & CdP & CdI & Cad).
      assert (Cad' : ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) (List.firstn (ind_nu D) ps'))
        by (eapply canon_adm_beside; eassumption).
      destruct (con_prefix (List.length gs) (le_n _)) as [Hnr _].
      rewrite List.firstn_all, !List.firstn_all2 in Hnr by lia.
      apply ind_rel_con with (gs := gs);
        [ exact Hns | exact Hcon | exact Hlp | exact Hlp' | exact Cad | exact Cad' | exact Hnsd
        | exact (tnr_refl_r p D ups _ _ _ (decl_closed_params D Hc) CnP CnI CaP CaI CdP CdI _ _ Hns)
        | exact (tele_full_of_pre _ _ _ _ Hnr) |].
      pose proof (con_args_rel gs nil eq_refl) as H; cbn [List.length List.skipn nonrec_vals List.firstn] in H.
      repeat rewrite List.app_nil_r in H; exact H.
    Qed.
  End ConArgs.

  Lemma con_tele_ass : tele_ass (List.rev (cargs_ctx p D gs ++ ind_params D)).
  Proof.
    apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params D Hc) ].
  Qed.

  (** The constructor at related arguments, at the inductive type. *)
  Lemma con_at_args : forall zs zs', per_gargs (List.rev (cargs_ctx p D gs ++ ind_params D)) nil nil zs zs' ->
      List.length zs = List.length (List.rev (cargs_ctx p D gs ++ ind_params D)) ->
      Dom d_con p c zs ≈ d_con p c zs' ∈
        per_head (apps (a_ind p) (ind_pvars D (List.length gs))) (apps (a_ind p) (ind_pvars D (List.length gs)))
          (env_args nil zs) (env_args nil zs').
  Proof.
    intros * Hg Hlz i0 Rb bb bb' Ebb Ebb' HRb.
    pose proof (decl_closed_nu D Hc) as Hle.
    rewrite List.length_rev, List.length_app, length_cargs_ctx in Hlz.
    pose proof (per_gargs_length _ _ _ _ _ Hg) as [Hlz' _].
    set (ps := List.firstn (ind_np D) zs); set (ps' := List.firstn (ind_np D) zs').
    set (as1 := List.skipn (ind_np D) zs); set (as1' := List.skipn (ind_np D) zs').
    assert (Hz : zs = ps ++ as1) by (symmetry; apply List.firstn_skipn).
    assert (Hz' : zs' = ps' ++ as1') by (symmetry; apply List.firstn_skipn).
    assert (Hlp : List.length ps = ind_np D) by (unfold ps; rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (Hlp' : List.length ps' = ind_np D) by (unfold ps'; rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (Hla : List.length as1 = List.length gs) by (unfold as1; rewrite List.length_skipn; unfold ind_np in *; lia).
    rewrite Hz, Hz', List.rev_app_distr in Hg.
    assert (L1 : List.length ps = List.length (List.rev (ind_params D))) by (rewrite List.length_rev; exact Hlp).
    assert (L2 : List.length ps' = List.length (List.rev (ind_params D))) by (rewrite List.length_rev; exact Hlp').
    destruct (per_gargs_app _ _ _ _ _ _ _ _ L1 Hg L2) as [Hgp Hga].
    rewrite Hz in Ebb |- *; rewrite Hz' in Ebb' |- *.
    pose proof (con_rel ps ps' as1 as1' Hgp Hlp Hga Hla) as Hrel.
    destruct (con_ups ps ps' as1 as1' Hgp Hlp Hga Hla) as (Hgu & _ & Hlu & _).
    destruct (con_sort ps ps' as1 as1' Hgp Hlp Hga Hla) as [a Ha].
    destruct (con_ns ps ps' as1 as1' Hgp Hlp Hga Hla) as [Hns _].
    pose proof (ind_relate _ _ _ _ _ Hgu Hlu Ha Hns) as Hind.
    rewrite List.firstn_skipn in Hind.
    (** The type at the arguments is the type former at the parameters. *)
    assert (Ebd : ⟦ apps (a_ind p) (ind_pvars D (List.length gs)) ⟧ env_args nil (ps ++ as1) ↘ d_ind p ps).
    { apply eval_apps_exp; exists (d_ind p nil), ps; split; [ constructor | split ].
      - unfold ind_pvars; rewrite <- Hla, <- Hlp; exact (eval_vars_from_args ps nil as1).
      - change (d_ind p ps) with (d_ind p (nil ++ ps)); apply eval_apps_ind; cbn; lia. }
    assert (bb = d_ind p ps) as -> by (eapply functional_eval_exp; eassumption).
    assert (E : Rb <~> ind_rel p D (ind_adm D (List.firstn (ind_nu D) ps) (ind_nr D (List.firstn (ind_nu D) ps))
                                      (ind_ar D (List.firstn (ind_nu D) ps)) (ind_dr (List.firstn (ind_nu D) ps)))
                       (ind_nr D (List.firstn (ind_nu D) ps))
                       (ind_ar D (List.firstn (ind_nu D) ps)) (ind_dr (List.firstn (ind_nu D) ps))
                       (List.skipn (ind_nu D) ps) (List.skipn (ind_nu D) ps'))
      by (eapply per_univ_elem_right_irrel; [ exact HRb | exact Hind ]).
    apply E; exact Hrel.
  Qed.

  Lemma valid_exp_under_ctx_con : forall i, ⋅ ⊨ con_ty p D gs : Typeω@i ->
      ⋅ ⊨ a_con p c : con_ty p D gs.
  Proof.
    intros i HT.
    destruct (rel_exp_of_typ_inversion_simple HT) as (R & HR & Hsimp).
    assert (HRall : forall ρ ρ', R ρ ρ') by (intros; inversion HR; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    apply (rel_exp_closed_intro _ _ i); [ intros; exact (con_ty_sub p D c gs _ Hc Hcon) | intros; reflexivity |].
    intros ρ ρ'.
    destruct (Hsimp ρ ρ' (HRall _ _)) as (a & a' & Ea & Ea' & [R0 HR0]).
    exists a, a', R0, (d_con p c nil), (d_con p c nil).
    split; [ exact Ea | split; [ exact Ea' | split; [ exact HR0 | split; [ constructor | split; [ constructor |] ] ] ] ].
    destruct (Hsimp nil nil (HRall _ _)) as (b & b' & Eb & Eb' & [R1 HR1]).
    destruct (Hsimp ρ nil (HRall _ _)) as (a0 & b0 & Ea0 & Eb0 & [R2 HR2]).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HR2 HR1) as (R3 & HR3 & E3).
    assert (E : R0 <~> R1)
      by (etransitivity; [ eapply per_univ_elem_right_irrel; [ exact HR0 | exact HR2 ] |];
          etransitivity; [ exact E3 | eapply per_univ_elem_left_irrel; [ exact HR3 | exact HR1 ] ]).
    apply E.
    unfold con_ty in Eb, Eb'; rewrite <- ctx_pi_app, <- (List.rev_involutive (cargs_ctx p D gs ++ ind_params D)) in Eb, Eb'.
    eapply (ctx_pi_rel_elem (ind_np D + List.length gs) (d_con p c) _
              ltac:(intros xs x Hx; eapply eval_app_con; [ exact Hl | exact Hcon | exact Hx ])
              (List.rev (cargs_ctx p D gs ++ ind_params D)) con_tele_ass nil nil nil nil);
      [ rewrite List.length_rev, List.length_app, length_cargs_ctx; cbn; unfold ind_np; lia | reflexivity
      | exact Eb | exact Eb' | exact HR1 | ].
    intros zs zs' Hg Hlz; cbn [List.app env_args List.fold_left] in *.
    exact (con_at_args _ _ Hg Hlz).
  Qed.

End Sort.

End Fixed_GCtx.
