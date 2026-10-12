(** * Inductive Types: the Type Former and the Constructors

    A declaration is semantically valid ([sem_decl]) when its telescopes and
    types are: these are the judgments of its typing, read in the PER model.
    From them, the inductive type at related parameters is a type of the
    universe its sort denotes ([ind_relate]), with the canonical relations of
    [Core.Semantic.IndPER]; the type former and the constructors are then
    elements of their [Π]-types. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping IndSyntax GlobalPresup.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases GlobalSem MemberReps
  IndSem.
From Mctt.Core.Semantic Require Import Realizability IndPER Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Semantic Validity of a Declaration

    The context of the first [k] non-uniform parameters, and of the first
    [k] non-recursive arguments of a constructor. *)
Definition npre (D : ind_decl) (k : nat) : ctx := List.rev (List.firstn k (List.rev (ind_nparams D))).
Definition astrat (gs : list carg) (k : nat) : ctx := List.rev (List.firstn k (List.map ce_ass (cargs_nonrec gs))).

Record sem_core (D : ind_decl) : Prop := mk_sem_core
{ sd_params : ⊨ ind_params D
; sd_sort : exists i, ind_uparams D ⊨ ind_sort D : Typeω@i
; sd_ty : exists i, ⋅ ⊨ ind_ty D : Typeω@i
; sd_npar : forall k A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
    npre D k ++ ind_uparams D ⊨ A : (ind_sort D)[wk_shiftn k]ʷ /\
    exists j, npre D k ++ ind_uparams D ⊨ A : Typeω@j
; sd_strat : forall c gs k, ind_con D c = Some gs -> k <= List.length (cargs_nonrec gs) ->
    ⊨ astrat gs k ++ ind_params D
; sd_arg : forall c gs k A, ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
    astrat gs k ++ ind_params D ⊨ A : (ind_sort D)[wk_shiftn (k + ind_nn D)]ʷ /\
    exists j, astrat gs k ++ ind_params D ⊨ A : Typeω@j
; sd_nodup : List.NoDup (List.map fst (ind_cons D))
; sd_rec : forall c gs gs1 Ps gs2 m P T, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
    List.nth_error (ptyp_ps Ps) m = Some P ->
    List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_nonrec gs1) + ind_nn D))) (ptyp_ps Ps)) m
      = Some T ->
    astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D ⊨ P : T
}.

(** The judgments of the declaration's constructors: their contexts of
    arguments and their types, which mention the type former, so that
    they are read once the type former is known to be valid. *)
Record sem_decl (D : ind_decl) : Prop := mk_sem_decl
{ sd_c :> sem_core D
; sd_cargs : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    ⊨ cargs_ctx p D gs ++ ind_params D
; sd_cod : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    exists j, cargs_ctx p D gs ++ ind_params D ⊨ apps (a_ind p) (ind_pvars D (List.length gs)) : Typeω@j
; sd_conty : forall p c gs, ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    exists j, ⋅ ⊨ con_ty p D gs : Typeω@j
}.

(** ** Lists *)

Lemma length_npre : forall D k, k <= ind_nn D -> List.length (npre D k) = k.
Proof. intros; unfold npre; rewrite List.length_rev, List.length_firstn, List.length_rev, length_nparams; lia. Qed.

Lemma length_astrat : forall gs k, k <= List.length (cargs_nonrec gs) -> List.length (astrat gs k) = k.
Proof. intros; unfold astrat; rewrite List.length_rev, List.length_firstn, List.length_map; lia. Qed.

Lemma npre_suffix : forall D k, exists Δ, ind_params D = Δ ++ npre D k ++ ind_uparams D.
Proof.
  intros; exists (List.rev (List.skipn k (List.rev (ind_nparams D)))).
  rewrite params_split, List.app_assoc; f_equal.
  unfold npre; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
Qed.

Lemma rev_npre : forall D k, List.rev (npre D k ++ ind_uparams D) = List.rev (ind_uparams D) ++ List.firstn k (List.rev (ind_nparams D)).
Proof. intros; unfold npre; rewrite List.rev_app_distr, List.rev_involutive; reflexivity. Qed.

Lemma rev_astrat : forall D gs k, List.rev (astrat gs k ++ ind_params D) =
    List.rev (ind_uparams D) ++ List.rev (ind_nparams D) ++ List.firstn k (List.map ce_ass (cargs_nonrec gs)).
Proof.
  intros; unfold astrat; rewrite List.rev_app_distr, List.rev_involutive, rev_params_split, List.app_assoc; reflexivity.
Qed.

Lemma tele_ass_map_ass : forall As, tele_ass (List.map ce_ass As).
Proof. induction As; constructor; eauto. Qed.

Lemma cargs_nonrec_length : forall gs1 gs, cargs_nonrec gs1 = List.firstn (List.length (cargs_nonrec gs1)) (cargs_nonrec (gs1 ++ gs)).
Proof. intros; rewrite cargs_nonrec_app, firstn_app_exact by reflexivity; reflexivity. Qed.


(** ** The Declaration's Judgments, Positionwise

    The typing of a declaration states its judgments at decompositions of
    its lists; the semantic validity states them at positions. *)

Lemma cargs_strat_nonrec : forall gs, cargs_strat gs = List.rev (List.map ce_ass (cargs_nonrec gs)).
Proof. induction gs as [| [A | Ps] gs IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma astrat_prefix : forall gs1 gs2, cargs_strat gs1 = astrat (gs1 ++ gs2) (List.length (cargs_nonrec gs1)).
Proof.
  intros; unfold astrat; rewrite cargs_strat_nonrec, cargs_nonrec_app, List.map_app, List.firstn_app.
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
    exists Δ1, ind_nparams D = Δ1 ++ ce_ass A :: npre D k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & Hl & Hlen).
  exists (List.rev l2).
  assert (Hf : List.firstn k (List.rev (ind_nparams D)) = l1)
    by (rewrite Hl, <- Hlen, List.firstn_app, Nat.sub_diag, List.firstn_all; cbn; apply List.app_nil_r).
  unfold npre; rewrite Hf, <- (List.rev_involutive (ind_nparams D)), Hl, List.rev_app_distr; cbn.
  rewrite <- List.app_assoc; reflexivity.
Qed.

(** ** A Telescope at the Sort

    A type of a declaration in the context [Pre] over the uniform parameters,
    of the sort shifted past [Pre], evaluates at related arguments to types
    of the universe the sort denotes at the uniform parameters. *)
Section Sort.
  Variable (D : ind_decl).
  Hypothesis (HD : sem_core D) (Hc : decl_closed D) (Hsu : ind_sort_univ (ind_sort D)).

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
    destruct (sem_ctx_per_ctx_env HC) as [R HR].
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
    destruct (sd_sort _ HD) as [i HS].
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
         List.rev (List.firstn j ts) ++ Pre0 ++ ind_uparams D ⊨ A : (ind_sort D)[wk_shiftn (j + List.length Pre0)]ʷ) ->
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

  Lemma npre_S : forall k A, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
      npre D (S k) = ce_ass A :: npre D k.
  Proof. intros * H; unfold npre; rewrite (firstn_S_snoc _ _ _ H), List.rev_app_distr; reflexivity. Qed.

  Lemma npre_full : npre D (ind_nn D) = ind_nparams D.
  Proof. unfold npre; rewrite List.firstn_all2 by (rewrite List.length_rev, length_nparams; lia); apply List.rev_involutive. Qed.

  Lemma length_rec_ps : forall c gs gs1 Ps gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      List.length (ptyp_ps Ps) = ind_nn D.
  Proof.
    intros * Hcon Heq; pose proof Hc as (_ & _ & _ & _ & _ & _ & HPl).
    exact (HPl _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq).
  Qed.

  (** The parameters of a recursive argument, at related arguments before it,
      are related at the non-uniform parameters. *)
  Lemma rec_closure : forall c gs gs1 Ps gs2, ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
      forall ups ups' ms ms' ws ws',
        List.length ups = ind_nu D -> List.length ms = ind_nn D -> List.length ws = List.length (cargs_nonrec gs1) ->
        List.length ups' = ind_nu D -> List.length ms' = ind_nn D -> List.length ws' = List.length (cargs_nonrec gs1) ->
        per_gargs (List.rev (astrat gs (List.length (cargs_nonrec gs1)) ++ ind_params D)) nil nil
          (ups ++ ms ++ ws) (ups' ++ ms' ++ ws') ->
        exists bs bs', ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ms ++ ws) ↘ bs /\
          ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ ms' ++ ws') ↘ bs' /\
          per_gargs (List.rev (ind_nparams D)) (env_args nil ups) (env_args nil ups') bs bs' /\
          (forall m P T, List.nth_error (ptyp_ps Ps) m = Some P ->
             List.nth_error (tele_insts (ind_nparams D)
                               (sb_of_wk (wk_shiftn (List.length (cargs_nonrec gs1) + ind_nn D))) (ptyp_ps Ps)) m = Some T ->
             (per_head T T (env_args nil (ups ++ ms ++ ws)) (env_args nil (ups' ++ ms' ++ ws'))
                <~> ind_nr D ups m (List.firstn m bs))).
  Proof.
    intros * Hcon Heq * Hu Hm Hw Hu' Hm' Hw' Hg.
    pose proof (decl_closed_nu D Hc) as Hle.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (L := K + ind_nn D).
    set (Ξ0 := astrat gs K ++ ind_params D).
    set (E := env_args nil (ups ++ ms ++ ws)); set (E' := env_args nil (ups' ++ ms' ++ ws')).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (HΞ0 : ⊨ Ξ0) by exact (sd_strat _ HD _ _ _ Hcon HK).
    destruct (sem_ctx_per_ctx_env HΞ0) as [R0 HR0].
    assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
    assert (HEE : R0 E E').
    { apply (gargs_env_rel Ξ0 R0 (ups ++ ms ++ ws) (ups' ++ ms' ++ ws') nil nil); [ exact HR0 | exact HΞ0 | | exact Hg ].
      unfold Ξ0; rewrite !List.length_app, length_astrat by exact HK.
      rewrite params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; lia. }
    pose proof (length_rec_ps _ _ _ _ _ Hcon Heq) as HPl.
    assert (HwkE : ⟪wk_shiftn L⟫ E = env_args nil ups).
    { unfold E, L; rewrite env_args_app; replace (K + ind_nn D) with (List.length (ms ++ ws))
        by (rewrite List.length_app; lia); apply eval_wk_shiftn_args. }
    assert (HwkE' : ⟪wk_shiftn L⟫ E' = env_args nil ups').
    { unfold E', L; rewrite env_args_app; replace (K + ind_nn D) with (List.length (ms' ++ ws'))
        by (rewrite List.length_app; lia); apply eval_wk_shiftn_args. }
    (** The substitution of the uniform parameters: a shift past the
        arguments and the non-uniform parameters. *)
    assert (Hwk : Ξ0 ⊨s sb_of_wk (wk_shiftn L) ≈ sb_of_wk (wk_shiftn L) : ind_uparams D).
    { apply rel_sub_of_wk.
      assert (HL : L = List.length (astrat gs K ++ ind_nparams D))
        by (unfold L; rewrite List.length_app, length_astrat, length_nparams by exact HK; reflexivity).
      assert (HΞe : Ξ0 = (astrat gs K ++ ind_nparams D) ++ ind_uparams D)
        by (unfold Ξ0; rewrite params_split, List.app_assoc; reflexivity).
      rewrite HΞe, HL; apply rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0. }
    (** The induction over the parameters of the recursive argument. *)
    assert (Hall : forall m, m <= ind_nn D ->
               Ξ0 ⊨s sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps) ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps)
                 : npre D m ++ ind_uparams D /\
               exists bs bs', ⟦ List.firstn m Ps ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ bs /\
                 ⟦ List.firstn m Ps ⟧* gc_deps ⍮ gc_stack ⍮ E' ↘ bs' /\
                 per_gargs (List.firstn m (List.rev (ind_nparams D))) (env_args nil ups) (env_args nil ups') bs bs' /\
                 (forall m' P T, m' < m -> List.nth_error Ps m' = Some P ->
                    List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) Ps) m' = Some T ->
                    (per_head T T E E' <~> ind_nr D ups m' (List.firstn m' bs)))).
    { induction m as [| m IH]; intros Hmn.
      - cbn [List.firstn sb_of_list]; unfold npre; cbn [List.firstn List.rev List.app].
        split; [ exact Hwk |]; exists nil, nil; split; [ constructor | split; [ constructor | split; [ constructor | intros; lia ] ] ].
      - destruct (IH ltac:(lia)) as (Hτ & bs & bs' & Ebs & Ebs' & Hgb & Hil).
        destruct (nth_error_lt_some' Ps m ltac:(lia)) as [P HP].
        assert (HT : exists T, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) Ps) m = Some T).
        { apply nth_error_lt_some'.
          rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc).
          rewrite length_nparams; lia. }
        destruct HT as [T HT].
        destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
        pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HT) as HPv.
        destruct (sd_npar _ HD _ _ HA) as (_ & j & HAv).
        set (τ := sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn m Ps)) in *.
        (** The new entry, and the substitution extended by it. *)
        assert (Hτ' : Ξ0 ⊨s sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) Ps)
                        ≈ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn (S m) Ps) : npre D (S m) ++ ind_uparams D).
        { rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (npre_S _ _ HA); cbn [sb_of_list List.app].
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
    destruct (npre_suffix D 0) as [Δ HΔ]; unfold npre in HΔ; cbn [List.firstn List.rev List.app] in HΔ.
    pose proof (sd_params _ HD) as H; rewrite HΔ in H; exact (sem_ctx_app_r _ _ H).
  Qed.

  Lemma npre_sem : forall k, ⊨ npre D k ++ ind_uparams D.
  Proof. intros; destruct (npre_suffix D k) as [Δ HΔ]; pose proof (sd_params _ HD) as H; rewrite HΔ in H; exact (sem_ctx_app_r _ _ H). Qed.

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
      split; [ exact (npre_sem j) | exact (proj1 (sd_npar _ HD _ _ HA)) ].
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
      destruct (sd_arg _ HD _ _ _ _ Hcon HA0) as [HAv _].
      rewrite length_nparams, <- params_split.
      split; [ exact (sd_strat _ HD _ _ j Hcon ltac:(lia)) | exact HAv ].
    - intros j A pre HA.
      rewrite List.nth_error_map in HA.
      destruct (List.nth_error (cargs_nonrec gs) j) as [A0 |] eqn:HA0; cbn in HA; [ injection HA as -> | discriminate ].
      unfold ind_ar; rewrite (nth_atyp_eq _ _ _ _ _ Hcon HA0); reflexivity.
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
      pose proof (proj1 (sd_npar _ HD _ _ HA)) as HAv; rewrite <- (length_npre D k) in HAv at 2 by lia.
      eapply (sort_typ_rel (npre D k) A (npre_sem k) HAv ups ups2 vs vs');
        [ rewrite length_npre; lia | rewrite length_npre; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite rev_npre; apply per_gargs_app_intro; [ rewrite Hlu; exact Hu | exact Hg2 | exact Hgv ]. 
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
      destruct (sd_arg _ HD _ _ _ _ Hcon HA) as [HAv _].
      assert (HC : ⊨ (astrat gs k ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact (sd_strat _ HD _ _ k Hcon ltac:(lia))).
      assert (HT : (astrat gs k ++ ind_nparams D) ++ ind_uparams D
                     ⊨ A : (ind_sort D)[wk_shiftn (List.length (astrat gs k ++ ind_nparams D))]ʷ)
        by (rewrite <- List.app_assoc, <- params_split, List.length_app, length_astrat, length_nparams by lia; exact HAv).
      eapply (sort_typ_rel (astrat gs k ++ ind_nparams D) A HC HT ups ups2 (ms ++ vs) (ms' ++ vs'));
        [ rewrite !List.length_app, length_astrat, length_nparams by lia; lia
        | rewrite !List.length_app, length_astrat, length_nparams by lia; lia | exact Hu | exact Hu2 | | exact Ha ].
      rewrite <- List.app_assoc, <- params_split, List.rev_app_distr, !List.app_assoc.
      apply per_gargs_app_intro; [ rewrite List.length_app; rewrite List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; lia
                                 | exact Hpg |].
      unfold astrat; rewrite List.rev_involutive; exact Hgv. 
    Qed.

    Lemma canon_hc : forall ups2, per_gargs (List.rev (ind_uparams D)) nil nil ups ups2 ->
               forall ms ms' c gs gs1 Ps gs2 ws ws', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms' ->
               ind_con D c = Some gs -> gs = gs1 ++ ca_rec Ps :: gs2 ->
               tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
               exists bs bs', ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ms ++ ws) ↘ bs /\
                 ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups2 ++ ms' ++ ws') ↘ bs' /\
                 tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs'.
    Proof.
      intros ups2 Hg2 * Hm Hcon Heq Hp.
      pose proof (length_ups_gargs _ _ Hg2 Hu) as Hu2.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
        by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      pose proof (ar_gargs _ _ _ _ _ _ _ Hcon Hg2 Hu Ha Hm _ ws ws' HK Hp) as Hgv.
      pose proof (params_gargs _ _ _ _ _ Hg2 Hu Ha Hm) as Hpg.
      pose proof Hp as Hp0; rewrite tele_pre_iff in Hp0; destruct Hp0 as (Hlw & Hlw' & _).
      pose proof Hm as Hm0; rewrite tele_full_iff in Hm0; destruct Hm0 as (Hlm & Hlm' & _).
      rewrite List.length_rev, length_nparams in Hlm, Hlm'.
      destruct (rec_closure _ _ _ _ _ Hcon Heq ups ups2 ms ms' ws ws' Hu Hlm Hlw Hu2 Hlm' Hlw') as (bs & bs' & Ebs & Ebs' & Hgb & _).
      { unfold astrat; rewrite List.rev_app_distr, List.rev_involutive.
        rewrite (List.app_assoc ups), (List.app_assoc ups2).
        apply per_gargs_app_intro; [ rewrite List.length_app, List.length_rev, params_split, List.length_app,
                                       length_nparams, length_ind_uparams by exact Hle; lia | exact Hpg | exact Hgv ]. }
      exists bs, bs'; split; [ exact Ebs | split; [ exact Ebs' |] ].
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
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) ups.
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
      split; [| split; [| split; [| split ] ] ].
      - exact (canon_n_P _ D ups ups Hn).
      - exact (canon_n_I _ D ups ups (decl_closed_params D Hc) Hu Hu Hn).
      - exact (canon_a_P _ D ups ups Hv).
      - exact (canon_a_I _ D ups ups (decl_closed_params D Hc) Hu Hu Hn Hv).
      - apply (canon_adm (univ_idx a) D ups ups Hn Hv); intros; eapply canon_hc; eassumption.
    Qed.
  End Canon.

  Lemma ind_relate : forall ups ups' ns ns' a,
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups' ->
      List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ a ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns' ->
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_univ_elem (univ_idx a)
        ↘ (ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns).
  Proof.
    intros * Hg Hu Ha Hns.
    pose proof (length_ups_gargs _ _ Hg Hu) as Hu'.
    pose proof (uparams_refl_l _ _ Hg) as Hgd.
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (Hlu : List.length (List.rev (ind_uparams D)) = ind_nu D)
      by (rewrite List.length_rev; apply length_ind_uparams; exact Hle).
    eapply per_univ_elem_indty_canon;
      [ exact Hl | exact (decl_closed_params D Hc) | exact Hu | exact Hu' | | (eapply canon_hn; eassumption) | (eapply canon_ha; eassumption)
      | (eapply canon_hn; eassumption) | (eapply canon_ha; eassumption) | (eapply canon_hc; eassumption) | (eapply canon_hc; eassumption) | exact Hns ].
    intros s; exact (per_gargs_top _ _ _ _ _ Hg ltac:(rewrite Hlu; exact Hu) s).
  Qed.

  Lemma rev_params_sem : ⊨ List.rev (List.rev (ind_params D)) ++ ⋅.
  Proof. rewrite List.rev_involutive, List.app_nil_r; exact (sd_params _ HD). Qed.

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
    destruct (sd_sort _ HD) as [i HS].
    destruct (sem_ctx_per_ctx_env uparams_sem) as [RU HRU].
    pose proof (uparams_refl_l _ _ Hgu) as Hgu0.
    assert (Huass : tele_ass (List.rev (ind_uparams D))) by (apply List.Forall_rev, (decl_uparams_ass D Hc)).
    pose proof (per_gargs_base _ _ _ per_ctx_env_nil_true rev_uparams_sem Huass nil nil ρ nil _ _ I I I Hgu0) as Hgρ.
    assert (HRUρ : RU (env_args ρ ups) (env_args nil ups)) by exact (gargs_env_rel _ _ _ _ _ _ HRU uparams_sem Hlur Hgρ).
    destruct (rel_exp_of_typ_inversion_simple_at HRU HS _ _ HRUρ) as (a0 & a & Ea0 & Ea & _).
    (** The index of the sort's universe, at the parameters' values and at the
        uniform ones. *)
    assert (Hub : is_univ b) by exact (sort_wk_univ _ _ _ Eb).
    destruct (per_univ_elem_univ _ _ _ _ HR0 Hub) as [_ ER0].
    destruct (sem_ctx_per_ctx_env (sd_params _ HD)) as [RP HRP].
    assert (HPP : PER RP) by (eapply per_env_PER; exact HRP).
    assert (HRP0 : RP (env_args ρ ys) (env_args ρ' ys'))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRP (sd_params _ HD)); [ unfold ind_np in Hlen; exact Hlen | exact Hg ]).
    assert (HRPd : RP (env_args ρ ys) (env_args ρ ys)) by (etransitivity; [ exact HRP0 | symmetry; exact HRP0 ]).
    assert (HCp : ⊨ ind_nparams D ++ ind_uparams D) by (rewrite <- params_split; exact (sd_params _ HD)).
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
  Lemma valid_exp_ind0 : ⋅ ⊨ a_ind p : ind_ty D.
  Proof.
    destruct (sd_ty _ HD) as [i HT].
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
    exact (sem_ctx_app_r _ _ H).
  Qed.

  (** The weakening of a prefix of the arguments to its non-recursive ones. *)
  Lemma cargs_wk : forall gs1 gs2, gs = gs1 ++ gs2 ->
      cargs_ctx p D gs1 ++ ind_params D ⊨w (wk_pat (cargs_pat gs1)) : cargs_strat gs1 ++ ind_params D.
  Proof.
    induction gs1 as [| g gs1 IH] using List.rev_ind; intros gs2 Heq.
    - cbn [cargs_ctx cargs_ctx_aux cargs_strat cargs_pat List.rev List.map List.app].
      destruct (sem_ctx_per_ctx_env (sd_params _ HD)) as [R HR].
      eapply rel_wk_under_ctx_intro; [ exact HR | exact HR | exact (rel_wk_id R) ].
    - rewrite <- List.app_assoc in Heq; cbn [List.app] in Heq.
      pose proof (IH _ Heq) as IHw.
      pose proof (cargs_prefix_sem (gs1 ++ g :: nil) gs2 ltac:(rewrite <- List.app_assoc; exact Heq)) as HC.
      rewrite cargs_ctx_snoc, cargs_pat_snoc in *.
      destruct g as [A | Ps]; cbn [cargs_ctx_aux List.app wk_pat] in *.
      + rewrite cargs_strat_snoc_arg.
        assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (sd_arg _ HD _ _ _ _ Hcon HA) as (_ & j & HAv).
        rewrite Heq, <- astrat_prefix in HAv.
        exact (rel_wk_under_ctx_q IHw HAv).
      + rewrite cargs_strat_snoc_rec.
        exact (rel_wk_under_ctx_compose _ _ _ _ _ (rel_wk_under_ctx_shift HC) IHw).
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
      destruct (sd_sort _ HD) as [i HS].
      destruct (sem_ctx_per_ctx_env uparams_sem) as [RU HRU].
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
      destruct (sd_arg _ HD _ _ _ _ Hcon HA) as (_ & jA & HAv).
      rewrite Heq, <- astrat_prefix in HAv.
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

    Lemma con_rec_step : forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1))
          (nonrec_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_vals gs1 (List.firstn (List.length gs1) as1)) ->
        exists x x' bs, List.nth_error as1 (List.length gs1) = Some x /\ List.nth_error as1' (List.length gs1) = Some x' /\
          ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1)) ↘ bs /\
          ind_rel p D ups (ind_nr D ups) (ind_ar D ups) bs x x'.
    Proof.
      intros * Heq INV.
      pose proof (decl_closed_nu D Hc) as Hle.
      set (fa := List.firstn (List.length gs1) as1) in *.
      set (nv := nonrec_vals gs1 fa) in *.
      set (K := List.length (cargs_nonrec gs1)) in *.
      assert (Hlk : List.length fa = List.length gs1)
        by (unfold fa; rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
      assert (Hlnv : List.length nv = K) by (apply length_nonrec_vals; exact Hlk).
      assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
      destruct con_ups as (Hgu & Hgu0 & Hlu & Hlp').
      destruct con_sort as [a Ha].
      destruct con_ns as (Hns & Hnsd).
      assert (Hlns : List.length ns = ind_nn D) by (unfold ns; rewrite List.length_skipn; unfold ind_nn; lia).
      assert (Hgs : per_gargs (List.rev (astrat gs K ++ ind_params D)) nil nil (ups ++ ns ++ nv) (ups ++ ns ++ nv)).
      { unfold astrat; rewrite List.rev_app_distr, List.rev_involutive, (List.app_assoc ups).
        apply per_gargs_app_intro;
          [ rewrite List.length_app, List.length_rev, params_split, List.length_app, length_nparams, length_ind_uparams by exact Hle; lia
          | exact (params_gargs _ _ _ _ _ Hgu0 Hlu Ha Hnsd)
          | exact (ar_gargs _ _ _ _ _ _ _ Hcon Hgu0 Hlu Ha Hnsd _ _ _ HK INV) ]. }
      destruct (rec_closure _ _ _ _ _ Hcon Heq ups ups ns ns nv nv Hlu Hlns Hlnv Hlu Hlns Hlnv Hgs)
        as (bs & bs0 & Ebs & _ & _ & Hil).
      destruct (con_entry _ _ _ Heq) as (T & x & x' & i & Rk & HT & Hx & Hx' & [t t' Et Et' HRk] & Hxx).
      cbn [cargs_ctx_aux List.app] in HT; injection HT as <-.
      fold fa in Et.
      set (E1 := env_args nil (ps ++ fa)) in *.
      set (E2 := env_args nil (ups ++ ns ++ nv)) in *.
      assert (HwkE : ⟪wk_pat (cargs_pat gs1)⟫ E1 = E2).
      { unfold E1, E2; rewrite env_args_app, eval_wk_pat_args by exact Hlk.
        rewrite <- env_args_app, (List.app_assoc ups), <- con_ps; reflexivity. }
      destruct (sem_ctx_per_ctx_env (cargs_prefix_sem _ _ Heq)) as [RΓ HΓ].
      pose proof (con_prefix_env _ _ Heq _ HΓ) as HE1; fold fa E1 in HE1.
      assert (HlPs : List.length Ps = ind_nn D) by exact (length_rec_ps _ _ _ _ _ Hcon Heq).
      assert (HTex : forall m, m < ind_nn D ->
                 exists Tm, List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (K + ind_nn D))) Ps) m = Some Tm).
      { intros m Hm; apply nth_error_lt_some'.
        rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
      assert (Hlink : forall m P Tm, List.nth_error Ps m = Some P ->
                 List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (K + ind_nn D))) Ps) m = Some Tm ->
                 exists b1 b, ⟦ P[wk_pat (cargs_pat gs1)]ʷ ⟧ E1 ↘ b1 /\ ⟦ P ⟧ E2 ↘ b /\
                   ind_nr D ups m (List.firstn m bs) b b1).
      { intros * HP HTm.
        pose proof (sd_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HTm) as HPv.
        rewrite Heq, <- astrat_prefix in HPv.
        destruct (rel_exp_under_ctx_wk_simple (cargs_wk _ _ Heq) HPv) as (RΓ' & HΓ' & i1 & Hwk).
        assert (ER : RΓ <~> RΓ') by (eapply per_ctx_env_right_irrel; eassumption).
        destruct (Hwk _ _ (proj1 (ER _ _) HE1)) as (u & u' & Ru & Eu & Eu' & HRu & b1 & b & Eb1 & Eb & Hbb).
        fold fa E1 in Eu, Eu', Eb1, Eb.
        rewrite HwkE in Eu', Eb.
        pose proof (Hil _ _ _ HP HTm) as Hcan.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRu) HRu) as HRuu.
        pose proof (per_head_iff Eu' Eu' HRuu) as Rel.
        assert (HPu : PER Ru) by (eapply per_elem_PER; exact HRu).
        exists b1, b; split; [ exact Eb1 | split; [ exact Eb | apply Hcan, Rel; symmetry; exact Hbb ] ]. }
      destruct (eval_exps_each (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) E1) as [bs1 Ebs1].
      { intros m M HM; rewrite List.nth_error_map in HM.
        destruct (List.nth_error Ps m) as [P |] eqn:HP; cbn in HM; [ injection HM as <- | discriminate ].
        assert (Hm : m < ind_nn D) by (rewrite <- HlPs; apply List.nth_error_Some; congruence).
        destruct (HTex _ Hm) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & _ & Eb1 & _); eauto. }
      assert (Htf : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs1).
      { rewrite tele_full_iff, List.length_rev, length_nparams.
        rewrite (eval_exps_length _ _ _ Ebs), (eval_exps_length _ _ _ Ebs1), List.length_map.
        split; [ exact HlPs | split; [ exact HlPs |] ].
        intros j y y' Hy Hy'.
        assert (Hj : j < ind_nn D) by (rewrite <- HlPs, <- (eval_exps_length _ _ _ Ebs); apply List.nth_error_Some; congruence).
        destruct (nth_error_lt_some' Ps j ltac:(lia)) as [P HP].
        destruct (HTex _ Hj) as [Tm HTm].
        destruct (Hlink _ _ _ HP HTm) as (b1 & b & Eb1 & Eb & Hr).
        destruct (eval_exps_nth _ _ _ _ _ Ebs HP) as (b0 & Hb0 & Eb0).
        destruct (eval_exps_nth _ _ _ _ _ Ebs1 ltac:(rewrite List.nth_error_map, HP; reflexivity)) as (b2 & Hb2 & Eb2).
        assert (b0 = b) as -> by (eapply functional_eval_exp; eassumption).
        assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
        rewrite Hy in Hb0; injection Hb0 as ->; rewrite Hy' in Hb2; injection Hb2 as ->; exact Hr. }
      pose proof (ind_relate _ _ _ _ _ Hgu0 Hlu Ha Htf) as Hind.
      pose proof (per_univ_sym _ _ _ _ Hind) as Hind'.
      assert (Et0 : ⟦ apps (a_ind p) (ind_uvars D (List.length (cargs_pat gs1)) ++ List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ) Ps) ⟧ E1
                      ↘ d_ind p (ups ++ bs1)).
      { apply eval_apps_exp; exists (d_ind p nil), (ups ++ bs1); split; [ constructor | split ].
        - apply eval_exps_app; [| exact Ebs1 ].
          unfold ind_uvars; rewrite length_cargs_pat.
          unfold E1; rewrite con_ps, <- List.app_assoc.
          replace (List.length gs1 + ind_nn D) with (List.length (ns ++ fa)) by (rewrite List.length_app; lia).
          replace (ind_nu D) with (List.length ups) by exact Hlu.
          apply eval_vars_from_args.
        - change (d_ind p (ups ++ bs1)) with (d_ind p (nil ++ (ups ++ bs1))).
          apply eval_apps_ind; rewrite List.length_app, (eval_exps_length _ _ _ Ebs1), List.length_map; cbn; unfold ind_nn in *; lia. }
      assert (t = d_ind p (ups ++ bs1)) as Ht by (eapply functional_eval_exp; eassumption).
      rewrite Ht in HRk.
      assert (ERk : Rk <~> ind_rel p D ups (ind_nr D ups) (ind_ar D ups) bs)
        by (eapply per_univ_elem_right_irrel; [ exact HRk | exact Hind' ]).
      exists x, x', bs; split; [ exact Hx | split; [ exact Hx' | split; [ exact Ebs | apply ERk, Hxx ] ] ].
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
        ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups)
          (env_args nil (ups ++ ns ++ nonrec_vals gs1 (List.firstn (List.length gs1) as1))) gs2
          (List.skipn (List.length gs1) as1) (List.skipn (List.length gs1) as1').
    Proof.
      pose proof con_las' as Hla'.
      induction gs2 as [| g gs2 IH]; intros gs1 Heq.
      - rewrite List.app_nil_r in Heq.
        rewrite !List.skipn_all2 by (rewrite <- Heq; lia); constructor.
      - assert (Hk : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
        destruct (nth_error_lt_some' as1 (List.length gs1) ltac:(lia)) as [x Hx].
        destruct (nth_error_lt_some' as1' (List.length gs1) ltac:(lia)) as [x' Hx'].
        rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx').
        assert (Heq' : gs = (gs1 ++ g :: nil) ++ gs2) by (rewrite <- List.app_assoc; exact Heq).
        pose proof (IH _ Heq') as IHg.
        rewrite List.length_app in IHg; cbn [List.length] in IHg; rewrite Nat.add_1_r in IHg.
        rewrite (firstn_S_snoc _ _ _ Hx), nonrec_vals_app in IHg by (rewrite List.length_firstn; lia).
        destruct g as [A | Ps]; cbn [nonrec_vals] in IHg.
        + constructor.
          rewrite !List.app_assoc, env_args_snoc in IHg; rewrite !List.app_assoc; exact IHg.
        + assert (Hpre : List.firstn (List.length gs1) gs = gs1)
            by (rewrite Heq, firstn_app_exact by reflexivity; reflexivity).
          destruct (con_prefix (List.length gs1) ltac:(lia)) as [_ INVd].
          rewrite Hpre in INVd.
          destruct (con_rec_step _ _ _ Heq INVd) as (y & y' & bs & Hy & Hy' & Ebs & Hrel).
          rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
          econstructor; [ exact Ebs | exact Hrel |].
          rewrite List.app_nil_r in IHg; exact IHg.
    Qed.

    Lemma con_rel : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns (d_con p c (ps ++ as1)) (d_con p c (ps' ++ as1')).
    Proof.
      pose proof con_las' as Hla'.
      destruct con_ups as (_ & _ & _ & Hlp').
      destruct con_ns as (Hns & Hnsd).
      destruct (con_prefix (List.length gs) (le_n _)) as [Hnr _].
      rewrite List.firstn_all, !List.firstn_all2 in Hnr by lia.
      econstructor; [ exact Hnsd | exact Hcon | exact Hlp | exact Hlp' | exact Hnsd | exact Hns
                    | exact (tele_full_of_pre _ _ _ _ Hnr) |].
      pose proof (con_args_rel gs nil eq_refl) as H; cbn [List.length List.skipn nonrec_vals List.firstn] in H.
      rewrite List.app_nil_r in H; exact H.
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
    assert (E : Rb <~> ind_rel p D (List.firstn (ind_nu D) ps) (ind_nr D (List.firstn (ind_nu D) ps))
                       (ind_ar D (List.firstn (ind_nu D) ps)) (List.skipn (ind_nu D) ps))
      by (eapply per_univ_elem_right_irrel; [ exact HRb | exact Hind ]).
    apply E; exact Hrel.
  Qed.

  Lemma valid_exp_con0 : forall i, ⋅ ⊨ con_ty p D gs : Typeω@i -> ⋅ ⊨ a_con p c : con_ty p D gs.
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
