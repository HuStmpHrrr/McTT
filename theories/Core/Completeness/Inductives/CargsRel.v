(** * The Arguments of a Constructor, Related Canonically

    The arguments of a constructor of a member of a valid group, related
    at the telescope of their types ([cargs_ctx]), are related at the
    group's canonical relations ([con_args_rel], with the non-recursive
    ones at [canon_args_rel]), and conversely.  A recursive argument's type
    is related by its shape ([shape_char]), which asks the relations of
    the types of the members its shape ends in ([view_end_rel],
    [rview_end_rel]): these are premises here, so that the record views'
    coherence ([RviewEnds]) can use the lemmas before the rank induction
    gives the relations for every member. *)

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
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The recursive argument at a position of related arguments, by its
    shape. *)
Lemma con_args_rel_at : forall p D okr nr ar dr k u u' pre pre' gs vs vs',
    con_args_rel p D okr nr ar dr k u u' pre pre' gs vs vs' ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists x x', List.nth_error vs (List.length gs1) = Some x /\ List.nth_error vs' (List.length gs1) = Some x' /\
      rec_arg_rel p D okr nr ar dr k u u' (pre ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs))
        (pre' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) vs')) t x x'.
Proof.
  induction 1; intros [| g gs1] Qs gs2 Heq; cbn [List.app] in Heq; inversion Heq; subst;
    try match goal with IH : forall _ _ _, _ = _ -> _ |- _ => destruct (IH _ _ _ eq_refl) as (x & x' & Hx & Hx' & Hr0) end.
  - exists x, x'; cbn; rewrite <- !List.app_assoc in Hr0; repeat split; assumption.
  - do 2 eexists; cbn; rewrite !List.app_nil_r; repeat split; eassumption.
  - exists x, x'; cbn; repeat split; assumption.
Qed.

(** ** From the Telescope to the Canonical Relations

    Parameters [ps], [ps'] related at the member's telescope and arguments
    [as1], [as1'] related at the constructor's: related canonically, at
    the bases the parameters begin with. *)
Section ConArgs.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Variables (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HM : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨ := vg_cargs_sem p D Hg Hcv k Mk c gs HM Hcon.
  Variables (ps ps' as1 as1' : list domain).
  Hypotheses (Hgp : per_gargs (List.rev (im_params D Mk)) nil nil ps ps') (Hlp : List.length ps = im_np D Mk)
    (Hga : per_gargs (List.rev (cargs_ctx p D Mk gs)) (env_args nil ps) (env_args nil ps') as1 as1')
    (Hla : List.length as1 = List.length gs).
  Let ups := List.firstn (ind_nu D) ps.
  Let ns := List.skipn (ind_nu D) ps.
  Let ups' := List.firstn (ind_nu D) ps'.
  Let ns' := List.skipn (ind_nu D) ps'.
  (** The relations of the types of the members the recursive arguments'
      shapes end in *)
  Hypothesis (Hends : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    view_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t) /\
    rview_end_rel p D (List.firstn (ind_nu D) ps) (List.firstn (ind_nu D) ps) (ptyp_mem t)).

  Lemma con_ps : ps = ups ++ ns.
  Proof. symmetry; apply List.firstn_skipn. Qed.

  Lemma con_ps_len' : List.length ps' = im_np D Mk.
  Proof. destruct (per_gargs_length _ _ _ _ _ Hgp) as [H _]; lia. Qed.

  Lemma con_ups_rel : per_gargs (List.rev (ind_uparams D)) nil nil ups ups'.
  Proof. exact (proj1 (params_split_rel D HD Hc k Mk HM _ _ _ _ Hgp Hlp)). Qed.

  Lemma con_ups_len : List.length ups = ind_nu D.
  Proof. unfold ups; rewrite List.length_firstn; unfold im_np in Hlp; lia. Qed.

  Lemma con_ups_refl : per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (uparams_refl_l D HD Hc _ _ con_ups_rel). Qed.

  Lemma con_ns_len : List.length ns = im_nn Mk.
  Proof. unfold ns; rewrite List.length_skipn; unfold im_np in Hlp; lia. Qed.

  Lemma con_ns_rel : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns'.
  Proof.
    destruct (params_split_rel D HD Hc k Mk HM _ _ _ _ Hgp Hlp) as (_ & Hgn & _ & _).
    eapply (gargs_tele_canon _ (canon_nparams_rel D ups k) (env_args nil ups));
      [ | exact Hgn | rewrite List.length_rev, length_im_nparams; exact con_ns_len ].
    intros j A pre HA; unfold canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HM HA), env_args_app; reflexivity.
  Qed.

  Lemma con_ns_refl : tele_rel (canon_nparams_rel D ups k) (List.rev (im_nparams Mk)) ns ns.
  Proof.
    destruct (vg_canon p D Hg ups con_ups_refl con_ups_len) as [CnP CnI CaP CaI CdP CdI].
    exact (nparams_rel_refl_l p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI k Mk HM _ _ con_ns_rel).
  Qed.

  Lemma con_las' : List.length as1' = List.length gs.
  Proof. destruct (per_gargs_length _ _ _ _ _ Hga) as [H _]; lia. Qed.

  Lemma con_args_split : forall gs1 gs2, gs = gs1 ++ gs2 ->
      per_gargs (List.rev (cargs_ctx p D Mk gs1)) (env_args nil ps) (env_args nil ps')
        (List.firstn (List.length gs1) as1) (List.firstn (List.length gs1) as1') /\
      per_gargs (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) gs2))
        (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))
        (List.skipn (List.length gs1) as1) (List.skipn (List.length gs1) as1').
  Proof.
    intros * Heq.
    pose proof con_las' as Hla'.
    set (n := List.length gs1).
    assert (Hk : n <= List.length gs) by (unfold n; rewrite Heq, List.length_app; lia).
    pose proof Hga as H.
    unfold cargs_ctx in H; rewrite Heq, cargs_ctx_aux_app, List.app_nil_r, List.rev_app_distr in H.
    rewrite <- (List.firstn_skipn n as1), <- (List.firstn_skipn n as1') in H.
    assert (L1 : List.length (List.firstn n as1) = List.length (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)))
      by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold n; lia).
    assert (L2 : List.length (List.firstn n as1') = List.length (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)))
      by (rewrite List.length_firstn, List.length_rev, length_cargs_ctx_aux; unfold n; lia).
    destruct (per_gargs_app (List.rev (cargs_ctx_aux p D (im_nn Mk) nil gs1)) (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) gs2))
                _ _ (List.firstn n as1) (List.firstn n as1') (List.skipn n as1) (List.skipn n as1') L1 H L2) as [H1 H2].
    split; [ exact H1 | rewrite !env_args_app; exact H2 ].
  Qed.

  (** The environment of the parameters and the first arguments is one of
      the context of their types. *)
  Lemma con_prefix_env : forall gs1 gs2, gs = gs1 ++ gs2 ->
      forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
        R (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps ++ List.firstn (List.length gs1) as1)).
  Proof.
    intros * Heq R HR.
    pose proof (cargs_prefix_sem D p Mk gs HΨ _ _ Heq) as HC.
    pose proof con_las' as Hla'.
    assert (HPR : PER R) by (eapply per_env_PER; exact HR).
    assert (Hk : List.length gs1 <= List.length gs) by (rewrite Heq, List.length_app; lia).
    assert (Hcross : R (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR HC).
      - rewrite !List.length_app, length_cargs_ctx, List.length_firstn, length_im_params; unfold im_np in *; lia.
      - rewrite List.rev_app_distr; apply per_gargs_app_intro; [ rewrite List.length_rev, length_im_params; exact Hlp | exact Hgp |].
        exact (proj1 (con_args_split _ _ Heq)). }
    etransitivity; [ exact Hcross | symmetry; exact Hcross ].
  Qed.

  (** The argument at a position, related at its type. *)
  Lemma con_entry : forall gs1 g gs2, gs = gs1 ++ g :: gs2 -> forall x x',
      List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
      per_gargs (List.rev (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) (g :: nil)))
        (env_args nil (ps ++ List.firstn (List.length gs1) as1)) (env_args nil (ps' ++ List.firstn (List.length gs1) as1'))
        (x :: nil) (x' :: nil).
  Proof.
    intros * Heq x x' Hx Hx'.
    destruct (con_args_split _ _ Heq) as [_ H2].
    rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx') in H2.
    destruct g as [A | t]; cbn [cargs_ctx_aux List.app] in H2 |- *; rewrite List.rev_app_distr in H2; cbn [List.rev List.app] in H2 |- *;
      inversion H2 as [| i T ? ? ? ? ? ? ? R HT Hxx]; subst;
      (econstructor; [ exact HT | exact Hxx | constructor ]).
  Qed.

  Lemma con_arg_step : forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 -> forall x x',
      List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
      canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) x x' /\
      canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) x x.
  Proof.
    intros * Heq x x' Hx Hx'.
    assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
      by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
    pose proof (con_entry _ _ _ Heq x x' Hx Hx') as He.
    cbn [cargs_ctx_aux List.app List.rev] in He.
    inversion He as [| i T ? ? ? ? ? ? ? Rk [t t' Et Et' HRk] Hxx]; clear He.
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (valid_ind_decl_arg _ HD _ _ _ _ _ _ HM Hcon HA) as (_ & jA & HAv).
    rewrite Heq, <- nonrec_args_prefix_cargs_strat in HAv.
    destruct (rel_exp_under_ctx_wk_simple (cargs_wk D p k Mk c gs HD HM Hcon HΨ _ _ Heq) HAv) as (RΓ & HΓ & i0 & Hwk).
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
    assert (Hcan : canon_args_rel D ups k ns c (List.length (cargs_nonrec gs1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
                     <~> Rm).
    { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HM Hcon HA).
      rewrite List.app_assoc, <- con_ps.
      symmetry; exact (per_head_iff Em' Em' HRd). }
    assert (HPk : PER Rk) by (eapply per_elem_PER; exact HRk).
    split.
    - apply Hcan, ERk, Hxx.
    - apply Hcan, ERk; etransitivity; [ exact Hxx | symmetry; exact Hxx ].
  Qed.

  Lemma con_rec_step : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1))
        (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec gs1))
        (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1)) (nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) ->
      forall x x', List.nth_error as1 (List.length gs1) = Some x -> List.nth_error as1' (List.length gs1) = Some x' ->
        rec_arg_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
          k ups ups' (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
          (ns' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) t x x'.
  Proof.
    intros * Heq INV INVc x x' Hx Hx'.
    pose proof (con_entry _ _ _ Heq x x' Hx Hx') as He.
    cbn [cargs_ctx_aux List.app List.rev] in He.
    inversion He as [| i T ? ? ? ? ? ? ? Rk [a a' Ea Ea' HRk] Hxx]; clear He.
    pose proof (per_univ_trans _ _ _ _ _ _ HRk (per_univ_sym _ _ _ _ HRk)) as HRd.
    assert (Hlk : List.length (List.firstn (List.length gs1) as1) = List.length gs1)
      by (rewrite List.length_firstn; rewrite Hla, Heq, List.length_app; cbn; lia).
    assert (Hpre : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
               R (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1)) (env_args nil (ups ++ ns ++ List.firstn (List.length gs1) as1))).
    { intros R HR; rewrite List.app_assoc, <- con_ps; exact (con_prefix_env _ _ Heq R HR). }
    rewrite con_ps, <- List.app_assoc in Ea.
    destruct (Hends _ _ _ Heq) as [Hend Hrend].
    pose proof (shape_char p D Hg Hcv k Mk c gs HM Hcon HΨ _ _ _ Heq ups ns _ con_ups_len con_ns_len Hlk con_ups_refl con_ns_refl
                  INV Hpre Hend Hrend (List.length (ptyp_doms t)) 0 nil a i Rk eq_refl (tele_prefix_rel_nil _) ltac:(cbn; constructor)
                  ltac:(rewrite List.app_nil_r; exact Ea) HRd) as Hsh.
    rewrite List.app_nil_r in Hsh; cbn [ptyp_skip] in Hsh; apply Hsh in Hxx.
    apply (vg_rec_arg_move_right p D Hg k Mk c gs1 t gs2 ups ups' ns ns' _ _ x x' HM ltac:(rewrite <- Heq; exact Hcon)
             con_ups_rel con_ups_len con_ns_rel INVc).
    exact Hxx.
  Qed.

  Lemma con_split_at : forall n g, List.nth_error gs n = Some g ->
      gs = List.firstn n gs ++ g :: List.skipn (S n) gs /\ List.length (List.firstn n gs) = n.
  Proof.
    intros * Hg0; split; [ rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity |].
    rewrite List.length_firstn; assert (n < List.length gs) by (apply List.nth_error_Some; congruence); lia.
  Qed.

  Lemma con_prefix : forall n, n <= List.length gs ->
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec (List.firstn n gs)))
        (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)) (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1')) /\
      tele_prefix_rel (canon_args_rel D ups k ns c) (List.length (cargs_nonrec (List.firstn n gs)))
        (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)) (nonrec_arg_vals (List.firstn n gs) (List.firstn n as1)).
  Proof.
    pose proof con_las' as Hla'.
    induction n as [| n IH]; intros Hn; [ cbn; split; apply tele_prefix_rel_nil |].
    destruct (IH ltac:(lia)) as [IHc IHd].
    destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg0].
    destruct (nth_error_lt_some' as1 n ltac:(lia)) as [x Hx].
    destruct (nth_error_lt_some' as1' n ltac:(lia)) as [x' Hx'].
    destruct (con_split_at _ _ Hg0) as [Heq Hlf].
    rewrite (firstn_S_snoc _ _ _ Hg0), (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
    rewrite !nonrec_arg_vals_app by (rewrite !List.length_firstn; lia).
    rewrite cargs_nonrec_app.
    destruct g as [A | t]; cbn [nonrec_arg_vals cargs_nonrec].
    - rewrite <- Hlf in Hx, Hx'.
      destruct (con_arg_step _ _ _ Heq x x' Hx Hx') as [Hr Hrd].
      rewrite Hlf in Hr, Hrd.
      rewrite List.length_app, Nat.add_1_r.
      split; apply tele_prefix_rel_snoc; assumption.
    - rewrite !List.app_nil_r; split; assumption.
  Qed.

  Lemma con_args_relate : forall gs2 gs1, gs = gs1 ++ gs2 ->
      con_args_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
        k ups ups' (ns ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1))
        (ns' ++ nonrec_arg_vals gs1 (List.firstn (List.length gs1) as1')) gs2
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
      rewrite (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx'), !nonrec_arg_vals_app in IHg by (rewrite List.length_firstn; lia).
      destruct g as [A | t]; cbn [nonrec_arg_vals] in IHg.
      + constructor.
        rewrite <- !List.app_assoc; exact IHg.
      + assert (Hpre : List.firstn (List.length gs1) gs = gs1)
          by (rewrite Heq, firstn_app_exact by reflexivity; reflexivity).
        destruct (con_prefix (List.length gs1) ltac:(lia)) as [INVc INVd].
        rewrite Hpre in INVc, INVd.
        constructor; [ exact (con_rec_step _ _ _ Heq INVd INVc x x' Hx Hx') |].
        repeat rewrite List.app_nil_r in IHg; exact IHg.
  Qed.

  (** The arguments related canonically, after the non-uniform
      parameters. *)
  Lemma con_args_canon :
      tele_rel (canon_args_rel D ups k ns c) (cargs_nonrec gs) (nonrec_arg_vals gs as1) (nonrec_arg_vals gs as1') /\
      con_args_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
        k ups ups' ns ns' gs as1 as1'.
  Proof.
    pose proof con_las' as Hla'.
    destruct (con_prefix (List.length gs) (le_n _)) as [Hnr _].
    rewrite List.firstn_all, !List.firstn_all2 in Hnr by lia.
    split; [ exact (tele_rel_of_pre _ _ _ _ Hnr) |].
    pose proof (con_args_relate gs nil eq_refl) as H; cbn [List.length List.skipn nonrec_arg_vals List.firstn] in H.
    repeat rewrite List.app_nil_r in H; exact H.
  Qed.

  (** The constructor at the arguments, at a member that is not a record
      view. *)
  Lemma con_rel : forall cs cs', im_is_rview Mk = false -> List.length cs = im_unu D Mk -> List.length cs' = im_unu D Mk ->
      ind_rel p D (okr_at D ups (canon_nparams_rel D ups)) (canon_nparams_rel D ups) (canon_args_rel D ups) (canon_doms_rel ups)
        k ups ups' ns ns'
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs ++ ns) ++ as1))
        (d_con (fst (im_ref p k Mk)) (snd (im_ref p k Mk)) c ((cs' ++ ns') ++ as1')).
  Proof.
    intros cs cs' Hrv Hcs Hcs'.
    pose proof con_las' as Hla'.
    pose proof con_ps_len' as Hlp'.
    assert (Hsk : forall (l1 l2 : list domain), List.length l1 = im_unu D Mk -> List.skipn (im_unu D Mk) (l1 ++ l2) = l2)
      by (intros l1 l2 Hl1; rewrite <- Hl1, List.skipn_app, List.skipn_all, Nat.sub_diag; reflexivity).
    assert (Hlns' : List.length ns' = im_nn Mk) by (unfold ns'; rewrite List.length_skipn; unfold im_np in *; lia).
    destruct (vg_canon p D Hg ups con_ups_refl con_ups_len) as [CnP CnI CaP CaI CdP CdI].
    destruct con_args_canon as [Hnr Hia].
    eapply ind_rel_con with (gs := gs) (Mk := Mk);
      [ exact HM | exact Hrv | apply surjective_pairing | exact con_ns_rel | exact Hcon
      | rewrite List.length_app, Hcs, con_ns_len; lia | rewrite List.length_app, Hcs', Hlns'; lia
      | rewrite (Hsk _ _ Hcs); exact con_ns_refl
      | rewrite (Hsk _ _ Hcs'); exact (nparams_rel_refl_r p D ups _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HM _ _ con_ns_rel)
      | rewrite (Hsk _ _ Hcs); exact Hnr |].
    rewrite (Hsk _ _ Hcs), (Hsk _ _ Hcs'); exact Hia.
  Qed.
End ConArgs.

(** ** From the Canonical Relations to the Telescope

    Arguments related canonically at the bases [u0], after the stored
    non-uniform parameters [X] and [X'] of the two constructors, are
    related at the telescope of their types there. *)
Section ConCanon.
  Variables (p : qname) (D : ind_decl).
  Hypotheses (Hg : valid_group p D) (Hcv : containers_valid D).
  Let HD := valid_group_valid _ _ Hg.
  Let Hc := valid_group_closed _ _ Hg.
  Let Hsu := valid_group_sort _ _ Hg.
  Let Hass := valid_group_ass _ _ Hg.
  Variable (u0 : list domain).
  Hypotheses (u0_gargs : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0) (u0_len : List.length u0 = ind_nu D).
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  #[local] Abbreviation Hcp := (vg_canon p D Hg u0 u0_gargs u0_len).
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation trefl_l := (nparams_rel_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
  Variable (k : nat) (Mk : imember) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hcon : ind_con Mk c = Some gs).
  Let HΨ := vg_cargs_sem p D Hg Hcv k Mk c gs HMk Hcon.
  Let T := List.rev (im_nparams Mk).
  (** The relations of the types of the members the recursive arguments'
      shapes end in *)
  Hypothesis (Hends : forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    view_end_rel p D u0 u0 (ptyp_mem t) /\ rview_end_rel p D u0 u0 (ptyp_mem t)).

  Lemma cargs_gargs : forall X X' vs vs',
      tele_rel (nr k) T X X' ->
      tele_rel (ar k X c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
      con_args_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 X X' gs vs vs' ->
      forall n, n <= List.length gs ->
      per_gargs (List.rev (cargs_ctx p D Mk (List.firstn n gs))) (env_args nil (u0 ++ X)) (env_args nil (u0 ++ X'))
        (List.firstn n vs) (List.firstn n vs').
  Proof.
    intros * Hab Har Hia.
    destruct (sort_value D HD u0 u0_gargs u0_len) as [a0 Ha0].
    pose proof (trefl_l _ _ HMk _ _ Hab) as Haa.
    destruct (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia) as [Hlv Hlv'].
    pose proof Hab as H0; rewrite tele_rel_iff in H0; destruct H0 as (Lna & Lnb & _).
    unfold T in Lna, Lnb; rewrite List.length_rev, length_im_nparams in Lna, Lnb.
    pose proof (params_gargs D HD Hc Hsu k Mk HMk u0 u0 a0 X X' u0_gargs u0_len Ha0 Hab) as Hpg.
    pose proof (params_gargs D HD Hc Hsu k Mk HMk u0 u0 a0 X X u0_gargs u0_len Ha0 Haa) as Hpgd.
    induction n as [| n IH]; intros Hn; [ cbn; constructor |].
    destruct (nth_error_lt_some' gs n ltac:(lia)) as [g Hg0].
    destruct (nth_error_lt_some' vs n ltac:(lia)) as [x Hx].
    destruct (nth_error_lt_some' vs' n ltac:(lia)) as [x' Hx'].
    assert (Heq : gs = List.firstn n gs ++ g :: List.skipn (S n) gs)
      by (rewrite <- (skipn_nth_cons' _ _ _ Hg0), List.firstn_skipn; reflexivity).
    assert (Lk : List.length (List.firstn n gs) = n) by (rewrite List.length_firstn; lia).
    set (gs1 := List.firstn n gs) in *.
    set (fa := List.firstn n vs); set (fa' := List.firstn n vs').
    assert (Lfa : List.length fa = n) by (unfold fa; rewrite List.length_firstn; lia).
    assert (Lfa' : List.length fa' = n) by (unfold fa'; rewrite List.length_firstn; lia).
    pose proof (IH ltac:(lia)) as IHk.
    rewrite (firstn_S_snoc _ _ _ Hg0), (firstn_S_snoc _ _ _ Hx), (firstn_S_snoc _ _ _ Hx').
    fold gs1 fa fa'.
    rewrite cargs_ctx_snoc, List.rev_app_distr.
    (** The prefix's context, and the entry's type there. *)
    pose proof (cargs_prefix_sem D p Mk gs HΨ (gs1 ++ g :: nil) (List.skipn (S n) gs)
                  ltac:(rewrite <- List.app_assoc; exact Heq)) as HC1.
    rewrite cargs_ctx_snoc, <- List.app_assoc in HC1.
    pose proof (rel_ctx_wf_app_r _ _ HC1) as HC0.
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
    assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
    assert (Lc : forall Y (zs : list domain), List.length Y = im_nn Mk -> List.length zs = n ->
               List.length ((u0 ++ Y) ++ zs) = List.length (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (intros; rewrite !List.length_app, length_cargs_ctx, length_im_params, u0_len; unfold im_np; lia).
    assert (HE : R0 (env_args nil ((u0 ++ X) ++ fa)) (env_args nil ((u0 ++ X') ++ fa'))).
    { apply (gargs_env_rel _ _ _ _ _ _ HR0 HC0 (Lc _ _ Lna Lfa)).
      rewrite List.rev_app_distr; apply per_gargs_app_intro;
        [ rewrite List.length_rev, length_im_params, List.length_app, u0_len, Lna; unfold im_np; lia | exact Hpg |].
      exact IHk. }
    assert (HEE : R0 (env_args nil ((u0 ++ X) ++ fa)) (env_args nil ((u0 ++ X) ++ fa)))
      by (etransitivity; [ exact HE | symmetry; exact HE ]).
    assert (Hgd : per_gargs (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) nil nil (u0 ++ X ++ fa) (u0 ++ X ++ fa)).
    { assert (HC0' : ⊨ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HC0).
      assert (HR0' : EF List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅
                       ≈ List.rev (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)) ++ ⋅ ∈ per_ctx_env ↘ R0)
        by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
      assert (L1 : List.length ((u0 ++ X) ++ fa) = List.length (List.rev (cargs_ctx p D Mk gs1 ++ im_params D Mk)))
        by (rewrite List.length_rev; exact (Lc _ _ Lna Lfa)).
      pose proof (proj2 (rel_gargs _ _ _ _ per_ctx_env_nil_true HC0'
                           (List.Forall_rev (proj2 (List.Forall_app _ _ _) (conj (cargs_ctx_aux_ass _ _ _ _ _) (member_params_ass D Hc _ _ HMk))))
                           HR0' nil nil _ _ L1 L1 HEE)) as H.
      rewrite <- List.app_assoc in H; exact H. }
    assert (Hpre : forall R, EF cargs_ctx p D Mk gs1 ++ im_params D Mk ≈ cargs_ctx p D Mk gs1 ++ im_params D Mk ∈ per_ctx_env ↘ R ->
               R (env_args nil (u0 ++ X ++ fa)) (env_args nil (u0 ++ X ++ fa))).
    { intros R HR; assert (E : R0 <~> R) by (eapply per_ctx_env_right_irrel; eassumption).
      apply E; rewrite List.app_assoc; exact HEE. }
    (** The non-recursive arguments before, canonically. *)
    set (K := List.length (cargs_nonrec gs1)).
    assert (Hnv : forall ws, List.length ws = List.length gs -> List.firstn K (nonrec_arg_vals gs ws) = nonrec_arg_vals gs1 (List.firstn n ws)).
    { intros ws Lw; rewrite <- (List.firstn_skipn n ws) at 1.
      rewrite Heq at 1; fold gs1.
      rewrite nonrec_arg_vals_app by (rewrite List.length_firstn; lia).
      rewrite firstn_app_exact by (apply length_nonrec_arg_vals; rewrite List.length_firstn; lia); reflexivity. }
    assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hpk0 : tele_prefix_rel (ar k X c) K (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa')).
    { unfold fa, fa'; rewrite <- (Hnv vs Hlv), <- (Hnv vs' Hlv').
      apply tele_prefix_rel_of_full with (T := cargs_nonrec gs); [ exact Har | exact HKl ]. }
    assert (Hpk : tele_prefix_rel (ar k X c) K (nonrec_arg_vals gs1 fa) (nonrec_arg_vals gs1 fa))
      by exact (args_rel_pre_refl_l p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HMk X c gs Haa Hcon K _ _ HKl Hpk0).
    pose proof Har as Har0; rewrite tele_rel_iff in Har0; destruct Har0 as (_ & _ & Harr).
    destruct g as [A | t]; cbn [cargs_ctx_aux List.app List.rev] in HC1 |- *.
    - destruct (rel_ctx_wf_ass_inv HC1) as [j HT].
      destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (t & t' & Et & Et' & [R HR]).
      pose proof Et as Et0; rewrite env_args_app in Et, Et'.
      destruct (per_univ_elem_to_nat _ _ _ _ HR) as [m0 Hm0].
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ m0 R); [ rewrite List.length_rev, length_cargs_ctx; lia | exact IHk
                                                   | exact (mk_rel_mod_eval _ _ Et Et' Hm0) |].
      destruct (vg_arg_head p D Hg Hcv k Mk c gs gs1 A _ u0 X fa HMk Hcon Heq u0_len Lna (eq_trans Lfa (eq_sym Lk)) Hgd)
        as (iA0 & Rh & a & Ea & Haa' & ERh).
      rewrite <- List.app_assoc in Et0.
      assert (a = t) as -> by (eapply functional_eval_exp; eassumption).
      assert (E1 : R <~> Rh) by (eapply per_univ_elem_right_irrel; [ exact HR | exact Haa' ]).
      apply E1, ERh.
      assert (HxK : List.nth_error (nonrec_arg_vals gs vs) K = Some x /\ List.nth_error (nonrec_arg_vals gs vs') K = Some x').
      { rewrite <- (List.firstn_skipn n vs), <- (List.firstn_skipn n vs'); fold fa fa'.
        rewrite (skipn_nth_cons' _ _ _ Hx), (skipn_nth_cons' _ _ _ Hx').
        rewrite Heq at 1 2; fold gs1.
        rewrite !nonrec_arg_vals_app by lia; cbn [nonrec_arg_vals].
        rewrite !List.nth_error_app2 by (rewrite length_nonrec_arg_vals by lia; unfold K; lia).
        rewrite !length_nonrec_arg_vals by lia; fold K; rewrite Nat.sub_diag; split; reflexivity. }
      pose proof (Harr K x x' (proj1 HxK) (proj2 HxK)) as Hr; rewrite (Hnv vs Hlv) in Hr; fold fa in Hr.
      exact Hr.
    - destruct (rel_ctx_wf_ass_inv HC1) as [j HT].
      destruct (rel_exp_of_typ_inversion_simple_at HR0 HT _ _ HE) as (a & a' & Ea & Ea' & [R HR]).
      pose proof Ea as Ea0; rewrite env_args_app in Ea, Ea'.
      destruct (per_univ_elem_to_nat _ _ _ _ HR) as [m0 Hm0].
      apply (per_gargs_snoc _ _ _ _ _ _ _ _ m0 R); [ rewrite List.length_rev, length_cargs_ctx; lia | exact IHk
                                                   | exact (mk_rel_mod_eval _ _ Ea Ea' Hm0) |].
      pose proof (per_univ_trans _ _ _ _ _ _ HR (per_univ_sym _ _ _ _ HR)) as HRd.
      rewrite <- List.app_assoc in Ea0.
      destruct (Hends _ _ _ Heq) as [Hend Hrend].
      pose proof (shape_char p D Hg Hcv k Mk c gs HMk Hcon HΨ gs1 t _ Heq u0 X fa u0_len Lna (eq_trans Lfa (eq_sym Lk)) u0_gargs Haa Hpk Hpre
                    Hend Hrend (List.length (ptyp_doms t)) 0 nil a j R eq_refl (tele_prefix_rel_nil _) ltac:(cbn; constructor)
                    ltac:(rewrite List.app_nil_r; exact Ea0) HRd) as ER.
      repeat rewrite List.app_nil_r in ER; cbn [ptyp_skip] in ER.
      apply ER.
      destruct (con_args_rel_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hia gs1 t _ Heq) as (y & y' & Hy & Hy' & Hrel).
      rewrite Lk in Hy, Hy', Hrel; rewrite Hx in Hy; injection Hy as <-; rewrite Hx' in Hy'; injection Hy' as <-.
      fold fa fa' in Hrel.
      exact (proj2 (vg_rec_arg_move_right p D Hg k Mk c gs1 t _ u0 u0 X X' _ _ x x' HMk
                      ltac:(rewrite <- Heq; exact Hcon) u0_gargs u0_len Hab Hpk0) Hrel).
  Qed.
End ConCanon.

End Fixed_GCtx.
