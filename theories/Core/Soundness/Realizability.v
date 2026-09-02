From Stdlib Require Import Nat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations Wk_Notations.

Open Scope list_scope.

(** A Kripke weakening is [⇑^n] on the nose ([kripke_shiftn]), so it acts on a
    variable by index arithmetic alone.  This replaces the [var_weaken_gen]
    induction of the explicit-substitution development, which had to compute
    [#(length Γ1)[σ]] for an arbitrary weakening [σ] by way of a context-lookup
    analysis ([wf_ctx_sub_ctx_lookup]) and a subtyping detour. *)
Lemma wk_var_kripke : forall Γ Δ φ x,
    Δ ⊢k φ : Γ ->
    φ x = x + (length Δ - length Γ).
Proof.
  intros * H%kripke_shiftn; destruct H as [_ Hφ].
  now rewrite (Hφ x).
Qed.

(** The instance the gluing model needs: the canonical variable of an extended
    context is read back as the de Bruijn *index* counting down from the length
    of wherever the weakening lands. *)
Corollary wk_var0_kripke : forall Γ A Δ φ,
    Δ ⊢k φ : Γ ▹ A ->
    φ 0 = length Δ - length Γ - 1.
Proof. intros * H; pose proof (wk_var_kripke _ _ _ 0 H); simpl in *; lia. Qed.

Lemma var_glu_elem_bot : forall a i P El Γ A,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A⟨↑⟩ ® #ᵈ (length Γ) ∈ glu_elem_bot i a.
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 4.
  - eapply glu_univ_elem_typ_monotone; eauto.
    mauto 4.
  - intros. progressive_inversion.
    assert (φ 0 = length Δ - length Γ - 1) as <- by (eapply wk_var0_kripke; eassumption).
    change #(φ 0) with #0⟨φ⟩.
    mauto 5.
Qed.

Theorem realize_glu_univ_elem_gen : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    (forall Γ A R,
        DF a ≈ a ∈ per_univ_elem i ↘ R ->
        Γ ⊢ A ® P ->
        Γ ⊢ A ® glu_typ_top i a) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
          Γ ⊢ M : A ® ⇑ a m ∈ El) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          DG a ∈ glu_univ_elem i ↘ P ↘ El ->
          Γ ⊢ M : A ® m ∈ El ->
          DF a ≈ a ∈ per_univ_elem i ↘ R ->
          Dom m ≈ m ∈ R ->
          Γ ⊢ M : A ® m ∈ glu_elem_top i a).
Proof.
  simpl. induction 1 using glu_univ_elem_ind.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct H as []);
    destruct_all.
  (* univ *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    clear_dups.
    apply_equiv_left.
    repeat split; eauto.
    repeat eexists.
    + glu_univ_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H5. trivial.
      * intros. saturate_kripke_escape.
        eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
    firstorder.
    specialize (H _ _ _ H10) as [? []].
    econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      deepexec H ltac:(fun H => destruct H).
      progressive_invert H16.
      deepexec H20 ltac:(fun H => pose proof H).
      functional_read_rewrite_clear.
      eapply wf_exp_eq_conv'; [ eassumption | mauto 3 ].
  (* nat *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    econstructor; trivial.
    intros.
    eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv'; [ eapply glu_nat_readback; eassumption | mauto 3 ].
  (* pi *)
  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_kripke_escape.
      pose proof (H13 Γ wk_id ltac:(mauto 3)) as HIT.
      rewrite exp_wk_id in HIT.
      dir_inversion_clear_by_head read_typ.
      assert (Γ ⊢ IT ® glu_typ_top i a) as [] by mauto 3.
      assert (Δ ⊢ A⟨φ⟩ ≈ Π IT⟨φ⟩ OT⟨wk_q φ⟩ : Type@i) as HA' by (rewrite <- exp_wk_pi; mauto 3).
      rewrite HA'.
      simpl. apply wf_exp_eq_pi_cong'; [ firstorder | ].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      pose proof (H13 _ _ H16) as HIPφ.
      assert (IEl (Δ ▹ IT⟨φ⟩) IT⟨φ⟩⟨↑⟩ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      assert (⊢ Δ ▹ IT⟨φ⟩) by mauto 3.
      assert (Δ ▹ IT⟨φ⟩ ⊢k φ ⊙ ↑ : Γ) as Hk by mauto 3.
      pose proof (H14 _ _ _ _ Hk HEl H24) as HOP.
      rewrite exp_sub_of_wk_q_extend in HOP.
      specialize (H8 _ _ _ H27 HOP) as [].
      rewrite <- (exp_wk_id OT⟨wk_q φ⟩).
      mauto 3.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.
    intros.
    saturate_kripke_escape.
    saturate_glu_info.
    match_by_head1 per_univ_elem invert_per_univ_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert (Δ ⊢ A⟨φ⟩ ≈ Π IT⟨φ⟩ OT⟨wk_q φ⟩ : Type@i) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
    assert (Δ ⊢ M⟨φ⟩ : Π IT⟨φ⟩ OT⟨wk_q φ⟩) as HM by mauto 3.
    assert (Δ ⊢ M⟨φ⟩ $ N : OT[(ι φ),,N]) as HMN
      by (rewrite <- exp_sub_wk_q_extend; eapply wf_app'; eassumption).
    pose proof (H10 _ _ _ _ H17 H18 equiv_n) as HOP.
    pose proof (H1 _ equiv_n _ H22) as HG.
    pose proof (H15 _ _ _ _ _ H H18 H0 equiv_n) as HNtop.
    destruct HNtop as [? ? ? ? ? HNtoprel HNrb].
    eapply glu_elem_bot_make with (P := OP n equiv_n) (El := OEl n equiv_n); try eassumption.
    + mauto 3 using domain_app_per.
    + intros Δ0 φ0 M' Hk Hrb.
      progressive_invert Hrb.
      assert (Δ0 ⊢k φ ⊙ φ0 : Γ) as Hkc by (eapply kripke_compose; eassumption).
      assert (Δ0 ⊢ A⟨φ ⊙ φ0⟩ ≈ Π IT⟨φ ⊙ φ0⟩ OT⟨wk_q (φ ⊙ φ0)⟩ : Type@i) as HAeq'
        by (rewrite <- exp_wk_pi; mauto 3).
      rewrite exp_wk_sub_of_wk_extend, <- exp_sub_wk_q_extend, exp_wk_app, exp_wk_wk.
      eapply wf_exp_eq_app_cong'.
      * eapply wf_exp_eq_conv'; [ eapply H12; eassumption | eassumption ].
      * rewrite <- exp_wk_wk. eapply HNrb; eassumption.
  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros Δ φ w Hk Hrb.
      saturate_kripke_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert Hrb.
      assert (⊢ Γ) by mauto 2.
      pose proof (H10 _ _ Hk) as HIPφ.
      pose proof (H10 Γ wk_id ltac:(mauto 3)) as HITId.
      rewrite exp_wk_id in HITId.
      assert (Γ ⊢ IT ® glu_typ_top i a) as [? ? HITrb] by mauto 3.
      assert (Δ ⊢ A⟨φ⟩ ≈ Π IT⟨φ⟩ OT⟨wk_q φ⟩ : Type@i) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
      assert (Δ ⊢ M⟨φ⟩ : Π IT⟨φ⟩ OT⟨wk_q φ⟩) as HM by mauto 3.
      eapply wf_exp_eq_conv'; [ | symmetry; eapply HAeq ].
      (** Read back a function by η-expanding it and recursing into the body. *)
      etransitivity; [ eapply wf_exp_eq_fn_eta'; eassumption | ].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; [ eapply HITrb; eassumption | ].
      assert (⊢ Δ ▹ IT⟨φ⟩) by mauto 3.
      assert (Δ ▹ IT⟨φ⟩ ⊢k φ ⊙ ↑ : Γ) as Hk' by mauto 3.
      pose proof (var_per_elem (length Δ) H0) as Hvar.
      assert (IEl (Δ ▹ IT⟨φ⟩) IT⟨φ⟩⟨↑⟩ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      destruct (H14 _ _ _ _ Hk' HEl Hvar) as [mn [Happ HOEl]].
      rewrite exp_sub_of_wk_q_extend in HOEl.
      rewrite exp_wk_wk.
      functional_eval_rewrite_clear.
      pose proof (H1 _ Hvar _ H20) as HG.
      destruct (H2 _ Hvar _ H20) as [? [? Htop]].
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      specialize (Htop _ _ _ _ _ HG HOEl ltac:(eassumption) ltac:(eassumption)) as [? ? ? ? ? ? Hrbtop].
      specialize (Hrbtop (Δ ▹ IT⟨φ⟩) wk_id M0 ltac:(mauto 3) Hrb).
      repeat rewrite exp_wk_id in Hrbtop.
      trivial.
  (* neut *)
  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    econstructor; eauto.
    + intros s. destruct (H3 s) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H11 (length Δ)) as [? []].
      firstorder.
Qed.

Corollary realize_glu_typ_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A,
      Γ ⊢ A ® P ->
      Γ ⊢ A ® glu_typ_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ glu_elem_bot i a ->
      Γ ⊢ M : A ® ⇑ a m ∈ El.
Proof.
  intros.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top : forall a i P El,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M m,
      Γ ⊢ M : A ® m ∈ El ->
      Γ ⊢ M : A ® m ∈ glu_elem_top i a.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
  eapply glu_univ_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.

Corollary var0_glu_elem : forall {i a P El Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A⟨↑⟩ ® ⇑! a (length Γ) ∈ El.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.
