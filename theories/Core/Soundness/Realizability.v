From Stdlib Require Import Nat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations Wk_Notations Fixed_Notations.

Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A Kripke weakening is [⇑^n] on the nose ([kripke_shiftn]), so it acts on
    a variable by index arithmetic alone. *)
Lemma wk_var_kripke : forall Γ Δ φ x,
    Δ ⊢k φ : Γ ->
    φ x = x + (length Δ - length Γ).
Proof.
  intros * H%kripke_shiftn; destruct H as [_ Hφ].
  now rewrite (Hφ x).
Qed.

(** The instance the gluing model needs: the canonical variable of an extended
    context reads back as the de Bruijn index counting down from the length of
    the context the weakening lands in. *)
Corollary wk_var0_kripke : forall Γ A Δ φ,
    Δ ⊢k φ : Γ ▹ A ->
    φ 0 = length Δ - length Γ - 1.
Proof. intros * H; pose proof (wk_var_kripke _ _ _ 0 H); simpl in *; lia. Qed.

Lemma var_glu_elem_bot : forall a i P El Γ A,
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® #ᵈ (length Γ) ∈ glu_elem_bot i a.
Proof.
  intros. saturate_glu_info.
  (** The ambient universe of the index is the large universe [Typeω@(ulvl i)],
      at which the syntactic rules apply directly. *)
  econstructor; mauto 4.
  - eapply glu_univ_elem_typ_monotone; eauto.
    mauto 4.
  - intros. progressive_inversion.
    assert (φ 0 = length Δ - length Γ - 1) as <- by (eapply wk_var0_kripke; eassumption).
    change #(φ 0) with #0[φ]ʷ.
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
  simpl. glu_univ_elem_induction1.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct H as []);
    destruct_all.
  (** The two universe clauses, large then small.  The large one's equations
      are at the ambient [Typeω@(ulvl i)].  The small one's element predicate
      carries its own readback clause, at the element's type, so its top case
      is that clause, and its bottom case lifts the neutral's equations to the
      ambient [Typeω@0] by cumulativity. *)
  1:{ econstructor; eauto; intros.
      progressive_inversion.
      mauto 3. }
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      repeat split; eauto.
      repeat eexists.
      + glu_univ_elem_econstructor; eauto; reflexivity.
      + simpl. repeat split.
        * eapply wf_conv'; eassumption.
        * intros. saturate_kripke_escape.
          eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ]. }
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
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
        eapply wf_exp_eq_conv'; [ eassumption | mauto 3 ]. }
  (** The small universe as a type: it reads back as the universe at the
      canonical form of its level, which its glued level term is equal to. *)
  1:{ econstructor; [ gen_presups; eassumption | eassumption |].
      intros Δ φ W Hφ Hr.
      assert (⊢ Δ) by (eapply kripke_dom; eassumption).
      inversion Hr; subst.
      assert (Δ ⊢ H4[φ]ʷ ≈ nf_lvl_of L : Level) by (eapply glu_lvl_readback; eassumption).
      assert (Δ ⊢ A[φ]ʷ ≈ Type⟨H4[φ]ʷ⟩ : Typeω@(ulvl i)) by mauto 3.
      etransitivity; [ eassumption |].
      apply wf_exp_eq_univ_cong_large_tm; [ assumption | gen_presups; assumption | assumption ]. }
  (** A neutral of a small universe: its type-level gluing is a neutral type's
      at the ambient [Typeω@0], which cumulativity reaches from the small
      universe, and its readback clause is the neutral's. *)
  1:{ handle_functional_glu_univ_elem.
      match_by_head glu_univ_elem invert_glu_univ_elem.
      clear_dups.
      apply_equiv_left.
      match goal with
      | H : suniv_glu_typ_pred _ _ _ _ |- _ => destruct H as [t [Ht HAt]]
      | H : exists t, glu_lvl _ t _ /\ _ |- _ => destruct H as [t [Ht HAt]]
      end.
      repeat apply conj; [ assumption | exists t; split; assumption | |].
      + do 2 eexists; split; [ glu_univ_elem_econstructor; eauto; reflexivity |].
        cbn; split; [ eapply suniv_elem_large; eassumption |].
        intros Δ φ M' Hφ Hr.
        eapply suniv_elem_eq_large; [ eauto | mauto 3 ].
      + intros Δ φ W Hφ Hr.
        inversion Hr; subst; eauto. }
  (** An element of a small universe reads back by its own readback clause,
      which is at its type. *)
  1:{ deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
      match goal with Hx : per_univ _ m m |- _ => destruct Hx as [? Hx] end.
      match goal with
      | Hx : per_univ_elem (us _) ?x m m, Ht : glu_lvl _ ?t l |- _ =>
          econstructor; [ assumption | eassumption | apply_equiv_left; cbn; exists t; split; assumption | |];
          [ intros s; destruct (per_univ_then_per_top_typ Hx s) as [W [HW _]];
            exists W; split; constructor; assumption
          | intros Δ φ w Hφ Hr; inversion Hr; subst; eauto ]
      end. }
  (* Level *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; [ eauto | mauto 3 |].
    intros Δ φ L **.
    progressive_inversion.
    eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv'; [ eapply glu_lvl_readback; eassumption | mauto 3 ].
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
  (* True *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    mauto 3.
  - econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      progressive_inversion.
      eapply wf_exp_eq_conv'; [ apply wf_exp_eq_true_eta; mauto 3 | mauto 3 ].
  (* False *)
  - econstructor; eauto; intros.
    progressive_inversion.
    mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    intros.
    eapply wf_exp_eq_conv'; [ firstorder | mauto 3 ].
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_kripke_escape.
      eapply wf_exp_eq_conv'; [ eapply glu_False_readback; eassumption | mauto 3 ].
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
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HA' by (rewrite <- exp_wk_pi; mauto 3).
      rewrite HA'.
      simpl. apply wf_exp_eq_pi_cong'; [ firstorder | ].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      pose proof (H13 _ _ H16) as HIPφ.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢k φ ⊙ ↑ : Γ) as Hk by mauto 3.
      pose proof (H14 _ _ _ _ Hk HEl H24) as HOP.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq _ _ _ (Typeω@(ulvl i)) _ _ (ulvl i) H12 H17 H16);
            cbn in Hqv; exact Hqv).
      specialize (H8 _ _ _ H27 HOP) as [].
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact HOT |].
      rewrite <- (exp_wk_id OT[ι (φ ⊙ ↑),,#0]).
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
    assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
    assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
    assert (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N]) as HMN
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
      assert (Δ0 ⊢ A[φ ⊙ φ0]ʷ ≈ Π IT[φ ⊙ φ0]ʷ OT[wk_q (φ ⊙ φ0)]ʷ : Typeω@(ulvl i)) as HAeq'
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
      assert (Δ ⊢ A[φ]ʷ ≈ Π IT[φ]ʷ OT[wk_q φ]ʷ : Typeω@(ulvl i)) as HAeq by (rewrite <- exp_wk_pi; mauto 3).
      assert (Δ ⊢ M[φ]ʷ : Π IT[φ]ʷ OT[wk_q φ]ʷ) as HM by mauto 3.
      eapply wf_exp_eq_conv'; [ | symmetry; eapply HAeq ].
      (** Read back a function by η-expanding it and recursing into the body. *)
      etransitivity; [ eapply wf_exp_eq_fn_eta'; eassumption | ].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; [ eapply HITrb; eassumption | ].
      assert (⊢ Δ ▹ IT[φ]ʷ) by mauto 3.
      assert (Δ ▹ IT[φ]ʷ ⊢k φ ⊙ ↑ : Γ) as Hk' by mauto 3.
      pose proof (var_per_elem (length Δ) H0) as Hvar.
      assert (IEl (Δ ▹ IT[φ]ʷ) IT[φ]ʷ[↑]ʷ #0 ⇑! a (length Δ)) as HEl
        by mauto 3 using var_glu_elem_bot.
      rewrite exp_wk_wk in HEl.
      destruct (H14 _ _ _ _ Hk' HEl Hvar) as [mn [Happ HOEl]].
      rewrite exp_wk_wk.
      functional_eval_rewrite_clear.
      pose proof (H1 _ Hvar _ H20) as HG.
      destruct (H2 _ Hvar _ H20) as [? [? Htop]].
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      specialize (Htop _ _ _ _ _ HG HOEl ltac:(eassumption) ltac:(eassumption)) as [? ? ? ? ? ? Hrbtop].
      specialize (Hrbtop (Δ ▹ IT[φ]ʷ) wk_id M0 ltac:(mauto 3) Hrb).
      repeat rewrite exp_wk_id in Hrbtop.
      assert (HOT : Δ ▹ IT[φ]ʷ ⊢ OT[ι (φ ⊙ ↑),,#0] ≈ OT[wk_q φ]ʷ : Typeω@(ulvl i))
        by (assert (Hqv := kripke_q_var_eq Δ Γ IT (Typeω@(ulvl i)) OT φ (ulvl i) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption));
            cbn in Hqv; exact Hqv).
      eapply wf_exp_eq_conv'; [ exact Hrbtop | exact HOT ].
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

Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.

Corollary var0_glu_elem : forall {i : uidx} {a P El Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ▹ A ⊢ #0 : A[↑]ʷ ® ⇑! a (length Γ) ∈ El.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.
