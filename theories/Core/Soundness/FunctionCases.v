(** * Π-Types in the Gluing Model

    The Π gluing predicates quantify over Kripke weakenings, so a codomain
    obligation has the form [OT[(ι φ),,M]]. [exp_sub_q_extend_wk] relates it
    to the [q]-form, and [sb_wk σ φ] is a substitution followed by a Kripke
    weakening.

    The extended context PER is built with [per_ctx_env_extend] from what
    [rel_exp_of_typ_inversion_simple] delivers, so the head obligations follow
    from [per_env_extend_intro'] and [per_head_of]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem SubstitutionCases UniverseCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations Wk_Notations.

(** [cons_glu_sub_pred_helper] postcomposed by a Kripke weakening. Since
    [A[σ][φ]ʷ] and [A[(sb_wk σ φ)]] are the same expression, the head premise
    needs only a [rewrite]. *)
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma cons_glu_sub_pred_pi_helper : forall {Γ Sb Γ' σ ρ A a} {i : nat} {P El Γ'' φ M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ' ⊢s σ ® ρ ∈ Sb ->
    Γ ⊢ A : Type@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ'' ⊢k φ : Γ' ->
    Γ'' ⊢ M : A[σ][φ]ʷ ® c ∈ El ->
    Γ'' ⊢s (sb_wk σ φ),,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros.
  assert (Γ'' ⊢s (sb_wk σ φ) ® ρ ∈ Sb) by (eapply glu_ctx_env_sub_monotone; eassumption).
  eapply cons_glu_sub_pred_helper; try eassumption.
  rewrite <- exp_wk_sub; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_pi_helper : mctt.

(** β at a substitution followed by a Kripke weakening. Both sides of the
    equation needed by the application clause of [pi_glu_exp_pred] are
    instances of [wf_exp_eq_pi_beta] at [(sb_wk σ φ)], once [exp_wk_sub] has
    merged the two steps into one substitution and [exp_sub_q_extend] has put
    both bodies into [q]-form. *)
Lemma exp_eq_fn_sub_wk_beta : forall {Γ Δ Δ' σ φ A B M N} {i : nat},
    Δ ⊢s σ : Γ ->
    Γ ⊢ A : Type@i ->
    Γ ▹ A ⊢ B : Type@i ->
    Γ ▹ A ⊢ M : B ->
    Δ' ⊢k φ : Δ ->
    Δ' ⊢ N : A[(sb_wk σ φ)] ->
    Δ' ⊢ (λ A M)[σ][φ]ʷ $ N ≈ M[(sb_wk σ φ),,N] : B[(sb_wk σ φ),,N].
Proof.
  intros.
  saturate_kripke_escape.
  assert (Δ' ⊢s (sb_wk σ φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
  assert (Δ' ⊢ A[(sb_wk σ φ)] : Type@i) by mauto 3.
  assert (Δ' ▹ A[(sb_wk σ φ)] ⊢s q (sb_wk σ φ) : Γ ▹ A) by mauto 3.
  assert (Δ' ▹ A[(sb_wk σ φ)] ⊢ B[q (sb_wk σ φ)] : Type@i) by mauto 3.
  assert (Δ' ▹ A[(sb_wk σ φ)] ⊢ M[q (sb_wk σ φ)] : B[q (sb_wk σ φ)]) by mauto 3.
  rewrite exp_wk_sub.
  rewrite <- (exp_sub_q_extend M), <- (exp_sub_q_extend B).
  mauto 3.
Qed.

(** [Π] at either tier: the rule keeps both sides in the same universe, so
    the proof is one, at an index [u]. *)
Lemma glu_rel_exp_pi_univ : forall {Γ A B} {u : uidx},
    Γ ⊩ A : univ_tm u ->
    Γ ▹ A ⊩ B : univ_tm u ->
    Γ ⊩ Π A B : univ_tm u.
Proof.
  intros * HA HB.
  assert (⊩ Γ) as [SbΓ] by mauto.
  assert (Γ ⊢ A : univ_tm u) by mauto 3 using glu_rel_exp_to_wf_exp.
  assert (Γ ⊢ A : Type@(ulvl u))
    by (eapply (lift_exp_uidx _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | eassumption ]).
  pose proof (glu_rel_exp_of_univ_inversion ltac:(eassumption) HA) as HAg.
  assert (EG Γ ▹ A ∈ glu_ctx_env ↘ cons_glu_sub_pred (ulvl u) Γ A SbΓ)
    by (eapply glu_ctx_env_cons; [ eassumption | eassumption
                                 | intros Δ σ ρ HΔ; apply glu_rel_typ_with_sub_uidx;
                                   destruct (HAg _ _ _ HΔ); eassumption
                                 | reflexivity ]).
  assert (Γ ▹ A ⊢ B : univ_tm u) by mauto 3 using glu_rel_exp_to_wf_exp.
  pose proof (glu_rel_exp_of_univ_inversion ltac:(eassumption) HB) as HBg.
  assert (Γ ⊨ A : univ_tm u) as [env_relΓ [HΓ HAsimple]]%rel_exp_of_univ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  assert (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
            exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ (ulvl u)) as HAlarge
      by (intros ρ ρ' Hρ; destruct (HAsimple _ _ Hρ) as [a [a' [? [? ?]]]];
          exists a, a'; repeat split; try eassumption;
          eapply (per_univ_cumu_uidx (u := u)); [ apply uidx_le_ulvl | eassumption ]).
  pose proof (per_ctx_env_extend HΓ HAlarge) as HΓA.
  assert (Γ ▹ A ⊨ B : univ_tm u) as [env_relΓA [HΓA' HBsimple]]%rel_exp_of_univ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  handle_per_ctx_env_irrel.
  eapply glu_rel_exp_of_univ; [ eassumption |].
  intros Δ σ ρ HSb.
  assert (Δ ⊢s σ : Γ) by mauto 4.
  destruct (HAg _ _ _ HSb) as [HAσ [a [Hae [[in_rel Hin] HaP]]]].
  assert (Δ ▹ A[σ] ⊢s q σ : Γ ▹ A) by mauto 3.
  assert (Δ ▹ A[σ] ⊢ B[q σ] : univ_tm u)
    by (rewrite <- (exp_sub_univ_tm u (q σ)); mauto 3).
  split; [ cbn; apply wf_pi_univ; assumption |].
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  assert (Dom Πᵈ a ρ B ≈ Πᵈ a ρ B ∈ per_univ u) as [elem_rel Helem].
  {
    eexists.
    eapply per_univ_elem_pi_canonical; [ eassumption |].
    intros c c' Hc.
    assert (Dom ρ ↦ c ≈ ρ ↦ c' ∈ per_env_extend A A env_relΓ)
      by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct (HBsimple _ _ ltac:(eassumption)) as [b [b' [? [? [R ?]]]]].
    exists b, b', R; mauto 3.
  }
  eexists; repeat split; mauto 3.
  intros P El HPEl.
  invert_glu_univ_elem HPEl.
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  (** [(Π A B)[σ]] is [Π A[σ] B[q σ]] by definition, so the first premise of
      [mk_pi_glu_typ_pred] is reflexivity; it determines [IT] and [OT]. *)
  assert (Δ ⊢ Π A[σ] B[q σ] ≈ Π A[σ] B[q σ] : univ_tm u) as HPieq by mauto 3.
  econstructor; [ eassumption | mauto 3 | eassumption | | ]; intros Δ' φ **.
  - (** The domain's gluing predicate is an existential from
        [invert_glu_univ_elem], so take it from the context. *)
    match goal with Hx : glu_univ_elem u ?P ?El a |- _ =>
      assert (Δ ⊢ A[σ] ® P) by exact (HaP P El Hx) end.
    eapply glu_univ_elem_typ_monotone; eassumption.
  - rewrite exp_sub_q_extend_wk.
    (** The entry of the glued context is at the large level [ulvl u], so the
        element of the domain moves up by cumulativity. *)
    match goal with Hx : glu_univ_elem u ?P ?El a, HM : ?El _ _ ?M ?m |- _ =>
      assert (exists P' El', DG a ∈ glu_univ_elem (ulvl u) ↘ P' ↘ El') as [P' [El' Hl]]
        by (eapply (glu_univ_elem_cumu_ge_uidx (i := u)); [ apply uidx_le_ulvl | exact Hx ]);
      assert (Δ' ⊢ M : A[σ][φ]ʷ ® m ∈ El')
        by (eapply (glu_univ_elem_exp_cumu_ge_uidx (i := u) (j := ulvl u));
            [ apply uidx_le_ulvl | exact Hx | exact Hl | exact HM ]) end.
    assert (Δ' ⊢s (sb_wk σ φ),,M ® ρ ↦ m ∈ cons_glu_sub_pred (ulvl u) Γ A SbΓ) as Hcons by mauto 2.
    destruct (HBg _ _ _ Hcons) as [? [b [Hbe [? HbP]]]].
    simplify_evals.
    (** The codomain families are existentials from [invert_glu_univ_elem], so
        take the instance needed here from the family rather than by name. *)
    match goal with
    | H : forall c (equiv_c : in_rel c c) b, ⟦ B ⟧ ρ ↦ c ↘ b -> glu_univ_elem _ _ _ b |- _ =>
        exact (HbP _ _ (H m equiv_m _ ltac:(eassumption)))
    end.
Qed.

Lemma glu_rel_exp_pi : forall {Γ A B} {i : nat},
    Γ ⊩ A : Type@i ->
    Γ ▹ A ⊩ B : Type@i ->
    Γ ⊩ Π A B : Type@i.
Proof. intros; apply (glu_rel_exp_pi_univ (u := ul i)); assumption. Qed.

Lemma glu_rel_exp_pi_small : forall {Γ A B} {n : nat},
    Γ ⊩ A : Typeˢ@n ->
    Γ ▹ A ⊩ B : Typeˢ@n ->
    Γ ⊩ Π A B : Typeˢ@n.
Proof. intros; apply (glu_rel_exp_pi_univ (u := us n)); assumption. Qed.

Hint Resolve glu_rel_exp_pi : mctt.

Lemma glu_rel_exp_of_pi : forall {Γ M A B} {i : nat} {Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊨ Π A B : Type@i ->
    (forall Δ σ ρ,
        Δ ⊢s σ ® ρ ∈ Sb ->
        exists a m,
          ⟦ A ⟧ ρ ↘ a /\
            ⟦ M ⟧ ρ ↘ m /\
            forall (P : glu_typ_pred) (El : glu_exp_pred), DG Πᵈ a ρ B ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : (Π A B)[σ] ® m ∈ El) ->
    Γ ⊩ M : Π A B.
Proof.
  intros * ? HPi%rel_exp_of_typ_inversion_simple Hbody.
  destruct HPi as [env_relΓ [HΓ HPisimple]].
  eexists; split; mauto 3.
  eexists; intros Δ σ ρ HSb.
  edestruct Hbody as [a [m [? [? Hglu]]]]; [eassumption |].
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct (HPisimple _ _ ltac:(eassumption)) as [? [? [? [? ?]]]].
  simplify_evals.
  mauto 4.
Qed.

Lemma glu_rel_exp_fn_helper : forall {Γ M A B} {i : nat},
    Γ ⊩ A : Type@i ->
    Γ ▹ A ⊩ B : Type@i ->
    Γ ▹ A ⊩ M : B ->
    Γ ⊩ λ A M : Π A B.
Proof.
  intros * HA HB HM.
  assert (⊩ Γ) as [SbΓ] by mauto 3.
  assert (Γ ⊢ A : Type@i) by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert (EG Γ ▹ A ∈ glu_ctx_env ↘ SbΓA) by (econstructor; mauto 3; reflexivity).
  assert (Γ ▹ A ⊢ B : Type@i) by mauto 3.
  assert (Γ ▹ A ⊢ M : B) by mauto 3.
  invert_glu_rel_exp HM.
  destruct_conjs.
  assert (Γ ⊨ A : Type@i) as [env_relΓ [HΓ HAsimple]]%rel_exp_of_typ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  pose proof (per_ctx_env_extend HΓ HAsimple) as HΓA.
  assert (Γ ▹ A ⊨ M : B) as [env_relΓA [HΓA' [k HMsimple]]]%rel_exp_under_ctx_simple
      by mauto 3 using completeness_fundamental_exp.
  handle_per_ctx_env_irrel.
  assert (Γ ⊨ Π A B : Type@i) by mauto 3 using completeness_fundamental_exp.
  eapply glu_rel_exp_of_pi; mauto 3.
  intros Δ σ ρ HSb.
  assert (Δ ⊢s σ : Γ) by mauto 4.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  rename m into a.
  do 2 eexists; repeat split; mauto 3.
  intros P El HPEl.
  invert_glu_univ_elem HPEl.
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  apply_relation_equivalence.
  assert (Δ ▹ A[σ] ⊢s q σ : Γ ▹ A) by mauto 3.
  assert (Δ ▹ A[σ] ⊢ B[q σ] : Type@i) by mauto 3.
  assert (Δ ⊢ Π A[σ] B[q σ] ≈ Π A[σ] B[q σ] : Type@i) as HPieq by mauto 3.
  econstructor; [ mauto 3 | | eassumption | mauto 3 | eassumption | | ]; intros.
  - assert (Dom ρ ↦ c ≈ ρ ↦ c' ∈ per_env_extend A A env_relΓ) as HrelΓA
        by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct_rel_mod_eval.
    destruct (HMsimple _ _ HrelΓA) as [? [? [? ?]]].
    destruct_conjs.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - assert (Dom ρ ↦ n ≈ ρ ↦ n ∈ per_env_extend A A env_relΓ) as HrelΓA
        by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct_rel_mod_eval.
    destruct (HMsimple _ _ HrelΓA) as [? [? [? ?]]].
    destruct_conjs.
    handle_per_univ_elem_irrel.
    eexists; split; [mauto 3 |].
    match goal with
    | _: ⟦ B ⟧ ρ ↦ n ↘ ?b' |- _ => rename b' into b
    end.
    assert (DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n) by mauto 3.
    rewrite exp_sub_q_extend_wk.
    assert (Δ0 ⊢ N : A[(sb_wk σ φ)]) by (rewrite <- exp_wk_sub; mauto 2 using glu_univ_elem_trm_escape).
    (** The [pi_glu_exp_pred] app clause states the head in [exp_sub]-reduced
        form, so the [β] equation must be spelled that way for [rewrite]. *)
    assert (Δ0 ⊢ (λ A[σ] M[q σ])[φ]ʷ $ N ≈ M[(sb_wk σ φ),,N] : B[(sb_wk σ φ),,N]) as ->
        by (eapply exp_eq_fn_sub_wk_beta; eassumption).
    assert (Δ0 ⊢s (sb_wk σ φ),,N ® ρ ↦ n ∈ SbΓA) as HSbΓA by (unfold SbΓA; mauto 2).
    (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    handle_functional_glu_univ_elem.
    eassumption.
Qed.

Lemma glu_rel_exp_fn : forall {Γ M A B} {i : nat},
    Γ ⊩ A : Type@i ->
    Γ ▹ A ⊩ M : B ->
    Γ ⊩ λ A M : Π A B.
Proof.
  intros * HA HM.
  assert (exists j, Γ ▹ A ⊩ B : Type@j) as [j] by mauto 3.
  assert (⊩ Γ) by mauto 3.
  assert (i <= max i j) by lia.
  assert (Γ ⊢ Type@i ⊆ Type@(max i j)) by mauto 4.
  assert (Γ ⊩ A : Type@(max i j)) by mauto 3.
  assert (⊩ Γ ▹ A) by mauto 3.
  assert (j <= max i j) by lia.
  assert (Γ ▹ A ⊢ Type@j ⊆ Type@(max i j)) by mauto 4.
  assert (Γ ▹ A ⊩ B : Type@(max i j)) by mauto 3.
  mauto 3 using glu_rel_exp_fn_helper.
Qed.

Hint Resolve glu_rel_exp_fn : mctt.

Lemma glu_rel_exp_app_helper : forall {Γ M N A B} {i : nat},
    Γ ⊩ A : Type@i ->
    Γ ▹ A ⊩ B : Type@i ->
    Γ ⊩ M : Π A B ->
    Γ ⊩ N : A ->
    Γ ⊩ M $ N : B[Id,,N].
Proof.
  intros * HA HB HM HN.
  assert (⊩ Γ) as [SbΓ] by mauto 3.
  assert (Γ ⊩ Π A B : Type@i) by mauto 4.
  assert (Γ ⊢ N : A) by mauto 2.
  invert_glu_rel_exp HN.
  assert (Γ ⊢ A : Type@i) by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert (EG Γ ▹ A ∈ glu_ctx_env ↘ SbΓA) by (econstructor; mauto 3; reflexivity).
  assert (Γ ▹ A ⊢ B : Type@i) by mauto 2.
  invert_glu_rel_exp HB.
  destruct_conjs.
  assert (Γ ⊢ M : Π A B) by mauto 2.
  invert_glu_rel_exp HM.
  (** The type of an application is an instantiated codomain, which the gluing
      model cannot evaluate: [⟦B[Id,,N]⟧ρ] is stuck, and it is not
      [⟦B⟧(ρ ↦ ⟦N⟧ρ)]. [per_univ_of_instance] relates the two, and
      [glu_univ_elem_resp_per_univ] transports the predicate. *)
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  assert (Γ ▹ A ⊨ B : Type@i) by mauto 3 using completeness_fundamental_exp.
  assert (Γ ⊨ N : A) by mauto 3 using completeness_fundamental_exp.
  eexists; split; [eassumption |].
  eexists.
  intros Δ σ ρ HSb.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  inversion_clear_by_head pi_glu_exp_pred.
  match goal with
  | _: ⟦ N ⟧ ρ ↘ ?n' |- _ => rename n' into n
  end.
  assert (Dom a ≈ a ∈ per_univ i) as [] by mauto 3.
  handle_per_univ_elem_irrel.
  assert (Dom n ≈ n ∈ in_rel) as equiv_n by (eapply glu_univ_elem_per_elem; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  simplify_evals.
  match goal with
  | _: ⟦ B ⟧ ρ ↦ n ↘ ?b' |- _ => rename b' into b
  end.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct (per_univ_of_instance HΓ ltac:(eassumption) ltac:(eassumption) _ _ ltac:(eassumption) ltac:(eassumption))
    as [c [b' [Hc [Hb' [Hcc Hcb]]]]].
  functional_eval_rewrite_clear.
  eapply mk_glu_rel_exp_with_sub''; [ exact Hc | mauto 3 | exact Hcc |].
  intros P El HPEl.
  assert (DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n) by mauto 3.
  (** The gluing predicate lives at [b]; move it to [c] along [Hcb]. *)
  assert (Dom b ≈ c ∈ per_univ i) by (symmetry; eassumption).
  assert (DG c ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n)
      by (eapply glu_univ_elem_resp_per_univ; eassumption).
  handle_functional_glu_univ_elem.
  assert (Δ ⊢k wk_id : Δ) by mauto 3.
  assert (Δ ⊢ IT[wk_id]ʷ ® IP) as HIT by mauto 2.
  rewrite exp_wk_id in HIT.
  assert (Δ ⊢ IT : Type@i) by (eapply (glu_univ_elem_univ_lvl (ul i)); revgoals; [ eassumption | eassumption | reflexivity ]).
  assert (Δ ⊢ IT ≈ A[σ] : Type@i) as HAeq
      by (eapply (glu_univ_elem_typ_unique_upto_exp_eq' (i := ul i)); revgoals; eassumption).
  assert (Δ ⊢ N[σ] : IT[wk_id]ʷ ® n ∈ IEl) by (rewrite exp_wk_id, HAeq; eassumption).
  assert (exists mn, $| m & n |↘ mn /\ Δ ⊢ M[σ][wk_id]ʷ $ N[σ] : OT[(ι wk_id),,N[σ]] ® mn ∈ OEl n equiv_n) as [] by mauto 2.
  destruct_conjs.
  functional_eval_rewrite_clear.
  rewrite exp_wk_id in *.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  assert (Δ ⊢ N[σ] : A[σ]) by mauto 2.
  assert (Δ ⊢ N[σ] : A[σ][wk_id]ʷ ® n ∈ IEl) by (rewrite exp_wk_id; eassumption).
  assert (Δ ⊢s σ,,N[σ] ® ρ ↦ n ∈ SbΓA) as Hcons by (unfold SbΓA; mauto 2).
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
  simplify_evals.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  rewrite exp_sub_extend_sub.
  assert (Δ ⊢ OT[(ι wk_id),,N[σ]] ® OP n equiv_n) by (eapply glu_univ_elem_trm_typ; eassumption).
  assert (Δ ⊢ B[σ,,N[σ]] ≈ OT[(ι wk_id),,N[σ]] : Type@i) as ->
      by (eapply (glu_univ_elem_typ_unique_upto_exp_eq' (i := ul _)); revgoals; eassumption).
  eassumption.
Qed.

Lemma glu_rel_exp_app : forall {Γ M N A B} {i : nat},
    Γ ▹ A ⊩ B : Type@i ->
    Γ ⊩ M : Π A B ->
    Γ ⊩ N : A ->
    Γ ⊩ M $ N : B[Id,,N].
Proof.
  intros * HB HM HN.
  assert (⊩ Γ ▹ A) as [SbΓA] by mauto 3.
  match_by_head (glu_ctx_env SbΓA) invert_glu_ctx_env.
  apply_predicate_equivalence.
  rename i0 into j.
  rename TSb into SbΓ.
  assert (Γ ▹ A ⊩ B : Type@i) by mauto 4.
  assert (Γ ⊩ A : Type@j) by (eexists; intuition; eexists; mauto 4).
  assert (⊩ Γ) by mauto 2.
  assert (j <= max i j) by lia.
  assert (Γ ⊢ Type@j ⊆ Type@(max i j)) by mauto 3.
  assert (Γ ⊩ A : Type@(max i j)) by mauto 3.
  assert (⊩ Γ ▹ A) by mauto 2.
  assert (i <= max i j) by lia.
  assert (Γ ▹ A ⊢ Type@i ⊆ Type@(max i j)) by mauto 4.
  assert (Γ ▹ A ⊩ B : Type@(max i j)) by mauto 3.
  mauto 2 using glu_rel_exp_app_helper.
Qed.

Hint Resolve glu_rel_exp_app : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_pi : mctt.
#[export]
Hint Resolve glu_rel_exp_fn : mctt.
#[export]
Hint Resolve glu_rel_exp_app : mctt.
