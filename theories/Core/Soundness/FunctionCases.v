(** * Π-Types in the Gluing Model

    The two pi predicates quantify over Kripke weakenings, so a codomain
    obligation arrives as [OT[^(ι φ),,M]] where it used to arrive as
    [OT[q τ][Id,,M]].  [exp_sub_q_extend_wk] is what bridges the two, replacing
    the deleted [sub_decompose_q_typ], and [sb_wk σ φ] replaces [σ ∘ τ]
    throughout.

    The extended context PER is built canonically with [per_ctx_env_extend], out
    of exactly what [rel_exp_of_typ_inversion_simple] delivers, so the head
    obligations are [per_env_extend_intro'] followed by [per_head_of]. *)

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

(** [cons_glu_sub_pred_helper] postcomposed by a Kripke weakening: [A[σ]⟨φ⟩] and
    [A[^(sb_wk σ φ)]] are the same expression, so the head premise needs only a
    [rewrite] rather than the old instance of [Sub-Comp]. *)
Lemma cons_glu_sub_pred_pi_helper : forall {Γ Sb Γ' σ ρ A a i P El Γ'' φ M c},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ'' ⊢k φ : Γ' }} ->
    {{ Γ'' ⊢ M : A[σ]⟨φ⟩ ® c ∈ El }} ->
    {{ Γ'' ⊢s ^(sb_wk σ φ),,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb }}.
Proof.
  intros.
  assert {{ Γ'' ⊢s ^(sb_wk σ φ) ® ρ ∈ Sb }} by (eapply glu_ctx_env_sub_monotone; eassumption).
  eapply cons_glu_sub_pred_helper; try eassumption.
  rewrite <- exp_wk_sub; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_pi_helper : mctt.

(** β at a substitution followed by a Kripke weakening.  Both sides of the
    equation the [pi_glu_exp_pred] app clause needs are instances of
    [wf_exp_eq_pi_beta] at [^(sb_wk σ φ)] once [exp_wk_sub] has collapsed the two
    steps into one substitution and [exp_sub_q_extend] has put the two bodies
    into [q]-form. *)
Lemma exp_eq_fn_sub_wk_beta : forall {Γ Δ Δ' σ φ A B M N i},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ, A ⊢ M : B }} ->
    {{ Δ' ⊢k φ : Δ }} ->
    {{ Δ' ⊢ N : A[^(sb_wk σ φ)] }} ->
    {{ Δ' ⊢ (λ A M)[σ]⟨φ⟩ N ≈ M[^(sb_wk σ φ),,N] : B[^(sb_wk σ φ),,N] }}.
Proof.
  intros.
  saturate_kripke_escape.
  assert {{ Δ' ⊢s ^(sb_wk σ φ) : Γ }} by (rewrite sb_wk_compose; mauto 3).
  assert {{ Δ' ⊢ A[^(sb_wk σ φ)] : Type@i }} by mauto 3.
  assert {{ Δ', A[^(sb_wk σ φ)] ⊢s q ^(sb_wk σ φ) : Γ, A }} by mauto 3.
  assert {{ Δ', A[^(sb_wk σ φ)] ⊢ B[q ^(sb_wk σ φ)] : Type@i }} by mauto 3.
  assert {{ Δ', A[^(sb_wk σ φ)] ⊢ M[q ^(sb_wk σ φ)] : B[q ^(sb_wk σ φ)] }} by mauto 3.
  rewrite exp_wk_sub.
  rewrite <- (exp_sub_q_extend M), <- (exp_sub_q_extend B).
  mauto 3.
Qed.

Lemma glu_rel_exp_pi : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Π A B : Type@i }}.
Proof.
  intros * HA HB.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  invert_glu_rel_exp HA.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ cons_glu_sub_pred i Γ A SbΓ }} by (econstructor; mauto; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  invert_glu_rel_exp HB.
  assert {{ Γ ⊨ A : Type@i }} as [env_relΓ [HΓ HAsimple]]%rel_exp_of_typ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  pose proof (per_ctx_env_extend HΓ HAsimple) as HΓA.
  assert {{ Γ, A ⊨ B : Type@i }} as [env_relΓA [HΓA' HBsimple]]%rel_exp_of_typ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  handle_per_ctx_env_irrel.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros Δ σ ρ HSb.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  rename m into a.
  (** The domain's own PER, read off its gluing predicate. *)
  assert {{ Dom a ≈ a ∈ per_univ i }} as [in_rel Hin] by mauto 3.
  assert {{ Dom Π a ρ B ≈ Π a ρ B ∈ per_univ i }} as [elem_rel Helem].
  {
    eexists.
    eapply per_univ_elem_pi_canonical; [ eassumption |].
    intros c c' Hc.
    assert {{ Dom ρ ↦ c ≈ ρ ↦ c' ∈ per_env_extend A A env_relΓ }}
      by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct (HBsimple _ _ ltac:(eassumption)) as [b [b' [? [? [R ?]]]]].
    exists b, b', R; mauto 3.
  }
  eexists; repeat split; mauto 3.
  intros P El HPEl.
  invert_glu_univ_elem HPEl.
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  (** [(Π A B)[σ]] *is* [Π A[σ] B[q σ]], so the first premise of
      [mk_pi_glu_typ_pred] is reflexivity and it is what pins [IT] and [OT]. *)
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ Π A[σ] B[q σ] ≈ Π A[σ] B[q σ] : Type@i }} as HPieq by mauto 3.
  econstructor; [ eassumption | mauto 3 | eassumption | | ]; intros Δ' φ **.
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - rewrite exp_sub_q_extend_wk.
    assert {{ Δ' ⊢s ^(sb_wk σ φ),,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ A SbΓ }} as Hcons by mauto 2.
    (on_all_hyp: fun H => destruct (H _ _ _ Hcons)).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    (** The codomain families are the [invert_glu_univ_elem] existentials, so pull
        the obligation's own instance out of the family rather than by name. *)
    match goal with
    | H : forall c (equiv_c : in_rel c c) b, {{ ⟦ B ⟧ ρ ↦ c ↘ b }} -> glu_univ_elem i _ _ b |- _ =>
        pose proof (H m equiv_m _ ltac:(eassumption))
    end.
    handle_functional_glu_univ_elem.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mctt.

Lemma glu_rel_exp_of_pi : forall {Γ M A B i Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊨ Π A B : Type@i }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (P : glu_typ_pred) (El : glu_exp_pred), {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ M[σ] : (Π A B)[σ] ® m ∈ El }}) ->
    {{ Γ ⊩ M : Π A B }}.
Proof.
  intros * ? HPi%rel_exp_of_typ_inversion_simple Hbody.
  destruct HPi as [env_relΓ [HΓ HPisimple]].
  eexists; split; mauto 3.
  eexists; intros Δ σ ρ HSb.
  edestruct Hbody as [a [m [? [? Hglu]]]]; [eassumption |].
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct (HPisimple _ _ ltac:(eassumption)) as [? [? [? [? ?]]]].
  simplify_evals.
  mauto 4.
Qed.

Lemma glu_rel_exp_fn_helper : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Proof.
  intros * HA HB HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 3.
  assert {{ Γ, A ⊢ M : B }} by mauto 3.
  invert_glu_rel_exp HM.
  destruct_conjs.
  assert {{ Γ ⊨ A : Type@i }} as [env_relΓ [HΓ HAsimple]]%rel_exp_of_typ_inversion_simple
      by mauto 3 using completeness_fundamental_exp.
  pose proof (per_ctx_env_extend HΓ HAsimple) as HΓA.
  assert {{ Γ, A ⊨ M : B }} as [env_relΓA [HΓA' [k HMsimple]]]%rel_exp_under_ctx_simple
      by mauto 3 using completeness_fundamental_exp.
  handle_per_ctx_env_irrel.
  assert {{ Γ ⊨ Π A B : Type@i }} by mauto 3 using completeness_fundamental_exp.
  eapply glu_rel_exp_of_pi; mauto 3.
  intros Δ σ ρ HSb.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
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
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ Π A[σ] B[q σ] ≈ Π A[σ] B[q σ] : Type@i }} as HPieq by mauto 3.
  econstructor; [ mauto 3 | | eassumption | mauto 3 | eassumption | | ]; intros.
  - assert {{ Dom ρ ↦ c ≈ ρ ↦ c' ∈ per_env_extend A A env_relΓ }} as HrelΓA
        by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct_rel_mod_eval.
    destruct (HMsimple _ _ HrelΓA) as [? [? [? ?]]].
    destruct_conjs.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n ∈ per_env_extend A A env_relΓ }} as HrelΓA
        by (apply per_env_extend_intro'; [eassumption | eapply per_head_of; eassumption]).
    destruct_rel_mod_eval.
    destruct (HMsimple _ _ HrelΓA) as [? [? [? ?]]].
    destruct_conjs.
    handle_per_univ_elem_irrel.
    eexists; split; [mauto 3 |].
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?b' }} |- _ => rename b' into b
    end.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
    rewrite exp_sub_q_extend_wk.
    assert {{ Δ0 ⊢ N : A[^(sb_wk σ φ)] }} by (rewrite <- exp_wk_sub; mauto 2 using glu_univ_elem_trm_escape).
    (** The [pi_glu_exp_pred] app clause states the head in [exp_sub]-reduced
        form, so the [β] equation must be spelled that way for [rewrite]. *)
    assert {{ Δ0 ⊢ (λ A[σ] M[q σ])⟨φ⟩ N ≈ M[^(sb_wk σ φ),,N] : B[^(sb_wk σ φ),,N] }} as ->
        by (eapply exp_eq_fn_sub_wk_beta; eassumption).
    assert {{ Δ0 ⊢s ^(sb_wk σ φ),,N ® ρ ↦ n ∈ SbΓA }} as HSbΓA by (unfold SbΓA; mauto 2).
    (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    handle_functional_glu_univ_elem.
    eassumption.
Qed.

Lemma glu_rel_exp_fn : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Proof.
  intros * HA HM.
  assert (exists j, {{ Γ, A ⊩ B : Type@j }}) as [j] by mauto 3.
  assert {{ ⊩ Γ }} by mauto 3.
  assert (i <= max i j) by lia.
  assert {{ Γ ⊢ Type@i ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ ⊩ A : Type@(max i j) }} by mauto 3.
  assert {{ ⊩ Γ, A }} by mauto 3.
  assert (j <= max i j) by lia.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ, A ⊩ B : Type@(max i j) }} by mauto 3.
  mauto 3 using glu_rel_exp_fn_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_fn : mctt.

Lemma glu_rel_exp_app_helper : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Proof.
  intros * HA HB HM HN.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊩ Π A B : Type@i }} by mauto 4.
  assert {{ Γ ⊢ N : A }} by mauto 2.
  invert_glu_rel_exp HN.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 2.
  invert_glu_rel_exp HB.
  destruct_conjs.
  assert {{ Γ ⊢ M : Π A B }} by mauto 2.
  invert_glu_rel_exp HM.
  (** The type of an application is an *instantiated* codomain, which the gluing
      model cannot evaluate: [⟦B[Id,,N]⟧ρ] is stuck, and it is not
      [⟦B⟧(ρ ↦ ⟦N⟧ρ)] either.  [per_univ_of_instance] relates the two and
      [glu_univ_elem_resp_per_univ] transports the predicate. *)
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }}) as [env_relΓ HΓ] by mauto 3.
  assert {{ Γ, A ⊨ B : Type@i }} by mauto 3 using completeness_fundamental_exp.
  assert {{ Γ ⊨ N : A }} by mauto 3 using completeness_fundamental_exp.
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
  | _: {{ ⟦ N ⟧ ρ ↘ ^?n' }} |- _ => rename n' into n
  end.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [] by mauto 3.
  handle_per_univ_elem_irrel.
  assert {{ Dom n ≈ n ∈ in_rel }} as equiv_n by (eapply glu_univ_elem_per_elem; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  simplify_evals.
  match goal with
  | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?b' }} |- _ => rename b' into b
  end.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct (per_univ_of_instance HΓ ltac:(eassumption) ltac:(eassumption) _ _ ltac:(eassumption) ltac:(eassumption))
    as [c [b' [Hc [Hb' [Hcc Hcb]]]]].
  functional_eval_rewrite_clear.
  eapply mk_glu_rel_exp_with_sub''; [ exact Hc | mauto 3 | exact Hcc |].
  intros P El HPEl.
  assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
  (** The gluing predicate lives at [b]; move it to [c] along [Hcb]. *)
  assert {{ Dom b ≈ c ∈ per_univ i }} by (symmetry; eassumption).
  assert {{ DG c ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }}
      by (eapply glu_univ_elem_resp_per_univ; eassumption).
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢k wk_id : Δ }} by mauto 3.
  assert {{ Δ ⊢ IT⟨wk_id⟩ ® IP }} as HIT by mauto 2.
  rewrite exp_wk_id in HIT.
  assert {{ Δ ⊢ IT : Type@i }} by (eapply glu_univ_elem_univ_lvl; revgoals; eassumption).
  assert {{ Δ ⊢ IT ≈ A[σ] : Type@i }} as HAeq by (eapply glu_univ_elem_typ_unique_upto_exp_eq'; revgoals; eassumption).
  assert {{ Δ ⊢ N[σ] : IT⟨wk_id⟩ ® n ∈ IEl }} by (rewrite exp_wk_id, HAeq; eassumption).
  assert (exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ]⟨wk_id⟩ N[σ] : OT[^(ι wk_id),,N[σ]] ® mn ∈ OEl n equiv_n }}) as [] by mauto 2.
  destruct_conjs.
  functional_eval_rewrite_clear.
  rewrite exp_wk_id in *.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Δ ⊢ N[σ] : A[σ]⟨wk_id⟩ ® n ∈ IEl }} by (rewrite exp_wk_id; eassumption).
  assert {{ Δ ⊢s σ,,N[σ] ® ρ ↦ n ∈ SbΓA }} as Hcons by (unfold SbΓA; mauto 2).
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
  simplify_evals.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  rewrite exp_sub_extend_sub.
  assert {{ Δ ⊢ OT[^(ι wk_id),,N[σ]] ® OP n equiv_n }} by (eapply glu_univ_elem_trm_typ; eassumption).
  assert {{ Δ ⊢ B[σ,,N[σ]] ≈ OT[^(ι wk_id),,N[σ]] : Type@i }} as ->
      by (eapply glu_univ_elem_typ_unique_upto_exp_eq'; revgoals; eassumption).
  eassumption.
Qed.

Lemma glu_rel_exp_app : forall {Γ M N A B i},
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Proof.
  intros * HB HM HN.
  assert {{ ⊩ Γ, A }} as [SbΓA] by mauto 3.
  match_by_head (glu_ctx_env SbΓA) invert_glu_ctx_env.
  apply_predicate_equivalence.
  rename i0 into j.
  rename TSb into SbΓ.
  assert {{ Γ, A ⊩ B : Type@i }} by mauto 4.
  assert {{ Γ ⊩ A : Type@j }} by (eexists; intuition; eexists; mauto 4).
  assert {{ ⊩ Γ }} by mauto 2.
  assert (j <= max i j) by lia.
  assert {{ Γ ⊢ Type@j ⊆ Type@(max i j) }} by mauto 3.
  assert {{ Γ ⊩ A : Type@(max i j) }} by mauto 3.
  assert {{ ⊩ Γ, A }} by mauto 2.
  assert (i <= max i j) by lia.
  assert {{ Γ, A ⊢ Type@i ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ, A ⊩ B : Type@(max i j) }} by mauto 3.
  mauto 2 using glu_rel_exp_app_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_app : mctt.
