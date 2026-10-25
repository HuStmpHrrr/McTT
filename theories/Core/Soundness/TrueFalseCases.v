(** * The Unit and Empty Types in the Gluing Model

    [⊤], [⋆] and [⊥] are closed, so their cases are those of [ℕ] and [zero].
    The eliminator of [⊥] only meets neutrals, since the gluing of [⊥] is that
    of the neutrals of [ℕ]; its case is the neutral case of the
    [ℕ]-eliminator's, without the branches. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import TrueFalseCases UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
Import Domain_Notations Wk_Notations.

Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Kripke-weakening the scrutinee's type collapses its two substitution steps
    into one with [sb_wk]. *)
Fact motive_sub_wk : forall A σ M φ,
    A[σ,,M][φ]ʷ = A[q (sb_wk σ φ)][Id,,M[φ]ʷ].
Proof.
  intros; rewrite exp_sub_q_extend; apply exp_wk_sub_extend_head.
Qed.

(** The lifting of a related substitution under a binder of type [A]. *)
Lemma cons_glu_sub_pred_q_helper : forall {Γ SbΓ Δ σ ρ} {i : nat} {A a},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    Γ ⊩ A : Typeω@i ->
    ⟦ A ⟧ ρ ↘ a ->
    Δ ▹ A[σ] ⊢ˢ q σ ® ρ ↦ ⇑! a (length Δ) ∈ cons_glu_sub_pred i Γ A SbΓ.
Proof.
  intros * ? ? HA ?.
  assert (Γ ⊢ A : Typeω@i) by mauto 2.
  invert_glu_rel_exp HA.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  destruct_glu_records.
  destruct_conjs.
  assert (Δ ⊢ˢ σ : Γ) by mauto 2.
  assert (⊢ Δ ▹ A[σ]) by mauto 3.
  assert (Δ ▹ A[σ] ⊢ᵏ ↑ : Δ) by mauto 3.
  unfold sb_q; eapply cons_glu_sub_pred_helper_gen; mauto 2.
  - eapply glu_ctx_env_sub_monotone; eassumption.
  - cbn [sentry_exp]; rewrite <- exp_wk_sub.
    eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mctt.

Lemma glu_rel_exp_True_univ : forall {Γ} {u : uidx},
    ⊩ Γ ->
    Γ ⊩ ⊤ : ulvl_tm u.
Proof.
  intros * [Sb].
  assert (⊢ Γ) by mauto.
  eapply glu_rel_exp_of_univ; mauto 3.
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  split; [ simplify_subs; apply wf_True_univ; assumption |].
  eexists; repeat split; mauto 3; [| closed_typ_readback ].
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold True_glu_typ_pred.
  simplify_subs; apply wf_exp_eq_True_cong_large; assumption.
Qed.

Lemma glu_rel_exp_True : forall {Γ} {i : nat},
    ⊩ Γ ->
    Γ ⊩ ⊤ : Typeω@i.
Proof. intros; apply (glu_rel_exp_True_univ (u := ul i)); assumption. Qed.

Lemma glu_rel_exp_True_small : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ ⊤ : Type@0.
Proof. intros; apply (glu_rel_exp_True_univ (u := us oz)); assumption. Qed.

Hint Resolve glu_rel_exp_True : mctt.

Lemma glu_rel_exp_False_univ : forall {Γ} {u : uidx},
    ⊩ Γ ->
    Γ ⊩ ⊥ : ulvl_tm u.
Proof.
  intros * [Sb].
  assert (⊢ Γ) by mauto.
  eapply glu_rel_exp_of_univ; mauto 3.
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  split; [ simplify_subs; apply wf_False_univ; assumption |].
  eexists; repeat split; mauto 3; [| closed_typ_readback ].
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold False_glu_typ_pred.
  simplify_subs; apply wf_exp_eq_False_cong_large; assumption.
Qed.

Lemma glu_rel_exp_False : forall {Γ} {i : nat},
    ⊩ Γ ->
    Γ ⊩ ⊥ : Typeω@i.
Proof. intros; apply (glu_rel_exp_False_univ (u := ul i)); assumption. Qed.

Lemma glu_rel_exp_False_small : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ ⊥ : Type@0.
Proof. intros; apply (glu_rel_exp_False_univ (u := us oz)); assumption. Qed.

Hint Resolve glu_rel_exp_False : mctt.

Lemma glu_rel_exp_true : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ ⋆ : ⊤.
Proof.
  intros * [Sb].
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := 0); [ mauto 3 |].
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  econstructor; mauto 3.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - simpl; split; mauto 3.
Qed.

Hint Resolve glu_rel_exp_true : mctt.

(** ** Extension by [⊥] *)
Lemma cons_glu_sub_pred_False_helper : forall {Γ SbΓ Δ σ ρ} {i : nat} {M m},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    False_glu_elem Δ M m ->
    Δ ⊢ˢ σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ ⊥ SbΓ.
Proof.
  intros * ? HM ?.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  assert (DG ⊥ᵈ ∈ glu_univ_elem i ↘ False_glu_typ_pred (ulvl_tm i) ↘ False_glu_exp_pred (ulvl_tm i))
    by (glu_univ_elem_econstructor; reflexivity).
  eapply cons_glu_sub_pred_helper; mauto 3.
  econstructor; [unfold False_glu_typ_pred |]; simplify_subs; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_False_helper : mctt.

(** [⊥[σ]] is [⊥], so this is [cons_glu_sub_pred_q_helper] up to
    conversion. *)
Lemma cons_glu_sub_pred_q_False_helper : forall {Γ SbΓ Δ σ ρ} {i : nat},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢ˢ σ ® ρ ∈ SbΓ ->
    Δ ▹ ⊥ ⊢ˢ q σ ® ρ ↦ ⇑! ⊥ᵈ (length Δ) ∈ cons_glu_sub_pred i Γ ⊥ SbΓ.
Proof.
  intros.
  assert (⊩ Γ) by (eexists; eassumption).
  assert (Γ ⊩ ⊥ : Typeω@i) by mauto 3.
  assert (⟦ ⊥ ⟧ ρ ↘ ⊥ᵈ) by mauto 3.
  exact (@cons_glu_sub_pred_q_helper Γ SbΓ Δ σ ρ i ⊥ ⊥ᵈ
           ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_False_helper : mctt.

(** ** The Eliminator

    The scrutinee is glued to a neutral, so the elimination is a neutral,
    glued by [realize_glu_elem_bot]; its readback is related by
    [per_bot_exfalso_diag], and the motive is read back by
    [realize_glu_typ_top] at a fresh variable. *)
Lemma glu_rel_exp_exfalso : forall {Γ} {i : nat} {A M},
    Γ ▹ ⊥ ⊩ A : Typeω@i ->
    Γ ⊩ M : ⊥ ->
    Γ ⊩ efq M return A : A[Id,,M].
Proof.
  intros * HA HM.
  assert (⊩ Γ) as [SbΓ] by mauto 2.
  assert (Γ ⊩ ⊥ : Typeω@i) as HF by mauto 3.
  assert (Γ ⊩ ⊥ : Typeω@0) by mauto 3.
  pose (SbΓF := cons_glu_sub_pred i Γ ⊥ SbΓ).
  assert (EG Γ ▹ ⊥ ∈ glu_ctx_env ↘ SbΓF)
    by (invert_glu_rel_exp HF; eapply glu_ctx_env_cons with (i := i); mauto 3; try reflexivity).
  assert (Γ ▹ ⊥ ⊩ Typeω@i : Typeω@(S i)) by mauto 3.
  assert (Γ ⊢ M : ⊥) by mauto 2.
  assert (Γ ▹ ⊥ ⊢ A : Typeω@i) by mauto 2.
  pose proof HA as HAglu.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  eapply mk_glu_rel_exp with (glu_rel_exp_lvl := i); [eassumption |].
  intros.
  assert (Δ ⊢ˢ σ : Γ) by mauto 3.
  saturate_sub.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  clear_dups.
  inversion_clear_by_head False_glu_exp_pred.
  match goal with H : False_glu_elem _ _ _ |- _ => rename H into HMglu end.
  inversion HMglu; subst.
  assert (Δ ⊢ˢ σ,,M[σ] ® ρ ↦ ⇑ a m0 ∈ SbΓF) by (unfold SbΓF; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  destruct_glu_records.
  destruct_conjs.
  clear_dups.
  match goal with
  | _: (⟦ A ⟧ ρ ↦ ⇑ a m0 ↘ ?a'), _: DG ?a' ∈ glu_univ_elem ?idx ↘ ?P' ↘ ?El' |- _ =>
      rename a' into am; rename P' into P; rename El' into El
  end.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  assert (Γ ▹ ⊥ ⊨ A : Typeω@i) by mauto 3 using completeness_fundamental_exp.
  assert (Γ ⊨ M : ⊥) by mauto 3 using completeness_fundamental_exp.
  assert (Δ ⊢ efq M[σ] return A[q σ] : A[σ,,M[σ]] ® ⇑ am (efqᵈ m0 under ρ return A) ∈ El)
    as Hefq.
  { eapply realize_glu_elem_bot; [ eassumption |].
    econstructor; [| eassumption | eassumption | |].
    - rewrite <- (exp_sub_q_extend A σ M[σ]).
      assert (Δ ▹ ⊥ ⊢ˢ q σ : Γ ▹ ⊥) by mauto 3.
      assert (Δ ▹ ⊥ ⊢ A[q σ] : Typeω@i) by mauto 3.
      assert (Δ ⊢ M[σ] : ⊥) by mauto 3.
      mauto 3.
    - eapply per_bot_exfalso_diag; eassumption.
    - intros Δ' φ W ? HW.
      saturate_kripke_escape.
      saturate_sub.
      assert (Δ' ⊢ˢ (sb_wk σ φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
      assert (Δ' ⊢ˢ (sb_wk σ φ) ® ρ ∈ SbΓ) by (eapply glu_ctx_env_sub_monotone; eassumption).
      assert (Δ' ▹ ⊥ ⊢ˢ q (sb_wk σ φ) ® ρ ↦ ⇑! ⊥ᵈ (length Δ') ∈ SbΓF) by (unfold SbΓF; mauto 3).
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      apply_predicate_equivalence.
      destruct_glu_records.
      destruct_conjs.
      handle_functional_glu_univ_elem.
      match_by_head read_ne ltac:(fun H => directed inversion_clear H).
      simplify_evals.
      handle_functional_glu_univ_elem.
      rewrite motive_sub_wk, exp_wk_sub_q.
      eapply wf_exp_eq_exfalso_cong'; fold ne_to_exp nf_to_exp.
      + assert (Δ' ▹ ⊥ ⊢ A[q (sb_wk σ φ)] ® glu_typ_top i m) as [? ? Hrbt]
          by (eapply realize_glu_typ_top; eassumption).
        assert (Δ' ▹ ⊥ ⊢ᵏ wk_id : Δ' ▹ ⊥) by mauto 3.
        assert (Δ' ▹ ⊥ ⊢ A[q (sb_wk σ φ)][wk_id]ʷ ≈ B' : Typeω@i) as Hat by (eapply Hrbt; eassumption).
        rewrite exp_wk_id in Hat; eassumption.
      + mauto 3. }
  destruct (per_univ_of_instance HΓ ltac:(eassumption) ltac:(eassumption) ρ (⇑ a m0)
              ltac:(eassumption) ltac:(eassumption)) as [? [? [? [? [? [? ?]]]]]].
  functional_eval_rewrite_clear.
  saturate_glu_by_per.
  handle_functional_glu_univ_elem.
  econstructor; mauto 3.
  rewrite exp_sub_extend_sub.
  simplify_subs.
  eassumption.
Qed.

Hint Resolve glu_rel_exp_exfalso : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_True glu_rel_exp_False glu_rel_exp_true glu_rel_exp_exfalso : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_True :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊤ : Type@0 ).
Proof. glu_intro; apply glu_rel_exp_True_small; assumption. Qed.

Lemma glu_true :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⋆ : ⊤ ).
Proof. glu_intro; apply glu_rel_exp_true; assumption. Qed.

Lemma glu_False :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊥ : Type@0 ).
Proof. glu_intro; apply glu_rel_exp_False_small; assumption. Qed.

Lemma glu_exfalso :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ efq M return A : A[Id,,M] ).
Proof. glu_intro; eapply glu_rel_exp_exfalso; eassumption. Qed.

Lemma glu_exp_eq_True_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_true_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_False_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_exfalso_cong :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_true_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : ⊤ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
