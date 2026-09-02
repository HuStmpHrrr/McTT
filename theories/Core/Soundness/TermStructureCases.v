(** * Variables and Presuppositions

    The old [glu_rel_exp_sub] is gone with the [⊩s] judgment: there is no
    substitution rule, because [⟦M[σ]⟧(ρ) = ⟦M⟧(⟦σ⟧ρ)] fails as an
    equation and the gluing predicates are indexed by values, not by relations. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.
Import Wk_Notations.

Lemma presup_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    ⊩ Γ /\ (exists i, Γ ⊩ A : Type@i).
Proof.
  intros * [? [? []]].
  split; [eexists; eassumption |].
  do 2 eexists; intuition.
  eexists; mauto 4.
Qed.

Lemma presup_ctx_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    ⊩ Γ.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mctt.

Lemma presup_typ_glu_rel_exp : forall {Γ M A},
    Γ ⊩ M : A ->
    exists i, Γ ⊩ A : Type@i.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mctt.

(** Syntactically the variable case is now cheap — [#(S n)[σ]] *is*
    [#n[Wk⨟σ]] and [ρ (S n)] *is* [ρ↯ n], so the old chain of [wf_exp_eq]
    rewrites collapses to one [exp_sub_shift].  What is not cheap is the type
    *value*: [cons_glu_sub_pred] supplies [⟦A⟧(ρ↯)] while the goal reads
    [⟦A⟨↑⟩⟧(ρ)], and those are not equal.
    [completeness_fundamental_typ_shift] relates them, and
    [glu_univ_elem_resp_per_univ] moves [P] and [El] across. *)
Lemma glu_rel_exp_vlookup : forall {Γ x A},
    ⊩ Γ ->
    Γ ∋ #x : A ->
    Γ ⊩ #x : A.
Proof.
  intros * [Sb] Hx. gen Sb.
  induction Hx; intros;
    match_by_head1 glu_ctx_env ltac:(fun H => invert_glu_ctx_env H).
  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists i.
    intros Δ σ ρ HSb.
    assert (glu_ctx_env (cons_glu_sub_pred i Γ A TSb) (Γ ▹ A))
      by (econstructor; try reflexivity; eassumption).
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (exists R, EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R) as [env_relΓA] by mauto 3.
    assert (Dom ρ ≈ ρ ∈ env_relΓA) by (eapply glu_ctx_env_per_env; eassumption).
    destruct (completeness_fundamental_typ_shift (B := A) (A := A)
                ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
      as [a' [a'' [? [? ?]]]].
    destruct_by_head cons_glu_sub_pred.
    functional_eval_rewrite_clear.
    assert (glu_univ_elem i P El a')
      by (eapply glu_univ_elem_resp_per_univ; [symmetry |]; eassumption).
    econstructor; mauto 3.
  - assert (Γ ⊩ #n : A) as Hn by mauto.
    assert (exists i, Γ ⊢ A : Type@i) as [j] by (gen_presups; mauto 3).
    invert_glu_rel_exp Hn.
    rename x into k.
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists (max j k).
    intros Δ σ ρ HSb.
    assert (glu_ctx_env (cons_glu_sub_pred i Γ B TSb) (Γ ▹ B))
      by (econstructor; try reflexivity; eassumption).
    assert (⊢ Γ ▹ B) by mauto 3.
    assert (exists R, EF Γ ▹ B ≈ Γ ▹ B ∈ per_ctx_env ↘ R) as [env_relΓB] by mauto 3.
    assert (Dom ρ ≈ ρ ∈ env_relΓB) by (eapply glu_ctx_env_per_env; eassumption).
    assert (Γ ⊢ A : Type@(max j k)) by mauto 3 using lift_exp_max_left.
    destruct (completeness_fundamental_typ_shift (B := B) (A := A) (i := max j k)
                ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
      as [a' [a'' [? [? ?]]]].
    destruct_by_head cons_glu_sub_pred.
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    assert (exists P' El', glu_univ_elem (max j k) P' El' a'') as [P' [El' HP']]
      by (eapply glu_univ_elem_cumu_max_right; eassumption).
    assert (glu_univ_elem (max j k) P' El' a')
      by (eapply glu_univ_elem_resp_per_univ; [symmetry |]; eassumption).
    econstructor; try eassumption.
    1: mauto 3.
    rewrite exp_sub_shift.
    eapply glu_univ_elem_exp_cumu_max_right; [| exact HP' |]; eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mctt.
