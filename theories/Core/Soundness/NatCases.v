(** * ℕ and its Eliminator in the Gluing Model

    Substituting a [natrec] is definitional here, so every congruence step that
    used to relate [(rec M …)[σ]] to [rec M[σ] …] is reflexivity, and [Δ ▹ ℕ[σ]]
    *is* [Δ ▹ ℕ].  What the port has to pay for instead is that [⟦A[Id,,zero]⟧ρ]
    is stuck: the two instantiated motives of the eliminator are not
    values of [A] at an extended environment, only related to them.
    [per_univ_zero_instance] and [per_univ_nat_step_instance] supply those two
    relations, and [saturate_glu_by_per] moves the gluing predicates along
    them. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem NatCases SubstitutionCases UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations Wk_Notations.

Lemma glu_rel_exp_nat : forall {Γ i},
    ⊩ Γ ->
    Γ ⊩ ℕ : Type@i.
Proof.
  intros * [Sb].
  assert (⊢ Γ) by mauto.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold nat_glu_typ_pred.
  simplify_subs; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mctt.

Lemma glu_rel_exp_clean_inversion2'' : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : ℕ ->
    glu_rel_exp_clean_inversion2_result 0 Sb M ℕ.
Proof.
  intros * ? HM.
  assert (Γ ⊩ ℕ : Type@0) by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

Ltac invert_glu_rel_exp H ::=
  (unshelve eapply (glu_rel_exp_clean_inversion2'' _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2' _) in H; shelve_unifiable; [eassumption |];
     unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
     unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Lemma glu_rel_exp_of_nat : forall {Γ Sb M},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    (forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ Sb -> exists m, ⟦ M ⟧ ρ ↘ m /\ glu_nat Δ M[σ] m) ->
    Γ ⊩ M : ℕ.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  exists 0.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  edestruct Hbody as [? []]; mauto 3.
  econstructor; mauto 3.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - simpl; split; mauto 3.
Qed.

Lemma glu_rel_exp_zero : forall {Γ},
    ⊩ Γ ->
    Γ ⊩ zero : ℕ.
Proof.
  intros * [Sb].
  eapply glu_rel_exp_of_nat; mauto 3.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  eexists; split; [mauto 3 |].
  econstructor; simplify_subs; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mctt.

Lemma glu_rel_exp_succ : forall {Γ M},
    Γ ⊩ M : ℕ ->
    Γ ⊩ succ M : ℕ.
Proof.
  intros * HM.
  assert (⊩ Γ) as [SbΓ] by mauto 3.
  assert (Γ ⊢ M : ℕ) by mauto 3.
  invert_glu_rel_exp HM.
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  inversion_clear_by_head nat_glu_exp_pred.
  eexists; split; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mctt.

(** ** Instantiated Motives

    [eval_exp] has no clause for [exp_sub], so [⟦A[Id,,zero]⟧ρ] is a stuck
    evaluation rather than [⟦A⟧(ρ ↦ zero)].  The two are nonetheless related in
    [per_univ i], which is all a gluing predicate needs to move between them. *)
Lemma per_univ_zero_instance : forall {i Γ SbΓ A Δ σ ρ az am},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊢ A : Type@i ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    ⟦ A[Id,,zero] ⟧ ρ ↘ az ->
    ⟦ A ⟧ ρ ↦ zeroᵈ ↘ am ->
    Dom az ≈ am ∈ per_univ i.
Proof.
  intros.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  assert (⊢ Γ) by mauto 2.
  assert (Γ ▹ ℕ ⊨ A : Type@i) by mauto 3 using completeness_fundamental_exp.
  assert (Γ ⊨ zero : ℕ) by mauto 3 using completeness_fundamental_exp.
  destruct (per_univ_of_instance HΓ ltac:(eassumption) ltac:(eassumption) ρ zeroᵈ
              ltac:(eassumption) ltac:(mauto 3)) as [? [? [? [? [? ?]]]]].
  functional_eval_rewrite_clear.
  eassumption.
Qed.

(** The successor branch's motive, at the environment its own gluing context
    supplies.  [rel_typ_of_nat_step_gen] delivers the four-value pattern whose
    outer two values are exactly the stuck value and the one the eliminator
    wants; [pairwise] reads off the pair. *)
Lemma per_univ_nat_step_instance : forall {i Γ SbΓ A Sb Δ σ ρ p am},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊢ A : Type@i ->
    EG Γ ▹ ℕ ▹ A ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    ⟦ A[Wk ⨟ Wk,,succ #1] ⟧ ρ ↘ p ->
    ⟦ A ⟧ (drop_env (drop_env ρ)) ↦ succᵈ (drop_env ρ 0) ↘ am ->
    Dom p ≈ am ∈ per_univ i.
Proof.
  intros.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  assert (⊢ Γ) by mauto 2.
  assert (Γ ▹ ℕ ⊨ A : Type@i) as HAsem by mauto 3 using completeness_fundamental_exp.
  assert (Γ ⊨ ℕ : Type@0) by mauto 3 using completeness_fundamental_exp.
  assert (Dom ρ ≈ ρ ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
      by (eapply glu_ctx_env_per_env;
          [ eassumption
          | eapply per_ctx_env_of_typ; [ eapply per_ctx_env_of_typ |]; eassumption
          | eassumption ]).
  destruct (rel_typ_of_nat_step_gen HΓ HAsem ρ ρ ltac:(eassumption))
    as [? [? [? [? [? [? [? [? ?]]]]]]]].
  functional_eval_rewrite_clear.
  pairwise.
Qed.

Lemma cons_glu_sub_pred_nat_helper : forall {Γ SbΓ Δ σ ρ i M m},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    glu_nat Δ M m ->
    Δ ⊢s σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ ℕ SbΓ.
Proof.
  intros * ? HM ?.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  assert (DG ℕᵈ ∈ glu_univ_elem i ↘ nat_glu_typ_pred i ↘ nat_glu_exp_pred i) by (glu_univ_elem_econstructor; reflexivity).
  eapply cons_glu_sub_pred_helper; mauto 3.
  econstructor; [unfold nat_glu_typ_pred |]; simplify_subs; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_nat_helper : mctt.

Lemma glu_rel_exp_natrec_zero_helper : forall {i Γ SbΓ A MZ MS Δ M σ ρ am P El},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊢ A : Type@i ->
    Γ ⊩ A[Id,,zero] : Type@i ->
    Γ ⊩ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1] ->
    Δ ⊢ M ≈ zero : ℕ ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    ⟦ A ⟧ ρ ↦ zeroᵈ ↘ am ->
    DG am ∈ glu_univ_elem i ↘ P ↘ El ->
    exists r,
      ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
        Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El.
Proof.
  intros * HSbΓ ? ? HMZ **.
  assert (Γ ⊢ MZ : A[Id,,zero]) by mauto 3.
  invert_glu_rel_exp HMZ.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m into mz.
  eexists mz; split; [mauto 3 |].
  destruct (per_univ_zero_instance HSbΓ ltac:(eassumption) ltac:(eassumption)
              ltac:(eassumption) ltac:(eassumption)) as [? ?].
  saturate_glu_by_per.
  handle_functional_glu_univ_elem.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  saturate_sub.
  assert (Δ ▹ ℕ ⊢s q σ : Γ ▹ ℕ) by mauto 3.
  assert (Δ ▹ ℕ ⊢ A[q σ] : Type@i) by mauto 3.
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢s q (q σ) : Γ ▹ ℕ ▹ A) by mauto 3.
  assert (Δ ⊢ MZ[σ] : A[q σ][Id,,zero])
      by (rewrite exp_sub_q_extend, <- exp_sub_extend_sub_zero; mauto 3).
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk ⨟ Wk,,succ #1])
      by (rewrite <- exp_sub_sub_natrec; mauto 3).
  assert (Δ ⊢ A[σ,,M] ≈ A[σ,,zero] : Type@i) as ->
      by (eapply exp_eq_sub_eq_head with (A := ℕ); mauto 3).
  assert (Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MZ[σ] : A[σ,,zero]) as ->;
    [| rewrite <- exp_sub_extend_sub_zero; eassumption].
  rewrite <- (exp_sub_q_extend A σ zero).
  transitivity rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end.
  - eapply wf_exp_eq_conv';
      [ eapply wf_exp_eq_natrec_cong'; mauto 3
      | eapply exp_eq_sub_eq_single; mauto 3 ].
  - eapply wf_exp_eq_nat_beta_zero'; mauto 3.
Qed.

Lemma glu_rel_exp_natrec_succ_helper : forall {i Γ SbΓ A MZ MS Δ M M' m' σ ρ am P El},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊩ A : Type@i ->
    Γ ⊢ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@i ->
    Γ ▹ ℕ ▹ A ⊩ MS : A[Wk ⨟ Wk,,succ #1] ->
    Δ ⊢ M ≈ succ M' : ℕ ->
    glu_nat Δ M' m' ->
    (forall σ ρ am P El,
        Δ ⊢s σ ® ρ ∈ SbΓ ->
        ⟦ A ⟧ ρ ↦ m' ↘ am ->
        DG am ∈ glu_univ_elem i ↘ P ↘ El ->
        exists r,
          ⟦rec m' return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
            Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® r ∈ El) ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    ⟦ A ⟧ ρ ↦ succᵈ m' ↘ am ->
    DG am ∈ glu_univ_elem i ↘ P ↘ El ->
    exists r,
      ⟦rec succᵈ m' return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
        Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El.
Proof.
  intros * HSbΓ HA ? ? HMS **.
  assert (⊩ Γ) by (eexists; eassumption).
  assert (Γ ⊩ ℕ : Type@i) as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred i Γ ℕ SbΓ).
  assert (EG Γ ▹ ℕ ∈ glu_ctx_env ↘ SbΓℕ) by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred i (Γ ▹ ℕ) A SbΓℕ).
  assert (EG Γ ▹ ℕ ▹ A ∈ glu_ctx_env ↘ SbΓℕA) as HgΓℕA by (econstructor; mauto 3; reflexivity).
  assert (Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1]) by mauto 2.
  invert_glu_rel_exp HMS.
  assert (Δ ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ) by (unfold SbΓℕ; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  match goal with
  | _: (⟦ A ⟧ ρ ↦ m' ↘ ?m), _: (DG ?m ∈ glu_univ_elem i ↘ ?P ↘ ?El) |- _ =>
      rename m into am';
      rename P into P';
      rename El into El'
  end.
  assert (⊢ Δ) by mauto 2.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  assert (Δ ⊢ M' : ℕ) by mauto 3.
  assert (Δ ▹ ℕ ⊢s q σ : Γ ▹ ℕ) by mauto 3.
  assert (Δ ▹ ℕ ⊢ A[q σ] : Type@i) by mauto 3.
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢s q (q σ) : Γ ▹ ℕ ▹ A) by mauto 3.
  assert (Δ ⊢ MZ[σ] : A[q σ][Id,,zero])
      by (rewrite exp_sub_q_extend, <- exp_sub_extend_sub_zero; mauto 3).
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk ⨟ Wk,,succ #1])
      by (rewrite <- exp_sub_sub_natrec; mauto 3).
  pose (R := rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end).
  assert (exists r, ⟦rec m' return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\ Δ ⊢ R : A[σ,,M'] ® r ∈ El')
      as [r' []] by mauto 3.
  assert (Δ ⊢s σ,,M',,R ® ρ ↦ m' ↦ r' ∈ SbΓℕA) by (unfold SbΓℕA; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  clear_dups.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  match goal with
  | _: ⟦ MS ⟧ ρ ↦ m' ↦ r' ↘ ?m |- _ => rename m into ms
  end.
  (** [MS]'s gluing predicate sits at the stuck [⟦A[Wk⨟Wk,,succ #1]⟧]; move it
      to the motive at [succ m']. *)
  destruct (per_univ_nat_step_instance HSbΓ ltac:(eassumption) HgΓℕA ltac:(eassumption)
              ltac:(eassumption) ltac:(eassumption)) as [? ?].
  saturate_glu_by_per.
  handle_functional_glu_univ_elem.
  exists ms; split; [mauto 3 |].
  assert (Δ ⊢ A[σ,,M] ≈ A[σ,,succ M'] : Type@i) as ->
      by (eapply exp_eq_sub_eq_head with (A := ℕ); mauto 3).
  assert (Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[σ,,M',,R] : A[σ,,succ M']) as ->;
    [| rewrite <- (exp_sub_natrec_step A σ M' R); eassumption ].
  rewrite <- (exp_sub_q_extend A σ succ M').
  rewrite <- (exp_sub_q_extend2 MS σ M' R).
  transitivity rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end.
  - eapply wf_exp_eq_conv';
      [ eapply wf_exp_eq_natrec_cong'; mauto 3
      | eapply exp_eq_sub_eq_single; mauto 3 ].
  - eapply wf_exp_eq_nat_beta_succ'; mauto 3.
Qed.

Lemma cons_glu_sub_pred_q_helper : forall {Γ SbΓ Δ σ ρ i A a},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    Γ ⊩ A : Type@i ->
    ⟦ A ⟧ ρ ↘ a ->
    Δ ▹ A[σ] ⊢s q σ ® ρ ↦ ⇑! a (length Δ) ∈ cons_glu_sub_pred i Γ A SbΓ.
Proof.
  intros * ? ? HA ?.
  assert (Γ ⊢ A : Type@i) by mauto 2.
  invert_glu_rel_exp HA.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  assert (⊢ Δ ▹ A[σ]) by mauto 3.
  assert (Δ ▹ A[σ] ⊢k ↑ : Δ) by mauto 3.
  eapply cons_glu_sub_pred_helper; mauto 2.
  - eapply glu_ctx_env_sub_monotone; eassumption.
  - rewrite <- exp_wk_sub.
    eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mctt.

(** [ℕ[σ]] is [ℕ], so this is [cons_glu_sub_pred_q_helper] verbatim — but only
    up to conversion, so the instance must be spelled out. *)
Lemma cons_glu_sub_pred_q_nat_helper : forall {Γ SbΓ Δ σ ρ i},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    Δ ▹ ℕ ⊢s q σ ® ρ ↦ ⇑! ℕᵈ (length Δ) ∈ cons_glu_sub_pred i Γ ℕ SbΓ.
Proof.
  intros.
  assert (⊩ Γ) by (eexists; eassumption).
  assert (Γ ⊩ ℕ : Type@i) by mauto 3.
  assert (⟦ ℕ ⟧ ρ ↘ ℕᵈ) by mauto 3.
  exact (@cons_glu_sub_pred_q_helper Γ SbΓ Δ σ ρ i ℕ ℕᵈ
           ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_nat_helper : mctt.

(** Kripke-weakening the scrutinee's type collapses its two substitution steps
    into one with [sb_wk]. *)
Fact natrec_typ_sub_wk : forall A σ M φ,
    A[σ,,M]⟨φ⟩ = A[q (sb_wk σ φ)][Id,,M⟨φ⟩].
Proof.
  intros; rewrite exp_sub_q_extend; apply exp_wk_sub_extend_head.
Qed.

Lemma glu_rel_exp_natrec_neut_helper : forall {i Γ SbΓ A MZ MS Δ M a m σ ρ am P El},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊩ A : Type@i ->
    Γ ⊩ A[Id,,zero] : Type@i ->
    Γ ⊩ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@i ->
    Γ ▹ ℕ ▹ A ⊩ MS : A[Wk ⨟ Wk,,succ #1] ->
    Dom m ≈ m ∈ per_bot ->
    (forall Δ' φ V, Δ' ⊢k φ : Δ -> Rne m in length Δ' ↘ V -> Δ' ⊢ M⟨φ⟩ ≈ V : ℕ) ->
    Δ ⊢s σ ® ρ ∈ SbΓ ->
    ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am ->
    DG am ∈ glu_univ_elem i ↘ P ↘ El ->
    exists r,
      ⟦rec ⇑ a m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
        Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El.
Proof.
  intros * HSbΓ HA ? HMZ ? HMS **.
  assert (Δ ⊢s σ : Γ) by mauto 3.
  saturate_sub.
  assert (Γ ⊢ MZ : A[Id,,zero]) by mauto 2.
  invert_glu_rel_exp HMZ.
  assert (⊩ Γ) by (eexists; eassumption).
  assert (Γ ⊩ ℕ : Type@i) as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred i Γ ℕ SbΓ).
  assert (EG Γ ▹ ℕ ∈ glu_ctx_env ↘ SbΓℕ) by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
  pose proof HA as HAglu.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred i (Γ ▹ ℕ) A SbΓℕ).
  assert (EG Γ ▹ ℕ ▹ A ∈ glu_ctx_env ↘ SbΓℕA) as HgΓℕA by (econstructor; mauto 3; reflexivity).
  assert (Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1]) by mauto 2.
  invert_glu_rel_exp HMS.
  assert (glu_nat Δ M ⇑ a m) by (econstructor; eassumption).
  assert (Δ ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ) by (unfold SbΓℕ; mauto 3).
  assert (glu_nat Δ zero zeroᵈ) by (econstructor; mauto 3).
  assert (Δ ⊢s σ,,zero ® ρ ↦ zeroᵈ ∈ SbΓℕ) by (unfold SbΓℕ; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  match goal with
  | _: ⟦ MZ ⟧ ρ ↘ ?v |- _ => rename v into mz
  end.
  match goal with
  | _: ⟦ A[Id,,zero] ⟧ ρ ↘ ?v |- _ => rename v into az
  end.
  match goal with
  | _: ⟦ A ⟧ ρ ↦ zeroᵈ ↘ ?v |- _ => rename v into azero
  end.
  (** [MZ]'s predicate is at the stuck [az]; move it to the motive at [zero]. *)
  destruct (per_univ_zero_instance HSbΓ ltac:(eassumption) ltac:(eassumption)
              ltac:(eassumption) ltac:(eassumption)) as [? ?].
  saturate_glu_by_per.
  handle_functional_glu_univ_elem.
  assert (Δ ⊢ M : ℕ) by mauto 3.
  assert (Δ ▹ ℕ ⊢s q σ : Γ ▹ ℕ) by mauto 3.
  assert (Δ ▹ ℕ ⊢ A[q σ] : Type@i) by mauto 3.
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢s q (q σ) : Γ ▹ ℕ ▹ A) by mauto 3.
  assert (Δ ⊢ MZ[σ] : A[q σ][Id,,zero])
      by (rewrite exp_sub_q_extend, <- exp_sub_extend_sub_zero; mauto 3).
  assert (Δ ▹ ℕ ▹ A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk ⨟ Wk,,succ #1])
      by (rewrite <- exp_sub_sub_natrec; mauto 3).
  eexists; split; [mauto 3 |].
  enough (Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end
             : A[σ,,M] ® recᵈ m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot i am)
      by (eapply realize_glu_elem_bot; mauto 3).
  econstructor; [| eassumption | eassumption | |].
  - rewrite <- (exp_sub_q_extend A σ M); mauto 3.
  - (** [per_bot_natrec_diag] replaces the hand-rolled readback-existence
        argument: its zero obligation is [MZ]'s own semantic element. *)
    assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
    assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    assert (Γ ▹ ℕ ⊨ A : Type@i) by mauto 3 using completeness_fundamental_exp.
    assert (Γ ▹ ℕ ▹ A ⊨ MS : A[Wk ⨟ Wk,,succ #1]) by mauto 3 using completeness_fundamental_exp.
    assert (Dom azero ≈ azero ∈ per_univ i) as [Rz ?] by mauto 3.
    assert (Dom mz ≈ mz ∈ Rz) by (eapply glu_univ_elem_per_elem; revgoals; eassumption).
    assert (DF mz ≈ mz ∈ per_head A A (ρ ↦ zeroᵈ) ↘ ρ ↦ zeroᵈ)
        by (eapply per_head_of; eassumption).
    eapply per_bot_natrec_diag; eassumption.
  - intros Δ' φ W ? HW.
    saturate_kripke_escape.
    saturate_sub.
    assert (Δ' ⊢s (sb_wk σ φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
    assert (Δ' ⊢s (sb_wk σ φ) ® ρ ∈ SbΓ) by (eapply glu_ctx_env_sub_monotone; eassumption).
    assert (Δ' ▹ ℕ ⊢s q (sb_wk σ φ) ® ρ ↦ ⇑! ℕᵈ (length Δ') ∈ SbΓℕ) by (unfold SbΓℕ; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    (** The scrutinee's readback names the four components it recurses on:
        [m0] is [⟦A⟧] at a fresh variable, [bs] its instance at [succ], and
        [B'], [MZ0], [MS'], [M0] are the readbacks to be matched. *)
    match_by_head read_ne ltac:(fun H => directed inversion_clear H).
    simplify_evals.
    handle_functional_glu_univ_elem.
    rewrite natrec_typ_sub_wk, exp_wk_sub_q2, exp_wk_sub_q, exp_wk_sub.
    assert (Δ' ▹ ℕ ▹ A[q (sb_wk σ φ)] ⊢s q (q (sb_wk σ φ))
                ® ρ ↦ ⇑! ℕᵈ (length Δ') ↦ ⇑! m0 (S (length Δ')) ∈ SbΓℕA)
        by (unfold SbΓℕA; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    clear_dups.
    handle_functional_glu_univ_elem.
    (** The successor branch's predicate again sits at the stuck value. *)
    destruct (per_univ_nat_step_instance HSbΓ ltac:(eassumption) HgΓℕA ltac:(eassumption)
                ltac:(eassumption) ltac:(eassumption)) as [? ?].
    saturate_glu_by_per.
    handle_functional_glu_univ_elem.
    eapply wf_exp_eq_natrec_cong'; fold ne_to_exp nf_to_exp.
    + assert (Δ' ▹ ℕ ⊢ A[q (sb_wk σ φ)] ® glu_typ_top i m0) as [? ? Hrbt]
          by (eapply realize_glu_typ_top; eassumption).
      assert (Δ' ▹ ℕ ⊢k wk_id : Δ' ▹ ℕ) by mauto 3.
      assert (Δ' ▹ ℕ ⊢ A[q (sb_wk σ φ)]⟨wk_id⟩ ≈ B' : Type@i) as Hat by (eapply Hrbt; eassumption).
      rewrite exp_wk_id in Hat; eassumption.
    + rewrite exp_sub_q_extend, <- exp_sub_extend_sub_zero.
      assert (Δ' ⊢ MZ[(sb_wk σ φ)] : A[Id,,zero][(sb_wk σ φ)] ® mz ∈ glu_elem_top i azero)
          as [? ? ? ? ? ? Hrbz] by (eapply realize_glu_elem_top; eassumption).
      assert (Δ' ⊢k wk_id : Δ') by mauto 3.
      assert (Δ' ⊢ MZ[(sb_wk σ φ)]⟨wk_id⟩ ≈ MZ0 : A[Id,,zero][(sb_wk σ φ)]⟨wk_id⟩) as Hmz
          by (eapply Hrbz; eassumption).
      rewrite ! exp_wk_id in Hmz; eassumption.
    + rewrite <- exp_sub_sub_natrec.
      assert (Δ' ▹ ℕ ▹ A[q (sb_wk σ φ)] ⊢ MS[q (q (sb_wk σ φ))]
                  : A[Wk ⨟ Wk,,succ #1][q (q (sb_wk σ φ))] ® ms ∈ glu_elem_top i bs)
          as [? ? ? ? ? ? Hrbs] by (eapply realize_glu_elem_top; eassumption).
      assert (Δ' ▹ ℕ ▹ A[q (sb_wk σ φ)] ⊢k wk_id : Δ' ▹ ℕ ▹ A[q (sb_wk σ φ)]) by mauto 3.
      assert (Δ' ▹ ℕ ▹ A[q (sb_wk σ φ)] ⊢ MS[q (q (sb_wk σ φ))]⟨wk_id⟩ ≈ MS'
                  : A[Wk ⨟ Wk,,succ #1][q (q (sb_wk σ φ))]⟨wk_id⟩) as Hms
          by (eapply Hrbs; eassumption).
      rewrite ! exp_wk_id in Hms; eassumption.
    + mauto 3.
Qed.

Lemma glu_rel_exp_natrec_helper : forall {i Γ SbΓ A MZ MS},
    EG Γ ∈ glu_ctx_env ↘ SbΓ ->
    Γ ▹ ℕ ⊩ A : Type@i ->
    Γ ⊩ A[Id,,zero] : Type@i ->
    Γ ⊩ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@i ->
    Γ ▹ ℕ ▹ A ⊩ MS : A[Wk ⨟ Wk,,succ #1] ->
    forall {Δ M m},
      glu_nat Δ M m ->
      forall {σ ρ am P El},
        Δ ⊢s σ ® ρ ∈ SbΓ ->
        ⟦ A ⟧ ρ ↦ m ↘ am ->
        DG am ∈ glu_univ_elem i ↘ P ↘ El ->
        exists r,
          ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
            Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El.
Proof.
  intros * ? ? ? ? ? ?.
  assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
  assert (Γ ⊢ MZ : A[Id,,zero]) by mauto 2.
  assert (Γ ▹ ℕ ▹ A ⊢ MS : A[Wk ⨟ Wk,,succ #1]) by mauto 2.
  induction 1; intros; rename Γ0 into Δ.
  - (** [glu_nat_zero] *)
    mauto 4 using glu_rel_exp_natrec_zero_helper.
  - (** [glu_nat_succ] *)
    mauto 3 using glu_rel_exp_natrec_succ_helper.
  - (** [glu_nat_neut] *)
    mauto 3 using glu_rel_exp_natrec_neut_helper.
Qed.

Lemma glu_rel_exp_natrec_intro : forall {Γ i A MZ MS M},
    Γ ▹ ℕ ⊩ A : Type@i ->
    Γ ⊩ A[Id,,zero] : Type@i ->
    Γ ⊩ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@i ->
    Γ ▹ ℕ ▹ A ⊩ MS : A[Wk ⨟ Wk,,succ #1] ->
    Γ ⊩ M : ℕ ->
    Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M].
Proof.
  intros * HA ? ? ? ? HM.
  assert (⊩ Γ) as [SbΓ] by mauto 2.
  assert (Γ ⊩ ℕ : Type@i) as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred i Γ ℕ SbΓ).
  assert (EG Γ ▹ ℕ ∈ glu_ctx_env ↘ SbΓℕ) by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity).
  assert (Γ ▹ ℕ ⊩ Type@i : Type@(S i)) by mauto 3.
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_exp HA.
  eexists; split; [eassumption |].
  eexists.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  clear_dups.
  inversion_clear_by_head nat_glu_exp_pred.
  assert (Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ) by (unfold SbΓℕ; mauto 2).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  inversion_clear_by_head nat_glu_exp_pred.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  clear_dups.
  match_by_head nat_glu_typ_pred ltac:(fun H => clear H).
  match goal with
  | _: (⟦ A ⟧ ρ ↦ m ↘ ?a'),
      _: DG ?a' ∈ glu_univ_elem i ↘ ?P' ↘ ?El' |- _ =>
      rename a' into a;
      rename P' into P;
      rename El' into El
  end.
  assert (exists r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r /\
                 El Δ A[σ,,M[σ]] rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end r)
      as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4).
  (** [A[Id,,M]] is a stuck substitution, so its evaluation is not computable;
      [per_univ_of_instance] supplies it, and the predicate moves over by PER. *)
  assert (Γ ⊢ M : ℕ) by mauto 3.
  assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
  assert (⊢ Γ) by mauto 2.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  assert (Γ ▹ ℕ ⊨ A : Type@i) by mauto 3 using completeness_fundamental_exp.
  assert (Γ ⊨ M : ℕ) by mauto 3 using completeness_fundamental_exp.
  destruct (per_univ_of_instance HΓ ltac:(eassumption) ltac:(eassumption) ρ m
              ltac:(eassumption) ltac:(eassumption)) as [? [? [? [? [? [? ?]]]]]].
  functional_eval_rewrite_clear.
  saturate_glu_by_per.
  handle_functional_glu_univ_elem.
  econstructor; mauto 3.
  rewrite exp_sub_extend_sub.
  simplify_subs.
  eassumption.
Qed.

Lemma glu_rel_exp_natrec : forall {Γ i A MZ MS M},
    Γ ▹ ℕ ⊩ A : Type@i ->
    Γ ⊩ MZ : A[Id,,zero] ->
    Γ ▹ ℕ ▹ A ⊩ MS : A[Wk ⨟ Wk,,succ #1] ->
    Γ ⊩ M : ℕ ->
    Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M].
Proof.
  intros * HA HMZ HMS HM.
  (** The two instantiated motives are stuck evaluations, so they cannot be
      derived from [HA]; they come from the branches, at their own levels. *)
  assert (exists j, Γ ⊩ A[Id,,zero] : Type@j) as [j] by mauto 3.
  assert (exists k, Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@k) as [k] by mauto 3.
  assert (⊩ Γ) by mauto 2.
  assert (Γ ⊩ ℕ : Type@0) by mauto 3.
  assert (⊩ Γ ▹ ℕ) by mauto 3.
  assert (⊩ Γ ▹ ℕ ▹ A) by mauto 3.
  assert (i <= max i (max j k)) by lia.
  assert (j <= max i (max j k)) by lia.
  assert (k <= max i (max j k)) by lia.
  assert (Γ ▹ ℕ ⊢ Type@i ⊆ Type@(max i (max j k))) by mauto 4.
  assert (Γ ⊢ Type@j ⊆ Type@(max i (max j k))) by mauto 4.
  assert (Γ ▹ ℕ ▹ A ⊢ Type@k ⊆ Type@(max i (max j k))) by mauto 4.
  assert (Γ ▹ ℕ ⊩ A : Type@(max i (max j k))) by mauto 3.
  assert (Γ ⊩ A[Id,,zero] : Type@(max i (max j k))) by mauto 3.
  assert (Γ ▹ ℕ ▹ A ⊩ A[Wk ⨟ Wk,,succ #1] : Type@(max i (max j k))) by mauto 3.
  mauto 3 using glu_rel_exp_natrec_intro.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mctt.
