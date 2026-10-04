(** * Local Definitions in the Gluing Model

    A [let] is glued through its body: [⟦ℓ A ≔ M in B⟧ρ] is [⟦B⟧(ρ ↦ ⟦M⟧ρ)],
    and [σ,,M[σ]] glues with [ρ ↦ ⟦M⟧ρ] into [Γ ▸ A ≔ M].  The type
    [C[Id,,M]] is related to [⟦C⟧(ρ ↦ ⟦M⟧ρ)] by [per_univ_of_instance_def],
    and the term is moved from [B[σ,,M[σ]]] to [(ℓ A ≔ M in B)[σ]] by [ζ]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LetCases.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  TermStructureCases.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [σ,,M[σ]] into a definition entry, as [cons_glu_sub_pred_helper] for an
    assumption entry. *)
Lemma cons_def_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ A a i P El M m},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    Γ ⊢ A : Type@i ->
    Γ ⊢ M : A ->
    ⟦ A ⟧ ρ ↘ a ->
    ⟦ M ⟧ ρ ↘ m ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M[σ] : A[σ] ® m ∈ El ->
    Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ cons_def_glu_sub_pred i Γ A M Sb.
Proof.
  intros * HΓ Hσ HA HM Ha Hm Hglu HMσ.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  assert (Δ ⊢ M[σ] : A[σ]) by mauto 2 using glu_univ_elem_trm_escape.
  assert (Δ ⊢s σ,,M[σ] : Γ ▸ A ≔ M) by (eapply wf_sub_extend_def; mauto 3).
  econstructor; try eassumption.
  - rewrite exp_sub_shift_extend; eassumption.
  - exists m; split; [ eassumption |].
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR].
    eapply per_head_of; [ eassumption | eassumption | exact HR |].
    eapply glu_univ_elem_per_elem; eassumption.
Qed.

Lemma glu_rel_exp_let_helper : forall {Γ oA A i M B C k},
    Γ ⊩ A : Type@i ->
    Γ ⊩ M : A ->
    Γ ▸ A ≔ M ⊩ C : Type@k ->
    Γ ▸ A ≔ M ⊩ B : C ->
    let_ann oA A ->
    Γ ⊩ a_let (b_def oA M) B : C[Id,,M].
Proof.
  intros * HA HM HC HB Hann.
  assert (⊩ Γ) as [SbΓ] by mauto 3.
  assert (Γ ⊢ A : Type@i) by mauto 3.
  assert (Γ ⊢ M : A) by mauto 3.
  assert (Γ ▸ A ≔ M ⊢ C : Type@k) by mauto 3.
  assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 3.
  assert (HAc : Γ ⊨ A : Type@i) by mauto 3 using completeness_fundamental_exp.
  assert (HMc : Γ ⊨ M : A) by mauto 3 using completeness_fundamental_exp.
  assert (HCc : Γ ▸ A ≔ M ⊨ C : Type@k) by mauto 3 using completeness_fundamental_exp.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_def_glu_sub_pred i Γ A M SbΓ).
  assert (EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ SbΓA) by (econstructor; mauto 3; reflexivity).
  invert_glu_rel_exp HB.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ HΓ] by mauto 3.
  eexists; split; [ eassumption |].
  exists k.
  intros Δ σ ρ HSb.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  match goal with
  | HMg : forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ SbΓ -> glu_rel_exp_with_sub i Δ M A σ ρ |- _ =>
      destruct (HMg _ _ _ HSb) as [a m P El Ha Hm Hglu HMσ]
  end.
  assert (HSbA : Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓA)
    by (unfold SbΓA; eapply cons_def_glu_sub_pred_helper; eassumption).
  match goal with
  | HBg : forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ SbΓA -> glu_rel_exp_with_sub k Δ B C σ ρ |- _ =>
      destruct (HBg _ _ _ HSbA) as [c b Pc Elc Hc Hb Hgluc HBσ]
  end.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct (per_univ_of_instance_def HΓ HAc HMc HCc _ _ ltac:(eassumption) Hm)
    as [c' [c'' [Hc' [Hc'' [Hc'c' Hc'c]]]]].
  functional_eval_rewrite_clear.
  assert (DG c' ∈ glu_univ_elem k ↘ Pc ↘ Elc)
    by (eapply glu_univ_elem_resp_per_univ; [ symmetry |]; eassumption).
  econstructor; [ exact Hc' | eapply eval_exp_let; eassumption | eassumption |].
  (** [ζ] along [σ], with both instances in the form [_[σ,,M[σ]]]. *)
  assert (Hζ : Δ ⊢ (a_let (b_def oA M) B)[σ] ≈ B[Id,,M][σ] : C[Id,,M][σ])
    by (eapply sub_preserves_exp_eq; [ eapply wf_exp_eq_let_zeta; cycle 3; [ solve_let_ann | eassumption .. ] | eassumption ]).
  repeat rewrite exp_sub_extend_sub in Hζ.
  repeat rewrite exp_sub_extend_sub.
  eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | exact HBσ |].
  apply wf_exp_eq_sym; exact Hζ.
Qed.

Lemma glu_rel_exp_let : forall {Γ oA A i M B C},
    Γ ⊩ A : Type@i ->
    Γ ⊩ M : A ->
    Γ ▸ A ≔ M ⊩ B : C ->
    let_ann oA A ->
    Γ ⊩ a_let (b_def oA M) B : C[Id,,M].
Proof.
  intros * HA HM HB Hann.
  destruct (presup_typ_glu_rel_exp HB) as [k HC].
  eapply glu_rel_exp_let_helper; eassumption.
Qed.

Hint Resolve glu_rel_exp_let : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_let : mctt.
