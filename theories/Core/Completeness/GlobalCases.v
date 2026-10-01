(** * Every Well-Formed Global Context is Semantically Sound

    Every resolved global's generalized type and body, and every parameter's
    type, is valid at [⋅] in the context itself: [global_induction] for the
    PER model, whose sound substitutions are [sem_msub]. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Completeness Require Export ModuleCases.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases NatCases SubstitutionCases SubtypingCases
  UniverseCases VariableCases LogicalRelation.
From Mctt.Core.Semantic Require Import Realizability Bridge.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The PER model *)

Definition sem_valid (Θ : gdeps) (Ξ : gstack) (A M : exp) : Prop :=
  @rel_exp_under_ctx (gc_mk Θ Ξ) ⋅ A M M.

Definition sem_snd Θ1 Ξ1 Θ2 Ξ2 μ : Prop := sem_msub Θ1 Ξ1 Θ2 Ξ2 μ nil.

(** Every parameter from [k] out of a source frame has its image valid, so the
    image frame's parameters from the image of [k] out do. *)
Lemma emb_params_from : forall Θ1 Ξ1 Θ2 Ξ2 μ n U k T n' U' k',
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> SP sem_valid Θ1 Ξ1 Θ2 Ξ2 μ ->
    List.nth_error Ξ1 n = Some U -> gu_params U ∋ #k : T ->
    $[n, k][μ]ᵐ = $[n', k'] -> List.nth_error Ξ2 n' = Some U' ->
    forall k2 T2, k' <= k2 -> gu_params U' ∋ #k2 : T2 -> vtyp sem_valid Θ2 Ξ2 (T2[↑ₘ (S n')]ᵐ[sb_params n']).
Proof.
  intros * He HP Hn Hk Heq Hn' k2 T2 Hle Hk2.
  destruct He as [_ _ Hp _ Hf].
  destruct (Hf _ _ _ _ Hn Hk) as (n'' & U'' & o & Hn'' & Hlen & Hmap).
  pose proof (ctx_lookup_length _ _ _ Hk) as Hkl.
  rewrite (Hmap _ Hkl) in Heq; injection Heq as <- <-.
  rewrite Hn' in Hn''; injection Hn'' as <-.
  pose proof (ctx_lookup_length _ _ _ Hk2) as Hk2l.
  destruct (ctx_lookup_exists (gu_params U) (k2 - o) ltac:(lia)) as [T0 Hk0].
  destruct (Hp _ _ _ _ Hn Hk0) as (n3 & U3 & k3 & T3 & Heq3 & Hn3 & Hk3 & HT3).
  rewrite (Hmap (k2 - o) ltac:(lia)) in Heq3; injection Heq3 as <- <-.
  rewrite Hn' in Hn3; injection Hn3 as <-.
  replace (k2 - o + o) with k2 in Hk3 by lia.
  pose proof (ctx_lookup_det _ _ _ _ Hk3 Hk2) as <-.
  rewrite <- HT3; unfold SP in HP; eapply HP; eassumption.
Qed.

Theorem sem_msub_emb : forall Θ1 Ξ1 Θ2 Ξ2 μ,
    Emb Θ1 Ξ1 Θ2 Ξ2 μ -> SG sem_valid Θ1 Ξ1 Θ2 Ξ2 μ -> SP sem_valid Θ1 Ξ1 Θ2 Ξ2 μ ->
    sem_snd Θ1 Ξ1 Θ2 Ξ2 μ.
Proof.
  intros * He HG HP; pose proof He as [Hg Hq Hp Hl Hf].
  assert (Hb : ⊢ Θ2 ⍮ Ξ2 ⍮ ⋅) by (constructor; assumption).
  assert (Hsc : gs_scoped Ξ2) by (destruct wf_scoped as [Hc _]; apply (Hc _ _ _ Hb)).
  assert (Hqe : forall n (X : exp), X[ms_qn n μ]ᵐ = X[μ]ᵐ) by (intros; apply exp_msub_ext, Hq).
  constructor; [ constructor | | | | ].
  - exact Hb.
  - intros * Hn Hk _ HΓ; rewrite !Hqe.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    rewrite Heq, HT; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn by assumption; split; econstructor; eassumption.
  - intros * Hl0 _ HΓ; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    rewrite Heq, ctx_pi_msub_qn, ctx_fn_msub_qn by assumption; econstructor; eassumption.
  - constructor.
  - intros * Hn Hk _ HΓs; rewrite !Hqe.
    destruct (Hp _ _ _ _ Hn Hk) as (n' & U' & k' & T' & Heq & Hn' & Hk' & HT).
    pose proof (HP _ _ _ _ Hn Hk) as HPv.
    rewrite Heq, HT in *.
    eapply closed_weaken_sem; [ eassumption | | | reflexivity | reflexivity ].
    + apply (param_sem_gen _ _ Hg _ _ _ _ Hn' Hk').
      intros k2 T2 Hle Hk2; exact (emb_params_from _ _ _ _ _ _ _ _ _ _ _ _ He HP Hn Hk Heq Hn' _ _ Hle Hk2).
    + eapply exp_closed_wk, param_type_scoped; eassumption.
  - intros * Hl0 _ HΓs; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    destruct (HG _ _ _ _ _ _ Hl0) as [HT HM].
    rewrite Heq, ctx_pi_msub_qn in * by assumption.
    eapply closed_weaken_sem; [ eassumption | | | reflexivity | reflexivity ].
    + apply (glob_sem_of_raw _ _ Hg _ _ _ _ _ _ Hl').
      split; [ exact HT |].
      intros M' HB; destruct B as [M |]; cbn in HB; inversion HB; subst.
      rewrite <- ctx_fn_msub_qn by assumption; apply HM; reflexivity.
    + eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
  - intros * Hl0 _ HΓs; rewrite !Hqe.
    destruct (Hl _ _ _ _ _ _ Hl0) as (r' & Heq & Hl').
    destruct (HG _ _ _ _ _ _ Hl0) as [HT HM].
    rewrite Heq, ctx_pi_msub_qn, ctx_fn_msub_qn in * by assumption.
    eapply closed_weaken_sem; [ eassumption | | | reflexivity | ].
    + apply (glob_sem_of_raw _ _ Hg _ _ _ _ _ _ Hl'); [| reflexivity | reflexivity ].
      split; [ exact HT |].
      intros M' HB; cbn in HB; inversion HB; subst.
      rewrite <- ctx_fn_msub_qn by assumption; apply HM; reflexivity.
    + eapply exp_closed_wk, wf_gc_lookup_type_closed; eassumption.
    + eapply exp_closed_wk, wf_gc_lookup_body_closed; eassumption.
Qed.

(** Reading a judgment at the source off at the target. *)
Lemma kread : forall Θ1 Ξ1 Θ2 Ξ2 μ A M,
    sem_snd Θ1 Ξ1 Θ2 Ξ2 μ ->
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    sem_valid Θ2 Ξ2 A[μ]ᵐ M[μ]ᵐ.
Proof.
  intros * Hμ HM; destruct kripke_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ _ HM _ _ _ _ Hμ) as [_ H]; exact H.
Qed.

Theorem gctx_sem : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> sem_rwf_raw Θ Ξ /\ sem_pwf_raw Θ Ξ.
Proof. exact (global_induction sem_valid sem_snd sem_msub_emb kread). Qed.
