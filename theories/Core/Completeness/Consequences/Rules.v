(** * Consequences of Completeness: normal forms respect context equality

    Context equality is no longer a judgment, so the hypothesis here is the
    semantic one.  [per_ctx_of_exp_eq] is the only instance anything needs:
    extending one context by two judgmentally equal types. *)

From Stdlib Require Import RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Completeness Require Import ContextCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Corollary per_ctx_of_exp_eq : forall {Γ A A' i},
    Γ ⊢ A ≈ A' : Type@i ->
    ⊨ Γ ▹ A ≈ Γ ▹ A'.
Proof.
  intros * H.
  assert (⊢ Γ) by mauto 2.
  eapply rel_ctx_extend; [ apply sem_ctx_per_ctx | ]; mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_of_exp_eq : mctt.

Lemma ctxeq_nbe_eq : forall Γ Γ' M A,
    Γ ⊢ M : A ->
    ⊨ Γ ≈ Γ' ->
    exists W, nbe Γ M A W /\ nbe Γ' M A W.
Proof.
  intros * HM%completeness_fundamental_exp HΓΓ'.
  pose proof (per_ctx_respects_length HΓΓ') as Hlen.
  destruct HM as [env_relΓ [HΓ [i HMgen]]].
  destruct HΓΓ' as [env_rel HΓΓ'].
  assert (Hirrel : env_rel <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [ exact HΓΓ' | exact HΓ ]).
  (** The two initial environments are related, so the judgment may be read with
      one on each side. *)
  pose proof (per_ctx_then_per_env_initial_env HΓΓ') as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  rewrite Hirrel in Hrel.
  destruct (HMgen _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hrel
                  (eval_sub_id _) (eval_sub_id _)) as [elem_rel [Htyp Hexp]].
  pose proof (rel_typ_elem_PER Htyp) as HPER.
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Ha : DF a2 ≈ a3 ∈ per_univ_elem i ↘ elem_rel) by pairwise.
  assert (Hm : Dom m2 ≈ m3 ∈ elem_rel) by pairwise.
  destruct (per_elem_then_per_top Ha Hm (length Γ)) as [W [HW HW']].
  exists W.
  split.
  - econstructor; eassumption.
  - econstructor; try eassumption.
    rewrite <- Hlen; eassumption.
Qed.

Corollary ctxeq_nbe_eq' : forall Γ Γ' M A W,
    Γ ⊢ M : A ->
    ⊨ Γ ≈ Γ' ->
    nbe Γ M A W ->
    nbe Γ' M A W.
Proof.
  intros.
  assert (exists W, nbe Γ M A W /\ nbe Γ' M A W) as [? []] by mauto 3 using ctxeq_nbe_eq.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Corollary ctxeq_nbe_ty_eq : forall Γ Γ' A i,
    Γ ⊢ A : Type@i ->
    ⊨ Γ ≈ Γ' ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ' A W.
Proof.
  intros.
  assert (exists W, nbe Γ A Type@i W /\ nbe Γ' A Type@i W)
    as [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]] by mauto 3 using ctxeq_nbe_eq.
  firstorder.
Qed.

Corollary ctxeq_nbe_ty_eq' : forall Γ Γ' A i W,
    Γ ⊢ A : Type@i ->
    ⊨ Γ ≈ Γ' ->
    nbe_ty Γ A W ->
    nbe_ty Γ' A W.
Proof.
  intros.
  assert (exists W, nbe_ty Γ A W /\ nbe_ty Γ' A W) as [? []]
      by mauto 3 using ctxeq_nbe_ty_eq.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
