(** * Completeness of Normalization by Evaluation

    The fundamental theorem instantiated at the identity substitution and the
    initial environment, where only the inner two values of each chain of
    [rel_exp_under_ctx] are used. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

(** A semantic equality read at the initial environment of its own context. *)
Lemma rel_exp_under_ctx_at_initial_env : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists ρ i elem_rel a m m',
      initial_env Γ ρ /\
      {{ ⟦ A ⟧ ρ ↘ a }} /\ {{ ⟦ M ⟧ ρ ↘ m }} /\ {{ ⟦ M' ⟧ ρ ↘ m' }} /\
      {{ DF a ≈ a ∈ per_univ_elem i ↘ elem_rel }} /\
      {{ Dom m ≈ m' ∈ elem_rel }}.
Proof.
  intros * H.
  destruct H as [env_relΓ [HΓ [i HMgen]]].
  pose proof (per_ctx_then_per_env_initial_env HΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HMgen _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hrel
                  (eval_sub_id _) (eval_sub_id _)) as [elem_rel [Htyp Hexp]].
  pose proof (rel_typ_elem_PER Htyp) as HPER.
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (a3 = a2) as -> by (eapply functional_eval_exp; eassumption).
  exists ρ, i, elem_rel, a2, m2, m3.
  repeat apply conj; try eassumption.
  - pairwise.
  - pairwise.
Qed.

(** The same at a type equality, where the element relation is [per_univ i]. *)
Lemma rel_typ_under_ctx_at_initial_env : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    exists ρ a a',
      initial_env Γ ρ /\ {{ ⟦ A ⟧ ρ ↘ a }} /\ {{ ⟦ A' ⟧ ρ ↘ a' }} /\
      {{ Dom a ≈ a' ∈ per_univ i }}.
Proof.
  intros * H%rel_exp_of_typ_inversion_simple.
  destruct H as [env_relΓ [HΓ HA]].
  pose proof (per_ctx_then_per_env_initial_env HΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HA _ _ Hrel) as [a [a' [Ha [Ha' Haa']]]].
  exists ρ, a, a'.
  repeat apply conj; eassumption.
Qed.

Theorem completeness : forall {Γ M M' A},
    {{ Γ ⊢ M ≈ M' : A }} ->
    exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_exp_under_ctx_at_initial_env H)
    as [ρ [i [elem_rel [a [m [m' [Hρ [Ha [Hm [Hm' [Htyp Hrel]]]]]]]]]]].
  destruct (per_elem_then_per_top Htyp Hrel (length Γ)) as [W [HW HW']].
  exists W.
  split; econstructor; eassumption.
Qed.

Corollary completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.
