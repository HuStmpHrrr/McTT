(** * The Fundamental Theorem of the PER Model

    In four parts: contexts, terms, term equality, subtyping.  There is no substitution conjunct, and there cannot be:
    [wf_sub] constrains [σ] only at the indices [Δ] types, whereas [eval_sub] is
    total, so [⋅ ⊢s (fun _ => zero $ zero) : ⋅] holds vacuously while
    its semantic counterpart would need [zero zero] to have a value.  Nothing
    needs the general statement; it is only ever appealed to at concrete
    substitutions, which the lemmas of [SubstitutionCases.v] build directly.
    Context refinement and context equality are likewise gone, being
    [Δ ⊢s Id : Γ] in one and both directions. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases NatCases SubstitutionCases SubtypingCases
  UniverseCases VariableCases.
From Mctt.Core.Completeness Require Export LogicalRelation.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.
Import Wk_Notations.

Section FundamentalTheorem.

  Theorem completeness_fundamental :
    (forall Γ, ⊢ Γ -> ⊨ Γ) /\
      (forall Γ A M, Γ ⊢ M : A -> Γ ⊨ M : A) /\
      (forall Γ A M M', Γ ⊢ M ≈ M' : A -> Γ ⊨ M ≈ M' : A) /\
      (forall Γ A A', Γ ⊢ A ⊆ A' -> Γ ⊨ A ⊆ A').
  Proof.
    apply syntactic_wf_mut_ind; mauto 3.
    (** [mauto] misses the rules whose semantic lemma is in [valid_] form while
        the goal's head is [rel_exp_under_ctx] (so [Hint Resolve] never fires),
        the two PER rules, and [Sub-Univ], stated at [i <= j] rather than
        [i < j]. *)
    - intros; apply valid_exp_typ; assumption.
    - intros; apply valid_exp_nat; assumption.
    - intros; apply valid_exp_zero; assumption.
    - intros; eapply valid_exp_var; eassumption.
    - intros; apply rel_exp_under_ctx_sym; assumption.
    - intros; eapply rel_exp_under_ctx_trans; eassumption.
    - intros; apply subtyp_univ; [ assumption | lia ].
  Qed.

  #[local]
  Ltac solve_it := pose proof completeness_fundamental; firstorder.

  Theorem completeness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊨ Γ.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊨ M : A.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_exp_eq : forall Γ M M' A, Γ ⊢ M ≈ M' : A -> Γ ⊨ M ≈ M' : A.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_subtyp : forall Γ A A', Γ ⊢ A ⊆ A' -> Γ ⊨ A ⊆ A'.
  Proof. solve_it. Qed.

End FundamentalTheorem.

(** The substitution instance soundness needs, in its [Π]-β case. *)
Corollary completeness_fundamental_sub_single : forall Γ M A,
    Γ ⊢ M : A ->
    Γ ⊨s Id,,M : Γ ▹ A.
Proof.
  intros * HM%completeness_fundamental_exp.
  pose proof (presup_rel_exp_under_ctx HM) as [i HA].
  pose proof HM as [env_relΓ [HΓ _]].
  eapply rel_sub_under_ctx_extend;
    [ apply (rel_sub_id (ex_intro _ _ HΓ)) | eassumption |].
  rewrite exp_sub_id.
  eassumption.
Qed.

(** The weakening instance soundness needs, in its variable case.  [⟦A⟨↑⟩⟧(ρ)]
    and [⟦A⟧(ρ↯)] are not equal; this relatedness replaces the equation, and
    moving [P] and [El] along it with [glu_univ_elem_resp_per_univ] is all
    soundness does with it. *)
Corollary completeness_fundamental_typ_shift : forall {Γ B A i env_rel ρ},
    ⊢ Γ ▹ B ->
    Γ ⊢ A : Type@i ->
    EF Γ ▹ B ≈ Γ ▹ B ∈ per_ctx_env ↘ env_rel ->
    Dom ρ ≈ ρ ∈ env_rel ->
    exists a a',
      ⟦ A⟨↑⟩ ⟧ ρ ↘ a /\
      ⟦ A ⟧ ρ↯ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * ? ? Hper Hρ.
  assert (Γ ▹ B ⊨w ↑ : Γ)
    by (apply rel_wk_under_ctx_shift, completeness_fundamental_ctx; eassumption).
  assert (Γ ⊨ A : Type@i) by (apply completeness_fundamental_exp; eassumption).
  destruct (rel_exp_of_typ_inversion_wk ltac:(eassumption) ltac:(eassumption))
    as [env_rel' [Hper' Hbridge]].
  handle_per_ctx_env_irrel.
  destruct (Hbridge _ _ Hρ) as [a [a' ?]].
  exists a, a'; eassumption.
Qed.

#[export]
Hint Resolve completeness_fundamental_ctx completeness_fundamental_exp
             completeness_fundamental_exp_eq completeness_fundamental_subtyp
             completeness_fundamental_sub_single : mctt.
