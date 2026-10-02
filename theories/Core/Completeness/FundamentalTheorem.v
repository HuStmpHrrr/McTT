(** * The Fundamental Theorem of the PER Model

    In four parts: contexts, terms, term equality and subtyping.  There is no
    substitution part, and there cannot be: [wf_sub] constrains [σ] only at the
    indices [Δ] types, whereas [eval_sub] is total, so
    [⋅ ⊢s (fun _ => zero $ zero) : ⋅] holds vacuously while its semantic
    counterpart would need [zero zero] to have a value.  The concrete semantic
    substitutions that are needed are built directly by the lemmas of
    [SubstitutionCases.v].  Context refinement and context equality are not
    separate judgments: they are [Δ ⊢s Id : Γ] in one direction and in both. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases NatCases SubstitutionCases SubtypingCases
  UniverseCases VariableCases.
From Mctt.Core.Completeness Require Export LogicalRelation.
From Mctt.Core.Completeness Require Import ModuleCases.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Section FundamentalTheorem.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma sem_msub_id_gc : ⊢g gc_deps ⍮ gc_stack -> sem_emb gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (gctx_sem _ _). Qed.

  Theorem completeness_fundamental :
    (forall Γ, ⊢ Γ -> ⊨ Γ) /\
      (forall Γ A M, Γ ⊢ M : A -> Γ ⊨ M : A) /\
      (forall Γ A M M', Γ ⊢ M ≈ M' : A -> Γ ⊨ M ≈ M' : A) /\
      (forall Γ A A', Γ ⊢ A ⊆ A' -> Γ ⊨ A ⊆ A').
  Proof.
    destruct kripke_fundamental as (Kc & Ke & Kq & Ks).
    repeat split; intros * H;
      [ pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ H)) as Hid
      | pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H))) as Hid
      | pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_eq_ctx H))) as Hid
      | pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_subtyp_ctx H))) as Hid ];
      [ pose proof (Kc _ _ _ H _ _ Hid) as H'
      | destruct (Ke _ _ _ _ _ H _ _ Hid) as [_ H']
      | destruct (Kq _ _ _ _ _ _ H _ _ Hid) as [_ H']
      | destruct (Ks _ _ _ _ _ H _ _ Hid) as [_ H'] ];
      idtac;
      destruct GC; exact H'.
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

Section Corollaries.
  Context {GC : GCtx}.

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

(** The weakening instance soundness needs, in its variable case.  [⟦A[↑]ʷ⟧(ρ)]
    and [⟦A⟧(ρ↯)] are not equal; this relatedness replaces the equation, and
    moving [P] and [El] along it with [glu_univ_elem_resp_per_univ] is all
    soundness does with it. *)
Corollary completeness_fundamental_typ_shift : forall {Γ e A i env_rel ρ},
    ⊢ (e :: Γ)%list ->
    Γ ⊢ A : Type@i ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ env_rel ->
    Dom ρ ≈ ρ ∈ env_rel ->
    exists a a',
      ⟦ A[↑]ʷ ⟧ ρ ↘ a /\
      ⟦ A ⟧ ρ↯ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * ? ? Hper Hρ.
  assert ((e :: Γ)%list ⊨w ↑ : Γ)
    by (apply rel_wk_under_ctx_shift, completeness_fundamental_ctx; eassumption).
  assert (Γ ⊨ A : Type@i) by (apply completeness_fundamental_exp; eassumption).
  destruct (rel_exp_of_typ_inversion_wk ltac:(eassumption) ltac:(eassumption))
    as [env_rel' [Hper' Hbridge]].
  handle_per_ctx_env_irrel.
  destruct (Hbridge _ _ Hρ) as [a [a' ?]].
  rewrite eval_wk_shift in *.
  exists a, a'; eassumption.
Qed.

End Corollaries.

#[export]
Hint Resolve completeness_fundamental_ctx completeness_fundamental_exp
             completeness_fundamental_exp_eq completeness_fundamental_subtyp
             completeness_fundamental_sub_single : mctt.
