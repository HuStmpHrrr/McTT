(** * The Fundamental Theorem of the PER Model, at One Global Context

    [completeness_fundamental] ([KripkeCases.v]) states every judgment of a
    global context semantically, along every sound embedding.  A
    well-formed global context embeds soundly into itself ([gctx_sem]); at
    that embedding the semantic judgments are the relations at the global
    context, as the corollaries below state them for contexts, terms, term
    equality, subtyping and the module judgments.  There is no
    substitution part, and there cannot be: [wf_sub] constrains [σ] only at the
    indices [Δ] types, whereas [eval_sub] is total, so
    [⋅ ⊢ˢ (fun _ => zero $ zero) : ⋅] holds vacuously while its semantic
    counterpart would need [zero zero] to have a value.  The concrete semantic
    substitutions that are needed are built directly by the lemmas of
    [SubstitutionCases.v].  Context refinement and context equality are not
    separate judgments: they are [Δ ⊢ˢ Id : Γ] in one direction and in both. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases FunctionCases SubstitutionCases SubtypingCases
  UniverseCases VariableCases.
From Mctt.Core.Completeness Require Export LogicalRelation.
From Mctt.Core.Completeness Require Import ModuleCases GlobalSem.
From Mctt.Core.Completeness Require Export KripkeCases.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Section FundamentalTheorem.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma sem_msub_id_gc : ⊢ᵍ gc_deps ⍮ gc_stack -> sem_emb gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (gctx_sem _ _). Qed.

  (** At the identity embedding, the semantic judgments of [GC] are the
      relations at [GC]. *)

  Corollary completeness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊨ Γ.
  Proof.
    intros * H; pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ H)) as Hid.
    destruct completeness_fundamental as (Kc & _).
    pose proof (kca_ctx (Kc _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊨ M : A.
  Proof.
    intros * H; pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & Ke & _).
    pose proof (kea_rel (Ke _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_exp_eq : forall Γ M M' A, Γ ⊢ M ≈ M' : A -> Γ ⊨ M ≈ M' : A.
  Proof.
    intros * H; pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_eq_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & _ & Kq & _).
    pose proof (kea_rel (Kq _ _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_subtyp : forall Γ A A', Γ ⊢ A ⊆ A' -> Γ ⊨ A ⊆ A'.
  Proof.
    intros * H; pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_subtyp_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & _ & _ & Ks & _).
    pose proof (ksa_rel (Ks _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  (** The module judgments. *)
  Corollary completeness_fundamental_modules :
    (forall Γ Ψ Ψ', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Γ ⊨ˣ Ψ ≈ Ψ') /\
      (forall Γ U U', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U' -> Γ ⊨ᵘ U ≈ U') /\
      (forall Γ H H', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H' -> Γ ⊨ᵐ H ≈ H').
  Proof.
    destruct completeness_fundamental as (_ & _ & _ & _ & _ & Kx & Ku & Km).
    split; [| split ]; intros * HJ;
      [ pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_ext_eq_ctx HJ))) as Hid
      | pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HJ))) as Hid
      | pose proof (sem_msub_id_gc (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HJ))) as Hid ];
      [ pose proof (kxa_rel (Kx _ _ _ _ _ HJ _ _ Hid)) as HR
      | pose proof (kna_rel (Ku _ _ _ _ _ HJ _ _ Hid)) as HR
      | pose proof (kma_rel (Km _ _ _ _ _ HJ _ _ Hid)) as HR ];
      destruct GC; exact HR.
  Qed.

End FundamentalTheorem.

Section Corollaries.
  Context {GC : GCtx}.

(** The substitution instance soundness needs, in its [Π]-β case. *)
Corollary completeness_fundamental_sub_single : forall Γ M A,
    Γ ⊢ M : A ->
    Γ ⊨ˢ Id,,M : Γ ▹ A.
Proof.
  intros * HM%completeness_fundamental_exp.
  pose proof (presup_rel_exp_under_ctx HM) as [i HA].
  pose proof HM as [env_relΓ HΓ _ _].
  eapply rel_sub_under_ctx_extend;
    [ apply (rel_sub_id (ex_intro _ _ HΓ)) | eassumption |].
  rewrite exp_sub_id.
  eassumption.
Qed.

(** The weakening instance soundness needs, in its variable case.  [⟦A[↑]ʷ⟧(ρ)]
    and [⟦A⟧(ρ↯)] are not equal; this relatedness replaces the equation, and
    moving [P] and [El] along it with [glu_univ_elem_resp_per_univ] is all
    soundness does with it. *)
Corollary completeness_fundamental_typ_shift : forall {Γ e A} {i : nat} {env_rel ρ},
    ⊢ (e :: Γ)%list ->
    Γ ⊢ A : Typeω@i ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ env_rel ->
    Dom ρ ≈ ρ ∈ env_rel ->
    exists a a',
      ⟦ A[↑]ʷ ⟧ ρ ↘ a /\
      ⟦ A ⟧ ρ↯ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * ? ? Hper Hρ.
  assert ((e :: Γ)%list ⊨ʷ ↑ : Γ)
    by (apply rel_wk_under_ctx_shift, completeness_fundamental_ctx; eassumption).
  assert (Γ ⊨ A : Typeω@i) by (apply completeness_fundamental_exp; eassumption).
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
