(** * The Fundamental Theorem of the Gluing Model

    The theorem has two parts, for contexts and for terms. There is no part for
    substitutions, since the gluing model has no substitution judgment, and none
    for equalities, since the model relates a term to a value rather than two
    terms to each other. It is [kglu_fundamental] at the identity embedding,
    which is sound because every well-formed global context glues
    ([gctx_glu]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import ModuleCases.
From Mctt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations Fixed_Notations.

Section soundness_fundamental.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma glu_msub_id_gc : ⊢g gc_ctx -> glu_emb gc_ctx gc_ctx.
  Proof. exact (gctx_glu _). Qed.

  Theorem soundness_fundamental :
    (forall Γ, ⊢ Γ -> ⊩ Γ) /\
      (forall Γ A M, Γ ⊢ M : A -> Γ ⊩ M : A).
  Proof.
    destruct kglu_fundamental as (Kc & Ke & _).
    split; intros * H;
      [ pose proof (Kc _ _ H _ (glu_msub_id_gc (ctx_wf_gctx _ _ H))) as H'
      | pose proof (Ke _ _ _ _ H _ (glu_msub_id_gc (ctx_wf_gctx _ _ (presup_exp_ctx H)))) as H' ];
      destruct GC; exact H'.
  Qed.

  #[local]
  Ltac solve_it := pose proof soundness_fundamental; firstorder.

  Theorem soundness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊩ Γ.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊩ M : A.
  Proof. solve_it. Qed.
End soundness_fundamental.

#[export]
Hint Resolve soundness_fundamental_ctx soundness_fundamental_exp : mctt.
