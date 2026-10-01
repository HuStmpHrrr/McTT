(** * The Fundamental Theorem of the Gluing Model

    In two parts: contexts and terms.  The substitution conjunct is gone with
    the [⊩s] judgment, and the equality
    judgments never had one — the gluing model relates a term to a value, not two
    terms to each other.  It is [kglu_fundamental] at the identity, which is
    sound because every well-formed global context glues ([gctx_glu]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import ModuleCases.
From Mctt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations Fixed_Notations.

Section soundness_fundamental.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma glu_msub_id_gc : ⊢g gc_deps ⍮ gc_stack -> glu_emb gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (gctx_glu _ _). Qed.

  Theorem soundness_fundamental :
    (forall Γ, ⊢ Γ -> ⊩ Γ) /\
      (forall Γ A M, Γ ⊢ M : A -> Γ ⊩ M : A).
  Proof.
    destruct kglu_fundamental as (Kc & Ke).
    split; intros * H;
      [ pose proof (Kc _ _ _ H _ _ (glu_msub_id_gc (ctx_wf_gctx _ _ _ H))) as H'
      | pose proof (Ke _ _ _ _ _ H _ _ (glu_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H)))) as H' ];
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
