(** * The Fundamental Theorem of the Gluing Model, at One Global Context

    [soundness_fundamental] ([KripkeCases.v]) states every judgment of a
    global context in the gluing model, along every sound embedding.  A
    well-formed global context embeds soundly into itself ([gctx_glu]); at
    that embedding the gluing judgments are the gluing relations at the
    global context, as the corollaries below state them for contexts and
    terms.  There is no part for substitutions, since the gluing model has
    no substitution judgment, and none for equalities, since the model
    relates a term to a value rather than two terms to each other. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import ModuleCases GlobalGlu.
From Mctt.Core.Soundness Require Export LogicalRelation KripkeCases.
Import Domain_Notations Fixed_Notations.

Section soundness_fundamental.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma glu_msub_id_gc : ⊢ᵍ gc_deps ⍮ gc_stack -> glu_emb gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (gctx_glu _ _). Qed.

  Corollary soundness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊩ Γ.
  Proof.
    intros * H; destruct soundness_fundamental as (Kc & _).
    pose proof (Kc _ _ _ H _ _ (glu_msub_id_gc (ctx_wf_gctx _ _ _ H))) as H'; destruct GC; exact H'.
  Qed.

  Corollary soundness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊩ M : A.
  Proof.
    intros * H; destruct soundness_fundamental as (_ & Ke & _).
    pose proof (Ke _ _ _ _ _ H _ _ (glu_msub_id_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H)))) as H'; destruct GC; exact H'.
  Qed.
End soundness_fundamental.

#[export]
Hint Resolve soundness_fundamental_ctx soundness_fundamental_exp : mctt.
