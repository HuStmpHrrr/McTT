(** * Every Well-Formed Global Context Glues

    [global_induction] for the gluing model, whose sound substitutions are
    [glu_msub]: every resolved global's generalized type and body, and every
    parameter's type, glues at [⋅] in the context itself. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Soundness Require Export ModuleCases.
Import Syntax_Notations GlobalCtx_Notations.

Theorem gctx_glu : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> glu_rwf_raw Θ Ξ /\ glu_pwf_raw Θ Ξ.
Proof. exact (global_induction glu_valid (fun Θ1 Ξ1 Θ2 Ξ2 μ => glu_msub Θ1 Ξ1 Θ2 Ξ2 μ nil) glu_msub_emb kglu_read). Qed.
