(** * Every Well-Formed Global Context Glues

    [global_induction] for the gluing model, whose Kripke fundamental theorem
    is [kglu_fundamental]: every resolved global's type and body, and every
    parameter's type, glues at [⋅] in the context itself.  Hence the identity is
    a glued extension ([glu_ext_id]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Soundness Require Export ModuleCases.
Import Syntax_Notations GlobalCtx_Notations.

Theorem gctx_glu : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> SG glu_valid Θ Ξ Θ Ξ /\ SP glu_valid Θ Ξ Θ Ξ.
Proof. exact (global_induction glu_valid kglu_read). Qed.

Corollary glu_ext_id : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> glu_ext Θ Ξ Θ Ξ.
Proof.
  intros * Hg; destruct (gctx_glu _ _ Hg) as [HS HP].
  apply glu_ext_of_raw; [ apply gc_ext_refl | assumption.. ].
Qed.
