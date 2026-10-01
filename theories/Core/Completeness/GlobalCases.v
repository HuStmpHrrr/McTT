(** * Every Well-Formed Global Context is Semantically Sound

    Every resolved global's type and body, and every parameter's type, is valid
    at [⋅] in the context itself: [global_induction] for the PER model, whose
    Kripke fundamental theorem is [ext_fundamental].  Hence the identity is a
    valid extension ([sem_ext_id]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Completeness Require Export ModuleCases.
From Mctt.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** Reading a judgment at the source off in a valid extension. *)
Lemma kread : forall Θ1 Ξ1 Θ2 Ξ2 A M,
    Θ1 ⍮ Ξ1 ⍮ ⋅ ⊢ M : A ->
    gc_ext Θ1 Ξ1 Θ2 Ξ2 -> ⊢g Θ2 ⍮ Ξ2 ->
    SG sem_valid Θ1 Ξ1 Θ2 Ξ2 -> SP sem_valid Θ1 Ξ1 Θ2 Ξ2 ->
    sem_valid Θ2 Ξ2 A M.
Proof.
  intros * HM He Hg HS HP; destruct ext_fundamental as (_ & Ke & _).
  destruct (Ke _ _ _ _ _ HM _ _ (sem_ext_of_raw _ _ _ _ He Hg HS HP)) as [_ H]; exact H.
Qed.

Theorem gctx_sem : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> SG sem_valid Θ Ξ Θ Ξ /\ SP sem_valid Θ Ξ Θ Ξ.
Proof. exact (global_induction sem_valid kread). Qed.

Corollary sem_ext_id : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> sem_ext Θ Ξ Θ Ξ.
Proof.
  intros * Hg; destruct (gctx_sem _ _ Hg) as [HS HP].
  apply sem_ext_of_raw; [ apply gc_ext_refl | assumption.. ].
Qed.
