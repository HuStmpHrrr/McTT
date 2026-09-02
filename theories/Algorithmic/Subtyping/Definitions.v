From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (at level 70, A at level 69, A' at level 69).
Reserved Notation "⊢anf A ⊆ A'" (at level 70, A at level 69, A' at level 69).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall A A',
    not_univ_pi A ->
    A = A' ->
    ⊢anf A ⊆ A'
| asnf_univ : forall i j,
    i <= j ->
    ⊢anf Typeⁿ@i ⊆ Typeⁿ@j
| asnf_pi : forall A B A' B',
    A = A' ->
    ⊢anf B ⊆ B' ->
    ⊢anf Πⁿ A B ⊆ Πⁿ A' B'
where "⊢anf A ⊆ A'" := (alg_subtyping_nf A A') : type_scope.

Inductive alg_subtyping : ctx -> typ -> typ -> Prop :=
| alg_subtyp_run : forall Γ A B A' B',
    nbe_ty Γ A A' ->
    nbe_ty Γ B B' ->
    ⊢anf A' ⊆ B' ->
    Γ ⊢a A ⊆ B
where "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) : type_scope.

#[export]
Hint Constructors alg_subtyping_nf alg_subtyping: mctt.
