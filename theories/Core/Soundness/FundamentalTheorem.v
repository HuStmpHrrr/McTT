(** * The Fundamental Theorem of the Gluing Model

    In two parts: contexts and terms.  The substitution conjunct is gone with
    the [⊩s] judgment, and the equality
    judgments never had one — the gluing model relates a term to a value, not two
    terms to each other. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  NatCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
From Mctt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Section soundness_fundamental.
  Theorem soundness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}).
  Proof.
    apply syntactic_wf_ctx_exp_mut_ind; mauto 3.
  Qed.

  #[local]
  Ltac solve_it := pose proof soundness_fundamental; firstorder.

  Theorem soundness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}.
  Proof. solve_it. Qed.
End soundness_fundamental.

#[export]
Hint Resolve soundness_fundamental_ctx soundness_fundamental_exp : mctt.
