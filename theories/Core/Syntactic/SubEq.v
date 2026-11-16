(** * Equivalent Substitutions Preserve Judgments

    The equality half, [sub_eq_preserves_exp_eq].  The typing half is
    [sub_eq_preserves_exp] in [Core.Syntactic.System.Lemmas], because
    presupposition needs it.

    Since presupposition is available, this is not an induction.  An
    equivalence [σ ≈ σ'] is both a pair of substitutions and a relation between
    them, so it can be used twice:

    - transport the judgment along [σ] alone, by [sub_preserves_wf];
    - move its right-hand side from [σ] to [σ'], by [sub_eq_preserves_exp]
      applied to the typing derivation of that right-hand side, which
      presupposition provides;
    - compose.

    No particular rule enters the argument. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Presup.
Import Syntax_Notations Wk_Notations.

(** ** The Equality Half *)

Lemma sub_eq_preserves_exp_eq : forall Θ Ξ Γ Δ A M M' σ σ',
    Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ].
Proof.
  intros * ? H; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ M' : A) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ] : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M'[σ] ≈ M'[σ'] : A[σ]) by mauto 2.
  etransitivity; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_exp_eq : mctt.
