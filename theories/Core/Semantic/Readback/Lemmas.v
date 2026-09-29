From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

  Lemma functional_read : forall Θ Ξ,
    (forall s m M1,
        Rnf m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
        forall M2,
          Rnf m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
          M1 = M2) /\
      (forall s m M1,
          Rne m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rne m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2) /\
      (forall s m M1,
          Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2).
  Proof.
    intros Θ Ξ; apply read_mut_ind; intros; progressive_inversion; (functional_eval_rewrite_clear; f_equal; solve [eauto]).
  Qed.

  Corollary functional_read_nf : forall Θ Ξ s m M1 M2,
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (functional_read Θ Ξ); firstorder.
  Qed.

  Lemma functional_read_ne : forall Θ Ξ s m M1 M2,
      Rne m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rne m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (functional_read Θ Ξ); firstorder.
  Qed.

  Lemma functional_read_typ : forall Θ Ξ s m M1 M2,
      Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (functional_read Θ Ξ); firstorder.
  Qed.

#[export]
Hint Resolve functional_read_nf functional_read_ne functional_read_typ : mctt.

Ltac functional_read_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_read equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (Rnf ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rnf ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rne ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rne ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rtyp ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rtyp ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_read_rewrite_clear := repeat functional_read_rewrite_clear1.
