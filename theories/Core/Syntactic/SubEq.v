(** * Equivalent Substitutions Preserve Judgments

    The equality and subtyping halves, [sub_eq_preserves_exp_eq] and
    [sub_eq_preserves_subtyp].  The typing half is [sub_eq_preserves_exp] in
    [Core.Syntactic.System.Lemmas], because presupposition needs it.

    Since presupposition is available, these two are not inductions.  An
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
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
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

(** ** The Subtyping Half

    The subtyping judgment has no symmetry and no [Typeω@i] to hang an equation
    on, so the second step goes through [wf_subtyp_refl]: [sub_eq_preserves_exp]
    gives the equation between the two instances of the right-hand side, and
    reflexivity of refinement turns it into a refinement. *)

Lemma sub_eq_preserves_subtyp : forall Θ Ξ Γ Δ A A' σ σ',
    Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ'].
Proof.
  intros * ? H; saturate_sub_eq.
  assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A' : Typeω@i) as [i ?] by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A'[σ'] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A'[σ] ≈ A'[σ'] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A'[σ] ⊆ A'[σ']) by mauto 2.
  etransitivity; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_subtyp : mctt.

(** ** Equal Arguments Give Equal Instances

    The form in which the elimination rules use all of the above.
    [wf_sub_eq_extend] builds the equivalence and [sub_eq_preserves_exp]
    transports the type along it. *)

Corollary exp_eq_sub_eq_head : forall Θ Ξ Γ Δ A B M M' σ i,
    Θ ⍮ Ξ ⍮ Δ ▹ A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B[σ,,M] ≈ B[σ,,M'] : Typeω@i.
Proof.
  intros.
  assert (exists j, Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@j) as [j ?] by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M' : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ : Δ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢s σ,,M ≈ σ,,M' : Δ ▹ A) by mauto 2.
  eapply sub_eq_preserves_typ; eassumption.
Qed.

(** The instance at a single substitution, which is how the [ℕ]- and
    [Π]-eliminators state their types. *)
Corollary exp_eq_sub_eq_single : forall Θ Ξ Γ A B M M' i,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,M] ≈ B[Id,,M'] : Typeω@i.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A[Id]) by (rewrite exp_sub_id; assumption).
  eapply exp_eq_sub_eq_head; [ eassumption | mauto 2 | eassumption ].
Qed.

#[export]
Hint Resolve exp_eq_sub_eq_head exp_eq_sub_eq_single : mctt.
