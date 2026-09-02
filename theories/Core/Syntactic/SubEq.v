(** * Equivalent Substitutions Preserve Judgments

    The equality and subtyping halves, [sub_eq_preserves_exp_eq] and
    [sub_eq_preserves_subtyp].  The typing half is [sub_eq_preserves_exp] in
    [Core.Syntactic.System.Lemmas], where it has to be, because presupposition
    needs it.

    Proving all three by one mutual induction on the derivation, case by case, is
    unavoidable if they come *before* presupposition.  In the order this
    development uses — typing, then presupposition, then the rest — these two are
    not inductions at all.  An equivalence [σ ≈ σ'] is both a pair of
    substitutions and a relation between them, so it can always be used twice:

    - transport the judgment along [σ] alone, by [sub_preserves_wf];
    - move its right-hand side from [σ] to [σ'], by [sub_eq_preserves_exp]
      applied to that right-hand side — which is a *typing* derivation, and is exactly what
      presupposition provides;
    - compose.

    Nothing about any particular rule enters, so the fifteen cases a direct
    induction works through (β for [Π], both β rules for [ℕ], η, and the
    congruences) all disappear.  This is the one place where having presupposition first pays for
    the extra arguments [Definitions] carries to get it. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Presup.
Import Syntax_Notations Wk_Notations.

(** ** The Equality Half *)

Lemma sub_eq_preserves_exp_eq : forall Γ Δ A M M' σ σ',
    Δ ⊢ M ≈ M' : A ->
    Γ ⊢s σ ≈ σ' : Δ ->
    Γ ⊢ M[σ] ≈ M'[σ'] : A[σ].
Proof.
  intros * ? H; saturate_sub_eq.
  assert (Δ ⊢ M' : A) by mauto 2.
  assert (Γ ⊢ M[σ] ≈ M'[σ] : A[σ]) by mauto 2.
  assert (Γ ⊢ M'[σ] ≈ M'[σ'] : A[σ]) by mauto 2.
  etransitivity; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_exp_eq : mctt.

(** ** The Subtyping Half

    The subtyping judgment has no symmetry and no [Type@i] to hang an equation
    on, so the second step goes through [wf_subtyp_refl]: [sub_eq_preserves_exp]
    gives the equation between the two instances of the right-hand side, and
    reflexivity of refinement turns it into a refinement. *)

Lemma sub_eq_preserves_subtyp : forall Γ Δ A A' σ σ',
    Δ ⊢ A ⊆ A' ->
    Γ ⊢s σ ≈ σ' : Δ ->
    Γ ⊢ A[σ] ⊆ A'[σ'].
Proof.
  intros * ? H; saturate_sub_eq.
  assert (exists i, Δ ⊢ A' : Type@i) as [i ?] by mauto 2.
  assert (Γ ⊢ A[σ] ⊆ A'[σ]) by mauto 2.
  assert (Γ ⊢ A'[σ'] : Type@i) by mauto 2.
  assert (Γ ⊢ A'[σ] ≈ A'[σ'] : Type@i) by mauto 2.
  assert (Γ ⊢ A'[σ] ⊆ A'[σ']) by mauto 2.
  etransitivity; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_subtyp : mctt.

(** ** Equal Arguments Give Equal Instances

    The form in which the elimination rules use all of the above.
    [wf_sub_eq_extend] builds the equivalence and [sub_eq_preserves_exp]
    transports the type along it. *)

Corollary exp_eq_sub_eq_head : forall Γ Δ A B M M' σ i,
    Δ ▹ A ⊢ B : Type@i ->
    Γ ⊢s σ : Δ ->
    Γ ⊢ M ≈ M' : A[σ] ->
    Γ ⊢ B[σ,,M] ≈ B[σ,,M'] : Type@i.
Proof.
  intros.
  assert (exists j, Δ ⊢ A : Type@j) as [j ?] by mauto 3.
  assert (Γ ⊢ M : A[σ]) by mauto 2.
  assert (Γ ⊢ M' : A[σ]) by mauto 2.
  assert (Γ ⊢s σ ≈ σ : Δ) by mauto 2.
  assert (Γ ⊢s σ,,M ≈ σ,,M' : Δ ▹ A) by mauto 2.
  eapply sub_eq_preserves_typ; eassumption.
Qed.

(** The instance at a single substitution, which is how the [ℕ]- and
    [Π]-eliminators state their types. *)
Corollary exp_eq_sub_eq_single : forall Γ A B M M' i,
    Γ ▹ A ⊢ B : Type@i ->
    Γ ⊢ M ≈ M' : A ->
    Γ ⊢ B[Id,,M] ≈ B[Id,,M'] : Type@i.
Proof.
  intros.
  assert (⊢ Γ) by mauto 3.
  assert (Γ ⊢ M ≈ M' : A[Id]) by (rewrite exp_sub_id; assumption).
  eapply exp_eq_sub_eq_head; [ eassumption | mauto 2 | eassumption ].
Qed.

#[export]
Hint Resolve exp_eq_sub_eq_head exp_eq_sub_eq_single : mctt.
