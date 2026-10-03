(** * Kripke Weakenings

    The gluing model is stable only under a subclass of the weakenings: those
    built from [↑] alone, past entries of any kind, with no lifting [q φ]
    under a binder. These are the Kripke weakenings, written [Γ ⊢k φ : Δ].

    The rules differ from a standard Kripke presentation in two ways, both to
    fit the gluing proofs:

    - The rules recurse on the codomain, so the domain [Γ] is a parameter.
      Composition ([kripke_compose]) is then an induction on the outer
      weakening; recursing on the domain would need a strengthening lemma,
      which the system does not have.
    - Both rules may coarsen their codomain by a refinement [Δ' ⊆ Δ], so the
      judgment is closed under [kripke_ctxsub], which the subtyping cases
      need. As a consequence [Γ ⊢k φ : Δ] does not imply [Γ ⊢w φ : Δ]:
      [wf_wk_lookup] demands a variable lookup in [Γ] at exactly [A[φ]ʷ], and
      refinement only gives a subtype of it. The escape lemma is therefore
      [kripke_escape], which lands in [wf_sub] via [ι].

    The [wk_eq] premise makes the judgment [Proper]: a weakening may be
    presented in any form pointwise equal to the canonical one, [⇑^n], which
    [kripke_shiftn] recovers. *)

From Stdlib Require Import Morphisms.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CtxSub SystemOpt.
From Mctt.Core.Semantic Require Export Fixed.
Import Syntax_Notations Wk_Notations Fixed_Notations.

Generalizable All Variables.

Reserved Notation "Γ ⊢k φ : Δ" (at level 70, φ constr at level 60, Δ at level 69).

Section Fixed_GCtx.
  Context {GC : GCtx}.

Inductive wk_kripke : ctx -> ctx -> wk -> Prop :=
| kwk_id :
  `( Γ ⊆ Δ ->
     wk_eq φ wk_id ->
     Γ ⊢k φ : Δ )
| kwk_shift :
  `( Γ ⊢k ψ : e :: Δ' ->
     Δ' ⊆ Δ ->
     wk_eq φ (↑ ⊙ ψ) ->
     Γ ⊢k φ : Δ )
where "Γ ⊢k φ : Δ" := (wk_kripke Γ Δ φ) : type_scope.

Hint Constructors wk_kripke : mctt.

#[local] Instance wk_kripke_Proper Γ Δ : Proper (wk_eq ==> iff) (wk_kripke Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> Γ ⊢k φ : Δ -> Γ ⊢k ψ : Δ) as Himp.
  {
    intros φ ψ Heq H; destruct H; econstructor;
      try eassumption; (etransitivity; [ symmetry; eassumption | eassumption ]).
  }
  intros φ ψ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

End Fixed_GCtx.

Notation "Γ ⊢k φ : Δ" := (wk_kripke Γ Δ φ) : type_scope.
#[export]
Hint Constructors wk_kripke : mctt.
#[export] Existing Instance wk_kripke_Proper.
