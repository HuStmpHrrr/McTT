(** * Kripke Weakenings

    The gluing model is stable only under a sub-class of the weakenings of
    Section 2.2: those built from [↑] alone, with
    no lifting [q φ] under a binder.  These are the *Kripke* weakenings, written
    [Γ ⊢k φ : Δ].

    Two deviations from the rules a Kripke presentation would give, both
    inherited from the shape the gluing proofs need:

    - The rules recurse on the *codomain*, so the domain [Γ] is a parameter.
      Composition ([kripke_compose]) is then an induction on the *outer*
      weakening; recursing on the domain instead would ask for a strengthening
      lemma in that case, which the system does not have.
    - Both rules may coarsen their codomain by a refinement [{{ ⊢ Δ' ⊆ Δ }}],
      so the judgment is closed under [kripke_ctxsub] — which the subtyping
      cases need.  The price is that [Γ ⊢k φ : Δ] no longer implies
      [Γ ⊢w φ : Δ]: [wf_wk_lookup] demands a variable *lookup* in [Γ] at the
      very type [A⟨φ⟩], and refinement only gives a subtype of it.  So the
      escape lemma is [kripke_escape], landing in [wf_sub] via [ι]; it
      transports judgments just as well.

    The [wk_eq] premise is the slack the old explicit-substitution presentation
    got from stating the rules up to [≈]: it makes the judgment [Proper], so a
    weakening may be presented in any form pointwise equal to the canonical one.
    [kripke_shiftn] recovers that canonical form, [⇑^n]. *)

From Stdlib Require Import Morphisms.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CtxSub SystemOpt.
Import Syntax_Notations Wk_Notations.

Generalizable All Variables.

Reserved Notation "Γ ⊢k φ : Δ" (in custom judg at level 80, Γ custom exp, φ constr at level 60, Δ custom exp).

Inductive wk_kripke : ctx -> ctx -> wk -> Prop :=
| kwk_id :
  `( {{ ⊢ Γ ⊆ Δ }} ->
     wk_eq φ wk_id ->
     {{ Γ ⊢k φ : Δ }} )
| kwk_shift :
  `( {{ Γ ⊢k ψ : Δ' , A }} ->
     {{ ⊢ Δ' ⊆ Δ }} ->
     wk_eq φ (↑ ⊙ ψ) ->
     {{ Γ ⊢k φ : Δ }} )
where "Γ ⊢k φ : Δ" := (wk_kripke Γ Δ φ) (in custom judg) : type_scope.

#[export]
Hint Constructors wk_kripke : mctt.

#[export]
Instance wk_kripke_Proper Γ Δ : Proper (wk_eq ==> iff) (wk_kripke Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> {{ Γ ⊢k φ : Δ }} -> {{ Γ ⊢k ψ : Δ }}) as Himp.
  {
    intros φ ψ Heq H; destruct H; econstructor;
      try eassumption; (etransitivity; [ symmetry; eassumption | eassumption ]).
  }
  intros φ ψ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.
