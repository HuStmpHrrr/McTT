(** * Presupposition

    This file proves two of the three presupposition statements: the two sides
    of a term equation are well-typed terms, and the two sides of a refinement
    are types.  The third — that the type of a well-typed term is a type — needs
    no induction over equality and is [presup_exp_typ] in
    [Core.Syntactic.System.Lemmas].

    A presentation with a fixed [ℕ]-eliminator motive can prove all three
    simultaneously, before substitution equivalence.  Here the three are
    separated and these two come *after* it, because [wf_exp_eq_natrec_cong]
    lets the motive vary: the type of the equation is [A[Id ,, M]] while the
    right-hand side is naturally typed at [A'[Id ,, M']], and bridging those two
    is exactly [sub_eq_preserves_exp].  That statement is about typing
    derivations only, so it is provable directly by induction on [wf_exp] and
    does not need presupposition itself — which is what breaks the apparent
    circularity.

    None of the three statements needs a mutual induction:

    - [presup_exp_eq]'s [wf_exp_eq_subtyp] case gets [Ψ ⍮ Γ ⊢ A' : Type@i] from a
      premise rather than from [presup_subtyp];
    - [presup_subtyp]'s [wf_subtyp_refl] case calls the finished
      [presup_exp_eq].

    Both facts are consequences of the extra arguments that [Definitions]
    carries on those two rules for precisely this purpose.

    Of the sixteen rules for term equality, six need an argument of their own,
    and all six need it for the same reason: a congruence rule states its
    equation at the type built from the *left* premises, so the right-hand side
    has to be built by its own typing rule, at its own type, and then moved to
    the type of the equation by [wf_conv].  The remaining rules — including [η],
    whose right-hand side is [wf_fn_eta_expand] — are hints. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Tactics.
Import Syntax_Notations Wk_Notations.

(** ** The Two Sides of a Term Equation *)

Lemma presup_exp_eq : forall {Ψ Γ M M' A},
    Ψ ⍮ Γ ⊢ M ≈ M' : A ->
    Ψ ⍮ Γ ⊢ M : A /\ Ψ ⍮ Γ ⊢ M' : A.
Proof.
  induction 1; assert (⊢ Ψ ⍮ Γ) by mauto 2; destruct_conjs; split; mauto 3.

  (** [rec], right.  The motive varies, so the eliminator has to be built at
      [A'[Id ,, M']] and then transported twice: along [Id ,, M' ≈ Id ,, M] by
      [sub_eq_preserves_exp], and along [A' ≈ A] by [sub_preserves_wf]. *)
  - assert (⊢ Ψ ⍮ Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢s Id,,zero : Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢s Id,,M : Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢s Id,,M' : Γ ▹ ℕ) by mauto 2.
    assert (⊢ Ψ ⍮ Γ ▹ ℕ ▹ A) by mauto 2.
    assert (⊢ Ψ ⍮ Γ ▹ ℕ ▹ A') by mauto 2.
    assert (Ψ ⍮ Γ ▹ ℕ ▹ A ⊢s Wk ⨟ Wk,,succ #1 : Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ A[Id,,zero] ≈ A'[Id,,zero] : Type@i) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ MZ' : A'[Id,,zero]) by mauto 3.
    assert (Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ A[Wk ⨟ Wk,,succ #1] ≈ A'[Wk ⨟ Wk,,succ #1] : Type@i) by mauto 2.
    assert (Ψ ⍮ Γ ▹ ℕ ▹ A ⊢ MS' : A'[Wk ⨟ Wk,,succ #1]) by mauto 3.
    assert (Ψ ⍮ Γ ▹ ℕ ▹ A' ⊢s Id : Γ ▹ ℕ ▹ A) by mauto 3.
    assert (Ψ ⍮ Γ ▹ ℕ ▹ A' ⊢ MS' : A'[Wk ⨟ Wk,,succ #1]) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end : A'[Id,,M']) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ M' ≈ M : ℕ) by mauto 3.
    assert (Ψ ⍮ Γ ⊢s Id,,M' ≈ Id,,M : Γ ▹ ℕ) by mauto 3.
    assert (Ψ ⍮ Γ ⊢ A'[Id,,M'] ≈ A'[Id,,M] : Type@i) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ A'[Id,,M] ≈ A[Id,,M] : Type@i) by mauto 3.
    assert (Ψ ⍮ Γ ⊢ A[Id,,M] : Type@i) by mauto 2.
    eapply wf_conv; [ eassumption | eassumption | mauto 2 ].

  (** [Π], right.  Only the codomain has to move, and it moves by context
      conversion: [Γ ▹ A'] refines [Γ ▹ A]. *)
  - assert (Ψ ⍮ Γ ▹ A' ⊢s Id : Γ ▹ A) by mauto 3.
    mauto 3.

  (** [λ], right.  The codomain [B] is not the type of any premise, so its
      level is unrelated to [i] and the bridging equation [Π A' B ≈ Π A B] has
      to be assembled at the maximum of the two. *)
  - assert (Ψ ⍮ Γ ▹ A' ⊢s Id : Γ ▹ A) by mauto 3.
    assert (exists j, Ψ ⍮ Γ ▹ A ⊢ B : Type@j) as [j] by mauto 2 using presup_exp_typ.
    assert (Ψ ⍮ Γ ▹ A' ⊢ B : Type@j) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ λ A' M' : Π A' B) by mauto 3.
    assert (Ψ ⍮ Γ ⊢ A' : Type@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Ψ ⍮ Γ ▹ A' ⊢ B : Type@(max i j)) by mauto 2 using lift_exp_max_right.
    assert (Ψ ⍮ Γ ⊢ A' ≈ A : Type@(max i j)) by mauto 3 using lift_exp_eq_max_left.
    assert (Ψ ⍮ Γ ⊢ A : Type@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Ψ ⍮ Γ ▹ A ⊢ B : Type@(max i j)) by mauto 2 using lift_exp_max_right.
    assert (Ψ ⍮ Γ ⊢ Π A B : Type@(max i j)) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ Π A' B ≈ Π A B : Type@(max i j)) by mauto 3.
    eapply wf_conv; eassumption.

  (** application, right: the type is the codomain at the argument, and the
      arguments are equal. *)
  - assert (Ψ ⍮ Γ ⊢s Id,,N : Γ ▹ A) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ M' $ N' : B[Id,,N']) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ N' ≈ N : A) by mauto 3.
    assert (Ψ ⍮ Γ ⊢s Id,,N' ≈ Id,,N : Γ ▹ A) by mauto 3.
    assert (Ψ ⍮ Γ ⊢ B[Id,,N'] ≈ B[Id,,N] : Type@i) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ B[Id,,N] : Type@i) by mauto 2.
    eapply wf_conv; eassumption.

  (** [rec]-[succ], right.  The right-hand side is a double substitution, and
      the type it gets from [wf_exp] is the motive under the step
      substitution — which is the type of the equation only after
      [exp_sub_natrec_step]. *)
  - assert (⊢ Ψ ⍮ Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢s Id,,M : Γ ▹ ℕ) by mauto 2.
    assert (Ψ ⍮ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M]) by mauto 2.
    assert (Ψ ⍮ Γ ⊢s Id,,M,,rec M return A | zero -> MZ | succ -> MS end : Γ ▹ ℕ ▹ A) by mauto 3.
    assert (Ψ ⍮ Γ ⊢ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end]
              : A[Wk ⨟ Wk,,succ #1][Id,,M,,rec M return A | zero -> MZ | succ -> MS end]) as H' by mauto 2.
    rewrite exp_sub_natrec_step in H'; assumption.

  (** [δ], left.  The recorded type is a type because the body is typed at it. *)
  - assert (exists i, Ψ ⍮ Γ ⊢ A : Type@i) as [] by mauto 2 using presup_exp_typ.
    mauto 3.
Qed.

Corollary presup_exp_eq_left : forall {Ψ Γ M M' A},
    Ψ ⍮ Γ ⊢ M ≈ M' : A ->
    Ψ ⍮ Γ ⊢ M : A.
Proof.
  intros * H; apply presup_exp_eq in H; destruct_conjs; assumption.
Qed.

Corollary presup_exp_eq_right : forall {Ψ Γ M M' A},
    Ψ ⍮ Γ ⊢ M ≈ M' : A ->
    Ψ ⍮ Γ ⊢ M' : A.
Proof.
  intros * H; apply presup_exp_eq in H; destruct_conjs; assumption.
Qed.

#[export]
Hint Resolve presup_exp_eq_left presup_exp_eq_right : mctt.

(** ** The Two Sides of a Refinement

    A refinement holds between types at a *common* universe level, which is what
    makes the statement existential and its cases uniform: in each of them the
    two sides are types at levels that need not agree, and [lift_exp_common]
    raises both.  ([wf_subtyp_refl]'s case is where [presup_exp_eq] is used, and
    the only place it is needed.) *)

Lemma presup_subtyp : forall {Ψ Γ A A'},
    Ψ ⍮ Γ ⊢ A ⊆ A' ->
    exists i, Ψ ⍮ Γ ⊢ A : Type@i /\ Ψ ⍮ Γ ⊢ A' : Type@i.
Proof.
  induction 1; destruct_conjs; eapply lift_exp_common; mauto 2.
Qed.

Corollary presup_subtyp_left : forall {Ψ Γ A A'},
    Ψ ⍮ Γ ⊢ A ⊆ A' ->
    exists i, Ψ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * H; apply presup_subtyp in H; destruct_conjs; eexists; eassumption.
Qed.

#[export]
Hint Resolve presup_subtyp_left : mctt.

(** ** Saturating the Context, with Equality

    [gen_presup] extends [gen_core_presup] with the two statements above.  The
    equality case calls [gen_core_presup] on the left-hand typing it has just
    produced, so that [⊢ Ψ ⍮ Γ] and the type of the equation are added as well —
    which is what the corresponding tactic did when presupposition was one
    four-way conjunction. *)

Ltac gen_presup1 H :=
  match type of H with
  | ?Ψ ⍮ ?Γ ⊢ ?M ≈ ?M' : ?A =>
      let HM := fresh "HM" in
      let HM' := fresh "HM'" in
      pose proof presup_exp_eq H as [HM HM'];
      try gen_core_presup HM
  | ?Ψ ⍮ ?Γ ⊢ ?A ⊆ ?A' =>
      let i := fresh "i" in
      let HA := fresh "HA" in
      let HA' := fresh "HA'" in
      pose proof presup_subtyp H as [i [HA HA']];
      try gen_core_presup HA
  | wf_sub_eq _ _ _ _ _ =>
      (** The two projections of [wf_sub_eq]; see [saturate_sub_eq]. *)
      let Hσ := fresh "Hσ" in
      let Hσ' := fresh "Hσ'" in
      pose proof (wf_sub_eq_left _ _ _ _ _ H) as Hσ;
      pose proof (wf_sub_eq_right _ _ _ _ _ H) as Hσ'
  end.

Ltac gen_presup H := first [ gen_presup1 H | gen_core_presup H ].

Ltac gen_presups :=
  (on_all_hyp: fun H => gen_presup H);
  invert_wf_ctx;
  (on_all_hyp: fun H => gen_lookup_presup H);
  saturate_wk;
  saturate_sub;
  clear_dups.
