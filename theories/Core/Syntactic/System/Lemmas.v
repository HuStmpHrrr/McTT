(** * Properties of the Judgments

    With substitution as a meta-level operation, the closure properties that an
    explicit-substitution presentation gets for free from the constructors of
    the substitution judgment have to be proved.  There are two groups:

    - the *algebraic* ones — that [wk_id], [↑], [wk_q], [_⊙_] and their
      substitution counterparts are well-typed;
    - the *transport* ones — that weakening and substitution preserve typing,
      term equality and subtyping ([wk_preserves_wf], [sub_preserves_wf],
      [sub_eq_preserves_exp]).

    The two groups are interleaved, because [wf_sub_q] needs
    [wk_preserves_wf]: it has to weaken the image of a substitution by one.
    The order below is therefore weakening typing, [wk_preserves_wf],
    substitution typing, [sub_preserves_wf].
 *)

From Stdlib Require Import Lia Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations Wk_Notations.

(** ** Basic Inversions and Presuppositions *)

Lemma ctx_lookup_lt : forall {Γ A x},
    {{ #x : A ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.

#[export]
Hint Resolve ctx_lookup_lt : mctt.

Lemma ctx_decomp : forall {Γ A},
    {{ ⊢ Γ , A }} ->
    {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  inversion 1; now eauto.
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }}.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

Corollary ctx_decomp_right : forall {Γ A}, {{ ⊢ Γ , A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

Lemma presup_exp_ctx : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_ctx : mctt.

Lemma presup_exp_eq_ctx : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

Lemma presup_subtyp_ctx : forall {Γ A B}, {{ Γ ⊢ A ⊆ B }} -> {{ ⊢ Γ }}.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_subtyp_ctx : mctt.

(** [wf_wk], [wf_sub] and [wf_sub_eq] carry the well-formedness of both
    contexts.  Rather than register the projections in [mctt] — which would let
    [eauto] chain them with the closure lemmas below and search for weakenings
    that do not exist — we saturate the context with them once, at the start of
    a proof that needs them. *)

Ltac saturate_wk :=
  match_by_head wf_wk ltac:(fun H => pose proof (wf_wk_dom _ _ _ H);
                                     pose proof (wf_wk_cod _ _ _ H));
  clear_dups.

Ltac saturate_sub :=
  match_by_head wf_sub ltac:(fun H => pose proof (wf_sub_dom _ _ _ H);
                                      pose proof (wf_sub_cod _ _ _ H));
  clear_dups.

(** ** Weakening Typing *)

Lemma wf_wk_id : forall Γ, {{ ⊢ Γ }} -> {{ Γ ⊢w wk_id : Γ }}.
Proof.
  intros; econstructor; try eassumption.
  intros; rewrite exp_wk_id; assumption.
Qed.

Lemma wf_wk_shift : forall Γ A, {{ ⊢ Γ , A }} -> {{ Γ , A ⊢w ↑ : Γ }}.
Proof.
  intros * H; econstructor; [ eassumption | mauto 2 | ].
  intros; simpl; mauto 2.
Qed.

(** The extra premise [Δ ⊢ A⟨φ⟩ : Type@i] is needed for [⊢ Δ , A⟨φ⟩], it is
    exactly what the induction hypothesis of [wk_preserves_wf] supplies at every
    binder, and [wf_sub_q] states the corresponding premise for substitutions
    explicitly. *)
Lemma wf_wk_q : forall Γ Δ φ A i,
    {{ Δ ⊢w φ : Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ ⊢ A⟨φ⟩ : Type@i }} ->
    {{ Δ , A⟨φ⟩ ⊢w wk_q φ : Γ , A }}.
Proof.
  intros * Hφ ? ?; saturate_wk.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x B Hlk.
  inversion Hlk; subst; simpl; rewrite exp_wk_shift_wk_q; econstructor.
  eapply wf_wk_lookup; eassumption.
Qed.

Lemma wf_wk_compose : forall Γ Δ Θ φ ψ,
    {{ Γ ⊢w ψ : Δ }} ->
    {{ Δ ⊢w φ : Θ }} ->
    {{ Γ ⊢w φ ⊙ ψ : Θ }}.
Proof.
  intros * Hψ Hφ; saturate_wk.
  econstructor; [ eassumption | eassumption | ].
  intros x B ?; simpl; rewrite <- exp_wk_wk.
  eapply wf_wk_lookup; [ eassumption | ].
  eapply wf_wk_lookup; eassumption.
Qed.

#[export]
Hint Resolve wf_wk_id wf_wk_shift wf_wk_q wf_wk_compose : mctt.

(** [ℕ] is closed, so lifting a weakening over a [ℕ] binder needs no premises.
    This is the shape the [ℕ]-eliminator rules present. *)
Corollary wf_wk_q_nat : forall Γ Δ φ,
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ , ℕ ⊢w wk_q φ : Γ , ℕ }}.
Proof.
  intros * Hφ; saturate_wk.
  apply (wf_wk_q Γ Δ φ {{{ ℕ }}} 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_wk_q_nat : mctt.

(** A weakening transports a variable by its defining property.  Registering
    this — rather than [wf_wk_lookup] itself — as a hint keeps [eauto] away from
    the record projection, whose conclusion is a bare [ctx_lookup] and would let
    the search wander. *)
Lemma wk_preserves_vlookup : forall Γ Δ φ x A,
    {{ Δ ⊢w φ : Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Δ ⊢ #(φ x) : A⟨φ⟩ }}.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

Lemma wk_preserves_vlookup_eq : forall Γ Δ φ x A,
    {{ Δ ⊢w φ : Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Δ ⊢ #(φ x) ≈ #(φ x) : A⟨φ⟩ }}.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

#[export]
Hint Resolve wk_preserves_vlookup wk_preserves_vlookup_eq : mctt.

(** ** Pushing an Operation Inwards

    Every type in an elimination rule is a substitution instance, so
    transporting a judgment along an operation produces a type with that
    operation on the *outside*, whereas the rule to be applied wants it on the
    inside.  [push_wk] alternates [simpl] — which distributes a weakening over
    the term formers — with the corollaries of [Substitution] that move it past
    a substitution.

    It has to normalise the induction hypotheses as well as the goal, and those
    are still universally quantified over the target context and the operation;
    plain [rewrite] does not descend under a binder, so [setoid_rewrite] is used
    throughout. *)

Ltac push_wk_step H :=
  first [ setoid_rewrite exp_wk_sub_extend in H
        | setoid_rewrite exp_wk_sub_extend2 in H
        | setoid_rewrite exp_wk_shift_wk_q in H ].

Ltac push_wk_in H :=
  try simpl in H; repeat (push_wk_step H; try simpl in H).

Ltac push_wk_goal :=
  try simpl;
  repeat (first [ setoid_rewrite exp_wk_sub_extend
                | setoid_rewrite exp_wk_sub_extend2
                | setoid_rewrite exp_wk_shift_wk_q ];
          try simpl).

(** The parentheses around [on_all_hyp:] are required, not cosmetic: its
    argument is parsed at [tactic4], which already includes [_ ; _], so an
    unparenthesised continuation is silently absorbed into the per-hypothesis
    tactic instead of running afterwards.  This is the spelling used throughout
    [Core.Completeness]. *)
Ltac push_wk :=
  (on_all_hyp: (fun H => try push_wk_in H));
  push_wk_goal.

(** ** Saturating with the Lifted Weakenings

    Every binder case of [wk_preserves_wf] needs the lifted weakening
    [Δ , A⟨φ⟩ ⊢w q φ : Γ , A] before the induction hypothesis for the body can
    be used.  It is derivable — [wf_wk_q] is a hint — but only from the
    induction hypothesis for the *domain*, so leaving it to [eauto] costs three
    extra levels of search on top of the rule application, which puts the wider
    cases ([λ]-E, [ℕ]-E) out of reach at any depth that terminates.  Adding
    each lifted weakening to the context up front costs one [assert] instead.

    [lift_wk_nat] seeds the [ℕ]-eliminator cases, whose first binder is over the
    closed type [ℕ]: [lift_wk_step] cannot start there, because the domain of
    that binder has no induction hypothesis of its own.  It is guarded by the
    presence of a motive [Γ , ℕ ⊢ A : Type@i] so that it fires only in those
    four cases. *)

Ltac lift_wk_nat :=
  match goal with
  | _ : wf_exp (cons a_nat ?Γ) (a_typ _) _, Hφ : wf_wk ?Δ ?Γ ?φ |- _ =>
      let T := constr:(wf_wk (cons a_nat Δ) (cons a_nat Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_wk_q_nat; exact Hφ)
  end.

Ltac lift_wk_step :=
  match goal with
  | Hφ : wf_wk ?Δ ?Γ ?φ,
    IH : forall _ _, wf_wk _ ?Γ _ -> wf_exp _ (a_typ _) (exp_wk ?A _) |- _ =>
      let T := constr:(wf_wk (cons (exp_wk A φ) Δ) (cons A Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_wk_q; [ exact Hφ | | exact (IH _ _ Hφ) ]; mauto 2)
  end.

Ltac lift_wk := repeat first [ lift_wk_nat | lift_wk_step ].

(** The successor branch of the [ℕ]-eliminator is typed at the motive under two
    binders, so its induction hypothesis produces [A[Wk⨟Wk,,succ #1]⟨q (q φ)⟩]
    where the rule wants [A⟨q φ⟩[Wk⨟Wk,,succ #1]].  [push_wk] cannot do this
    one: [exp_wk_sub_natrec] only applies to a *doubly lifted* weakening, and in
    the induction hypothesis the weakening is still universally quantified.  So
    we instantiate the hypothesis at the lifted weakening [lift_wk] built, and
    rewrite in the result. *)
Ltac lift_wk_natrec :=
  match goal with
  | IH : forall _ _, wf_wk _ (cons ?A (cons a_nat ?Γ)) _ -> _,
    Hq : wf_wk _ (cons ?A (cons a_nat ?Γ)) _ |- _ =>
      let H := fresh "HMS" in
      pose proof (IH _ _ Hq) as H;
      rewrite exp_wk_sub_natrec in H
  end.

(** ** Weakening Preserves the Judgments ([wk_preserves_wf]) *)

Lemma wk_preserves_wf :
  (forall Γ A M,
      {{ Γ ⊢ M : A }} ->
      forall Δ φ, {{ Δ ⊢w φ : Γ }} -> {{ Δ ⊢ M⟨φ⟩ : A⟨φ⟩ }}) /\
  (forall Γ A M M',
      {{ Γ ⊢ M ≈ M' : A }} ->
      forall Δ φ, {{ Δ ⊢w φ : Γ }} -> {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }}) /\
  (forall Γ A A',
      {{ Γ ⊢ A ⊆ A' }} ->
      forall Δ φ, {{ Δ ⊢w φ : Γ }} -> {{ Δ ⊢ A⟨φ⟩ ⊆ A'⟨φ⟩ }}).
Proof.
  apply syntactic_wf_mut_ind'; intros; saturate_wk; push_wk; lift_wk.
  (** With the weakenings pushed in and the lifted ones in the context, most
      cases are the corresponding rule applied to the induction hypotheses. *)
  all: try solve [ mauto 4 ].
  (** For the wider rules the rule application itself is what [eauto] does not
      reach in time, so we take that step by hand. *)
  all: try solve [ econstructor; mauto 3 ].
  (** What is left are exactly the four rules for the [ℕ]-eliminator. *)
  all: lift_wk_natrec; econstructor; mauto 2.
Qed.

Corollary wk_preserves_exp : forall Γ Δ A M φ,
    {{ Γ ⊢ M : A }} ->
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ ⊢ M⟨φ⟩ : A⟨φ⟩ }}.
Proof.
  pose proof wk_preserves_wf; intros; destruct_all; eauto.
Qed.

Corollary wk_preserves_exp_eq : forall Γ Δ A M M' φ,
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }}.
Proof.
  pose proof wk_preserves_wf; intros; destruct_all; eauto.
Qed.

Corollary wk_preserves_subtyp : forall Γ Δ A A' φ,
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ ⊢ A⟨φ⟩ ⊆ A'⟨φ⟩ }}.
Proof.
  pose proof wk_preserves_wf; intros; destruct_all; eauto.
Qed.

#[export]
Hint Resolve wk_preserves_exp wk_preserves_exp_eq wk_preserves_subtyp : mctt.

(** ** Reflexivity of Term Equality

    Reflexivity at a well-typed term is not a rule: every congruence rule of
    the equality judgment carries one premise per subterm, so reflexivity is an induction
    over typing.  (This is what the three congruence rules [wf_exp_eq_typ_cong],
    [wf_exp_eq_nat_cong] and [wf_exp_eq_zero_cong] are for; with explicit
    substitutions their instances were derivable from the [_sub] equations.)

    It is needed before [sub_preserves_wf], whose [Var] case for the equality judgment
    asks for [Γ ⊢ σ x ≈ σ x : A[σ]] at an arbitrary image of the substitution —
    something no congruence rule provides. *)

Lemma wf_exp_eq_refl : forall {Γ A M}, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof.
  induction 1; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_refl : mctt.

(** This is what lets [saturate_refl] and the [Proper] machinery of [LibTactics]
    see a well-typed term as a reflexive point of [≈]. *)
#[export]
Instance wf_exp_eq_per_elem Γ A : PERElem _ (wf_exp Γ A) (wf_exp_eq Γ A).
Proof.
  intros ? ?; mauto 2.
Qed.

(** Refinement is reflexive at a type.  [wf_subtyp_refl] asks for an equation,
    which for reflexivity is [wf_exp_eq_refl]; stating the composite is what lets
    a goal [Γ ⊢ A ⊆ A] be closed from a typing derivation in one step, which is
    how every inversion lemma's introduction case ends.  (Once presupposition is
    available, [Core.Syntactic.SystemOpt] drops the typing premise of
    [wf_subtyp_refl] outright; this lemma stays because going through that one
    costs a level of search that [mauto] cannot always spare.) *)
Lemma wf_subtyp_refl_typ : forall Γ A i, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A ⊆ A }}.
Proof.
  intros; eapply wf_subtyp_refl; mauto 2.
Qed.

#[export]
Hint Resolve wf_subtyp_refl_typ : mctt.

(** ** Substitution Typing *)

(** A weakening is a substitution.  An explicit-substitution presentation has
    no counterpart to this: there [⇑] is a substitution in its own right.  Here [Wk] is [ι ↑], so
    every rule whose type mentions [Wk] — the successor branch of the
    [ℕ]-eliminator, typed at [A[Wk⨟Wk,,succ #1]] — needs this bridge. *)
Lemma wf_sub_of_wk : forall Γ Δ φ,
    {{ Γ ⊢w φ : Δ }} ->
    {{ Γ ⊢s ^(ι φ) : Δ }}.
Proof.
  intros * Hφ; saturate_wk.
  econstructor; [ eassumption | eassumption | ].
  intros x A ?; simpl; rewrite exp_sub_of_wk; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_of_wk : mctt.

(** [wf_sub_id] and its companion for [Wk].  Both are the corresponding
    weakening lemma transported along [ι]; [sb_of_wk_id] and
    [sb_of_wk_shift] are equalities of the pointwise relation [sb_eq], so
    rewriting with them in a judgment goes through [wf_sub_Proper]. *)

Corollary wf_sub_id : forall Γ, {{ ⊢ Γ }} -> {{ Γ ⊢s Id : Γ }}.
Proof.
  intros; rewrite <- sb_of_wk_id; mauto 3.
Qed.

Corollary wf_sub_shift : forall Γ A, {{ ⊢ Γ , A }} -> {{ Γ , A ⊢s Wk : Γ }}.
Proof.
  intros; rewrite <- sb_of_wk_shift; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id wf_sub_shift : mctt.

(** [wf_sub_extend] *)
Lemma wf_sub_extend : forall Γ Δ σ A M i,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s σ ,, M : Δ , A }}.
Proof.
  intros * Hσ ? ?; saturate_sub.
  econstructor; [ eassumption | mauto 2 | ].
  intros x B Hlk.
  (** Both bindings of [Δ , A] are looked up at a type of the form [B⟨↑⟩], and
      [exp_sub_shift_extend] is precisely the statement that an
      extension is invisible to such a type. *)
  inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
    [ assumption | eapply wf_sub_apply; eassumption ].
Qed.

(** [wf_sub_single] *)
Corollary wf_sub_single : forall Γ A M i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id ,, M : Γ , A }}.
Proof.
  intros.
  eapply wf_sub_extend; [ mauto 3 | eassumption | rewrite exp_sub_id; eassumption ].
Qed.

(** [wf_sub_wk] *)
Lemma wf_sub_wk : forall Γ Γ' Δ σ φ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ' ⊢w φ : Γ }} ->
    {{ Γ' ⊢s ^(sb_wk σ φ) : Δ }}.
Proof.
  intros * Hσ Hφ; saturate_wk; saturate_sub.
  econstructor; [ eassumption | eassumption | ].
  intros x A ?; reduce_index; rewrite <- exp_wk_sub.
  eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
Qed.

(** [wf_sub_q].

    As in [wf_wk_q], the premise [Γ ⊢ A[σ] : Type@i] is taken explicitly.  It
    could be dropped once [sub_preserves_wf] is available; we keep it, because
    it is exactly what the induction hypothesis of [sub_preserves_wf] supplies
    at each binder, and dropping it would make [wf_sub_q] depend on
    [sub_preserves_wf], which depends on [wf_sub_q]. *)
Lemma wf_sub_q : forall Γ Δ σ A i,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A[σ] : Type@i }} ->
    {{ Γ , A[σ] ⊢s q σ : Δ , A }}.
Proof.
  intros * Hσ ? ?; saturate_sub.
  assert {{ ⊢ Γ , A[σ] }} by mauto 2.
  econstructor; [ eassumption | mauto 2 | ].
  intros x B Hlk.
  (** [exp_wk_shift_sub_q] at [n = 0] is what moves the [⟨↑⟩]
      of a lookup out through the lifted substitution. *)
  inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 2 | ].
  eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | mauto 2 ].
Qed.

#[export]
Hint Resolve wf_sub_extend wf_sub_single wf_sub_wk wf_sub_q : mctt.

(** [ℕ] is closed, so [ℕ[σ]] is [ℕ] by computation and lifting a substitution
    over a [ℕ] binder needs no premises.  Compare [wf_wk_q_nat]. *)
Corollary wf_sub_q_nat : forall Γ Δ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ , ℕ ⊢s q σ : Δ , ℕ }}.
Proof.
  intros * Hσ; saturate_sub.
  apply (wf_sub_q Γ Δ σ {{{ ℕ }}} 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_q_nat : mctt.

(** As with [wk_preserves_vlookup], it is these two rather than [wf_sub_apply]
    that go into [mctt]: the projection's conclusion mentions [σ x], which
    [eauto] would happily try to unify with any term at all. *)

Lemma sub_preserves_vlookup : forall Γ Δ σ x A,
    {{ Γ ⊢s σ : Δ }} ->
    {{ #x : A ∈ Δ }} ->
    {{ Γ ⊢ ^(σ x) : A[σ] }}.
Proof.
  intros; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_eq : forall Γ Δ σ x A,
    {{ Γ ⊢s σ : Δ }} ->
    {{ #x : A ∈ Δ }} ->
    {{ Γ ⊢ ^(σ x) ≈ ^(σ x) : A[σ] }}.
Proof.
  intros; apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
Qed.

#[export]
Hint Resolve sub_preserves_vlookup sub_preserves_vlookup_eq : mctt.

(** ** Pushing a Substitution Inwards

    The substitution counterpart of [push_wk].  Two differences from that
    tactic.

    - The single-substitution equation is [exp_sub_extend_comm],
      whose *right*-hand side is the unpushed form, so it is used backwards.
    - [sb_q] is [simpl never] — otherwise the laws about it could not be stated
      at all — so [simpl] leaves an application [q σ 0] behind, which the
      computation rule [sb_q_zero] finishes.  This comes up in the [η] rule,
      the only rule with a literal index under a binder. *)

Ltac push_sub_step H :=
  first [ setoid_rewrite exp_sub_sub_extend2 in H
        | setoid_rewrite <- exp_sub_extend_comm in H
        | setoid_rewrite exp_wk_shift_sub_q in H
        | setoid_rewrite sb_q_zero in H ].

Ltac push_sub_in H :=
  try simpl in H; repeat (push_sub_step H; try simpl in H).

Ltac push_sub_goal :=
  try simpl;
  repeat (first [ setoid_rewrite exp_sub_sub_extend2
                | setoid_rewrite <- exp_sub_extend_comm
                | setoid_rewrite exp_wk_shift_sub_q
                | setoid_rewrite sb_q_zero ];
          try simpl).

Ltac push_sub :=
  (on_all_hyp: (fun H => try push_sub_in H));
  push_sub_goal.

(** ** Saturating with the Lifted Substitutions

    Exactly the rôle [lift_wk] plays for [wk_preserves_wf]: [wf_sub_q] is a hint, but
    reconstructing a lifted substitution inside the [eauto] search costs three
    extra levels on top of the rule application, which the wider rules cannot
    afford.  One [assert] per binder instead. *)

Ltac lift_sub_nat :=
  match goal with
  | _ : wf_exp (cons a_nat ?Δ) (a_typ _) _, Hσ : wf_sub ?Γ ?Δ ?σ |- _ =>
      let T := constr:(wf_sub (cons a_nat Γ) (cons a_nat Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_q_nat; exact Hσ)
  end.

Ltac lift_sub_step :=
  match goal with
  | Hσ : wf_sub ?Γ ?Δ ?σ,
    IH : forall _ _, wf_sub _ ?Δ _ -> wf_exp _ (a_typ _) (exp_sub ?A _) |- _ =>
      let T := constr:(wf_sub (cons (exp_sub A σ) Γ) (cons A Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_q; [ exact Hσ | | exact (IH _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub := repeat first [ lift_sub_nat | lift_sub_step ].

(** The successor branch of the [ℕ]-eliminator again: its induction hypothesis
    produces [A[Wk⨟Wk,,succ #1][q (q σ)]] where the rule wants
    [A[q σ][Wk⨟Wk,,succ #1]].  [push_sub] cannot do it, because
    [exp_sub_sub_natrec] applies only to a doubly lifted substitution and in the
    hypothesis the substitution is still quantified.  So we instantiate at the
    lifted substitution [lift_sub] built and rewrite in the result. *)
Ltac lift_sub_natrec :=
  match goal with
  | IH : forall _ _, wf_sub _ (cons ?A (cons a_nat ?Δ)) _ -> _,
    Hq : wf_sub _ (cons ?A (cons a_nat ?Δ)) _ |- _ =>
      let H := fresh "HMS" in
      pose proof (IH _ _ Hq) as H;
      rewrite exp_sub_sub_natrec in H
  end.

(** ** Substitution Preserves the Judgments ([sub_preserves_wf]) *)

Lemma sub_preserves_wf :
  (forall Δ A M,
      {{ Δ ⊢ M : A }} ->
      forall Γ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M[σ] : A[σ] }}) /\
  (forall Δ A M M',
      {{ Δ ⊢ M ≈ M' : A }} ->
      forall Γ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M[σ] ≈ M'[σ] : A[σ] }}) /\
  (forall Δ A A',
      {{ Δ ⊢ A ⊆ A' }} ->
      forall Γ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ A[σ] ⊆ A'[σ] }}).
Proof.
  apply syntactic_wf_mut_ind'; intros; saturate_sub; push_sub; lift_sub.
  all: try solve [ mauto 4 ].
  all: try solve [ econstructor; mauto 3 ].
  all: lift_sub_natrec; econstructor; mauto 2.
Qed.

Corollary sub_preserves_exp : forall Γ Δ A M σ,
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] : A[σ] }}.
Proof.
  pose proof sub_preserves_wf; intros; destruct_all; eauto.
Qed.

Corollary sub_preserves_exp_eq : forall Γ Δ A M M' σ,
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M'[σ] : A[σ] }}.
Proof.
  pose proof sub_preserves_wf; intros; destruct_all; eauto.
Qed.

Corollary sub_preserves_subtyp : forall Γ Δ A A' σ,
    {{ Δ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  pose proof sub_preserves_wf; intros; destruct_all; eauto.
Qed.

#[export]
Hint Resolve sub_preserves_exp sub_preserves_exp_eq sub_preserves_subtyp : mctt.

(** [wf_sub_compose]: substitutions form a category over well-formed contexts.  The
    identity and associativity laws are [sb_compose_id_left],
    [sb_compose_id_right] and [sb_compose_assoc] in [Substitution]; this is the
    only part of the structure that needs the judgments. *)
Lemma wf_sub_compose : forall Γ Γ' Δ σ τ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ' ⊢s τ : Γ }} ->
    {{ Γ' ⊢s σ ⨟ τ : Δ }}.
Proof.
  intros * Hσ Hτ; saturate_sub.
  econstructor; [ eassumption | eassumption | ].
  intros x A ?; reduce_index; rewrite <- exp_sub_sub; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_compose : mctt.

(** The single substitution lemma, the form in which the elimination rules use
    all of the above. *)

Corollary exp_sub_single : forall Γ A B M N,
    {{ Γ , A ⊢ M : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M[Id ,, N] : B[Id ,, N] }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i ?] by mauto 3.
  eapply sub_preserves_exp; [ eassumption | eapply wf_sub_single; eassumption ].
Qed.

Corollary exp_eq_sub_single : forall Γ A B M M' N,
    {{ Γ , A ⊢ M ≈ M' : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M[Id ,, N] ≈ M'[Id ,, N] : B[Id ,, N] }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i ?] by mauto 3.
  eapply sub_preserves_exp_eq; [ eassumption | eapply wf_sub_single; eassumption ].
Qed.

#[export]
Hint Resolve exp_sub_single exp_eq_sub_single : mctt.

(** ** The Substitutions of the [ℕ]-Eliminator

    [wf_natrec] and its equations name three substitutions: the branches are
    typed at [Id ,, zero] and [Wk ⨟ Wk ,, succ #1], and the conclusion at
    [Id ,, M].  Each is well-typed as soon as its source context is, but getting
    there means recognising [ℕ] underneath an operation, which [eauto] will not
    do on its own — the same obstacle [wf_wk_q_nat] and [wf_sub_q_nat] address.
    These lemmas clear it once and for all, and are what the [ℕ] cases of
    presupposition are stated against. *)

Corollary wf_sub_nat_single : forall Γ M,
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢s Id ,, M : Γ , ℕ }}.
Proof.
  intros.
  assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
  eapply wf_sub_single; eassumption.
Qed.

Corollary wf_sub_zero : forall Γ,
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s Id ,, zero : Γ , ℕ }}.
Proof.
  intros; apply wf_sub_nat_single; mauto 2.
Qed.

(** [#1] is the [ℕ] of [Γ , ℕ , A]: the lookup derivation produces the type
    [ℕ⟨↑⟩⟨↑⟩], which is [ℕ] only up to computation. *)
Corollary ctx_lookup_nat_1 : forall Γ A, {{ #1 : ℕ ∈ Γ , ℕ , A }}.
Proof.
  intros.
  assert {{ #1 : ℕ⟨↑⟩⟨↑⟩ ∈ Γ , ℕ , A }} as H by mauto 2.
  exact H.
Qed.

(** The premise is context well-formedness rather than [{{ Γ , ℕ ⊢ A : Type@i }}]
    so that this applies at the motive of *either* side of a congruence. *)
Corollary wf_sub_natrec_step : forall Γ A,
    {{ ⊢ Γ , ℕ , A }} ->
    {{ Γ , ℕ , A ⊢s Wk ⨟ Wk ,, succ #1 : Γ , ℕ }}.
Proof.
  intros.
  assert {{ ⊢ Γ , ℕ }} by mauto 2.
  assert {{ Γ , ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ , ℕ , A ⊢s Wk : Γ , ℕ }} by mauto 2.
  assert {{ Γ , ℕ , A ⊢s Wk ⨟ Wk : Γ }} by mauto 2.
  assert {{ Γ , ℕ , A ⊢ succ #1 : ℕ }} by mauto 3 using ctx_lookup_nat_1.
  assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
  eapply wf_sub_extend; [ eassumption | eassumption | assumption ].
Qed.

#[export]
Hint Resolve wf_sub_nat_single wf_sub_zero wf_sub_natrec_step : mctt.

(** ** Context Conversion

    An explicit-substitution presentation needs two further inductive judgments
    for this — context subtyping [⊢ Δ ⊆ Γ] and context equivalence [⊢ Δ ≈ Γ] —
    each with a mutual induction of its own (this is what [Core.Syntactic.CtxSub]
    and [Core.Syntactic.CtxEq] used to be).  With substitution as an operation
    neither is needed: [Δ] refines [Γ] exactly when the *identity* substitution
    is well-typed from [Δ] to [Γ].  Indeed [wf_sub_apply] at [Id] says precisely
    that every binding of [Γ] is inhabited in [Δ] at the same type — up to
    subtyping, via [wf_exp_subtyp'] — because [A[Id]] is [A].  Transporting a
    judgment along a refinement is then [sub_preserves_wf] at [Id].

    So [{{ Δ ⊢s Id : Γ }}] is read "[Δ] refines [Γ]"; [wf_sub_id] is its
    reflexivity and [wf_sub_compose] its transitivity. *)

Corollary ctxsub_vlookup : forall Γ Δ x A,
    {{ Δ ⊢s Id : Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Δ ⊢ #x : A }}.
Proof.
  intros.
  assert {{ Δ ⊢ ^({{{ Id }}} x) : A[Id] }} as H' by mauto 2.
  rewrite exp_sub_id in H'; assumption.
Qed.

(** A lookup one binder in is a lookup weakened by [↑]; this is the shape the
    extension case below produces, and [eauto] cannot find it on its own because
    [#(S x)] has to be *recognised* as [#x⟨↑⟩] before [wk_preserves_exp]
    applies. *)
Corollary wk_preserves_vlookup_shift : forall Γ A B x i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ #x : B }} ->
    {{ Γ , A ⊢ #(S x) : B⟨↑⟩ }}.
Proof.
  intros.
  assert {{ ⊢ Γ , A }} by mauto 3.
  change {{{ #(S x) }}} with {{{ #x⟨↑⟩ }}}.
  mauto 3.
Qed.

Lemma wf_sub_id_extend : forall Γ Δ A A' i,
    {{ Δ ⊢s Id : Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ ⊢ A' : Type@i }} ->
    {{ Δ ⊢ A' ⊆ A }} ->
    {{ Δ , A' ⊢s Id : Γ , A }}.
Proof.
  intros * HId ? ? ?; saturate_sub.
  assert {{ ⊢ Δ , A' }} by mauto 2.
  assert {{ Δ , A' ⊢w ↑ : Δ }} by mauto 2.
  econstructor; [ eassumption | mauto 2 | ].
  intros x B Hlk.
  inversion Hlk; subst; reduce_index; rewrite exp_sub_id.
  - (** The top binding: [#0] has type [A'⟨↑⟩] there and [A'⟨↑⟩ ⊆ A⟨↑⟩] by
        weakening the given subtyping. *)
    eapply wf_exp_subtyp'; [ mauto 2 | ].
    eapply wk_preserves_subtyp; eassumption.
  - eapply wk_preserves_vlookup_shift; [ eassumption | ].
    eapply ctxsub_vlookup; eassumption.
Qed.

(** Equal types give refinements in both directions; this is the instance
    [wf_sub_eq] and the presupposition lemma need. *)
Corollary wf_sub_id_extend_eq : forall Γ A A' i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A' ⊢s Id : Γ , A }}.
Proof.
  intros.
  eapply wf_sub_id_extend; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id_extend wf_sub_id_extend_eq : mctt.

Corollary ctxsub_exp : forall Γ Δ A M,
    {{ Δ ⊢s Id : Γ }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Δ ⊢ M : A }}.
Proof.
  intros.
  assert {{ Δ ⊢ M[Id] : A[Id] }} as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_exp_eq : forall Γ Δ A M M',
    {{ Δ ⊢s Id : Γ }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ⊢ M ≈ M' : A }}.
Proof.
  intros.
  assert {{ Δ ⊢ M[Id] ≈ M'[Id] : A[Id] }} as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_subtyp : forall Γ Δ A A',
    {{ Δ ⊢s Id : Γ }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Δ ⊢ A ⊆ A' }}.
Proof.
  intros.
  assert {{ Δ ⊢ A[Id] ⊆ A'[Id] }} as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

#[export]
Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_subtyp : mctt.

(** ** Transporting a Type

    [Type@i] is closed, so [Type@i⟨φ⟩] and [Type@i[σ]] are [Type@i] — but only
    up to conversion, and [eauto]'s [simple apply] does not reduce.  These four
    spell it out; every "and the type is still a type" step below goes through
    one of them. *)

Corollary wk_preserves_typ : forall Γ Δ A φ i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ ⊢ A⟨φ⟩ : Type@i }}.
Proof.
  intros.
  assert (wf_exp Δ (exp_wk (a_typ i) φ) (exp_wk A φ)) by mauto 2.
  assumption.
Qed.

Corollary wk_preserves_typ_eq : forall Γ Δ A A' φ i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Δ ⊢w φ : Γ }} ->
    {{ Δ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Δ (exp_wk (a_typ i) φ) (exp_wk A φ) (exp_wk A' φ)) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ : forall Γ Δ A σ i,
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
  intros.
  assert (wf_exp Γ (exp_sub (a_typ i) σ) (exp_sub A σ)) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ_eq : forall Γ Δ A A' σ i,
    {{ Δ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_sub (a_typ i) σ) (exp_sub A σ) (exp_sub A' σ)) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve wk_preserves_typ wk_preserves_typ_eq
             sub_preserves_typ sub_preserves_typ_eq : mctt.

(** ** Lifting without the Extra Premise

    Now that [wk_preserves_wf] and [sub_preserves_wf] are available, the already-transported type
    premise of [wf_wk_q] and [wf_sub_q] is redundant: it *is* the conclusion of
    [wk_preserves_typ], respectively [sub_preserves_typ].  This is the
    simplification anticipated in the remark on [wf_sub_q].
    We supersede the original hints, as [Definitions] does for the subtyping
    rules. *)

Corollary wf_wk_q' : forall Γ Δ φ A i,
    {{ Δ ⊢w φ : Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ , A⟨φ⟩ ⊢w wk_q φ : Γ , A }}.
Proof.
  intros; eapply wf_wk_q; mauto 2.
Qed.

Corollary wf_sub_q' : forall Γ Δ σ A i,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ , A[σ] ⊢s q σ : Δ , A }}.
Proof.
  intros; eapply wf_sub_q; mauto 2.
Qed.

#[export]
Hint Resolve wf_wk_q' wf_sub_q' : mctt.
#[export]
Remove Hints wf_wk_q wf_sub_q : mctt.

(** ** Cumulativity

    With subtyping in the system these are no longer rules, but they are
    derivable, and the presupposition lemma needs them to put two types at a
    common universe. *)

Lemma wf_cumu : forall Γ A i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A : Type@(S i) }}.
Proof.
  intros; eapply wf_exp_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

Lemma wf_exp_eq_cumu : forall Γ A A' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@(S i) }}.
Proof.
  intros; eapply wf_exp_eq_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_subtyp_ge : forall {Γ i j},
    {{ ⊢ Γ }} ->
    i <= j ->
    {{ Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
  induction 2; mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma lift_exp_ge : forall Γ A i j,
    i <= j ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A : Type@j }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma lift_exp_eq_ge : forall Γ A A' i j,
    i <= j ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
Hint Resolve lift_exp_ge lift_exp_eq_ge : mctt.

Corollary lift_exp_max_left : forall Γ A i j,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A : Type@(max i j) }}.
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_max_right : forall Γ A i j,
    {{ Γ ⊢ A : Type@j }} ->
    {{ Γ ⊢ A : Type@(max i j) }}.
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_left : forall Γ A A' i j,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max i j) }}.
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_right : forall Γ A A' i j,
    {{ Γ ⊢ A ≈ A' : Type@j }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max i j) }}.
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

(** Transitivity across two different levels. *)
Lemma exp_eq_trans_typ_max : forall {Γ i i' A A' A''},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A' ≈ A'' : Type@i' }} ->
    {{ Γ ⊢ A ≈ A'' : Type@(max i i') }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i i') }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ ⊢ A' ≈ A'' : Type@(max i i') }} by eauto using lift_exp_eq_max_right; mautosolve 4.
Qed.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

(** Two types are always types at a *common* level.  Stating it in this form —
    with the level existentially quantified rather than spelled [max i j] — is
    what lets a proof reach it with [eapply] and leave both levels to
    unification, which is the only way to use cumulativity in a case whose level
    variables the induction named for us. *)
Corollary lift_exp_common : forall Γ A A' i j,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A' : Type@j }} ->
    exists k, {{ Γ ⊢ A : Type@k }} /\ {{ Γ ⊢ A' : Type@k }}.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** [wf_pi] checks the domain and the codomain at the *same* level, which is
    almost never how they arrive: the domain's level comes from its own premise
    and the codomain's from presupposition.  This is the form that takes them as
    they come.  It is a hint, and the level it produces is a [max] of two evars,
    so it only fires where the level of the [Π]-type is still open — which is
    exactly where the strict [wf_pi] cannot fire at all. *)
Corollary wf_pi_max : forall Γ A B i j,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ , A ⊢ B : Type@j }} ->
    {{ Γ ⊢ Π A B : Type@(max i j) }}.
Proof.
  intros.
  eapply wf_pi; [ eapply lift_exp_max_left | eapply lift_exp_max_right ]; eassumption.
Qed.

#[export]
Hint Resolve wf_pi_max : mctt.

(** [lift_exp_common] for the two components of a [Π]-type, which do not live in
    the same context and so are not two instances of it.  Every rule that
    mentions a [Π]-type checks both components at one level, and this is what
    supplies that level when they arrive at two. *)
Corollary lift_exp_pi_common : forall Γ A B i j,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ , A ⊢ B : Type@j }} ->
    exists k, {{ Γ ⊢ A : Type@k }} /\ {{ Γ , A ⊢ B : Type@k }}.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** ** Types in a Well-formed Context

    Every binding of a well-formed context is a type *in that context*: the
    weakening carried by [ctx_lookup] is exactly what makes this so. *)

Lemma ctx_lookup_wf : forall Γ x A,
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros * HΓ.
  induction 1; inversion_clear HΓ;
    [ | assert (exists i, {{ Γ ⊢ A : Type@i }}) as [] by eauto ];
    eexists; mauto 4.
Qed.

#[export]
Hint Resolve ctx_lookup_wf : mctt.

(** ** Presupposition for Typing

    The type of a well-typed term is itself a type.  Unlike the two companion
    statements — [presup_exp_eq] and [presup_subtyp], which live in
    [Core.Syntactic.Presup] — this one needs no mutual induction and nothing
    from substitution equivalence: the only case that is not immediate is
    [wf_exp_subtyp], and its second premise *is* the conclusion.

    In the elimination rules the type is a substitution instance, so the work is
    to produce the substitution; the [ℕ]-eliminator's is [wf_sub_nat_single] and
    the application's is [wf_sub_single], both hints.  ([λ] is the case that needs
    the domain and the codomain at a common level, and [wf_pi_max] is the hint
    that supplies it.) *)

Lemma presup_exp_typ : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  induction 1; assert {{ ⊢ Γ }} by mauto 2; destruct_conjs; mauto 3.
  (** [rec]: the type is the motive at [Id ,, M]. *)
  - eexists; mauto 3.
  (** application: the type is the codomain at [Id ,, N]. *)
  - eexists; mauto 3.
Qed.

Corollary presup_exp : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros; split; mauto 2 using presup_exp_typ.
Qed.

(** ** Context Conversion of Substitutions

    [Γ' ⊢s Id : Γ] transports substitutions too: compose with the inclusion and
    cancel the identity.  Which side it goes on is what distinguishes the two:
    [ctxsub_sub] refines the domain, [ctxsub_sub_cod] coarsens the codomain. *)

Corollary ctxsub_sub : forall Γ Γ' Δ σ,
    {{ Γ' ⊢s Id : Γ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ' ⊢s σ : Δ }}.
Proof.
  intros.
  rewrite <- (sb_compose_id_right σ); mauto 2.
Qed.

Corollary ctxsub_sub_cod : forall Γ Γ' Δ σ,
    {{ Γ ⊢s Id : Γ' }} ->
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ ⊢s σ : Γ' }}.
Proof.
  intros.
  rewrite <- (sb_compose_id_left σ); mauto 2.
Qed.

#[export]
Hint Resolve ctxsub_sub : mctt.

(** * Substitution Equivalence

    The closure properties below are the [wf_sub_eq] counterparts of
    [wf_sub_id]–[wf_sub_q].  Note the asymmetry: [Γ ⊢s σ ≈ σ' : Δ]
    equates the images at [A[σ]], so getting symmetry and transitivity needs to
    know that [A[σ]] and [A[σ']] are equal types.  That is
    [sub_eq_preserves_exp], which is why it comes first and why the [PER] instance comes last. *)

Lemma wf_sub_eq_refl : forall Γ Δ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
  intros; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_refl : mctt.

Lemma sub_eq_preserves_vlookup : forall Γ Δ σ σ' x A,
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ #x : A ∈ Δ }} ->
    {{ Γ ⊢ ^(σ x) ≈ ^(σ' x) : A[σ] }}.
Proof.
  intros; eapply wf_sub_eq_apply; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_vlookup : mctt.

(** [saturate_sub_eq] plays the role [saturate_sub] does for [sub_preserves_wf]: it
    injects the two typing components of every substitution equivalence in
    context, so that all the [mauto] calls below can reach them. *)

Ltac saturate_sub_eq :=
  match_by_head wf_sub_eq ltac:(fun H => pose proof (wf_sub_eq_left _ _ _ _ H);
                                         pose proof (wf_sub_eq_right _ _ _ _ H));
  clear_dups;
  saturate_sub.

Corollary ctxsub_sub_eq : forall Γ Γ' Δ σ σ',
    {{ Γ' ⊢s Id : Γ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ' ⊢s σ ≈ σ' : Δ }}.
Proof.
  intros * ? H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?.
  eapply ctxsub_exp_eq; mauto 2.
Qed.

#[export]
Hint Resolve ctxsub_sub_eq : mctt.

(** The tempting justification of the second component is
    "[sub_preserves_exp_eq] applied to reflexivity", which does not give it:
    [sub_preserves_wf] transports along a *single* substitution and so only
    yields [A[σ] ≈ A[σ]].  The equation really comes from [sub_eq_preserves_exp],
    which is proved by an induction that appeals to this lemma.  We break the
    cycle by taking the equation as a premise; that is precisely what the
    induction hypothesis for the domain supplies at every use site. *)

Lemma wf_sub_eq_q : forall Γ Δ σ σ' A i,
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }} ->
    {{ Γ , A[σ] ⊢s q σ ≈ q σ' : Δ , A }}.
Proof.
  intros * H ? ?; saturate_sub_eq.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[σ'] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ , A[σ] }} by mauto 2.
  assert {{ Γ , A[σ] ⊢w ↑ : Γ }} by mauto 2.
  econstructor; [ mauto 2 | | ].
  - eapply ctxsub_sub; [ eapply wf_sub_id_extend_eq; mauto 2 | mauto 2 ].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 3 | ].
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_q : mctt.

Corollary wf_sub_eq_q_nat : forall Γ Δ σ σ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ , ℕ ⊢s q σ ≈ q σ' : Δ , ℕ }}.
Proof.
  intros * H; saturate_sub_eq.
  apply (wf_sub_eq_q Γ Δ σ σ' {{{ ℕ }}} 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_nat : mctt.

Lemma wf_sub_eq_extend : forall Γ Δ σ σ' A M M' i,
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ M' : A[σ'] }} ->
    {{ Γ ⊢ M ≈ M' : A[σ] }} ->
    {{ Γ ⊢s σ ,, M ≈ σ' ,, M' : Δ , A }}.
Proof.
  intros * H ? ? ? ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x B Hlk.
  inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
    [ assumption | eapply wf_sub_eq_apply; eassumption ].
Qed.

(** The instance every elimination rule needs: two single substitutions of
    equal terms.  Stating it separately is what keeps [exp_sub_id] out of the
    call sites, which would otherwise have to rewrite [A[Id]] to [A] three
    times over. *)
Corollary wf_sub_eq_id_extend : forall Γ A M M' i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id ,, M ≈ Id ,, M' : Γ , A }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  apply (wf_sub_eq_extend Γ Γ sb_id sb_id A M M' i);
    [ mauto 3 | assumption
    | rewrite exp_sub_id; assumption
    | rewrite exp_sub_id; assumption
    | rewrite exp_sub_id; assumption ].
Qed.

Lemma wf_sub_eq_wk : forall Γ Γ' Δ σ σ' φ,
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ' ⊢w φ : Γ }} ->
    {{ Γ' ⊢s ^(sb_wk σ φ) ≈ ^(sb_wk σ' φ) : Δ }}.
Proof.
  intros * H ?; saturate_wk; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_wk_sub.
  eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_extend wf_sub_eq_id_extend wf_sub_eq_wk : mctt.

(** ** Equivalent Substitutions Preserve Typing

    This is about *typing* derivations only, so it is a plain induction on
    [wf_exp]: the subtyping premise of [wf_exp_subtyp] is discharged by
    [sub_preserves_subtyp] rather than by an induction hypothesis.  This matters
    for the order of the development.  Because McTT's [wf_exp_eq_natrec_cong]
    lets the motive vary — with a fixed motive this would not arise — the
    presupposition lemma needs to move a type along an equivalence of
    substitutions, i.e. it needs this lemma.  Its counterparts for equality and
    subtyping ([sub_eq_preserves_exp_eq], [sub_eq_preserves_subtyp]) in turn
    need presupposition for the symmetry case, and so come after it, in
    [Core.Syntactic.SubEq]. *)

Ltac lift_sub_eq_nat :=
  match goal with
  | _ : wf_exp (cons a_nat ?Δ) (a_typ _) _, Hσ : wf_sub_eq ?Γ ?Δ ?σ ?σ' |- _ =>
      let T := constr:(wf_sub_eq (cons a_nat Γ) (cons a_nat Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_eq_q_nat; exact Hσ)
  end.

Ltac lift_sub_eq_step :=
  match goal with
  | Hσ : wf_sub_eq ?Γ ?Δ ?σ ?σ',
    IH : forall _ _ _, wf_sub_eq _ ?Δ _ _ -> wf_exp_eq _ (a_typ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(wf_sub_eq (cons (exp_sub A σ) Γ) (cons A Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_eq_q; [ exact Hσ | | exact (IH _ _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub_eq := repeat first [ lift_sub_eq_nat | lift_sub_eq_step ].

(** [saturate_sub_typ] and [saturate_sub_eq_IH] are the counterparts of
    [push_sub]/[lift_sub] for the equivalence induction: the first transports
    every type premise along every substitution in context, the second
    instantiates every induction hypothesis at every substitution equivalence in
    context.  Together they leave all the premises of the congruence rule
    literally in the context, so that the search never has to guess a domain
    type through an evar. *)

Ltac saturate_sub_typ :=
  repeat match goal with
  | H : wf_exp ?Δ (a_typ ?i) ?A, Hσ : wf_sub ?Γ ?Δ ?σ |- _ =>
      let T := constr:(wf_exp Γ (a_typ i) (exp_sub A σ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply sub_preserves_typ; eassumption)
  end.

Ltac saturate_sub_eq_IH :=
  repeat match goal with
  | IH : forall _ _ _, wf_sub_eq _ ?Δ _ _ -> _, Hσ : wf_sub_eq _ ?Δ _ _ |- _ =>
      let T := type of (IH _ _ _ Hσ) in
      assert_fails (assert T by assumption);
      pose proof (IH _ _ _ Hσ)
  end.

(** [exp_sub_sub_natrec] cannot join the [push_sub] set — it rewrites in the
    opposite direction from [exp_sub_extend_comm] and the two together would
    loop.  It is applied once, at the end, to the instantiated hypotheses. *)

Ltac reduce_sub_natrec :=
  (on_all_hyp: (fun H => try setoid_rewrite exp_sub_sub_natrec in H)).

Lemma sub_eq_preserves_exp : forall Δ A M,
    {{ Δ ⊢ M : A }} ->
    forall Γ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ Γ ⊢ M[σ] ≈ M[σ'] : A[σ] }}.
Proof.
  induction 1; intros; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
    saturate_sub_typ; saturate_sub_eq_IH; reduce_sub_natrec.
  all: mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_preserves_exp : mctt.

Corollary sub_eq_preserves_typ : forall Γ Δ A σ σ' i,
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_sub (a_typ i) σ) (exp_sub A σ) (exp_sub A σ')) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_typ : mctt.

(** ** Substitution Equivalence is a PER

    Both directions need to move an image from [A[σ]] to [A[σ']], which is what
    [sub_eq_preserves_typ] and [ctx_lookup_wf] together provide. *)

Lemma wf_sub_eq_sym : forall Γ Δ σ σ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢s σ' ≈ σ : Δ }}.
Proof.
  intros * H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A Hlk.
  assert (exists i, {{ Δ ⊢ A : Type@i }}) as [i ?] by mauto 2.
  assert {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }} by mauto 2.
  eapply wf_exp_eq_subtyp';
    [ symmetry; eapply wf_sub_eq_apply; eassumption | mauto 3 ].
Qed.

Lemma wf_sub_eq_trans : forall Γ Δ σ σ' σ'',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢s σ' ≈ σ'' : Δ }} ->
    {{ Γ ⊢s σ ≈ σ'' : Δ }}.
Proof.
  intros * H1 H2; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A Hlk.
  assert (exists i, {{ Δ ⊢ A : Type@i }}) as [i ?] by mauto 2.
  assert {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ ^(σ' x) ≈ ^(σ'' x) : A[σ] }} by
    (eapply wf_exp_eq_subtyp'; [ eapply wf_sub_eq_apply; eassumption | mauto 4 ]).
  etransitivity; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

#[export]
Instance wf_sub_eq_PER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_per_elem Γ Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros ? ?; mauto 2.
Qed.

(** [sb_eq] is not a Leibniz equality, so a pointwise rearrangement of a
    substitution — [sb_compose_assoc] and its kin — has to be turned into a
    judgmental one before it can be used on a judgment that is not [Proper] for
    it, such as a gluing predicate. *)
Lemma wf_sub_eq_of_sb_eq : forall Γ Δ σ σ',
    {{ Γ ⊢s σ : Δ }} ->
    sb_eq σ σ' ->
    {{ Γ ⊢s σ ≈ σ' : Δ }}.
Proof.
  intros * ? Heq.
  econstructor; [ eassumption | now rewrite <- Heq | ].
  intros x A ?; rewrite <- (Heq x); mauto 2.
Qed.

(** ** Composition of Equivalent Substitutions

    The two one-sided halves are [sub_preserves_exp_eq] and
    [sub_eq_preserves_exp] respectively; the full congruence is their
    composite. *)

Lemma wf_sub_eq_compose_left : forall Γ Γ' Δ σ σ' τ,
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ' ⊢s τ : Γ }} ->
    {{ Γ' ⊢s σ ⨟ τ ≈ σ' ⨟ τ : Δ }}.
Proof.
  intros * H ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_sub_sub.
  eapply sub_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

Lemma wf_sub_eq_compose_right : forall Γ Γ' Δ σ τ τ',
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ' ⊢s τ ≈ τ' : Γ }} ->
    {{ Γ' ⊢s σ ⨟ τ ≈ σ ⨟ τ' : Δ }}.
Proof.
  intros * ? H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_sub_sub.
  eapply sub_eq_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
Qed.

Corollary wf_sub_eq_compose : forall Γ Γ' Δ σ σ' τ τ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ' ⊢s τ ≈ τ' : Γ }} ->
    {{ Γ' ⊢s σ ⨟ τ ≈ σ' ⨟ τ' : Δ }}.
Proof.
  intros * H1 H2; saturate_sub_eq.
  etransitivity;
    [ eapply wf_sub_eq_compose_left; [ eassumption | eassumption ]
    | eapply wf_sub_eq_compose_right; [ eassumption | eassumption ] ].
Qed.

#[export]
Hint Resolve wf_sub_eq_compose_left wf_sub_eq_compose_right wf_sub_eq_compose : mctt.

(** ** η-Expansion

    The right-hand side of [wf_exp_eq_fn_eta] is well-typed at the same type as
    the left.  Getting there is entirely a matter of moving between the two
    descriptions of a weakened [Π]-type: [(Π A B)⟨↑⟩] *is* [Π A⟨↑⟩ B⟨q ↑⟩], but
    only by computation, so [eauto] cannot see it and the step is taken by hand.
    The application's type is [B⟨q ↑⟩[Id ,, #0]], which is [B] by
    [exp_wk_q_shift_single]: lifting a weakening and then substituting the top
    variable for it is the identity. *)

Lemma wf_fn_eta_expand : forall Γ A B M i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ , A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ λ A (M⟨↑⟩ #0) : Π A B }}.
Proof.
  intros.
  assert {{ ⊢ Γ , A }} by mauto 3.
  assert {{ Γ , A ⊢w ↑ : Γ }} by mauto 2.
  assert (wf_exp {{{ Γ , A }}} (exp_wk {{{ Π A B }}} ↑) (exp_wk M ↑)) as H'
      by (eapply wk_preserves_exp; eassumption).
  assert {{ Γ , A ⊢ M⟨↑⟩ : Π A⟨↑⟩ B⟨wk_q ↑⟩ }} by exact H'.
  assert {{ Γ , A ⊢ A⟨↑⟩ : Type@i }} by (eapply wk_preserves_typ; eassumption).
  assert {{ Γ , A ⊢ #0 : A⟨↑⟩ }} by mauto 3.
  assert {{ Γ , A , A⟨↑⟩ ⊢ B⟨wk_q ↑⟩ : Type@i }}
      by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
  assert {{ Γ , A ⊢ M⟨↑⟩ #0 : B⟨wk_q ↑⟩[Id ,, #0] }} by (eapply wf_app; eassumption).
  rewrite exp_wk_q_shift_single in *.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_fn_eta_expand : mctt.

(** ** Closed Neutrals

    A neutral's head is a variable, and the empty context has none. *)

Lemma no_closed_neutral : forall {A} {W : ne},
    ~ {{ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head ctx_lookup.
Qed.

#[export]
Hint Resolve no_closed_neutral : mctt.

(** ** Conversion

    The rules the system would have had before subtyping was added: subsumption
    specialised to an equation.  They come last because, registered as hints,
    they let [eauto] change the type of a goal at will — which is what the
    presupposition proof needs on almost every case, and what the proofs above
    are deliberately kept free of. *)

Lemma wf_conv : forall Γ M A A' i,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros; mauto 3.
Qed.

Lemma wf_exp_eq_conv : forall Γ M M' A A' i,
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros; mauto 3.
Qed.

#[export]
Hint Resolve wf_conv wf_exp_eq_conv : mctt.
