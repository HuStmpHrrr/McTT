(** * Properties of the Judgments

    Substitution is a meta-level operation, so its closure properties are
    lemmas rather than rules.  There are two groups:

    - the algebraic ones: [wk_id], [↑], [wk_q], [_⊙_] and their substitution
      counterparts are well-typed;
    - the transport ones: weakening and substitution preserve typing, term
      equality and subtyping ([wk_preserves_wf], [sub_preserves_wf],
      [sub_eq_preserves_exp]).

    The two groups are interleaved, because [wf_sub_q] needs
    [wk_preserves_wf]: it has to weaken the image of a substitution by one.
    The order below is therefore weakening typing, [wk_preserves_wf],
    substitution typing, [sub_preserves_wf].
 *)

From Stdlib Require Import Lia Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Scoping.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Basic Inversions and Presuppositions *)

Lemma ctx_lookup_lt : forall {Γ A x},
    Γ ∋ #x : A ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.

#[export]
Hint Resolve ctx_lookup_lt : mctt.

(** The variable rules look up in the local context extended by the parameters
    in scope; a lookup in the local context is one of those. *)
Lemma ctx_lookup_app_l : forall {Γ Δ A x},
    Γ ∋ #x : A ->
    Γ ++ Δ ∋ #x : A.
Proof.
  induction 1; cbn; constructor; assumption.
Qed.

#[export]
Hint Resolve ctx_lookup_app_l : mctt.

(** [wf_ctx_extend] carries no context premise, so [⊢ Γ] is not an inversion of
    the context judgment but a presupposition of typing.  These come first, each
    by an induction that reads it off whichever premise is stated at [Γ];
    [ctx_decomp] is a consequence. *)

Lemma presup_exp_ctx : forall {Θ Ξ Γ M A}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_ctx : mctt.

Lemma presup_exp_eq_ctx : forall {Θ Ξ Γ M M' A}, Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

Lemma presup_subtyp_ctx : forall {Θ Ξ Γ A B}, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_subtyp_ctx : mctt.

Lemma ctx_decomp : forall {Θ Ξ Γ A},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  inversion 1; eauto using presup_exp_ctx.
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Θ Ξ Γ A}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

Corollary ctx_decomp_right : forall {Θ Ξ Γ A}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

Lemma ctx_decomp_def : forall {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  inversion 1; eauto using presup_exp_ctx.
Qed.

Corollary ctx_decomp_def_left : forall {Θ Ξ Γ A M}, ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * ?%ctx_decomp_def; easy.
Qed.

Corollary ctx_decomp_def_typ : forall {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * ?%ctx_decomp_def; easy.
Qed.

Corollary ctx_decomp_def_body : forall {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * ?%ctx_decomp_def; easy.
Qed.

#[export]
Hint Resolve ctx_decomp_def_left ctx_decomp_def_typ ctx_decomp_def_body : mctt.

(** The tail of a well-formed context, whatever its head. *)
Corollary ctx_decomp_tail : forall {Θ Ξ Γ e}, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * H; destruct e; eauto using ctx_decomp_left, ctx_decomp_def_left.
Qed.

#[export]
Hint Resolve ctx_decomp_tail : mctt.

(** [wf_wk], [wf_sub] and [wf_sub_eq] carry the well-formedness of both
    contexts.  Rather than register the projections in [mctt] — which would let
    [eauto] chain them with the closure lemmas below and search for weakenings
    that do not exist — we saturate the context with them once, at the start of
    a proof that needs them. *)

Ltac saturate_wk :=
  match_by_head wf_wk ltac:(fun H => pose proof (wf_wk_dom _ _ _ _ _ H);
                                     pose proof (wf_wk_cod _ _ _ _ _ H));
  clear_dups.

Ltac saturate_sub :=
  match_by_head wf_sub ltac:(fun H => pose proof (wf_sub_dom _ _ _ _ _ H);
                                      pose proof (wf_sub_cod _ _ _ _ _ H));
  clear_dups.

(** ** Weakening Typing *)

Lemma wf_wk_id : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢w wk_id : Γ.
Proof.
  intros; econstructor; try eassumption;
    intros; rewrite !exp_wk_id; assumption.
Qed.

Lemma wf_wk_shift : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Θ ⍮ Ξ ⍮ e :: Γ ⊢w ↑ : Γ.
Proof.
  intros * H; econstructor; [ eassumption | mauto 2 | |];
    intros; simpl; mauto 2.
Qed.

(** The extra premise [Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Type@i] is needed for [⊢ Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ], it is
    exactly what the induction hypothesis of [wk_preserves_wf] supplies at every
    binder, and [wf_sub_q] states the corresponding premise for substitutions
    explicitly. *)
Lemma wf_wk_q : forall Θ Ξ Γ Δ φ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢w wk_q φ : Γ ▹ A.
Proof.
  intros * Hφ ? ?; saturate_wk.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x B Hlk; simpl in Hlk.
    inversion Hlk; subst; simpl; rewrite exp_wk_shift_wk_q; econstructor.
    eapply wf_wk_lookup; eassumption.
  - intros x B N Hlk.
    inversion Hlk; subst; simpl; rewrite !exp_wk_shift_wk_q; econstructor.
    eapply wf_wk_lookup_def; eassumption.
Qed.

(** The same over a definition: the body is weakened along with its type. *)
Lemma wf_wk_q_def : forall Θ Ξ Γ Δ φ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ ->
    Θ ⍮ Ξ ⍮ Δ ▸ A[φ]ʷ ≔ M[φ]ʷ ⊢w wk_q φ : Γ ▸ A ≔ M.
Proof.
  intros * Hφ ? ? ? ?; saturate_wk.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x B Hlk; simpl in Hlk.
    inversion Hlk; subst; simpl; rewrite exp_wk_shift_wk_q;
      econstructor.
    eapply wf_wk_lookup; eassumption.
  - intros x B N Hlk.
    inversion Hlk; subst; simpl; rewrite !exp_wk_shift_wk_q; econstructor.
    eapply wf_wk_lookup_def; eassumption.
Qed.

Lemma wf_wk_compose : forall Θ Ξ Γ Δ Δ' φ ψ,
    Θ ⍮ Ξ ⍮ Γ ⊢w ψ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢w φ ⊙ ψ : Δ'.
Proof.
  intros * Hψ Hφ; saturate_wk.
  econstructor; [ eassumption | eassumption | |].
  - intros x B ?; simpl; rewrite <- exp_wk_wk.
    eapply wf_wk_lookup; [ eassumption | ].
    eapply wf_wk_lookup; eassumption.
  - intros x B N ?; simpl; rewrite <- !exp_wk_wk.
    eapply wf_wk_lookup_def; [ eassumption | ].
    eapply wf_wk_lookup_def; eassumption.
Qed.

#[export]
Hint Resolve wf_wk_id wf_wk_shift wf_wk_q wf_wk_q_def wf_wk_compose : mctt.

(** [ℕ] is closed, so lifting a weakening over a [ℕ] binder needs no premises.
    This is the shape the [ℕ]-eliminator rules present. *)
Corollary wf_wk_q_nat : forall Θ Ξ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ▹ ℕ ⊢w wk_q φ : Γ ▹ ℕ.
Proof.
  intros * Hφ; saturate_wk.
  apply (wf_wk_q Θ Ξ Γ Δ φ ℕ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_wk_q_nat : mctt.

(** The same for [⊥], the binder of the [⊥]-eliminator's motive. *)
Corollary wf_wk_q_False : forall Θ Ξ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ▹ ⊥ ⊢w wk_q φ : Γ ▹ ⊥.
Proof.
  intros * Hφ; saturate_wk.
  apply (wf_wk_q Θ Ξ Γ Δ φ ⊥ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_wk_q_False : mctt.

(** A weakening transports a variable by its defining property.  Registering
    this — rather than [wf_wk_lookup] itself — as a hint keeps [eauto] away from
    the record projection, whose conclusion is a bare [ctx_lookup] and would let
    the search wander. *)
Lemma wk_preserves_vlookup : forall Θ Ξ Γ Δ φ x A,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #(φ x) : A[φ]ʷ.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

Lemma wk_preserves_vlookup_eq : forall Θ Ξ Γ Δ φ x A,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #(φ x) ≈ #(φ x) : A[φ]ʷ.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

(** δ moved along a weakening: the image of a definition is the same
    definition. *)
Lemma wk_preserves_vlookup_def : forall Θ Ξ Γ Δ φ x A M,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Γ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #(φ x) ≈ M[φ]ʷ : A[φ]ʷ.
Proof.
  intros * Hφ ?; saturate_wk.
  eapply wf_exp_eq_var_delta; [ eassumption | eapply wf_wk_lookup_def; eassumption ].
Qed.

#[export]
Hint Resolve wk_preserves_vlookup wk_preserves_vlookup_eq wk_preserves_vlookup_def : mctt.

(** ** Pushing an Operation Inwards

    Every type in an elimination rule is a substitution instance, so
    transporting a judgment along an operation produces a type with that
    operation on the outside, whereas the rule to be applied wants it on the
    inside.  [push_wk] alternates [simpl] — which distributes a weakening over
    the term formers — with the corollaries of [Substitution] that move it past
    a substitution.

    It has to normalise the induction hypotheses as well as the goal, and those
    are still universally quantified over the target context and the operation;
    plain [rewrite] does not descend under a binder, so [setoid_rewrite] is used
    throughout. *)

(** What a global resolves to is closed in a well-formed context
    ([wf_gc_resolve_closed]), so an operation on it vanishes, and the transported
    type and the type the rule wants coincide.  It is a separate tactic rather
    than part of the sets below, because it applies in three cases only. *)

Ltac saturate_closed :=
  repeat match goal with
  | Hc : ⊢ ?Θ ⍮ ?Ξ ⍮ _, Hl : gc_resolve ?Θ ?Ξ _ = Some (ge_def _ _ ?A _) |- _ =>
      assert_fails (assert (exp_scoped 0 A) by eassumption);
      pose proof (wf_gc_resolve_type_closed _ _ _ _ _ _ _ _ Hc Hl)
  | Hc : ⊢ ?Θ ⍮ ?Ξ ⍮ _, Hl : gc_resolve ?Θ ?Ξ _ = Some (ge_def _ _ _ (Some ?M)) |- _ =>
      assert_fails (assert (exp_scoped 0 M) by eassumption);
      pose proof (wf_gc_resolve_body_closed _ _ _ _ _ _ _ _ Hc Hl)
  end.

Ltac push_closed :=
  saturate_closed;
  repeat match goal with
  | Hc : exp_scoped 0 ?X |- context [ exp_wk ?X ?φ ] => rewrite (exp_closed_wk X φ Hc)
  | Hc : exp_scoped 0 ?X |- context [ exp_sub ?X ?σ ] => rewrite (exp_closed_sub X σ Hc)
  end.

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
    tactic instead of running afterwards. *)
Ltac push_wk :=
  (on_all_hyp: (fun H => try push_wk_in H));
  push_wk_goal.

(** ** Saturating with the Lifted Weakenings

    Every binder case of [wk_preserves_wf] needs the lifted weakening
    [Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢w q φ : Γ ▹ A] before the induction hypothesis for the body can
    be used.  It is derivable — [wf_wk_q] is a hint — but only from the
    induction hypothesis for the domain, so leaving it to [eauto] costs three
    extra levels of search on top of the rule application, which puts the wider
    cases ([λ]-E, [ℕ]-E) out of reach at any depth that terminates.  Adding
    each lifted weakening to the context up front costs one [assert] instead.

    [lift_wk_nat] seeds the [ℕ]-eliminator cases, whose first binder is over the
    closed type [ℕ]: [lift_wk_step] cannot start there, because the domain of
    that binder has no induction hypothesis of its own.  It is guarded by the
    presence of a motive [Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i] so that it fires only in those
    four cases.  Its second branch does the same for the motive
    [Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Type@i] of the [⊥]-eliminator. *)

Ltac lift_wk_nat :=
  match goal with
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_nat) ?Γ) (a_typ _) _, Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ |- _ =>
      let T := constr:(wf_wk Θ Ξ (cons (ce_ass a_nat) Δ) (cons (ce_ass a_nat) Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_wk_q_nat; exact Hφ)
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Γ) (a_typ _) _, Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ |- _ =>
      let T := constr:(wf_wk Θ Ξ (cons (ce_ass a_False) Δ) (cons (ce_ass a_False) Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_wk_q_False; exact Hφ)
  end.

Ltac lift_wk_step :=
  match goal with
  | Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ,
    IH : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_wk ?A _) |- _ =>
      let T := constr:(wf_wk Θ Ξ (cons (ce_ass (exp_wk A φ)) Δ) (cons (ce_ass A) Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_wk_q; [ exact Hφ | | exact (IH _ _ Hφ) ]; mauto 2)
  end.

(** The lifted weakening over a definition, for the let rules.  It is built only
    where an induction hypothesis lives in the extended context. *)
Ltac lift_wk_def :=
  match goal with
  | Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ,
    _ : forall _ _, wf_wk ?Θ ?Ξ _ (cons (ce_def ?A ?M) ?Γ) _ -> _,
    IHA : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_wk ?A _),
    IHM : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (exp_wk ?A _) (exp_wk ?M _) |- _ =>
      let T := constr:(wf_wk Θ Ξ (cons (ce_def (exp_wk A φ) (exp_wk M φ)) Δ) (cons (ce_def A M) Γ) (wk_q φ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_wk_q_def; [ exact Hφ | | | exact (IHA _ _ Hφ) | exact (IHM _ _ Hφ) ]; mauto 2)
  end.

Ltac lift_wk := repeat first [ lift_wk_nat | lift_wk_step | lift_wk_def ].

(** The successor branch of the [ℕ]-eliminator is typed at the motive under two
    binders, so its induction hypothesis produces [A[Wk⨟Wk,,succ #1][q (q φ)]ʷ]
    where the rule wants [A[q φ]ʷ[Wk⨟Wk,,succ #1]].  [push_wk] cannot do this
    one: [exp_wk_sub_natrec] only applies to a doubly lifted weakening, and in
    the induction hypothesis the weakening is still universally quantified.  So
    we instantiate the hypothesis at the lifted weakening [lift_wk] built, and
    rewrite in the result. *)
Ltac lift_wk_natrec :=
  match goal with
  | IH : forall _ _, wf_wk _ _ _ (cons (ce_ass ?A) (cons (ce_ass a_nat) ?Γ)) _ -> _,
    Hq : wf_wk _ _ _ (cons (ce_ass ?A) (cons (ce_ass a_nat) ?Γ)) _ |- _ =>
      let H := fresh "HMS" in
      pose proof (IH _ _ Hq) as H;
      rewrite exp_wk_sub_natrec in H
  end.

(** ** Weakening Preserves the Judgments ([wk_preserves_wf]) *)

Lemma wk_preserves_wf :
  (forall Θ Ξ Γ A M,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ) /\
  (forall Θ Ξ Γ A M M',
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) /\
  (forall Θ Ξ Γ A A',
      Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ).
Proof.
  apply syntactic_wf_mut_ind'; intros; saturate_wk; push_wk; lift_wk.
  (** The [a_glob] cases: the recorded type is closed, so the operation on it
      disappears, and the rule applies at the type the induction hypothesis
      gives. *)
  all: try solve [ push_closed; mauto 3 ].
  (** With the weakenings pushed in and the lifted ones in the context, most
      cases are the corresponding rule applied to the induction hypotheses. *)
  all: try solve [ mauto 4 ].
  (** For the wider rules the rule application itself is what [eauto] does not
      reach in time, so we take that step by hand. *)
  all: try solve [ econstructor; mauto 3 ].
  (** What is left are exactly the four rules for the [ℕ]-eliminator. *)
  all: lift_wk_natrec; econstructor; mauto 2.
Qed.

Corollary wk_preserves_exp : forall Θ Ξ Γ Δ A M φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_exp_eq : forall Θ Ξ Γ Δ A M M' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_subtyp : forall Θ Ξ Γ Δ A A' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

#[export]
Hint Resolve wk_preserves_exp wk_preserves_exp_eq wk_preserves_subtyp : mctt.

(** ** Reflexivity of Term Equality

    Reflexivity at a well-typed term is not a rule: every congruence rule of
    the equality judgment carries one premise per subterm, so reflexivity is an
    induction over typing.  The congruence rules [wf_exp_eq_typ_cong],
    [wf_exp_eq_nat_cong] and [wf_exp_eq_zero_cong] exist for this purpose.

    It is needed before [sub_preserves_wf], whose [Var] case for the equality
    judgment asks for [Θ ⍮ Ξ ⍮ Γ ⊢ σ $ x ≈ σ $ x : A[σ]] at an arbitrary image
    of the substitution, which no congruence rule provides. *)

Lemma wf_exp_eq_refl : forall {Θ Ξ Γ A M}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M : A.
Proof.
  induction 1; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_refl : mctt.

(** This is what lets [saturate_refl] and the [Proper] machinery of [LibTactics]
    see a well-typed term as a reflexive point of [≈]. *)
#[export]
Instance wf_exp_eq_per_elem Θ Ξ Γ A : PERElem _ (wf_exp Θ Ξ Γ A) (wf_exp_eq Θ Ξ Γ A).
Proof.
  intros ? ?; mauto 2.
Qed.

(** Refinement is reflexive at a type.  [wf_subtyp_refl] asks for an equation,
    which for reflexivity is [wf_exp_eq_refl]; stating the composite is what lets
    a goal [Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A] be closed from a typing derivation in one step, which is
    how every inversion lemma's introduction case ends.  [Core.Syntactic.SystemOpt]
    drops the typing premise of [wf_subtyp_refl], but going through that costs
    a level of search that [mauto] cannot always spare. *)
Lemma wf_subtyp_refl_typ : forall Θ Ξ Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros; eapply wf_subtyp_refl; mauto 2.
Qed.

#[export]
Hint Resolve wf_subtyp_refl_typ : mctt.

(** ** Substitution Typing *)

(** A weakening is a substitution.  [Wk] is [ι ↑], so every rule whose type
    mentions [Wk], such as the successor branch of the [ℕ]-eliminator, typed at
    [A[Wk⨟Wk,,succ #1]], needs this bridge. *)
Lemma wf_sub_of_wk : forall Θ Ξ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢w φ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s (ι φ) : Δ.
Proof.
  intros * Hφ; saturate_wk.
  econstructor; [ eassumption | eassumption | |];
    intros; simpl; rewrite ?exp_sub_of_wk; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_of_wk : mctt.

(** [wf_sub_id] and its companion for [Wk].  Both are the corresponding
    weakening lemma transported along [ι]; [sb_of_wk_id] and
    [sb_of_wk_shift] are equalities of the pointwise relation [sb_eq], so
    rewriting with them in a judgment goes through [wf_sub_Proper]. *)

Corollary wf_sub_id : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢s Id : Γ.
Proof.
  intros; rewrite <- sb_of_wk_id; mauto 3.
Qed.

Corollary wf_sub_shift : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Θ ⍮ Ξ ⍮ e :: Γ ⊢s Wk : Γ.
Proof.
  intros; rewrite <- sb_of_wk_shift; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id wf_sub_shift : mctt.

(** [wf_sub_extend] *)
Lemma wf_sub_extend : forall Θ Ξ Γ Δ σ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ,,M : Δ ▹ A.
Proof.
  intros * Hσ ? ?; saturate_sub.
  econstructor; [ eassumption | mauto 2 | |].
  - intros x B Hlk.
    (** Both bindings of [Δ ▹ A] are looked up at a type of the form [B[↑]ʷ], and
        [exp_sub_shift_extend] is precisely the statement that an
        extension is invisible to such a type. *)
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
      [ assumption | eapply wf_sub_apply; eassumption ].
  - intros x B N Hlk.
    inversion Hlk; subst; reduce_index; rewrite !exp_sub_shift_extend.
    eapply wf_sub_apply_def; eassumption.
Qed.

(** Extension into a definition: the new image must equal the substituted
    body. *)
Lemma wf_sub_extend_def : forall Θ Ξ Γ Δ σ A M N i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ,,N : Δ ▸ A ≔ M.
Proof.
  intros * Hσ ? ? ? ?; saturate_sub.
  econstructor; [ eassumption | mauto 2 | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
      [ assumption | eapply wf_sub_apply; eassumption ].
  - intros x B L Hlk.
    inversion Hlk; subst; reduce_index; rewrite !exp_sub_shift_extend;
      [ assumption | eapply wf_sub_apply_def; eassumption ].
Qed.

(** [wf_sub_single] *)
Corollary wf_sub_single : forall Θ Ξ Γ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M : Γ ▹ A.
Proof.
  intros.
  eapply wf_sub_extend; [ mauto 3 | eassumption | rewrite exp_sub_id; eassumption ].
Qed.

Corollary wf_sub_single_def : forall Θ Ξ Γ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M : Γ ▸ A ≔ M.
Proof.
  intros.
  eapply wf_sub_extend_def; [ mauto 3 | eassumption | eassumption | rewrite exp_sub_id; eassumption |].
  rewrite !exp_sub_id; mauto 2.
Qed.

(** [wf_sub_wk] *)
Lemma wf_sub_wk : forall Θ Ξ Γ Γ' Δ σ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s (sb_wk σ φ) : Δ.
Proof.
  intros * Hσ Hφ; saturate_wk; saturate_sub.
  econstructor; [ eassumption | eassumption | |].
  - intros x A ?; reduce_index; rewrite <- exp_wk_sub.
    eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
  - intros x A M ?; reduce_index; rewrite <- !exp_wk_sub.
    eapply wk_preserves_exp_eq; [ eapply wf_sub_apply_def; eassumption | eassumption ].
Qed.

(** [wf_sub_q].

    As in [wf_wk_q], the premise [Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i] is taken explicitly.  It
    could be dropped once [sub_preserves_wf] is available; we keep it, because
    it is exactly what the induction hypothesis of [sub_preserves_wf] supplies
    at each binder, and dropping it would make [wf_sub_q] depend on
    [sub_preserves_wf], which depends on [wf_sub_q]. *)
Lemma wf_sub_q : forall Θ Ξ Γ Δ σ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢s q σ : Δ ▹ A.
Proof.
  intros * Hσ ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A[σ]) by mauto 2.
  econstructor; [ eassumption | mauto 2 | |].
  - intros x B Hlk.
    (** [exp_wk_shift_sub_q] at [n = 0] is what moves the [[↑]ʷ]
        of a lookup out through the lifted substitution. *)
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 2 | ].
    eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | mauto 2 ].
  - intros x B N Hlk.
    inversion Hlk; subst; reduce_index; rewrite !exp_wk_shift_sub_q.
    eapply wk_preserves_exp_eq; [ eapply wf_sub_apply_def; eassumption | mauto 2 ].
Qed.

(** The lifted substitution over a definition: its head [#0] is the substituted
    body by δ. *)
Lemma wf_sub_q_def : forall Θ Ξ Γ Δ σ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢s q σ : Δ ▸ A ≔ M.
Proof.
  intros * Hσ ? ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ]) by mauto 2.
  econstructor; [ eassumption | mauto 2 | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q;
      [ mauto 2 | ].
    eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | mauto 2 ].
  - intros x B N Hlk.
    inversion Hlk; subst; reduce_index; rewrite !exp_wk_shift_sub_q.
    + eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    + eapply wk_preserves_exp_eq; [ eapply wf_sub_apply_def; eassumption | mauto 2 ].
Qed.

#[export]
Hint Resolve wf_sub_extend wf_sub_extend_def wf_sub_single wf_sub_single_def wf_sub_wk wf_sub_q wf_sub_q_def : mctt.

(** [ℕ] is closed, so [ℕ[σ]] is [ℕ] by computation and lifting a substitution
    over a [ℕ] binder needs no premises.  Compare [wf_wk_q_nat]. *)
Corollary wf_sub_q_nat : forall Θ Ξ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢s q σ : Δ ▹ ℕ.
Proof.
  intros * Hσ; saturate_sub.
  apply (wf_sub_q Θ Ξ Γ Δ σ ℕ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_q_nat : mctt.

Corollary wf_sub_q_False : forall Θ Ξ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢s q σ : Δ ▹ ⊥.
Proof.
  intros * Hσ; saturate_sub.
  apply (wf_sub_q Θ Ξ Γ Δ σ ⊥ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_q_False : mctt.

(** As with [wk_preserves_vlookup], it is these two rather than [wf_sub_apply]
    that go into [mctt]: the projection's conclusion mentions [σ x], which
    [eauto] would happily try to unify with any term at all. *)

Lemma sub_preserves_vlookup : forall Θ Ξ Γ Δ σ x A,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (σ x) : A[σ].
Proof.
  intros; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_eq : forall Θ Ξ Γ Δ σ x A,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (σ x) ≈ (σ x) : A[σ].
Proof.
  intros; apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_def : forall Θ Ξ Γ Δ σ x A M,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Δ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ (σ x) ≈ M[σ] : A[σ].
Proof.
  intros; eapply wf_sub_apply_def; eassumption.
Qed.

#[export]
Hint Resolve sub_preserves_vlookup sub_preserves_vlookup_eq sub_preserves_vlookup_def : mctt.

(** ** Pushing a Substitution Inwards

    The substitution counterpart of [push_wk].  Two differences from that
    tactic.

    - The single-substitution equation is [exp_sub_extend_comm],
      whose right-hand side is the unpushed form, so it is used backwards.
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
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_nat) ?Δ) (a_typ _) _, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(wf_sub Θ Ξ (cons (ce_ass a_nat) Γ) (cons (ce_ass a_nat) Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_q_nat; exact Hσ)
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Δ) (a_typ _) _, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(wf_sub Θ Ξ (cons (ce_ass a_False) Γ) (cons (ce_ass a_False) Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_q_False; exact Hσ)
  end.

Ltac lift_sub_step :=
  match goal with
  | Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ,
    IH : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _) |- _ =>
      let T := constr:(wf_sub Θ Ξ (cons (ce_ass (exp_sub A σ)) Γ) (cons (ce_ass A) Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_q; [ exact Hσ | | exact (IH _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub_def :=
  match goal with
  | Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ,
    _ : forall _ _, wf_sub ?Θ ?Ξ _ (cons (ce_def ?A ?M) ?Δ) _ -> _,
    IHA : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _),
    IHM : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (exp_sub ?A _) (exp_sub ?M _) |- _ =>
      let T := constr:(wf_sub Θ Ξ (cons (ce_def (exp_sub A σ) (exp_sub M σ)) Γ) (cons (ce_def A M) Δ) (sb_q σ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_q_def; [ exact Hσ | | | exact (IHA _ _ Hσ) | exact (IHM _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub := repeat first [ lift_sub_nat | lift_sub_step | lift_sub_def ].

(** The successor branch of the [ℕ]-eliminator again: its induction hypothesis
    produces [A[Wk⨟Wk,,succ #1][q (q σ)]] where the rule wants
    [A[q σ][Wk⨟Wk,,succ #1]].  [push_sub] cannot do it, because
    [exp_sub_sub_natrec] applies only to a doubly lifted substitution and in the
    hypothesis the substitution is still quantified.  So we instantiate at the
    lifted substitution [lift_sub] built and rewrite in the result. *)
Ltac lift_sub_natrec :=
  match goal with
  | IH : forall _ _, wf_sub _ _ _ (cons (ce_ass ?A) (cons (ce_ass a_nat) ?Δ)) _ -> _,
    Hq : wf_sub _ _ _ (cons (ce_ass ?A) (cons (ce_ass a_nat) ?Δ)) _ |- _ =>
      let H := fresh "HMS" in
      pose proof (IH _ _ Hq) as H;
      rewrite exp_sub_sub_natrec in H
  end.

(** ** Substitution Preserves the Judgments ([sub_preserves_wf]) *)

Lemma sub_preserves_wf :
  (forall Θ Ξ Δ A M,
      Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ]) /\
  (forall Θ Ξ Δ A M M',
      Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ] : A[σ]) /\
  (forall Θ Ξ Δ A A',
      Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ]).
Proof.
  apply syntactic_wf_mut_ind'; intros; saturate_sub; push_sub; lift_sub.
  all: try solve [ push_closed; mauto 3 ].
  all: try solve [ mauto 4 ].
  all: try solve [ econstructor; mauto 3 ].
  all: lift_sub_natrec; econstructor; mauto 2.
Qed.

Corollary sub_preserves_exp : forall Θ Ξ Γ Δ A M σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_exp_eq : forall Θ Ξ Γ Δ A M M' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ] : A[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_subtyp : forall Θ Ξ Γ Δ A A' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

#[export]
Hint Resolve sub_preserves_exp sub_preserves_exp_eq sub_preserves_subtyp : mctt.

(** [wf_sub_compose]: substitutions form a category over well-formed contexts.  The
    identity and associativity laws are [sb_compose_id_left],
    [sb_compose_id_right] and [sb_compose_assoc] in [Substitution]; this is the
    only part of the structure that needs the judgments. *)
Lemma wf_sub_compose : forall Θ Ξ Γ Γ' Δ σ τ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s τ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ ⨟ τ : Δ.
Proof.
  intros * Hσ Hτ; saturate_sub.
  econstructor; [ eassumption | eassumption | |];
    intros; reduce_index; rewrite <- ?exp_sub_sub; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_compose : mctt.

(** The single substitution lemma, the form in which the elimination rules use
    all of the above. *)

Corollary exp_sub_single : forall Θ Ξ Γ A B M N,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[Id,,N] : B[Id,,N].
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i) as [i ?] by mauto 3.
  eapply sub_preserves_exp; [ eassumption | eapply wf_sub_single; eassumption ].
Qed.

Corollary exp_eq_sub_single : forall Θ Ξ Γ A B M M' N,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[Id,,N] ≈ M'[Id,,N] : B[Id,,N].
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i) as [i ?] by mauto 3.
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

Corollary wf_sub_nat_single : forall Θ Ξ Γ M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ℕ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M : Γ ▹ ℕ.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Type@0) by mauto 3.
  eapply wf_sub_single; eassumption.
Qed.

Corollary wf_sub_zero : forall Θ Ξ Γ,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,zero : Γ ▹ ℕ.
Proof.
  intros; apply wf_sub_nat_single; mauto 2.
Qed.

(** [#1] is the [ℕ] of [Γ ▹ ℕ ▹ A]: the lookup derivation produces the type
    [ℕ[↑]ʷ[↑]ʷ], which is [ℕ] only up to computation. *)
Corollary ctx_lookup_nat_1 : forall Γ A, Γ ▹ ℕ ▹ A ∋ #1 : ℕ.
Proof.
  intros.
  assert (Γ ▹ ℕ ▹ A ∋ #1 : ℕ[↑]ʷ[↑]ʷ) as H by mauto 2.
  exact H.
Qed.

(** The premise is context well-formedness rather than [Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢ A : Type@i]
    so that this applies at the motive of either side of a congruence. *)
Corollary wf_sub_natrec_step : forall Θ Ξ Γ A,
    ⊢ Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢s Wk ⨟ Wk,,succ #1 : Γ ▹ ℕ.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ ℕ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢s Wk : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢s Wk : Γ ▹ ℕ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢s Wk ⨟ Wk : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ ℕ ▹ A ⊢ succ #1 : ℕ)
    by (econstructor; eapply wf_vlookup; [ assumption | apply ctx_lookup_nat_1 ]).
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℕ : Type@0) by mauto 3.
  eapply wf_sub_extend; [ eassumption | eassumption | assumption ].
Qed.

#[export]
Hint Resolve wf_sub_nat_single wf_sub_zero wf_sub_natrec_step : mctt.

(** The substitution [Id ,, M] at which the [⊥]-eliminator is typed. *)
Corollary wf_sub_False_single : forall Θ Ξ Γ M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M : Γ ▹ ⊥.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Type@0) by mauto 3.
  eapply wf_sub_single; eassumption.
Qed.

#[export]
Hint Resolve wf_sub_False_single : mctt.

(** ** Context Conversion

    [Δ] refines [Γ] exactly when the identity substitution is well-typed from
    [Δ] to [Γ]: [wf_sub_apply] at [Id] says that every binding of [Γ] is
    inhabited in [Δ] at the same type, up to subtyping via [wf_exp_subtyp'],
    because [A[Id]] is [A].  Transporting a judgment along a refinement is then
    [sub_preserves_wf] at [Id].

    So [Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ] is read "[Δ] refines [Γ]"; [wf_sub_id] is its
    reflexivity and [wf_sub_compose] its transitivity. *)

Corollary ctxsub_vlookup : forall Θ Ξ Γ Δ x A,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #x : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ (Id x) : A[Id]) as H' by mauto 2.
  rewrite exp_sub_id in H'; assumption.
Qed.

(** A lookup one binder in is a lookup weakened by [↑]; this is the shape the
    extension case below produces, and [eauto] cannot find it on its own because
    [#(S x)] has to be recognised as [#x[↑]ʷ] before [wk_preserves_exp]
    applies. *)
Corollary wk_preserves_vlookup_shift : forall Θ Ξ Γ A B x i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x : B ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #(S x) : B[↑]ʷ.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  change #(S x) with #x[↑]ʷ.
  mauto 3.
Qed.

Corollary ctxsub_vlookup_def : forall Θ Ξ Γ Δ x A M,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Γ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #x ≈ M : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ (Id x) ≈ M[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

(** Extending a refinement by one binding on each side: the bindings below the
    heads are those of the refinement, weakened, so only the heads are left to
    the caller. *)
Lemma wf_sub_id_extend_gen : forall Θ Ξ Γ Δ e e',
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ e' :: Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Γ ->
    (forall B, e :: Γ ∋ #0 : B -> Θ ⍮ Ξ ⍮ e' :: Δ ⊢ #0 : B) ->
    (forall B N, e :: Γ ∋ #0 ≔ N : B -> Θ ⍮ Ξ ⍮ e' :: Δ ⊢ #0 ≈ N : B) ->
    Θ ⍮ Ξ ⍮ e' :: Δ ⊢s Id : e :: Γ.
Proof.
  intros * HId ? ? Hhd Hhdd; saturate_sub.
  assert (Θ ⍮ Ξ ⍮ e' :: Δ ⊢w ↑ : Δ) by mauto 2.
  econstructor; [ eassumption | eassumption | |].
  - intros [| x] B Hlk; reduce_index; rewrite exp_sub_id; [ auto |].
    inversion Hlk; subst.
    change #(S x) with #x[↑]ʷ.
    eapply wk_preserves_exp; [ eapply ctxsub_vlookup | ]; eassumption.
  - intros [| x] B N Hlk; reduce_index; rewrite !exp_sub_id; [ auto |].
    inversion Hlk; subst.
    change #(S x) with #x[↑]ʷ.
    eapply wk_preserves_exp_eq; [ eapply ctxsub_vlookup_def | ]; eassumption.
Qed.

Lemma wf_sub_id_extend : forall Θ Ξ Γ Δ A A' i,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢s Id : Γ ▹ A.
Proof.
  intros * HId ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▹ A') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢w ↑ : Δ) by mauto 2.
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | |];
    intros * Hlk; inversion Hlk; subst.
  (** The top binding: [#0] has type [A'[↑]ʷ] there and [A'[↑]ʷ ⊆ A[↑]ʷ] by
      weakening the given subtyping. *)
  eapply wf_exp_subtyp'; [ mauto 2 | ].
  eapply wk_preserves_subtyp; eassumption.
Qed.

(** A definition refines a definition of a supertype with an equal body. *)
Lemma wf_sub_id_extend_def : forall Θ Ξ Γ Δ A A' M M' i,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' ≈ M : A ->
    Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢s Id : Γ ▸ A ≔ M.
Proof.
  intros * HId ? ? ? ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢w ↑ : Δ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢ A'[↑]ʷ ⊆ A[↑]ʷ) by (eapply wk_preserves_subtyp; eassumption).
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | |];
    intros * Hlk; inversion Hlk; subst.
  - eapply wf_exp_subtyp'; [ mauto 2 | eassumption ].
  - eapply wf_exp_eq_trans; [ eapply wf_exp_eq_subtyp' | ].
    + eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    + eassumption.
    + eapply wk_preserves_exp_eq; eassumption.
Qed.

(** A definition refines an assumption of a supertype. *)
Lemma wf_sub_id_forget : forall Θ Ξ Γ Δ A A' M' i,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢s Id : Γ ▹ A.
Proof.
  intros * HId ? ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢w ↑ : Δ) by mauto 2.
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | |];
    intros * Hlk; inversion Hlk; subst.
  eapply wf_exp_subtyp'; [ mauto 2 | ].
  eapply wk_preserves_subtyp; eassumption.
Qed.

(** Equal types give refinements in both directions; this is the instance
    [wf_sub_eq] and the presupposition lemma need. *)
Corollary wf_sub_id_extend_eq : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢s Id : Γ ▹ A.
Proof.
  intros.
  eapply wf_sub_id_extend; mauto 3.
Qed.

(** The same for definitions, with equal bodies. *)
Corollary wf_sub_id_extend_def_eq : forall Θ Ξ Γ A A' M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢s Id : Γ ▸ A ≔ M.
Proof.
  intros.
  eapply wf_sub_id_extend_def; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id_extend wf_sub_id_extend_eq wf_sub_id_extend_def wf_sub_id_forget
             wf_sub_id_extend_def_eq : mctt.

Corollary ctxsub_exp : forall Θ Ξ Γ Δ A M,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ M[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_exp_eq : forall Θ Ξ Γ Δ A M M',
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ M[Id] ≈ M'[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_subtyp : forall Θ Ξ Γ Δ A A',
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A'.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ A[Id] ⊆ A'[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

#[export]
Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_subtyp : mctt.

(** ** Transporting a Type

    [Type@i] is closed, so [Type@i[φ]ʷ] and [Type@i[σ]] are [Type@i] — but only
    up to conversion, and [eauto]'s [simple apply] does not reduce.  These four
    spell it out; every "and the type is still a type" step below goes through
    one of them. *)

Corollary wk_preserves_typ : forall Θ Ξ Γ Δ A φ i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Type@i.
Proof.
  intros.
  assert (wf_exp Θ Ξ Δ (exp_wk (a_typ i) φ) (exp_wk A φ)) by mauto 2.
  assumption.
Qed.

Corollary wk_preserves_typ_eq : forall Θ Ξ Γ Δ A A' φ i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Type@i.
Proof.
  intros.
  assert (wf_exp_eq Θ Ξ Δ (exp_wk (a_typ i) φ) (exp_wk A φ) (exp_wk A' φ)) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ : forall Θ Ξ Γ Δ A σ i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i.
Proof.
  intros.
  assert (wf_exp Θ Ξ Γ (exp_sub (a_typ i) σ) (exp_sub A σ)) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ_eq : forall Θ Ξ Γ Δ A A' σ i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A'[σ] : Type@i.
Proof.
  intros.
  assert (wf_exp_eq Θ Ξ Γ (exp_sub (a_typ i) σ) (exp_sub A σ) (exp_sub A' σ)) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve wk_preserves_typ wk_preserves_typ_eq
             sub_preserves_typ sub_preserves_typ_eq : mctt.

(** ** Lifting without the Extra Premise

    Given [wk_preserves_wf] and [sub_preserves_wf], the transported type
    premise of [wf_wk_q] and [wf_sub_q] is redundant: it is the conclusion of
    [wk_preserves_typ], respectively [sub_preserves_typ] (see the remark on
    [wf_sub_q]).  These versions replace [wf_wk_q] and [wf_sub_q] as hints, as
    [Definitions] does for the subtyping rules. *)

Corollary wf_wk_q' : forall Θ Ξ Γ Δ φ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢w wk_q φ : Γ ▹ A.
Proof.
  intros; eapply wf_wk_q; mauto 2.
Qed.

Corollary wf_sub_q' : forall Θ Ξ Γ Δ σ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢s q σ : Δ ▹ A.
Proof.
  intros; eapply wf_sub_q; mauto 2.
Qed.

#[export]
Hint Resolve wf_wk_q' wf_sub_q' : mctt.
#[export]
Remove Hints wf_wk_q wf_sub_q : mctt.

(** ** Cumulativity

    Cumulativity is not a rule but is derivable.  The presupposition lemma
    needs it to put two types at a common universe. *)

Lemma wf_cumu : forall Θ Ξ Γ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@(S i).
Proof.
  intros; eapply wf_exp_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

Lemma wf_exp_eq_cumu : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@(S i).
Proof.
  intros; eapply wf_exp_eq_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_subtyp_ge : forall {Θ Ξ Γ i j},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@i ⊆ Type@j.
Proof.
  induction 2; mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma lift_exp_ge : forall Θ Ξ Γ A i j,
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@j.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma lift_exp_eq_ge : forall Θ Ξ Γ A A' i j,
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@j.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
Hint Resolve lift_exp_ge lift_exp_eq_ge : mctt.

Corollary lift_exp_max_left : forall Θ Ξ Γ A i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@(max i j).
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_max_right : forall Θ Ξ Γ A i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@(max i j).
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_left : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@(max i j).
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_right : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@(max i j).
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

(** Transitivity across two different levels. *)
Lemma exp_eq_trans_typ_max : forall {Θ Ξ Γ i i' A A' A''},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ A'' : Type@i' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A'' : Type@(max i i').
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@(max i i')) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ A'' : Type@(max i i')) by eauto using lift_exp_eq_max_right; mautosolve 4.
Qed.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

(** Two types are always types at a common level.  Stating it in this form —
    with the level existentially quantified rather than spelled [max i j] — is
    what lets a proof reach it with [eapply] and leave both levels to
    unification, which is the only way to use cumulativity in a case whose level
    variables the induction named for us. *)
Corollary lift_exp_common : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@j ->
    exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@k /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@k.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** [wf_pi] checks the domain and the codomain at the same level, which is
    almost never how they arrive: the domain's level comes from its own premise
    and the codomain's from presupposition.  This is the form that takes them as
    they come.  It is a hint, and the level it produces is a [max] of two evars,
    so it only fires where the level of the [Π]-type is still open — which is
    exactly where the strict [wf_pi] cannot fire at all. *)
Corollary wf_pi_max : forall Θ Ξ Γ A B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type@(max i j).
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
Corollary lift_exp_pi_common : forall Θ Ξ Γ A B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@j ->
    exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@k /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@k.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** ** Types in a Well-formed Context

    Every binding of a well-formed context is a type in that context: the
    weakening carried by [ctx_lookup] is exactly what makes this so. *)

(** What the global context guarantees about the parameters in scope: popping a
    frame leaves a well-formed context, whose parameters are well formed. *)

Lemma wf_gmod_ctx : forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ.
Proof.
  induction 1; assumption.
Qed.

Lemma wf_gctx_pop : forall Θ mp U Ξ,
    ⊢g Θ ⍮ (mp, U) :: Ξ ->
    ⊢g Θ ⍮ Ξ /\ ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ.
Proof.
  intros * Hg; inversion Hg as [? ? Hs]; inversion Hs; subst.
  split; [ constructor; assumption |].
  eapply wf_gmod_ctx, wf_gunit_mod; eassumption.
Qed.

Lemma ctx_wf_gctx : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢g Θ ⍮ Ξ.
Proof.
  intros Θ Ξ Γ; induction Γ as [| B Γ IH]; intros HΓ; inversion HΓ; subst;
    eauto using presup_exp_ctx.
Qed.

#[export]
Hint Resolve ctx_wf_gctx : mctt.

(** A local binding is a type in its context by the weakening [ctx_lookup]
    carries. *)
Lemma ctx_lookup_wf : forall Ξ Θ Γ x A,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Γ ∋ #x : A ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
Proof.
  intros * HΓ Hlk; gen HΓ; induction Hlk; intros HΓ;
    assert (Θ ⍮ Ξ ⍮ _ ⊢w ↑ : Γ) by (eapply wf_wk_shift; exact HΓ);
    [ destruct (ctx_decomp_right HΓ) as [k ?]
    | destruct (ctx_decomp_def_typ HΓ) as [k ?]
    | destruct IHHlk as [k ?]; [ mauto 2 |] ];
    exists k; change (Type@k) with (Type@k[↑]ʷ); mauto 2.
Qed.

(** The body of a definition entry is typed at its type, both weakened. *)
Lemma ctx_lookup_def_wf : forall Ξ Θ Γ x A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Γ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hlk; gen HΓ; induction Hlk; intros HΓ;
    assert (Θ ⍮ Ξ ⍮ _ ⊢w ↑ : Γ) by (eapply wf_wk_shift; exact HΓ);
    [ pose proof (ctx_decomp_def_body HΓ) | pose proof (IHHlk ltac:(mauto 2)) ];
    mauto 2.
Qed.

#[export]
Hint Resolve ctx_lookup_wf ctx_lookup_def_wf : mctt.
