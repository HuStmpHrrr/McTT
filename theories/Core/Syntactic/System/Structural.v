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
From Mctt.Core.Syntactic.System Require Export Scoping MemberLemmas.
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

Lemma presup_ext_eq_ctx : forall {Θ Ξ Γ Ψ Ψ'}, Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; auto.
Qed.

#[export]
Hint Resolve presup_ext_eq_ctx : mctt.

Lemma presup_unit_eq_ctx : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_unit_eq_ctx : mctt.

Lemma presup_modexp_eq_ctx : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_modexp_eq_ctx : mctt.

(** A unit equivalence presupposes the reflexive instances of both sides. *)
Lemma wf_unit_eq_refl_left : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply wf_unit_eq_trans; [ eassumption | apply wf_unit_eq_sym; eassumption ]. Qed.

Lemma wf_unit_eq_refl_right : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U'.
Proof. intros; eapply wf_unit_eq_trans; [ apply wf_unit_eq_sym; eassumption | eassumption ]. Qed.

Lemma wf_modexp_eq_refl_left : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply wf_me_trans; [ eassumption | apply wf_me_sym; eassumption ]. Qed.

Lemma wf_modexp_eq_refl_right : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H'.
Proof. intros; eapply wf_me_trans; [ apply wf_me_sym; eassumption | eassumption ]. Qed.

Lemma ctx_decomp_mod : forall {Θ Ξ Γ U},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  inversion 1; eauto using presup_unit_eq_ctx.
Qed.

Corollary ctx_decomp_mod_left : forall {Θ Ξ Γ U}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof. intros * ?%ctx_decomp_mod; easy. Qed.

Corollary ctx_decomp_mod_unit : forall {Θ Ξ Γ U}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros * ?%ctx_decomp_mod; easy. Qed.

#[export]
Hint Resolve ctx_decomp_mod_left ctx_decomp_mod_unit : mctt.

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
  intros * H; destruct e; eauto using ctx_decomp_left, ctx_decomp_def_left, ctx_decomp_mod_left.
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
    intros; rewrite ?exp_wk_id, ?gunit_wk_id; assumption.
Qed.

Lemma wf_wk_shift : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Θ ⍮ Ξ ⍮ e :: Γ ⊢w ↑ : Γ.
Proof.
  intros * H; econstructor; [ eassumption | mauto 2 | | |];
    intros; simpl; mauto 2.
Qed.

(** Lifting a weakening over any entry: the lookups move along with it.  The
    two contexts must be well formed; the rules below supply them. *)
Lemma wf_wk_q_gen : forall Θ Ξ Γ Δ φ e,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ centry_wk e φ :: Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Γ ->
    Θ ⍮ Ξ ⍮ centry_wk e φ :: Δ ⊢w wk_q φ : e :: Γ.
Proof.
  intros * Hφ ? ?.
  econstructor; [ assumption | assumption | | |].
  - intros x B Hlk; inversion Hlk; subst; simpl; rewrite exp_wk_shift_wk_q.
    + econstructor.
    + econstructor.
    + econstructor; eapply wf_wk_lookup; eassumption.
  - intros x B N Hlk.
    inversion Hlk; subst; simpl; rewrite !exp_wk_shift_wk_q; econstructor.
    eapply wf_wk_lookup_def; eassumption.
  - intros x U Hlk.
    inversion Hlk; subst; simpl; rewrite gunit_wk_shift_wk_q; econstructor.
    eapply wf_wk_lookup_mod; eassumption.
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
  intros * Hφ ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_ass A)); mauto 2.
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
  intros * Hφ ? ? ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_def A M)); mauto 2.
Qed.

(** The same over a module slot. *)
Lemma wf_wk_q_mod : forall Θ Ξ Γ Δ φ U,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U φ ->
    Θ ⍮ Ξ ⍮ Δ ▹ₘ gunit_wk U φ ⊢w wk_q φ : Γ ▹ₘ U.
Proof.
  intros * Hφ ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_mod U)); mauto 2.
Qed.

(** Lifting over a whole extension, given that both extended contexts are
    well formed. *)
Lemma wf_wk_ext : forall Θ Ξ Ψ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ⊢w wk_qn (length Ψ) φ : Ψ ++ Γ.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hφ HΔ HΓ; cbn in *; [ assumption |].
  apply wf_wk_q_gen; [ apply IH; eauto using ctx_decomp_tail | assumption | assumption ].
Qed.

Lemma wf_wk_compose : forall Θ Ξ Γ Δ Δ' φ ψ,
    Θ ⍮ Ξ ⍮ Γ ⊢w ψ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢w φ ⊙ ψ : Δ'.
Proof.
  intros * Hψ Hφ; saturate_wk.
  econstructor; [ eassumption | eassumption | | |].
  - intros x B ?; simpl; rewrite <- exp_wk_wk.
    eapply wf_wk_lookup; [ eassumption | ].
    eapply wf_wk_lookup; eassumption.
  - intros x B N ?; simpl; rewrite <- !exp_wk_wk.
    eapply wf_wk_lookup_def; [ eassumption | ].
    eapply wf_wk_lookup_def; eassumption.
  - intros x U ?; simpl; rewrite <- gunit_wk_wk.
    eapply wf_wk_lookup_mod; [ eassumption | ].
    eapply wf_wk_lookup_mod; eassumption.
Qed.

#[export]
Hint Resolve wf_wk_id wf_wk_shift wf_wk_q wf_wk_q_def wf_wk_q_mod wf_wk_compose : mctt.

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

(** ** Facts about Modules for the Transport Lemmas *)

Lemma ext_eq_ctx : forall Θ Ξ Γ Ψ Ψ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ /\ ⊢ Θ ⍮ Ξ ⍮ Ψ' ++ Γ.
Proof.
  induction 1; cbn; split; destruct_all; mauto 3 using wf_unit_eq_refl_left.
Qed.

Lemma ext_eq_ctx_left : forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ.
Proof. intros * H; exact (proj1 (ext_eq_ctx _ _ _ _ _ H)). Qed.

Lemma ext_eq_ctx_right : forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊢ Θ ⍮ Ξ ⍮ Ψ' ++ Γ.
Proof. intros * H; exact (proj2 (ext_eq_ctx _ _ _ _ _ H)). Qed.

#[export]
Hint Resolve ext_eq_ctx_left ext_eq_ctx_right : mctt.

(** The tail of a well-formed context [Ψ ++ Γ]. *)
Lemma ctx_app_wf_tail : forall Θ Ξ Ψ Γ, ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof. induction Ψ; intros; cbn in *; eauto using ctx_decomp_tail. Qed.

Lemma ctx_app_wf_suffix : forall Θ Ξ Ψ1 Ψ0 Γ, ⊢ Θ ⍮ Ξ ⍮ (Ψ1 ++ Ψ0) ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Ψ0 ++ Γ.
Proof. intros; rewrite <- List.app_assoc in *; eapply ctx_app_wf_tail; eassumption. Qed.

Lemma tele_ass_wk : forall Δ φ, tele_ass Δ -> tele_ass (tele_wk Δ φ).
Proof.
  induction 1 as [| e Δ [A ->] HΔ IH]; cbn; constructor; eauto.
Qed.

Lemma tele_ass_sub : forall Δ σ, tele_ass Δ -> tele_ass (tele_sub Δ σ).
Proof.
  induction 1 as [| e Δ [A ->] HΔ IH]; cbn; constructor; eauto.
Qed.

Lemma body_shape_wk : forall Φ Φ' φ φ', body_shape Φ Φ' -> body_shape (gmod_wk Φ φ) (gmod_wk Φ' φ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] * Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & -> & HE); repeat split; auto.
    destruct E as [? ? ? [] | ], E' as [? ? ? [] | ]; cbn in *; auto.
  - destruct Hs as (Hs & Hc); split; auto.
    destruct c, c'; cbn in *; auto.
Qed.

Lemma body_shape_sub : forall Φ Φ' σ σ', body_shape Φ Φ' -> body_shape (gmod_sub Φ σ) (gmod_sub Φ' σ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] * Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & -> & HE); repeat split; auto.
    destruct E as [? ? ? [] | ], E' as [? ? ? [] | ]; cbn in *; auto.
  - destruct Hs as (Hs & Hc); split; auto.
    destruct c, c'; cbn in *; auto.
Qed.

Lemma exp_wk_sub_extend_mod : forall M H φ,
    M[Id ,,ₘ H][φ]ʷ = M[wk_q φ]ʷ[Id ,,ₘ modexp_wk H φ].
Proof.
  intros; rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reflexivity.
Qed.

Lemma exp_sub_sub_extend_mod : forall M H σ,
    M[Id ,,ₘ H][σ] = M[q σ][Id ,,ₘ H[σ]ᵐ].
Proof.
  intros; rewrite exp_sub_extend_mod_sub, exp_sub_q_extend_mod; reflexivity.
Qed.

(** A well-typed weakening sends module slots to slots of the same unit, and a
    well-typed substitution sends them to the same unit. *)
Lemma wf_wk_mod_compat : forall Θ Ξ Γ Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> wk_mod_compat φ Δ Γ.
Proof. intros * Hφ x U HU; eapply wf_wk_lookup_mod; eassumption. Qed.

Lemma wf_sub_mod_compat : forall Θ Ξ Γ Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ -> sub_mod_compat σ Δ Γ.
Proof.
  intros * Hσ x U HU; destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ HU) as [[? _] | ?]; [ left | right ]; assumption.
Qed.

#[export]
Hint Resolve wf_wk_mod_compat wf_sub_mod_compat : mctt.

Lemma ext_eq_length : forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> length Ψ = length Ψ'.
Proof. induction 1; cbn; auto. Qed.

(** The lifted weakening into an extension, from the judgments about it. *)
Lemma wf_wk_ext_of_ext : forall Θ Ξ Γ Ψ Ψ' Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ ->
    Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ⊢w wk_qn (length Ψ) φ : Ψ ++ Γ /\
    Θ ⍮ Ξ ⍮ tele_wk Ψ' φ ++ Δ ⊢w wk_qn (length Ψ') φ : Ψ' ++ Γ.
Proof.
  intros * Hφ HΨ HΨφ; split; apply wf_wk_ext; eauto using ext_eq_ctx_left, ext_eq_ctx_right.
Qed.

(** The import checks of a body, moved along a weakening of the unit. *)
Lemma wk_body_checks : forall Θ Ξ Γ Δu Φ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ (body_ctx Φ ++ Δu) ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_wk (body_ctx Φ ++ Δu) φ ++ Δ ->
    (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks Φ) ->
       forall Δ1 φ0, Θ ⍮ Ξ ⍮ Δ1 ⊢w φ0 : body_ctx Φ0 ++ Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ1 ⊢ᵐ modexp_wk E φ0 ≈ modexp_wk E φ0) ->
    (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks Φ) -> List.In n ns ->
       member_ok Θ Ξ (body_ctx Φ0 ++ Δu ++ Γ) E n) ->
    (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks (gmod_wk Φ (wk_qn (length Δu) φ))) ->
       Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ tele_wk Δu φ ++ Δ ⊢ᵐ E ≈ E) /\
    (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks (gmod_wk Φ (wk_qn (length Δu) φ))) -> List.In n ns ->
       member_ok Θ Ξ (body_ctx Φ0 ++ tele_wk Δu φ ++ Δ) E n).
Proof.
  intros * Hφ HΨ HΨφ HE Hm.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt).
  split.
  - intros Φ0' E' ns Hin. rewrite gm_checks_wk in Hin. apply List.in_map_iff in Hin as [[Φ0 c] [Heq Hin]].
    injection Heq as Heq1 Hc'. subst Φ0'.
    destruct c as [E ns' | ? ?]; cbn in Hc'; [| discriminate ]. injection Hc' as Hc1 Hc2; subst E' ns'.
    destruct (gm_checks_body_ctx _ _ _ Hin) as [Ψ1 HΨ1].
    rewrite body_ctx_wk, List.app_assoc, <- tele_wk_app.
    assert (Hlift : Θ ⍮ Ξ ⍮ tele_wk (body_ctx Φ0 ++ Δu) φ ++ Δ ⊢w wk_qn (length (body_ctx Φ0 ++ Δu)) φ : (body_ctx Φ0 ++ Δu) ++ Γ).
    { rewrite HΨ1, <- !List.app_assoc in HΨ, HΨφ; rewrite tele_wk_app, <- List.app_assoc in HΨφ.
      apply wf_wk_ext; [ assumption | eapply ctx_app_wf_tail; eassumption | rewrite <- !List.app_assoc in HΨ |- *; exact (ctx_app_wf_tail _ _ Ψ1 _ HΨ) ]. }
    assert (Heqw : wk_eq (wk_qn (gm_binders Φ0) (wk_qn (length Δu) φ)) (wk_qn (length (body_ctx Φ0 ++ Δu)) φ))
      by (rewrite wk_qn_add, List.length_app, length_body_ctx; reflexivity).
    rewrite (modexp_wk_wk_eq _ _ _ Heqw); rewrite <- List.app_assoc in Hlift; eauto.
  - intros Φ0' E' ns n Hin. rewrite gm_checks_wk in Hin. apply List.in_map_iff in Hin as [[Φ0 c] [Heq Hin]].
    injection Heq as Heq1 Hc'. subst Φ0'.
    destruct c as [E ns' | ? ?]; cbn in Hc'; [| discriminate ]. injection Hc' as Hc1 Hc2; subst E' ns'.
    intros Hn.
    rewrite body_ctx_wk, List.app_assoc, <- tele_wk_app.
    assert (Heqw : wk_eq (wk_qn (gm_binders Φ0) (wk_qn (length Δu) φ)) (wk_qn (length (body_ctx Φ0 ++ Δu)) φ))
      by (rewrite wk_qn_add, List.length_app, length_body_ctx; reflexivity).
    rewrite (modexp_wk_wk_eq _ _ _ Heqw).
    destruct (Hm _ _ _ _ Hin Hn) as [(A & HA) | (A & HA)]; [ left | right ]; eexists;
      eapply (proj1 (member_type_wk _ _ Hc)); try eassumption;
      rewrite List.app_assoc; apply wk_mod_compat_ext; eauto with mctt.
Qed.

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
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ) /\
  (forall Θ Ξ Γ Ψ Ψ',
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ) /\
  (forall Θ Ξ Γ U U',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U' φ) /\
  (forall Θ Ξ Γ H H',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk H φ ≈ modexp_wk H' φ).
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
  all: try solve [ lift_wk_natrec; econstructor; mauto 2 ].
  (** The module rules. *)
  all: try solve [ rewrite ?exp_wk_sub_extend_mod; eapply wf_let_mod; eauto using wf_wk_q_mod ].
  all: try solve [ rewrite !exp_wk_sub_extend_mod; eapply wf_exp_eq_let_mod_zeta; eauto using wf_wk_q_mod ].
  all: try solve [ rewrite exp_wk_sub_extend_mod; eapply wf_exp_eq_let_mod_cong;
                   [ eauto | eauto 6 using wf_wk_q_mod, wf_unit_eq_refl_left | rewrite <- exp_wk_sub_extend_mod; eauto ] ].
  all: try solve [ first [ eapply wf_mem | eapply wf_exp_eq_mem_delta ];
                   [ apply me_noargs_wk; assumption | eauto
                   | eapply (proj1 (member_type_wk _ _ ltac:(eauto using wf_gctx_closed))); eauto using wf_wk_mod_compat
                   | eauto
                   | unfold member_unfold in *; eapply member_unfold_wk; eauto using wf_gctx_closed, wf_wk_mod_compat
                   | eauto ] ].
  all: try solve [ rewrite ?apps_wk, ?member_ref_wk; first [ eapply wf_mem_app | eapply wf_exp_eq_mem_app ];
                   [ eauto | apply modexp_spine_wk; eassumption
                   | match goal with H : _ <> nil |- _ => destruct args; [ contradiction H; reflexivity | discriminate ] end
                   | rewrite <- member_ref_wk, <- apps_wk; eauto ] ].
  all: try solve [ cbn [tele_wk]; first [ eapply wf_ext_eq_ass | eapply wf_ext_eq_def | eapply wf_ext_eq_mod ];
                   eauto 7 using wf_wk_ext, ext_eq_ctx_left, ext_eq_ctx_right, presup_exp_ctx, presup_exp_eq_ctx, presup_unit_eq_ctx ].
  all: try solve [ eapply wf_me_path; [ eauto | eapply (proj1 (member_type_wk _ _ ltac:(eauto using wf_gctx_closed))); eauto using wf_wk_mod_compat ] ].
  all: try solve [ eapply wf_me_var; [ eauto | eapply wf_wk_lookup_mod; eauto ] ].
  all: try solve [ eapply wf_me_mem;
                   [ eauto | eapply (proj1 (member_type_wk _ _ ltac:(eauto using wf_gctx_closed))); eauto using wf_wk_mod_compat
                   | eapply (proj1 (member_type_wk _ _ ltac:(eauto using wf_gctx_closed))); eauto using wf_wk_mod_compat ] ].
  (** Extensions: the entry is moved by the weakening lifted over the
      extension before it. *)
  all: try solve [ cbn [tele_wk];
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?Ψ ?Ψ', IHx : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_wk ?Ψ _) (tele_wk ?Ψ' _),
      Hφ : wf_wk _ _ ?Δ ?Γ ?φ |- _ =>
        let Hl := fresh "Hl" in
        let Hr := fresh "Hr" in
        destruct (wf_wk_ext_of_ext _ _ _ _ _ _ _ Hφ Hx (IHx _ _ Hφ)) as [Hl Hr];
        pose proof (ext_eq_length _ _ _ _ _ Hx) as Hlen;
        first [ eapply wf_ext_eq_ass | eapply wf_ext_eq_def | eapply wf_ext_eq_mod ];
        [ exact (IHx _ _ Hφ) | .. ];
        rewrite ?Hlen in *; eauto
    end ].
  (** Units. *)
  all: try solve [ rewrite !gunit_wk_mk; cbn [moddef_wk];
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?Ψ ?Ψ', IHx : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_wk ?Ψ _) (tele_wk ?Ψ' _),
      Hφ : wf_wk _ _ ?Δ ?Γ ?φ |- _ =>
        let Hl := fresh "Hl" in
        let Hr := fresh "Hr" in
        destruct (wf_wk_ext_of_ext _ _ _ _ _ _ _ Hφ Hx (IHx _ _ Hφ)) as [Hl Hr];
        pose proof (ext_eq_length _ _ _ _ _ Hx) as Hlen;
        eapply wf_unit_eq_alias; [ exact (IHx _ _ Hφ) | apply tele_ass_wk; assumption | apply tele_ass_wk; assumption | eauto | rewrite <- ?Hlen in *; eauto ]
    end ].
  all: try solve [ rewrite !gunit_wk_mk; cbn [moddef_wk];
    match goal with
    | IHx : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_wk (body_ctx ?Φ ++ ?Δu) _) (tele_wk (body_ctx ?Φ' ++ ?Δu') _),
      Hx : wf_ext_eq _ _ ?Γ _ _,
      HE : forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks ?Φ) -> forall _ _, _,
      Hm : forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks ?Φ) -> _,
      HE' : forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks ?Φ') -> forall _ _, _,
      Hm' : forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks ?Φ') -> _,
      Hφ : wf_wk _ _ _ ?Γ _ |- _ =>
        let Hxφ := fresh "Hxφ" in
        pose proof (IHx _ _ Hφ) as Hxφ;
        let Hc1 := fresh "Hc" in let Hc2 := fresh "Hc" in let Hc3 := fresh "Hc" in let Hc4 := fresh "Hc" in
        destruct (wk_body_checks _ _ _ Δu Φ _ _ Hφ ltac:(eauto with mctt) ltac:(eauto with mctt) HE Hm) as [Hc1 Hc2];
        destruct (wk_body_checks _ _ _ Δu' Φ' _ _ Hφ ltac:(eauto with mctt) ltac:(eauto with mctt) HE' Hm') as [Hc3 Hc4];
        eapply wf_unit_eq_body;
        [ rewrite !body_ctx_wk, <- !tele_wk_app; exact Hxφ
        | apply tele_ass_wk; assumption | apply tele_ass_wk; assumption
        | rewrite !length_tele_wk; assumption
        | apply body_shape_wk; assumption
        | rewrite gm_names_wk; assumption
        | exact Hc1 | exact Hc2 | exact Hc3 | exact Hc4 ]
    end ].
  (** The remaining cases name their induction hypotheses by shape. *)
  all: try solve [ rewrite !gunit_wk_mk; cbn [moddef_wk];
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?D ?D', IHx : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_ext_eq _ _ _ _ _,
      IHE : forall _ _, wf_wk _ _ _ (?D ++ ?Γ) _ -> wf_modexp_eq _ _ _ _ _,
      IHE' : forall _ _, wf_wk _ _ _ (?D' ++ ?Γ) _ -> wf_modexp_eq _ _ _ _ _,
      Hφ : wf_wk _ _ _ ?Γ _ |- wf_unit_eq _ _ _ (gu_mk (tele_wk ?D _) _) _ =>
        let Hl := fresh "Hl" in
        let Hr := fresh "Hr" in
        destruct (wf_wk_ext_of_ext _ _ _ _ _ _ _ Hφ Hx (IHx _ _ Hφ)) as [Hl Hr];
        pose proof (ext_eq_length _ _ _ _ _ Hx) as Hlen;
        eapply wf_unit_eq_alias;
        [ exact (IHx _ _ Hφ) | apply tele_ass_wk; assumption | apply tele_ass_wk; assumption
        | rewrite <- Hlen; exact (IHE _ _ Hl) | exact (IHE' _ _ Hr) ]
    end ].
  all: try solve [
    match goal with
    | Hm : member_type _ _ ?Γ (me_path ?p) nil mk_mod _, Hφ : wf_wk _ _ _ ?Γ _ |- _ =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        eapply wf_me_path; [ eauto | exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ _ Hm _ _ (wf_wk_mod_compat _ _ _ _ _ Hφ)) ]
    end ].
  all: try solve [
    match goal with
    | Hm : member_type _ _ ?Γ ?H nil mk_mod _, Hm' : member_type _ _ ?Γ ?H' nil mk_mod _,
      Hφ : wf_wk _ _ _ ?Γ _ |- wf_modexp_eq _ _ _ (me_app (modexp_wk ?H _) _) (me_app (modexp_wk ?H' _) _) =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        eapply wf_me_app;
        [ eauto
        | exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ _ Hm _ _ (wf_wk_mod_compat _ _ _ _ _ Hφ)) | eauto | eauto | eauto | eauto
        | exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ _ Hm' _ _ (wf_wk_mod_compat _ _ _ _ _ Hφ)) | eauto | eauto | eauto | eauto ]
    end ].
  all: try solve [
    match goal with
    | HU : wf_unit_eq _ _ ?Γ ?U ?U', IHU : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_unit_eq _ _ _ _ _,
      IHB : forall _ _, wf_wk _ _ _ (ce_mod ?U :: ?Γ) _ -> _,
      IHL : forall _ _, wf_wk _ _ _ ?Γ _ -> _,
      Hφ : wf_wk _ _ _ ?Γ _ |- _ =>
        pose proof (IHU _ _ Hφ) as HUφ;
        pose proof (IHL _ _ Hφ) as HL; rewrite exp_wk_sub_extend_mod in HL |- *;
        eapply wf_exp_eq_let_mod_cong;
        [ exact HUφ
        | apply IHB; apply wf_wk_q_mod; eauto using wf_unit_eq_refl_left
        | exact HL ]
    end ].
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

Corollary wk_preserves_ext : forall Θ Ξ Γ Δ Ψ Ψ' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_unit : forall Θ Ξ Γ Δ U U' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U' φ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_modexp : forall Θ Ξ Γ Δ H H' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    Θ ⍮ Ξ ⍮ Δ ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk H φ ≈ modexp_wk H' φ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

#[export]
Hint Resolve wk_preserves_exp wk_preserves_exp_eq wk_preserves_subtyp wk_preserves_ext wk_preserves_unit wk_preserves_modexp : mctt.

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
  induction 1; try mautosolve 3.
  all: first [ eapply wf_exp_eq_let_mod_cong; mauto 3
             | eapply wf_exp_eq_mem_cong; [ eassumption | eapply wf_mem; eassumption | eapply wf_mem; eassumption ]
             | eapply wf_exp_eq_mem_cong; [ eassumption | eapply wf_mem_app; eassumption | eapply wf_mem_app; eassumption ] ].
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
  econstructor; [ eassumption | eassumption | | |];
    intros; simpl; rewrite ?exp_sub_of_wk; mauto 2.
  right; eexists; split; [ reflexivity |].
  rewrite gunit_sub_of_wk; eapply wf_wk_lookup_mod; eassumption.
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

(** Extension of a substitution: the image of every binding of the tail is
    unchanged, so only the head is checked. *)
Lemma wf_sub_extend_gen : forall Θ Ξ Γ Δ σ e en,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Δ ->
    (forall A, e :: Δ ∋ #0 : A -> Θ ⍮ Ξ ⍮ Γ ⊢ sentry_exp en : A[sb_extend σ en]) ->
    (forall A M, e :: Δ ∋ #0 ≔ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ sentry_exp en ≈ M[sb_extend σ en] : A[sb_extend σ en]) ->
    (forall U, e :: Δ ∋ #0 ⇒ₘ U -> (en = se_mod (me_lit U[sb_extend σ en]ᵘ) /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[sb_extend σ en]ᵘ ≈ U[sb_extend σ en]ᵘ) \/
                                 exists y, en = se_var y /\ Γ ∋ #y ⇒ₘ U[sb_extend σ en]ᵘ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢s sb_extend σ en : e :: Δ.
Proof.
  intros * Hσ HΔ H0 H0d H0m; saturate_sub.
  econstructor; [ eassumption | eassumption | | |].
  - intros [| x] B Hlk; [ apply H0; assumption |].
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend.
    eapply wf_sub_apply; eassumption.
  - intros [| x] B L Hlk; [ apply H0d; assumption |].
    inversion Hlk; subst; reduce_index; rewrite !exp_sub_shift_extend.
    eapply wf_sub_apply_def; eassumption.
  - intros [| x] U Hlk; [ apply H0m; assumption |].
    inversion Hlk; subst; reduce_index; rewrite gunit_sub_shift_extend.
    eapply wf_sub_apply_mod; eassumption.
Qed.

(** [wf_sub_extend] *)
Lemma wf_sub_extend : forall Θ Ξ Γ Δ σ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ,,M : Δ ▹ A.
Proof.
  intros * Hσ ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn.
  rewrite exp_sub_shift_extend; assumption.
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
  intros * Hσ ? ? ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn; rewrite ?exp_sub_shift_extend; assumption.
Qed.

(** Extension into a module slot, by the literal of its unit.  The
    transported unit is taken well formed; [sub_preserves_unit] supplies it. *)
Lemma wf_sub_extend_mod : forall Θ Ξ Γ Δ σ U,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ,,ₘ me_lit U[σ]ᵘ : Δ ▹ₘ U.
Proof.
  intros * Hσ ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn.
  left; rewrite gunit_sub_shift_extend; split; [ reflexivity | assumption ].
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

Corollary wf_sub_single_mod : forall Θ Ξ Γ U,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id ,,ₘ me_lit U : Γ ▹ₘ U.
Proof.
  intros; rewrite <- (gunit_sub_id U) at 2; apply wf_sub_extend_mod; rewrite ?gunit_sub_id; mauto 3.
Qed.

(** [wf_sub_wk] *)
Lemma wf_sub_wk : forall Θ Ξ Γ Γ' Δ σ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s (sb_wk σ φ) : Δ.
Proof.
  intros * Hσ Hφ; saturate_wk; saturate_sub.
  econstructor; [ eassumption | eassumption | | |].
  - intros x A ?; rewrite <- !exp_wk_sub.
    eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
  - intros x A M ?; rewrite <- !exp_wk_sub.
    eapply wk_preserves_exp_eq; [ eapply wf_sub_apply_def; eassumption | eassumption ].
  - intros x U HU; reduce_index; rewrite <- gunit_wk_sub.
    destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ HU) as [[-> HUσ] | (y & -> & Hy)]; cbn.
    + left; split; [ reflexivity | eapply wk_preserves_unit; eassumption ].
    + right; eexists; split; [ reflexivity | eapply wf_wk_lookup_mod; eassumption ].
Qed.

(** Lifting a substitution over any entry.  As in [wf_wk_q_gen], the two
    contexts must be well formed. *)
Lemma wf_sub_q_gen : forall Θ Ξ Γ Δ σ e,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    ⊢ Θ ⍮ Ξ ⍮ centry_sub e σ :: Γ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Δ ->
    Θ ⍮ Ξ ⍮ centry_sub e σ :: Γ ⊢s q σ : e :: Δ.
Proof.
  intros * Hσ ? ?; saturate_sub.
  econstructor; [ eassumption | eassumption | | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; try (econstructor; [ eassumption | constructor ]).
    rewrite <- sentry_exp_wk; fold (exp_sub (a_var n) σ).
    eapply wk_preserves_exp; [ eapply wf_sub_apply; eassumption | mauto 2 ].
  - intros x B N Hlk.
    inversion Hlk; subst; reduce_index; rewrite !exp_wk_shift_sub_q.
    + eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    + rewrite <- sentry_exp_wk; fold (exp_sub (a_var n) σ).
      eapply wk_preserves_exp_eq; [ eapply wf_sub_apply_def; eassumption | mauto 2 ].
  - intros x U Hlk; inversion Hlk; subst; cbn.
    + right; exists 0; rewrite sb_q_zero, gunit_wk_shift_sub_q; split; [ reflexivity | constructor ].
    + rewrite sb_q_succ, gunit_wk_shift_sub_q.
      match goal with Hl : _ ∋ # _ ⇒ₘ _ |- _ => destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hl) as [[-> HUσ] | (y & -> & Hy)] end.
      * left; split; [ reflexivity | eapply wk_preserves_unit; [ eassumption | mauto 2 ] ].
      * right; exists (S y); split; [ reflexivity | constructor; assumption ].
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
  intros * Hσ ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_ass A)); mauto 2.
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
  intros * Hσ ? ? ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_def A M)); mauto 2.
Qed.

(** The lifted substitution over a module slot. *)
Lemma wf_sub_q_mod : forall Θ Ξ Γ Δ σ U,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U[σ]ᵘ ⊢s q σ : Δ ▹ₘ U.
Proof.
  intros * Hσ ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_mod U)); mauto 2.
Qed.

(** Lifting over a whole extension, given that both extended contexts are
    well formed. *)
Lemma wf_sub_ext : forall Θ Ξ Ψ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ⊢s sb_qn (length Ψ) σ : Ψ ++ Γ.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hσ HΔ HΓ; cbn in *; [ assumption |].
  apply wf_sub_q_gen; [ apply IH; eauto using ctx_decomp_tail | assumption | assumption ].
Qed.

#[export]
Hint Resolve wf_sub_extend wf_sub_extend_def wf_sub_extend_mod wf_sub_single wf_sub_single_def
  wf_sub_single_mod wf_sub_wk wf_sub_q wf_sub_q_def wf_sub_q_mod : mctt.

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
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] : A[σ].
Proof.
  intros; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_eq : forall Θ Ξ Γ Δ σ x A,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ #x[σ] : A[σ].
Proof.
  intros; apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_def : forall Θ Ξ Γ Δ σ x A M,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Δ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ M[σ] : A[σ].
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

(** The root of a well-formed module expression, if a slot, is a module slot. *)
Lemma modexp_eq_slot_root : forall Θ Ξ Γ H H',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> me_slot_root Γ H /\ me_slot_root Γ H'.
Proof.
  induction 1; cbn; destruct_all; eauto 6.
Qed.

Lemma wf_sub_ext_of_ext : forall Θ Ξ Γ Ψ Ψ' Δ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ ->
    Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ⊢s sb_qn (length Ψ) σ : Ψ ++ Γ /\
    Θ ⍮ Ξ ⍮ tele_sub Ψ' σ ++ Δ ⊢s sb_qn (length Ψ') σ : Ψ' ++ Γ.
Proof.
  intros * Hσ HΨ HΨσ; split; apply wf_sub_ext; eauto using ext_eq_ctx_left, ext_eq_ctx_right.
Qed.

(** The import checks of a body unit, moved by a substitution. *)
Lemma sub_body_checks : forall Θ Ξ Γ Δu Φ Δ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ (body_ctx Φ ++ Δu) ++ Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ ++ Δu) σ ++ Δ ->
    (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks Φ) ->
       forall Δ1 σ0, Θ ⍮ Ξ ⍮ Δ1 ⊢s σ0 : body_ctx Φ0 ++ Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ1 ⊢ᵐ E[σ0]ᵐ ≈ E[σ0]ᵐ) ->
    (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks Φ) -> List.In n ns ->
       member_ok Θ Ξ (body_ctx Φ0 ++ Δu ++ Γ) E n) ->
    (forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks (gmod_sub Φ (sb_qn (length Δu) σ))) ->
       Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ tele_sub Δu σ ++ Δ ⊢ᵐ E ≈ E) /\
    (forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks (gmod_sub Φ (sb_qn (length Δu) σ))) -> List.In n ns ->
       member_ok Θ Ξ (body_ctx Φ0 ++ tele_sub Δu σ ++ Δ) E n).
Proof.
  intros * Hσ HΨ HΨσ HE Hm.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt).
  split.
  - intros Φ0' E' ns Hin. rewrite gm_checks_sub in Hin. apply List.in_map_iff in Hin as [[Φ0 c] [Heq Hin]].
    injection Heq as Heq1 Hc'. subst Φ0'.
    destruct c as [E ns' | ? ?]; cbn in Hc'; [| discriminate ]. injection Hc' as Hc1 Hc2; subst E' ns'.
    destruct (gm_checks_body_ctx _ _ _ Hin) as [Ψ1 HΨ1].
    rewrite body_ctx_sub, List.app_assoc, <- tele_sub_app.
    assert (Hlift : Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δu) σ ++ Δ ⊢s sb_qn (length (body_ctx Φ0 ++ Δu)) σ : (body_ctx Φ0 ++ Δu) ++ Γ).
    { rewrite HΨ1, <- !List.app_assoc in HΨ, HΨσ; rewrite tele_sub_app, <- List.app_assoc in HΨσ.
      apply wf_sub_ext; [ assumption | eapply ctx_app_wf_tail; eassumption
                        | rewrite <- !List.app_assoc in HΨ |- *; exact (ctx_app_wf_tail _ _ Ψ1 _ HΨ) ]. }
    assert (Heqs : sb_eq (sb_qn (gm_binders Φ0) (sb_qn (length Δu) σ)) (sb_qn (length (body_ctx Φ0 ++ Δu)) σ))
      by (rewrite sb_qn_add, List.length_app, length_body_ctx; reflexivity).
    rewrite (modexp_sub_sb_eq _ _ _ Heqs); rewrite <- List.app_assoc in Hlift; eauto.
  - intros Φ0' E' ns n Hin. rewrite gm_checks_sub in Hin. apply List.in_map_iff in Hin as [[Φ0 c] [Heq Hin]].
    injection Heq as Heq1 Hc'. subst Φ0'.
    destruct c as [E ns' | ? ?]; cbn in Hc'; [| discriminate ]. injection Hc' as Hc1 Hc2; subst E' ns'.
    intros Hn.
    rewrite body_ctx_sub, List.app_assoc, <- tele_sub_app.
    assert (Heqs : sb_eq (sb_qn (gm_binders Φ0) (sb_qn (length Δu) σ)) (sb_qn (length (body_ctx Φ0 ++ Δu)) σ))
      by (rewrite sb_qn_add, List.length_app, length_body_ctx; reflexivity).
    rewrite (modexp_sub_sb_eq _ _ _ Heqs).
    destruct (Hm _ _ _ _ Hin Hn) as [(A & HA) | (A & HA)]; [ left | right ]; eexists;
      eapply (proj1 (member_type_sub _ _ Hc)); try eassumption;
      rewrite List.app_assoc; apply sub_mod_compat_ext; eauto with mctt.
Qed.

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
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ]) /\
  (forall Θ Ξ Δ Ψ Ψ',
      Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ) /\
  (forall Θ Ξ Δ U U',
      Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ]ᵘ) /\
  (forall Θ Ξ Δ H H',
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H[σ]ᵐ ≈ H'[σ]ᵐ).
Proof.
  apply syntactic_wf_mut_ind'; intros; saturate_sub; push_sub; lift_sub.
  all: try solve [ push_closed; mauto 3 ].
  all: try solve [ mauto 4 ].
  all: try solve [ econstructor; mauto 3 ].
  all: try solve [ lift_sub_natrec; econstructor; mauto 2 ].
  (** The module rules.  A local module is lifted over by [q σ] at the
      transported unit. *)
  all: try solve [ rewrite ?exp_sub_sub_extend_mod; eapply wf_let_mod; eauto using wf_sub_q_mod ].
  all: try solve [ rewrite !exp_sub_sub_extend_mod; eapply wf_exp_eq_let_mod_zeta; eauto using wf_sub_q_mod ].
  all: try solve [
    match goal with
    | HU : wf_unit_eq _ _ ?Γ ?U ?U', IHU : forall _ _, wf_sub _ _ _ ?Γ _ -> wf_unit_eq _ _ _ _ _,
      IHB : forall _ _, wf_sub _ _ _ (ce_mod ?U :: ?Γ) _ -> _,
      IHL : forall _ _, wf_sub _ _ _ ?Γ _ -> _,
      Hσ : wf_sub _ _ _ ?Γ _ |- _ =>
        pose proof (IHU _ _ Hσ) as HUσ;
        pose proof (IHL _ _ Hσ) as HL; rewrite exp_sub_sub_extend_mod in HL |- *;
        eapply wf_exp_eq_let_mod_cong;
        [ exact HUσ
        | apply IHB; apply wf_sub_q_mod; eauto using wf_unit_eq_refl_left
        | exact HL ]
    end ].
  (** Members.  The root of a well-formed module expression is a module slot
      or no slot, so it stays a root. *)
  all: try solve [
    match goal with
    | HH : wf_modexp_eq _ _ ?Γ ?H ?H, Hσ : wf_sub _ _ _ ?Γ ?σ |- _ =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        pose proof (wf_sub_mod_compat _ _ _ _ _ Hσ) as Hcm;
        pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ HH)) as Hr;
        first [ eapply wf_mem | eapply wf_exp_eq_mem_delta ];
        [ eapply me_noargs_sub; eassumption | eauto
        | eapply (proj1 (member_type_sub _ _ Hc)); eassumption
        | eauto
        | unfold member_unfold in *; eapply member_unfold_sub; eassumption
        | eauto ]
    end ].
  all: try solve [
    match goal with
    | HH : wf_modexp_eq _ _ ?Γ ?H ?H, Hσ : wf_sub _ _ _ ?Γ ?σ |- _ =>
        pose proof (wf_sub_mod_compat _ _ _ _ _ Hσ) as Hcm;
        pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ HH)) as Hr;
        rewrite ?apps_sub, ?member_ref_sub; first [ eapply wf_mem_app | eapply wf_exp_eq_mem_app ];
        [ eauto | eapply modexp_spine_sub; eassumption
        | match goal with H : _ <> nil |- _ => destruct args; [ contradiction H; reflexivity | discriminate ] end
        | rewrite <- member_ref_sub, <- apps_sub; eauto ]
    end ].
  (** Extensions. *)
  all: try solve [ cbn [tele_sub];
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?Ψ ?Ψ', IHx : forall _ _, wf_sub _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_sub ?Ψ _) (tele_sub ?Ψ' _),
      Hσ : wf_sub _ _ ?Δ ?Γ ?σ |- _ =>
        let Hl := fresh "Hl" in
        let Hr := fresh "Hr" in
        destruct (wf_sub_ext_of_ext _ _ _ _ _ _ _ Hσ Hx (IHx _ _ Hσ)) as [Hl Hr];
        pose proof (ext_eq_length _ _ _ _ _ Hx) as Hlen;
        first [ eapply wf_ext_eq_ass | eapply wf_ext_eq_def | eapply wf_ext_eq_mod ];
        [ exact (IHx _ _ Hσ) | .. ];
        rewrite ?Hlen in *; eauto
    end ].
  (** Units. *)
  all: try solve [ rewrite !gunit_sub_mk; cbn [moddef_sub];
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?D ?D', IHx : forall _ _, wf_sub _ _ _ ?Γ _ -> wf_ext_eq _ _ _ _ _,
      IHE : forall _ _, wf_sub _ _ _ (?D ++ ?Γ) _ -> wf_modexp_eq _ _ _ _ _,
      IHE' : forall _ _, wf_sub _ _ _ (?D' ++ ?Γ) _ -> wf_modexp_eq _ _ _ _ _,
      Hσ : wf_sub _ _ _ ?Γ _ |- wf_unit_eq _ _ _ (gu_mk (tele_sub ?D _) _) _ =>
        let Hl := fresh "Hl" in
        let Hr := fresh "Hr" in
        destruct (wf_sub_ext_of_ext _ _ _ _ _ _ _ Hσ Hx (IHx _ _ Hσ)) as [Hl Hr];
        pose proof (ext_eq_length _ _ _ _ _ Hx) as Hlen;
        eapply wf_unit_eq_alias;
        [ exact (IHx _ _ Hσ) | apply tele_ass_sub; assumption | apply tele_ass_sub; assumption
        | rewrite <- Hlen; exact (IHE _ _ Hl) | exact (IHE' _ _ Hr) ]
    end ].
  all: try solve [ rewrite !gunit_sub_mk; cbn [moddef_sub];
    match goal with
    | IHx : forall _ _, wf_sub _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_sub (body_ctx ?Φ ++ ?Δu) _) (tele_sub (body_ctx ?Φ' ++ ?Δu') _),
      Hx : wf_ext_eq _ _ ?Γ _ _,
      HE : forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks ?Φ) -> forall _ _, _,
      Hm : forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks ?Φ) -> _,
      HE' : forall Φ0 E ns, List.In (Φ0, bc_import E ns) (gm_checks ?Φ') -> forall _ _, _,
      Hm' : forall Φ0 E ns n, List.In (Φ0, bc_import E ns) (gm_checks ?Φ') -> _,
      Hσ : wf_sub _ _ _ ?Γ _ |- _ =>
        let Hxσ := fresh "Hxσ" in
        pose proof (IHx _ _ Hσ) as Hxσ;
        let Hc1 := fresh "Hc" in let Hc2 := fresh "Hc" in let Hc3 := fresh "Hc" in let Hc4 := fresh "Hc" in
        destruct (sub_body_checks _ _ _ Δu Φ _ _ Hσ ltac:(eauto with mctt) ltac:(eauto with mctt) HE Hm) as [Hc1 Hc2];
        destruct (sub_body_checks _ _ _ Δu' Φ' _ _ Hσ ltac:(eauto with mctt) ltac:(eauto with mctt) HE' Hm') as [Hc3 Hc4];
        eapply wf_unit_eq_body;
        [ rewrite !body_ctx_sub, <- !tele_sub_app; exact Hxσ
        | apply tele_ass_sub; assumption | apply tele_ass_sub; assumption
        | rewrite !length_tele_sub; assumption
        | apply body_shape_sub; assumption
        | rewrite gm_names_sub; assumption
        | exact Hc1 | exact Hc2 | exact Hc3 | exact Hc4 ]
    end ].
  (** Module expressions. *)
  all: try solve [
    match goal with
    | Hm : member_type _ _ ?Γ (me_path ?p) nil mk_mod _, Hσ : wf_sub _ _ _ ?Γ _ |- _ =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        eapply wf_me_path; [ eauto | exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ _ Hm _ _ (wf_sub_mod_compat _ _ _ _ _ Hσ)) ]
    end ].
  all: try solve [
    match goal with
    | Hx : _ ∋ #?x ⇒ₘ _, Hσ : wf_sub _ _ _ _ ?σ |- wf_modexp_eq _ _ _ (sentry_modexp (?σ ?x)) _ =>
        destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hx) as [[-> HUσ] | (y & -> & Hy)]; cbn;
        [ apply wf_me_lit; exact HUσ | eapply wf_me_var; eauto ]
    end ].
  all: try solve [
    match goal with
    | Hσ : wf_sub _ _ _ ?Γ _ |- _ =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        pose proof (wf_sub_mod_compat _ _ _ _ _ Hσ) as Hcm;
        first [ eapply wf_me_mem | eapply wf_me_app ];
        try (eapply (proj1 (member_type_sub _ _ Hc)); eassumption); eauto
    end ].
  all: try solve [
    match goal with
    | Hm : member_type _ _ ?Γ ?H nil mk_mod _, Hm' : member_type _ _ ?Γ ?H' nil mk_mod _,
      Hσ : wf_sub _ _ _ ?Γ _ |- wf_modexp_eq _ _ _ (me_app ?H[_]ᵐ _) (me_app ?H'[_]ᵐ _) =>
        assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eauto with mctt);
        eapply wf_me_app;
        [ eauto
        | exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ _ Hm _ _ (wf_sub_mod_compat _ _ _ _ _ Hσ)) | eauto | eauto | eauto | eauto
        | exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ _ Hm' _ _ (wf_sub_mod_compat _ _ _ _ _ Hσ)) | eauto | eauto | eauto | eauto ]
    end ].
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

Corollary sub_preserves_ext : forall Θ Ξ Γ Δ Ψ Ψ' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ.
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_unit : forall Θ Ξ Γ Δ U U' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ]ᵘ.
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_modexp : forall Θ Ξ Γ Δ H H' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H[σ]ᵐ ≈ H'[σ]ᵐ.
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

#[export]
Hint Resolve sub_preserves_exp sub_preserves_exp_eq sub_preserves_subtyp sub_preserves_ext sub_preserves_unit sub_preserves_modexp : mctt.

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
  econstructor; [ eassumption | eassumption | | |].
  - intros; rewrite <- !exp_sub_sub; mauto 3.
  - intros; rewrite <- !exp_sub_sub; mauto 3.
  - intros x U HU; reduce_index; rewrite <- gunit_sub_sub.
    destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ HU) as [[-> HUσ] | (y & -> & Hy)]; cbn.
    + left; split; [ reflexivity | eapply sub_preserves_unit; eassumption ].
    + eapply wf_sub_apply_mod; eassumption.
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
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ #x[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
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
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ #x[Id] ≈ M[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

(** A refinement keeps every module slot. *)
Corollary ctxsub_lookup_mod : forall Θ Ξ Γ Δ x U,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Γ ∋ #x ⇒ₘ U ->
    Δ ∋ #x ⇒ₘ U.
Proof.
  intros * H HU; destruct (wf_sub_apply_mod _ _ _ _ _ H _ _ HU) as [[[=] _] | (y & [= <-] & Hy)].
  rewrite gunit_sub_id in Hy; exact Hy.
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
    (forall U, e :: Γ ∋ #0 ⇒ₘ U -> e' :: Δ ∋ #0 ⇒ₘ U) ->
    Θ ⍮ Ξ ⍮ e' :: Δ ⊢s Id : e :: Γ.
Proof.
  intros * HId ? ? Hhd Hhdd Hhdm; saturate_sub.
  assert (Θ ⍮ Ξ ⍮ e' :: Δ ⊢w ↑ : Δ) by mauto 2.
  econstructor; [ eassumption | eassumption | | |].
  - intros [| x] B Hlk; reduce_index; rewrite exp_sub_id; [ auto |].
    inversion Hlk; subst.
    change #(S x) with #x[↑]ʷ.
    eapply wk_preserves_exp; [ eapply ctxsub_vlookup | ]; eassumption.
  - intros [| x] B N Hlk; reduce_index; rewrite !exp_sub_id; [ auto |].
    inversion Hlk; subst.
    change #(S x) with #x[↑]ʷ.
    eapply wk_preserves_exp_eq; [ eapply ctxsub_vlookup_def | ]; eassumption.
  - intros [| x] U Hlk; reduce_index; rewrite gunit_sub_id; right; eexists; split; try reflexivity; [ auto |].
    inversion Hlk; subst; constructor; eapply ctxsub_lookup_mod; eassumption.
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
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | | |];
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
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | | |];
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
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst.
  eapply wf_exp_subtyp'; [ mauto 2 | ].
  eapply wk_preserves_subtyp; eassumption.
Qed.

(** A module slot refines a slot of the same unit. *)
Lemma wf_sub_id_extend_mod : forall Θ Ξ Γ Δ U,
    Θ ⍮ Ξ ⍮ Δ ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ▹ₘ U ⊢s Id : Γ ▹ₘ U.
Proof.
  intros * HId ? ?; saturate_sub.
  eapply wf_sub_id_extend_gen; [ eassumption | mauto 2 | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; constructor.
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
             wf_sub_id_extend_def_eq wf_sub_id_extend_mod : mctt.

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
    eauto using presup_exp_ctx, presup_unit_eq_ctx.
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
