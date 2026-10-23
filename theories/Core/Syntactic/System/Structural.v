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
From Mctt.Core.Syntactic.System.Global Require Export MemberLemmas.
From Mctt.Core.Syntactic.System.Inductives Require Export Syntax.
From Mctt.Core.Syntactic.System.Records Require Export Syntax.
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

(** A small type is a type of every large universe. *)
Lemma wf_exp_small_large : forall {Θ Ξ Γ A o i},
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨𝕃ᵒ o⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof. intros; eapply wf_exp_subtyp'; [ eassumption | eapply wf_subtyp_small_large; mauto 3 ]. Qed.

(** The same at a level term, given that it is a level. *)
Lemma wf_exp_suniv_large : forall {Θ Ξ Γ A L i n},
    Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof. intros; eapply wf_exp_subtyp'; [ eassumption | eapply wf_subtyp_small_large; mauto 3 ]. Qed.

Lemma wf_exp_eq_suniv_large : forall {Θ Ξ Γ A A' L i n},
    Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨L⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp'; [ eassumption | eapply wf_subtyp_small_large; mauto 3 ]. Qed.

(** A type of a universe is a type of a large universe. *)
Lemma wf_exp_is_univ_large : forall {Θ Ξ Γ U A},
    Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊢ A : U -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof. intros * HU HA; inversion HU; subst; [ eexists; exact HA | exists 0; eapply wf_exp_suniv_large; eassumption ]. Qed.

(** The small [Π] and its congruence at a literal level, whose weakening is
    itself. *)
Lemma wf_pi_small_lit : forall {Θ Ξ Γ A B n},
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type⟨𝕃ᵒ n⟩.
Proof. intros * HA HB; eapply wf_pi_lvl; [ apply wf_llit_ord; mauto 2 | exact HA | exact HB ]. Qed.

Lemma wf_exp_eq_pi_cong_small_lit : forall {Θ Ξ Γ A A' B B' n},
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type⟨𝕃ᵒ n⟩.
Proof. intros * HA HAA HB; eapply wf_exp_eq_pi_cong_lvl; [ apply wf_llit_ord; mauto 2 | exact HA | exact HAA | exact HB ]. Qed.

Lemma wf_exp_eq_small_large : forall {Θ Ξ Γ A A' o i},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨𝕃ᵒ o⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp'; [ eassumption | eapply wf_subtyp_small_large; mauto 3 ]. Qed.

Lemma ctx_decomp : forall {Θ Ξ Γ A},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  inversion 1; eauto using presup_exp_ctx.
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Θ Ξ Γ A}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

Corollary ctx_decomp_right : forall {Θ Ξ Γ A}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * ?%ctx_decomp; easy.
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

Lemma ctx_decomp_def : forall {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  inversion 1; eauto using presup_exp_ctx.
Qed.

Corollary ctx_decomp_def_left : forall {Θ Ξ Γ A M}, ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  intros * ?%ctx_decomp_def; easy.
Qed.

Corollary ctx_decomp_def_typ : forall {Θ Ξ Γ A M},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
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

Lemma wf_wk_id : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ʷ wk_id : Γ.
Proof.
  intros; econstructor; try eassumption;
    intros; rewrite ?exp_wk_id, ?gunit_wk_id; assumption.
Qed.

Lemma wf_wk_shift : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Θ ⍮ Ξ ⍮ e :: Γ ⊢ʷ ↑ : Γ.
Proof.
  intros * H; econstructor; [ eassumption | mauto 2 | | |];
    intros; simpl; mauto 2.
Qed.

(** Lifting a weakening over any entry: the lookups move along with it.  The
    two contexts must be well formed; the rules below supply them. *)
Lemma wf_wk_q_gen : forall Θ Ξ Γ Δ φ e,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ centry_wk e φ :: Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Γ ->
    Θ ⍮ Ξ ⍮ centry_wk e φ :: Δ ⊢ʷ wk_q φ : e :: Γ.
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

(** The extra premise [Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Typeω@i] is needed for [⊢ Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ], it is
    exactly what the induction hypothesis of [wk_preserves_wf] supplies at every
    binder, and [wf_sub_q] states the corresponding premise for substitutions
    explicitly. *)
Lemma wf_wk_q : forall Θ Ξ Γ Δ φ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A.
Proof.
  intros * Hφ ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_ass A)); mauto 2.
Qed.

(** The same over a type of a universe. *)
Lemma wf_wk_q_univ : forall Θ Ξ Γ Δ φ A U U',
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊢ A : U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵤ U' -> Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : U' ->
    Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A.
Proof.
  intros * Hφ HU HA HU' HA'.
  destruct (wf_exp_is_univ_large HU HA), (wf_exp_is_univ_large HU' HA').
  apply (wf_wk_q_gen _ _ _ _ _ (ce_ass A)); [ assumption | eapply wf_ctx_extend; eassumption.. ].
Qed.

(** The same over a definition: the body is weakened along with its type. *)
Lemma wf_wk_q_def : forall Θ Ξ Γ Δ φ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ ->
    Θ ⍮ Ξ ⍮ Δ ▸ A[φ]ʷ ≔ M[φ]ʷ ⊢ʷ wk_q φ : Γ ▸ A ≔ M.
Proof.
  intros * Hφ ? ? ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_def A M)); mauto 2.
Qed.

(** The same over a module slot. *)
Lemma wf_wk_q_mod : forall Θ Ξ Γ Δ φ U,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U φ ->
    Θ ⍮ Ξ ⍮ Δ ▹ₘ gunit_wk U φ ⊢ʷ wk_q φ : Γ ▹ₘ U.
Proof.
  intros * Hφ ? ?; apply (wf_wk_q_gen _ _ _ _ _ (ce_mod U)); mauto 2.
Qed.

(** Lifting over a whole extension, given that both extended contexts are
    well formed. *)
Lemma wf_wk_ext : forall Θ Ξ Ψ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ⊢ʷ wk_qn (length Ψ) φ : Ψ ++ Γ.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hφ HΔ HΓ; cbn in *; [ assumption |].
  apply wf_wk_q_gen; [ apply IH; eauto using ctx_decomp_tail | assumption | assumption ].
Qed.

Lemma wf_wk_compose : forall Θ Ξ Γ Δ Δ' φ ψ,
    Θ ⍮ Ξ ⍮ Γ ⊢ʷ ψ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ʷ φ ⊙ ψ : Δ'.
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


(** The same for [⊥], the binder of the [⊥]-eliminator's motive. *)
Corollary wf_wk_q_False : forall Θ Ξ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ▹ ⊥ ⊢ʷ wk_q φ : Γ ▹ ⊥.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #(φ x) : A[φ]ʷ.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

Lemma wk_preserves_vlookup_eq : forall Θ Ξ Γ Δ φ x A,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #(φ x) ≈ #(φ x) : A[φ]ʷ.
Proof.
  intros * Hφ ?; saturate_wk.
  econstructor; [ eassumption | eapply wf_wk_lookup; eassumption ].
Qed.

(** δ moved along a weakening: the image of a definition is the same
    definition. *)
Lemma wk_preserves_vlookup_def : forall Θ Ξ Γ Δ φ x A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
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
  | Hc : ⊢ ?Θ ⍮ ?Ξ ⍮ _, Hl : ind_alias_lookup ?Θ ?Ξ _ = Some (?Δ, _, ?p, ?k, ?Ns), Hd : ind_lookup ?Θ ?Ξ ?p = Some ?D,
    HM : ind_member ?D ?k = Some ?Mk |- _ =>
      assert_fails (assert (exp_scoped 0 (ctx_pi Δ (ind_ty_at D Mk Ns))) by eassumption);
      let Ha := fresh "Ha" in
      pose proof (wf_ind_alias_closed _ _ _ _ _ _ _ _ _ _ _ Hc Hl Hd HM) as Ha; destruct Ha
  end.

Ltac push_closed :=
  saturate_closed;
  repeat match goal with
  | Hp : mod_qname ?H = Some _ |- context [ modexp_wk ?H ?φ ] => rewrite (mod_qname_wk H _ φ Hp)
  | Hp : mod_qname ?H = Some _ |- context [ modexp_sub ?H ?σ ] => rewrite (mod_qname_sub H _ σ Hp)
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
    [Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢ʷ q φ : Γ ▹ A] before the induction hypothesis for the body can
    be used.  It is derivable — [wf_wk_q] is a hint — but only from the
    induction hypothesis for the domain, so leaving it to [eauto] costs three
    extra levels of search on top of the rule application, which puts the wider
    cases ([λ]-E) out of reach at any depth that terminates.  Adding
    each lifted weakening to the context up front costs one [assert] instead.

    [lift_wk_False] seeds the [⊥]-eliminator case, whose binder is over the
    closed type [⊥]: [lift_wk_step] cannot start there, because the domain of
    that binder has no induction hypothesis of its own.  It is guarded by the
    presence of a motive [Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Typeω@i]. *)

Ltac lift_wk_False :=
  match goal with
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Γ) (a_typ _) _, Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass a_False) Δ ⊢ʷ wk_q φ : cons (ce_ass a_False) Γ) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_wk_q_False; exact Hφ)
  end.

Ltac lift_wk_step :=
  match goal with
  | Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ,
    IH : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_wk ?A _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_wk A φ)) Δ ⊢ʷ wk_q φ : cons (ce_ass A) Γ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_wk_q; [ exact Hφ | | exact (IH _ _ Hφ) ]; mauto 2)
  | Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ,
    IH : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (a_univ _) (exp_wk ?A _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_wk A φ)) Δ ⊢ʷ wk_q φ : cons (ce_ass A) Γ) in
      assert_fails (assert T by assumption);
      assert T by (eapply (wf_wk_q _ _ _ _ _ _ 0); [ exact Hφ | | exact (wf_exp_small_large (IH _ _ Hφ)) ];
                   eapply wf_exp_small_large; eassumption)
  end.

(** The lifted weakening over a definition, for the let rules.  It is built only
    where an induction hypothesis lives in the extended context. *)
Ltac lift_wk_def :=
  match goal with
  | Hφ : wf_wk ?Θ ?Ξ ?Δ ?Γ ?φ,
    _ : forall _ _, wf_wk ?Θ ?Ξ _ (cons (ce_def ?A ?M) ?Γ) _ -> _,
    IHA : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_wk ?A _),
    IHM : forall _ _, wf_wk ?Θ ?Ξ _ ?Γ _ -> wf_exp ?Θ ?Ξ _ (exp_wk ?A _) (exp_wk ?M _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_def (exp_wk A φ) (exp_wk M φ)) Δ ⊢ʷ wk_q φ : cons (ce_def A M) Γ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_wk_q_def; [ exact Hφ | | | exact (IHA _ _ Hφ) | exact (IHM _ _ Hφ) ]; mauto 2)
  end.

Ltac lift_wk := repeat first [ lift_wk_False | lift_wk_step | lift_wk_def ].

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

(** The motive's and the branches' contexts are of assumptions. *)
Lemma ihs_ctx_aux_ass : forall nn As Us na gs pat j, tele_ass (ihs_ctx_aux nn As Us na pat j gs).
Proof.
  induction gs as [| [] gs IH]; intros; cbn; [ constructor | apply IH |].
  apply List.Forall_app; split; [ apply IH | constructor; eauto ].
Qed.

Lemma elim_mctx_ass : forall pq D k M Us, decl_closed D -> ind_member D k = Some M -> tele_ass (elim_mctx pq D k M Us).
Proof.
  intros * HD HM; unfold elim_mctx; constructor; [ eauto | apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption ].
Qed.

Lemma elim_bctx_ass : forall pq D k M gs As Us, decl_closed D -> ind_member D k = Some M -> tele_ass (elim_bctx pq D M gs As Us).
Proof.
  intros * HD HM; unfold elim_bctx; apply List.Forall_app; split; [ apply ihs_ctx_aux_ass |].
  apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | eapply decl_closed_nparams_ass; eassumption ].
Qed.

(** The rest of an extension compared entry by entry. *)
Lemma ext_eq_cons_inv : forall Θ Ξ Γ e e' Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ e :: Ψ ≈ e' :: Ψ' -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma body_shape_wk : forall Φ Φ' φ φ', body_shape Φ Φ' -> body_shape (gmod_wk Φ φ) (gmod_wk Φ' φ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] * Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & -> & HE); repeat split; auto.
    destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in *; auto.
  - destruct Hs as (Hs & ->); split; auto.
Qed.

Lemma body_shape_sub : forall Φ Φ' σ σ', body_shape Φ Φ' -> body_shape (gmod_sub Φ σ) (gmod_sub Φ' σ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] * Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & -> & HE); repeat split; auto.
    destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in *; auto.
  - destruct Hs as (Hs & ->); split; auto.
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
Lemma wf_wk_mod_compat : forall Θ Ξ Γ Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> wk_mod_compat φ Δ Γ.
Proof. intros * Hφ x U HU; eapply wf_wk_lookup_mod; eassumption. Qed.

Lemma wf_sub_mod_compat : forall Θ Ξ Γ Δ σ, Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> sub_mod_compat σ Δ Γ.
Proof.
  intros * Hσ x U HU; destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ HU) as [[? _] | ?]; [ left | right ]; assumption.
Qed.

#[export]
Hint Resolve wf_wk_mod_compat wf_sub_mod_compat : mctt.

(** What a well-formed module expression denotes moves with a well-typed
    weakening or substitution, and so do its term part and its telescope. *)
Lemma wf_wk_mdenote : forall Θ Ξ Γ H H' R Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    mdenote Θ Ξ Δ (modexp_wk H φ) (ds_sub R (ι φ)).
Proof.
  intros * HH Hm Hφ; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply mdenote_wk; eauto using wf_gctx_closed, presup_modexp_eq_ctx, wf_wk_mod_compat.
Qed.

Lemma wf_wk_mdenote_mem : forall Θ Ξ Γ H H' x R Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    mdenote Θ Ξ Δ (me_mem (modexp_wk H φ) x) (ds_sub R (ι φ)).
Proof.
  intros * HH Hm Hφ; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  exact (mdenote_wk _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) _ _ _ Hm HΓ HHs _ _ (wf_wk_mod_compat _ _ _ _ _ Hφ)).
Qed.

Lemma wf_sub_mdenote : forall Θ Ξ Γ H H' R Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    mdenote Θ Ξ Δ H[σ]ᵐ (ds_sub R σ).
Proof.
  intros * HH Hm Hσ; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply mdenote_sub; eauto using wf_gctx_closed, presup_modexp_eq_ctx, wf_sub_mod_compat.
Qed.

Lemma wf_sub_mdenote_mem : forall Θ Ξ Γ H H' x R Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    mdenote Θ Ξ Δ (me_mem H[σ]ᵐ x) (ds_sub R σ).
Proof.
  intros * HH Hm Hσ; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  exact (mdenote_sub _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) _ _ _ Hm HΓ HHs _ _ (wf_sub_mod_compat _ _ _ _ _ Hσ)).
Qed.

Lemma wf_wk_ds_ty : forall Θ Ξ Γ Δ φ R A,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> ds_ty Θ Ξ R = Some A -> ds_ty Θ Ξ (ds_sub R (ι φ)) = Some A[φ]ʷ.
Proof. intros * Hφ; apply ds_ty_wk; eapply wf_gctx_closed, (wf_wk_dom _ _ _ _ _ Hφ). Qed.

Lemma wf_sub_ds_ty : forall Θ Ξ Γ Δ σ R A,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ -> ds_ty Θ Ξ R = Some A -> ds_ty Θ Ξ (ds_sub R σ) = Some A[σ].
Proof. intros * Hσ; apply ds_ty_sub; eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ). Qed.

Lemma wf_wk_ds_mtele : forall Θ Ξ Γ H H' R T Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> ds_mtele Θ Ξ R = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    ds_mtele Θ Ξ (ds_sub R (ι φ)) = Some (tele_wk T φ).
Proof.
  intros * HH Hm HT Hφ; eapply ds_mtele_wk; [ eapply wf_gctx_closed, presup_modexp_eq_ctx, HH | eapply wf_mdenote_scoped; eassumption | exact HT ].
Qed.

Lemma wf_wk_ds_mtele_mem : forall Θ Ξ Γ H H' x R T Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_mtele Θ Ξ R = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    ds_mtele Θ Ξ (ds_sub R (ι φ)) = Some (tele_wk T φ).
Proof.
  intros * HH Hm HT Hφ; eapply ds_mtele_wk; [ eapply wf_gctx_closed, presup_modexp_eq_ctx, HH | eapply wf_mdenote_mem_scoped; eassumption | exact HT ].
Qed.

Lemma wf_sub_ds_mtele : forall Θ Ξ Γ H H' R T Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> ds_mtele Θ Ξ R = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    ds_mtele Θ Ξ (ds_sub R σ) = Some (tele_sub T σ).
Proof.
  intros * HH Hm HT Hσ; eapply ds_mtele_sub; [ eapply wf_gctx_closed, presup_modexp_eq_ctx, HH | eapply wf_mdenote_scoped; eassumption | exact HT ].
Qed.

Lemma wf_sub_ds_mtele_mem : forall Θ Ξ Γ H H' x R T Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_mtele Θ Ξ R = Some T -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    ds_mtele Θ Ξ (ds_sub R σ) = Some (tele_sub T σ).
Proof.
  intros * HH Hm HT Hσ; eapply ds_mtele_sub; [ eapply wf_gctx_closed, presup_modexp_eq_ctx, HH | eapply wf_mdenote_mem_scoped; eassumption | exact HT ].
Qed.

Lemma ext_eq_length : forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> length Ψ = length Ψ'.
Proof. induction 1; cbn; auto. Qed.

(** The lifted weakening into an extension, from the judgments about it. *)
Lemma wf_wk_ext_of_ext : forall Θ Ξ Γ Ψ Ψ' Δ φ,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ ->
    Θ ⍮ Ξ ⍮ tele_wk Ψ φ ++ Δ ⊢ʷ wk_qn (length Ψ) φ : Ψ ++ Γ /\
    Θ ⍮ Ξ ⍮ tele_wk Ψ' φ ++ Δ ⊢ʷ wk_qn (length Ψ') φ : Ψ' ++ Γ.
Proof.
  intros * Hφ HΨ HΨφ; split; apply wf_wk_ext; eauto using ext_eq_ctx_left, ext_eq_ctx_right.
Qed.

(** ** Moving the Eliminator along an Operation

    The cases of the eliminator, with the induction hypotheses as premises,
    for any operation [R Δ σ Γ] that types a substitution [σ] from [Δ] to
    [Γ], has a well-formed domain, and lifts over a well-formed extension:
    a substitution ([wf_sub]), or a weakening seen as one ([wk_as_sub]).
    The declaration is closed, so the types of the parameters and arguments
    move with the terms they are instantiated at; the motives and the
    branches move under the binders their contexts add, which are well
    formed by the telescope premises. *)

Section ElimMove.
  Variables (Θ : gdeps) (Ξ : gstack) (R : ctx -> sub -> ctx -> Prop).
  Hypothesis R_dom : forall Δ σ Γ, R Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ.
  Hypothesis R_ext : forall Ψ Γ Δ σ, R Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
      R (tele_sub Ψ σ ++ Δ) (sb_qn (length Ψ) σ) (Ψ ++ Γ).

  Lemma mv_decl_closed : forall Δ σ Γ p D, R Δ σ Γ -> ind_lookup Θ Ξ p = Some D -> decl_closed D.
  Proof. intros * HR Hl; eapply gctx_closed_ind; [ eapply wf_gctx_closed, R_dom, HR | exact Hl ]. Qed.

  Lemma mv_ext : forall Γ Δ σ Ψ,
      R Δ σ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ σ ->
      R (tele_sub Ψ σ ++ Δ) (sb_qn (length Ψ) σ) (Ψ ++ Γ).
  Proof. intros * HR HΨ HΨσ; apply R_ext; eauto using ext_eq_ctx_left. Qed.

  Lemma mv_elim_params : forall Γ Δ σ D k M Ps,
      decl_closed D -> ind_member D k = Some M ->
      (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D M) Id Ps) j = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0]) ->
      R Δ σ Γ ->
      forall j P T, List.nth_error (List.map (fun P => P[σ]) Ps) j = Some P ->
        List.nth_error (tele_insts (im_params D M) Id (List.map (fun P => P[σ]) Ps)) j = Some T ->
        Θ ⍮ Ξ ⍮ Δ ⊢ P : T.
  Proof.
    intros * HD HM IH HR j P' T' HP HT.
    erewrite <- params_insts_sub in HT by eassumption.
    apply nth_error_map_inv in HP as (P & HP & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    eauto.
  Qed.

  (** The same for the pointwise equations of the congruence rule. *)
  Lemma mv_elim_params_eq : forall Γ Δ σ D k M Ps Ps',
      decl_closed D -> ind_member D k = Some M ->
      (forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error Ps' j = Some P' ->
         List.nth_error (tele_insts (im_params D M) Id Ps) j = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] ≈ P'[σ0] : T[σ0]) ->
      R Δ σ Γ ->
      forall j P P' T, List.nth_error (List.map (fun P => P[σ]) Ps) j = Some P ->
        List.nth_error (List.map (fun P => P[σ]) Ps') j = Some P' ->
        List.nth_error (tele_insts (im_params D M) Id (List.map (fun P => P[σ]) Ps)) j = Some T ->
        Θ ⍮ Ξ ⍮ Δ ⊢ P ≈ P' : T.
  Proof.
    intros * HD HM IH HR j P0 P0' T' HP HP' HT.
    erewrite <- params_insts_sub in HT by eassumption.
    apply nth_error_map_inv in HP as (P & HP & ->); apply nth_error_map_inv in HP' as (P' & HP' & ->).
    apply nth_error_map_inv in HT as (T & HT & ->).
    eauto.
  Qed.

  (** The uniform parameters an eliminator carries, moved. *)
  Lemma mv_elim_ups : forall D Ps Us σ, Us = List.firstn (ind_nu D) Ps ->
      List.map (fun U => U[σ]) Us = List.firstn (ind_nu D) (List.map (fun P => P[σ]) Ps).
  Proof. intros * ->; rewrite List.firstn_map; reflexivity. Qed.

  Lemma mv_elim_cargs : forall Γ Δ σ p D k M c gs Ps As,
      decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs -> List.length Ps = im_np D M ->
      (forall j N T, List.nth_error As j = Some N ->
         List.nth_error (tele_insts (cargs_ctx p D M gs) (sb_of_list Id Ps) As) j = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : T[σ0]) ->
      R Δ σ Γ ->
      forall j N T, List.nth_error (List.map (fun N => N[σ]) As) j = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D M gs) (sb_of_list Id (List.map (fun P => P[σ]) Ps))
                          (List.map (fun N => N[σ]) As)) j = Some T ->
        Θ ⍮ Ξ ⍮ Δ ⊢ N : T.
  Proof.
    intros * HD HM Hc Hl IH HR j N' T' HN HT.
    erewrite <- cargs_insts_sub in HT by eassumption.
    apply nth_error_map_inv in HN as (N & HN & ->); apply nth_error_map_inv in HT as (T & HT & ->).
    eauto.
  Qed.

  (** The context of a motive, of an annotation, of a branch. *)
  Lemma mv_motive_ctx : forall Γ Δ σ p D k M Us,
      decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D -> R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k M Us ≈ elim_mctx p D k M Us ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (elim_mctx p D k M Us) σ ≈ tele_sub (elim_mctx p D k M Us) σ ->
      R (elim_mctx p D k M (List.map (fun U => U[σ]) Us) ++ Δ) (sb_qn (S (im_nn M)) σ) (elim_mctx p D k M Us ++ Γ).
  Proof.
    intros * HD HM Hl HR HΨ HΨσ.
    erewrite <- elim_mctx_sub by eassumption; rewrite <- (length_elim_mctx p D k M Us).
    apply mv_ext; assumption.
  Qed.

  Lemma mv_ann_ctx : forall Γ Δ σ p D k M Us,
      decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D -> R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k M Us ≈ elim_mctx p D k M Us ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (elim_mctx p D k M Us) σ ≈ tele_sub (elim_mctx p D k M Us) σ ->
      R (tele_sub (im_nparams M) (sb_of_list Id (List.map (fun U => U[σ]) Us)) ++ Δ) (sb_qn (im_nn M) σ)
        (tele_sub (im_nparams M) (sb_of_list Id Us) ++ Γ).
  Proof.
    intros * HD HM Hl HR HΨ HΨσ; unfold elim_mctx in HΨ, HΨσ; cbn [tele_sub] in HΨσ.
    apply ext_eq_cons_inv in HΨ; apply ext_eq_cons_inv in HΨσ.
    erewrite <- nparams_sub by eassumption.
    rewrite <- (length_nparams_sub M (sb_of_list Id Us)).
    apply mv_ext; assumption.
  Qed.

  Lemma mv_branch_ctx : forall Γ Δ σ p D k M c gs Bks Us,
      decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs -> List.length Us = ind_nu D ->
      blocks_nm_ok D Bks -> R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D M gs (blocks_motives Bks) Us ≈ elim_bctx p D M gs (blocks_motives Bks) Us ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (elim_bctx p D M gs (blocks_motives Bks) Us) σ
                   ≈ tele_sub (elim_bctx p D M gs (blocks_motives Bks) Us) σ ->
      R (elim_bctx p D M gs (blocks_motives (blocks_sub Bks σ)) (List.map (fun U => U[σ]) Us) ++ Δ)
        (sb_qn (im_nn M + List.length gs + cargs_nrec gs) σ) (elim_bctx p D M gs (blocks_motives Bks) Us ++ Γ).
  Proof.
    intros * HD HM Hc Hl Hnm HR HΨ HΨσ.
    erewrite <- elim_bctx_sub; [| eassumption | eassumption | apply cons_lookup_in; eassumption | eassumption |].
    - replace (im_nn M + List.length gs + cargs_nrec gs) with (List.length (elim_bctx p D M gs (blocks_motives Bks) Us))
        by (rewrite length_elim_bctx; lia).
      apply mv_ext; assumption.
    - intros j Mj HMj; eapply blocks_motives_sub; eassumption.
  Qed.

  (** The blocks moved, premise by premise. *)
  Lemma mv_blocks_bctx : forall Γ Δ σ p D Bks Us,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> R Δ σ Γ ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0) ->
      forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Δ ⊢ˣ elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ)) (List.map (fun U => U[σ]) Us)
                     ≈ elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ)) (List.map (fun U => U[σ]) Us).
  Proof.
    intros * HD Hl Hnm HR IH k Mk c gs HMk Hc.
    erewrite <- elim_bctx_sub; [ eapply IH; eassumption | eassumption | eassumption | apply cons_lookup_in; eassumption
                               | eassumption |].
    intros j Mj HMj; eapply blocks_motives_sub; eassumption.
  Qed.

  Lemma mv_blocks_ann : forall Γ Δ σ p D Bks Us,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> R Δ σ Γ ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id Us) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk Us) σ0) ->
      forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.map (fun U => U[σ]) Us)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.map (fun U => U[σ]) Us).
  Proof.
    intros * HD Hl Hnm HR IHZ k Mk b' Z' HMk Hb' HZ'.
    rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm.
    destruct oZ as [Z |]; cbn in HZ'; [| discriminate ]; injection HZ' as <-.
    replace (im_nn Mk - 0) with (im_nn Mk) by lia.
    pose proof (IHZ _ _ _ _ HMk Hb eq_refl _ _ HR) as H.
    erewrite elim_mctx_sub in H by eassumption; cbn [tele_sub] in H.
    rewrite length_nparams_sub in H; erewrite nparams_sub in H by eassumption; exact H.
  Qed.

  Lemma mv_blocks_motive : forall Γ Δ σ p D Bks Us i,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> R Δ σ Γ ->
      (forall k Mk, ind_member D k = Some Mk -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk Us ≈ elim_mctx p D k Mk Us) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk Us) σ0 ≈ tele_sub (elim_mctx p D k Mk Us) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk Us ++ Γ) -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0]) ->
      forall k Mk b, ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.map (fun U => U[σ]) Us) ++ Δ ⊢ eb_motive b : Typeω@i.
  Proof.
    intros * HD Hl Hnm HR HΨ IHΨ IHA k Mk b' HMk Hb'.
    rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm.
    exact (IHA _ _ _ HMk Hb _ _ (mv_motive_ctx _ _ _ _ _ _ _ _ HD HMk Hl HR (HΨ _ _ HMk) (IHΨ _ _ HMk _ _ HR))).
  Qed.

  Lemma mv_blocks_motive_eq : forall Γ Δ σ p D Bks Bks' Us i,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> blocks_nm_ok D Bks' -> R Δ σ Γ ->
      (forall k Mk, ind_member D k = Some Mk -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk Us ≈ elim_mctx p D k Mk Us) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk Us) σ0 ≈ tele_sub (elim_mctx p D k Mk Us) σ0) ->
      (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk Us ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] ≈ (eb_motive b')[σ0] : Typeω@i[σ0]) ->
      forall k Mk b b', ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b ->
        List.nth_error (blocks_sub Bks' σ) k = Some b' ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.map (fun U => U[σ]) Us) ++ Δ ⊢ eb_motive b ≈ eb_motive b' : Typeω@i.
  Proof.
    intros * HD Hl Hnm Hnm' HR HΨ IHΨ IHA k Mk b1 b1' HMk Hb1 Hb1'.
    rewrite nth_error_blocks_sub in Hb1, Hb1'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb1; [| discriminate ]; injection Hb1 as <-.
    destruct (List.nth_error Bks' k) as [[nm' oZ' A' Bs'] |] eqn:Hb'; cbn in Hb1'; [| discriminate ]; injection Hb1' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; pose proof (Hnm' _ _ _ HMk Hb') as Enm'; cbn in Enm, Enm'; subst nm nm'.
    exact (IHA _ _ _ _ HMk Hb Hb' _ _ (mv_motive_ctx _ _ _ _ _ _ _ _ HD HMk Hl HR (HΨ _ _ HMk) (IHΨ _ _ HMk _ _ HR))).
  Qed.

  Lemma mv_blocks_names : forall D Bks σ,
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
      forall k Mk b, ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b -> brs_names (im_cons Mk) (eb_brs b).
  Proof.
    intros * Hn k Mk b' HMk Hb'; rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    cbn; unfold brs_sub; apply brs_names_map; exact (Hn _ _ _ HMk Hb).
  Qed.

  Lemma mv_blocks_fst : forall Bks Bks' σ,
      (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' -> List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
      forall k b b', List.nth_error (blocks_sub Bks σ) k = Some b -> List.nth_error (blocks_sub Bks' σ) k = Some b' ->
        List.map fst (eb_brs b) = List.map fst (eb_brs b').
  Proof.
    intros * Hf k b1 b1' Hb1 Hb1'; rewrite nth_error_blocks_sub in Hb1, Hb1'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb1; [| discriminate ]; injection Hb1 as <-.
    destruct (List.nth_error Bks' k) as [[nm' oZ' A' Bs'] |] eqn:Hb'; cbn in Hb1'; [| discriminate ]; injection Hb1' as <-.
    cbn; unfold brs_sub; rewrite !brs_fst_map; exact (Hf _ _ _ Hb Hb').
  Qed.

  Lemma mv_blocks_counts : forall D Bks σ,
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b ->
        ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat.
  Proof.
    intros * Hk k Mk b' c gs n B' HMk Hb' Hc Hin; rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    cbn in Hin; unfold brs_sub in Hin; apply brs_in_map in Hin as (B & Hin & ->).
    exact (Hk _ _ _ _ _ _ _ HMk Hb Hc Hin).
  Qed.

  Lemma mv_blocks_brs : forall Γ Δ σ p D Bks Us,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> R Δ σ Γ ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) Us ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) Us)[σ0]) ->
      forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b ->
        ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ)) (List.map (fun U => U[σ]) Us) ++ Δ
          ⊢ B : elim_bty p k Mk c gs (eb_motive b) (List.map (fun U => U[σ]) Us).
  Proof.
    intros * HD Hl Hnm HR HΨB IHΨB Hk IHB k Mk b' c gs n B' HMk Hb' Hc Hin.
    rewrite nth_error_blocks_sub in Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb'; [| discriminate ]; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm.
    cbn [eblock_sub eb_brs eb_motive] in Hin |- *; unfold brs_sub in Hin; apply brs_in_map in Hin as (B & Hin & ->); cbn [fst snd].
    pose proof (Hk _ _ _ _ _ _ _ HMk Hb Hc Hin) as En; cbn in En; subst n.
    erewrite <- elim_bty_sub by eassumption.
    apply (IHB _ _ _ _ _ _ _ HMk Hb Hc Hin).
    eapply mv_branch_ctx; eauto.
  Qed.

  Lemma mv_blocks_brs_eq : forall Γ Δ σ p D Bks Bks' Us,
      decl_closed D -> List.length Us = ind_nu D -> blocks_nm_ok D Bks -> blocks_nm_ok D Bks' -> R Δ σ Γ ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) Us ≈ elim_bctx p D Mk gs (blocks_motives Bks) Us) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) Us) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         List.nth_error Bks' k = Some b' ->
         List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (eb_brs b') i = Some (c, n, B') ->
         ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] ≈ B'[σ0] : (elim_bty p k Mk c gs (eb_motive b) Us)[σ0]) ->
      forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error (blocks_sub Bks σ) k = Some b ->
        List.nth_error (blocks_sub Bks' σ) k = Some b' ->
        List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (eb_brs b') i = Some (c, n, B') ->
        ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks σ)) (List.map (fun U => U[σ]) Us) ++ Δ
          ⊢ B ≈ B' : elim_bty p k Mk c gs (eb_motive b) (List.map (fun U => U[σ]) Us).
  Proof.
    intros * HD Hl Hnm Hnm' HR HΨB IHΨB Hk IHB k Mk b1 b1' i c gs n B1 B1' HMk Hb1 Hb1' Hi Hi' Hc.
    rewrite nth_error_blocks_sub in Hb1, Hb1'.
    destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:Hb; cbn in Hb1; [| discriminate ]; injection Hb1 as <-.
    destruct (List.nth_error Bks' k) as [[nm' oZ' A' Bs'] |] eqn:Hb'; cbn in Hb1'; [| discriminate ]; injection Hb1' as <-.
    pose proof (Hnm _ _ _ HMk Hb) as Enm; cbn in Enm; subst nm.
    cbn [eblock_sub eb_brs eb_motive] in Hi, Hi' |- *; unfold brs_sub in Hi, Hi'.
    apply nth_error_map_inv in Hi as ([[c1 n1] B] & Hi & Heq1); cbn in Heq1; injection Heq1 as -> -> ->.
    apply nth_error_map_inv in Hi' as ([[c2 n2] B'] & Hi' & Heq2); cbn in Heq2; injection Heq2 as -> -> ->.
    pose proof (Hk _ _ _ _ _ _ _ HMk Hb Hc (List.nth_error_In _ _ Hi)) as En; cbn in En; subst n2.
    erewrite <- elim_bty_sub by eassumption.
    apply (IHB _ _ _ _ _ _ _ _ _ _ HMk Hb Hb' Hi Hi' Hc).
    eapply mv_branch_ctx; eauto.
  Qed.

  (** The four rules of the eliminator. *)
  Lemma mv_elim_case : forall p D oq Us m Mm Bks bm Ps Γ M i Δ σ,
      ind_lookup Θ Ξ p = Some D ->
      elim_grp D oq p m ->
      ind_member D m = Some Mm ->
      List.nth_error Bks m = Some bm ->
      List.length Bks = List.length (ind_members D) ->
      List.length Ps = im_np D Mm ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[σ0]) ->
      Us = List.firstn (ind_nu D) Ps ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0]) ->
      (forall k Mk, ind_member D k = Some Mk ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                      ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim oq Us m Bks M)[σ] : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[σ].
  Proof.
    intros * Hl Hg HMm Hbm HlB HlP IHPs IHM Hann Hnm IHZ IHA HΨ IHΨ Hn HΨB IHΨB Hk IHB HR.
    pose proof (mv_decl_closed _ _ _ _ _ HR Hl) as HD.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
    rewrite exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
    eapply wf_elim; [ exact Hl | exact Hg | exact HMm | rewrite nth_error_blocks_sub, Hbm; reflexivity
                    | rewrite length_blocks_sub; exact HlB | rewrite List.length_map; exact HlP | .. ].
    - eapply mv_elim_params; eassumption.
    - rewrite <- ind_mty_split_sub by (try assumption; unfold im_np in HlP; lia); exact (IHM _ _ HR).
    - apply mv_elim_ups; exact Hann.
    - apply blocks_nm_ok_sub; exact Hnm.
    - rewrite List.firstn_map; eapply mv_blocks_ann; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_motive; eassumption.
    - intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption; exact (IHΨ _ _ HMk _ _ HR).
    - apply mv_blocks_names; exact Hn.
    - rewrite List.firstn_map; eapply mv_blocks_bctx; eassumption.
    - apply mv_blocks_counts; exact Hk.
    - rewrite List.firstn_map; eapply mv_blocks_brs; eassumption.
  Qed.

  Lemma mv_elim_cong_case : forall p D oq oq' Us Us' m Mm Bks Bks' bm Ps Ps' Γ M M' i Δ σ,
      ind_lookup Θ Ξ p = Some D ->
      elim_grp D oq p m ->
      elim_grp D oq' p m ->
      ind_member D m = Some Mm ->
      List.nth_error Bks m = Some bm ->
      List.length Bks = List.length (ind_members D) ->
      List.length Bks' = List.length (ind_members D) ->
      List.length Ps = im_np D Mm ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0]) ->
      List.length Ps' = im_np D Mm ->
      (forall k P P' T, List.nth_error Ps k = Some P -> List.nth_error Ps' k = Some P' ->
         List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] ≈ P'[σ0] : T[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] ≈ M'[σ0] : (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[σ0]) ->
      Us = List.firstn (ind_nu D) Ps ->
      Us' = List.firstn (ind_nu D) Ps' ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_nm b = S (im_nn Mk)) ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0]) ->
      (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] ≈ (eb_motive b')[σ0] : Typeω@i[σ0]) ->
      (forall k Mk, ind_member D k = Some Mk ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
      (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
         List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                      ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         List.nth_error Bks' k = Some b' ->
         List.nth_error (eb_brs b) i = Some (c, n, B) -> List.nth_error (eb_brs b') i = Some (c, n, B') ->
         ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] ≈ B'[σ0] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim oq Us m Bks M)[σ] ≈ (a_elim oq' Us' m Bks' M')[σ]
        : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[σ].
  Proof.
    intros * Hl Hg Hg' HMm Hbm HlB HlB' HlP IHPs HlP' IHPs' IHM Hann Hann' Hnm Hnm' IHZ IHZ' IHA IHAA HΨ IHΨ Hn Hf HΨB IHΨB Hk IHB HR.
    pose proof (mv_decl_closed _ _ _ _ _ HR Hl) as HD.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
    rewrite !exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
    eapply wf_exp_eq_elim_cong;
      [ exact Hl | exact Hg | exact Hg' | exact HMm | rewrite nth_error_blocks_sub, Hbm; reflexivity
      | rewrite length_blocks_sub; exact HlB | rewrite length_blocks_sub; exact HlB' | rewrite List.length_map; exact HlP | .. ].
    - eapply mv_elim_params; eassumption.
    - rewrite List.length_map; exact HlP'.
    - eapply mv_elim_params_eq; eassumption.
    - rewrite <- ind_mty_split_sub by (try assumption; unfold im_np in HlP; lia); exact (IHM _ _ HR).
    - apply mv_elim_ups; exact Hann.
    - apply mv_elim_ups; exact Hann'.
    - apply blocks_nm_ok_sub; exact Hnm.
    - apply blocks_nm_ok_sub; exact Hnm'.
    - rewrite List.firstn_map; eapply mv_blocks_ann; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_ann; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_motive; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_motive_eq; eassumption.
    - intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption; exact (IHΨ _ _ HMk _ _ HR).
    - apply mv_blocks_names; exact Hn.
    - apply mv_blocks_fst; exact Hf.
    - rewrite List.firstn_map; eapply mv_blocks_bctx; eassumption.
    - apply mv_blocks_counts; exact Hk.
    - rewrite List.firstn_map; eapply mv_blocks_brs_eq; eassumption.
  Qed.

  Lemma mv_elim_iota_case : forall p D oq Us m Mm Bks bm c gs Ps As Γ i n B Δ σ,
      ind_lookup Θ Ξ p = Some D ->
      elim_grp D oq p m ->
      ind_member D m = Some Mm ->
      List.nth_error Bks m = Some bm ->
      ind_con Mm c = Some gs ->
      List.length Bks = List.length (ind_members D) ->
      List.length Ps = im_np D Mm ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0]) ->
      List.length As = List.length gs ->
      (forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : T[σ0]) ->
      Us = List.firstn (ind_nu D) Ps ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0]) ->
      (forall k Mk, ind_member D k = Some Mk ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                      ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[σ0]) ->
      brs_lookup (eb_brs bm) c = Some (n, B) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                      (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As)))[σ]
        ≈ (B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                            elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As)])[σ]
        : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                            apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                              (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)])[σ].
  Proof.
    intros * Hl Hg HMm Hbm Hc HlB HlP IHPs HlA IHAs Hann Hnm IHZ IHA HΨ IHΨ Hn HΨB IHΨB Hk IHB HlkB HR.
    pose proof (mv_decl_closed _ _ _ _ _ HR Hl) as HD.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
    pose proof (brs_lookup_in _ _ _ _ HlkB) as HinB.
    pose proof (Hk _ _ _ _ _ _ _ HMm Hbm Hc HinB) as En.
    rewrite exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
    rewrite exp_sub_sb_of_list, !apps_exp_sub, !List.map_app; cbn [exp_sub].
    erewrite im_pre_sub, elim_ihs_sub_inst by first [ eassumption | apply cons_lookup_in; eassumption ].
    rewrite <- !List.skipn_map, <- List.firstn_map.
    replace (List.length (List.skipn (ind_nu D) Ps ++ As ++ elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As))
      with n by (rewrite !List.length_app, List.length_skipn, length_elim_ihs by assumption; unfold im_np in HlP; lia).
    eapply wf_exp_eq_elim_iota with (n := n) (B := B[sb_qn n σ]);
      [ exact (R_dom _ _ _ HR) | exact Hl | exact Hg | exact HMm | rewrite nth_error_blocks_sub, Hbm; reflexivity
      | exact Hc | rewrite length_blocks_sub; exact HlB | rewrite List.length_map; exact HlP | .. ].
    - eapply mv_elim_params; eassumption.
    - rewrite !List.length_map; exact HlA.
    - eapply mv_elim_cargs; eassumption.
    - apply mv_elim_ups; exact Hann.
    - apply blocks_nm_ok_sub; exact Hnm.
    - rewrite List.firstn_map; eapply mv_blocks_ann; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_motive; eassumption.
    - intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption; exact (IHΨ _ _ HMk _ _ HR).
    - apply mv_blocks_names; exact Hn.
    - rewrite List.firstn_map; eapply mv_blocks_bctx; eassumption.
    - apply mv_blocks_counts; exact Hk.
    - rewrite List.firstn_map; eapply mv_blocks_brs; eassumption.
    - destruct bm as [nm oZ A Bs]; cbn in HlkB |- *; rewrite brs_lookup_sub, HlkB; reflexivity.
  Qed.

  Lemma mv_elim_view_case : forall p D oq Us m Mm qc k' Is vm D' Bks bm Ps Γ M i Δ σ,
      ind_lookup Θ Ξ p = Some D ->
      elim_grp D oq p m ->
      ind_member D m = Some Mm ->
      im_head Mm = mh_view qc k' Is vm ->
      ind_lookup Θ Ξ qc = Some D' ->
      vwrap_ok D D' vm ->
      List.nth_error Bks m = Some bm ->
      List.length Bks = List.length (ind_members D) ->
      List.length Ps = im_np D Mm ->
      (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[σ0]) ->
      Us = List.firstn (ind_nu D) Ps ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
      (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         forall Δ0 σ0, R Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0]) ->
      (forall k Mk, ind_member D k = Some Mk ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                      ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
      (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0
                      ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
      (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
         ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
         forall Δ0 σ0, R Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim oq Us m Bks M)[σ]
        ≈ (a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
             (vwrap p D D' vm (List.firstn (ind_nu D) Ps) Bks) M)[σ]
        : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[σ].
  Proof.
    intros * Hl Hg HMm Hh HD' Hvw Hbm HlB HlP IHPs IHM Hann Hnm IHZ IHA HΨ IHΨ Hn HΨB IHΨB Hk IHB HR.
    pose proof (mv_decl_closed _ _ _ _ _ HR Hl) as HD.
    assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
    rewrite !exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
    rewrite (im_pre_sub D m Mm) by assumption.
    rewrite vwrap_sub, <- List.firstn_map by assumption.
    eapply wf_exp_eq_elim_view;
      [ exact Hl | exact Hg | exact HMm | exact Hh | exact HD' | exact Hvw | rewrite nth_error_blocks_sub, Hbm; reflexivity
      | rewrite length_blocks_sub; exact HlB | rewrite List.length_map; exact HlP | .. ].
    - eapply mv_elim_params; eassumption.
    - rewrite <- ind_mty_split_sub by (try assumption; unfold im_np in HlP; lia); exact (IHM _ _ HR).
    - apply mv_elim_ups; exact Hann.
    - apply blocks_nm_ok_sub; exact Hnm.
    - rewrite List.firstn_map; eapply mv_blocks_ann; eassumption.
    - rewrite List.firstn_map; eapply mv_blocks_motive; eassumption.
    - intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption; exact (IHΨ _ _ HMk _ _ HR).
    - apply mv_blocks_names; exact Hn.
    - rewrite List.firstn_map; eapply mv_blocks_bctx; eassumption.
    - apply mv_blocks_counts; exact Hk.
    - rewrite List.firstn_map; eapply mv_blocks_brs; eassumption.
  Qed.
End ElimMove.

(** ** The Rules of Records, Moved

    A record's declaration is closed, so only the parameters, the fields
    and the projected term move.  The premises about the declaration are
    about fixed contexts: their induction hypotheses are read back at the
    identity ([R_id]). *)
Section RecordMove.
  Variables (Θ : gdeps) (Ξ : gstack) (R : ctx -> sub -> ctx -> Prop).
  Hypothesis R_dom : forall Δ σ Γ, R Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ.

  Lemma mv_record_closed : forall Δ σ Γ p Rd, R Δ σ Γ -> record_lookup Θ Ξ p = Some Rd -> record_closed Rd.
  Proof. intros * HR Hl; eapply wf_record_closed; [ eapply R_dom, HR | exact Hl ]. Qed.

  Lemma mv_record_params : forall Γ Δ σ Rd Ns, record_closed Rd ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params Rd) Id Ns) j = Some A ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : A[σ0]) ->
      R Δ σ Γ ->
      forall j N A, List.nth_error (List.map (fun N => N[σ]) Ns) j = Some N ->
        List.nth_error (tele_insts (record_params Rd) Id (List.map (fun N => N[σ]) Ns)) j = Some A ->
        Θ ⍮ Ξ ⍮ Δ ⊢ N : A.
  Proof.
    intros * HRd IH HR j N' A' HN HA.
    rewrite <- record_params_insts_sub in HA by exact HRd.
    apply nth_error_map_inv in HN as (N & HN & ->); apply nth_error_map_inv in HA as (A & HA & ->).
    eauto.
  Qed.

  (** The first fields' context is a tail of all of them. *)
  Lemma record_fctx_split : forall Rd k, k <= List.length (record_fields Rd) ->
      exists Ψ, record_fctx Rd (List.length (record_fields Rd)) = Ψ ++ record_fctx Rd k.
  Proof.
    intros Rd k Hk; unfold record_fctx; rewrite List.firstn_all.
    generalize (record_fields Rd) as l; intros l.
    exists (List.rev (List.map (fun fT => ce_ass (snd fT)) (List.skipn k l))).
    rewrite <- (List.firstn_skipn k l) at 1; rewrite List.map_app, List.rev_app_distr; reflexivity.
  Qed.

  (** The premises of the type former's rule, in their fixed contexts, read
      back from their induction hypotheses at the identity. *)
  Lemma mv_record_premises : forall Rd i Δ σ Γ,
      (forall Γ0, ⊢ Θ ⍮ Ξ ⍮ Γ0 -> R Γ0 Id Γ0) ->
      (forall Δ0 σ0, R Δ0 σ0 ⋅ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (record_ty Rd)[σ0] : Typeω@i[σ0]) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx Rd (List.length (record_fields Rd)) ++ record_params Rd ->
      (forall Δ0 σ0, R Δ0 σ0 (record_params Rd) -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵤ (record_sort Rd)[σ0]) ->
      (forall k f T, List.nth_error (record_fields Rd) k = Some (f, T) ->
         forall Δ0 σ0, R Δ0 σ0 (record_fctx Rd k ++ record_params Rd) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] : ((record_sort Rd)[wk_shiftn k]ʷ)[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty Rd : Typeω@i /\
      Θ ⍮ Ξ ⍮ record_params Rd ⊢ᵤ record_sort Rd /\
      (forall k f T, List.nth_error (record_fields Rd) k = Some (f, T) ->
         Θ ⍮ Ξ ⍮ record_fctx Rd k ++ record_params Rd ⊢ T : (record_sort Rd)[wk_shiftn k]ʷ).
  Proof.
    intros * R_id Hty Hc Hs Hf HR.
    assert (Hnil : ⊢ Θ ⍮ Ξ ⍮ ⋅)
      by (apply (ctx_app_wf_tail _ _ Δ); rewrite List.app_nil_r; exact (R_dom _ _ _ HR)).
    split; [| split ].
    - pose proof (Hty _ _ (R_id _ Hnil)) as H; rewrite !exp_sub_id in H; exact H.
    - pose proof (Hs _ _ (R_id _ (ctx_app_wf_tail _ _ _ _ Hc))) as H; rewrite !exp_sub_id in H; exact H.
    - intros k f T Hk.
      destruct (record_fctx_split Rd k ltac:(pose proof (nth_error_lt_length _ _ _ Hk); lia)) as [Ψ HΨ].
      rewrite HΨ, <- List.app_assoc in Hc.
      pose proof (Hf _ _ _ Hk _ _ (R_id _ (ctx_app_wf_tail _ _ _ _ Hc))) as H; rewrite !exp_sub_id in H; exact H.
  Qed.

  Lemma mv_record_case : forall p Rd Γ i Δ σ,
      (forall Γ0, ⊢ Θ ⍮ Ξ ⍮ Γ0 -> R Γ0 Id Γ0) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.NoDup (List.map fst (record_fields Rd)) ->
      tele_ass (record_params Rd) ->
      (forall Δ0 σ0, R Δ0 σ0 ⋅ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (record_ty Rd)[σ0] : Typeω@i[σ0]) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx Rd (List.length (record_fields Rd)) ++ record_params Rd ->
      (forall Δ0 σ0, R Δ0 σ0 (record_params Rd) -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵤ (record_sort Rd)[σ0]) ->
      (forall k f T, List.nth_error (record_fields Rd) k = Some (f, T) ->
         forall Δ0 σ0, R Δ0 σ0 (record_fctx Rd k ++ record_params Rd) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] : ((record_sort Rd)[wk_shiftn k]ʷ)[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_record p)[σ] : (record_ty Rd)[σ].
  Proof.
    intros * R_id Hl Hnd Hass Hty Hc Hs Hf HR.
    destruct (mv_record_premises _ _ _ _ _ R_id Hty Hc Hs Hf HR) as (Hty' & Hs' & Hf').
    rewrite (record_ty_sub _ _ (mv_record_closed _ _ _ _ _ HR Hl)); cbn.
    eapply wf_record; eauto.
  Qed.

  Lemma mv_record_cong_case : forall p Rd Γ i Δ σ,
      (forall Γ0, ⊢ Θ ⍮ Ξ ⍮ Γ0 -> R Γ0 Id Γ0) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.NoDup (List.map fst (record_fields Rd)) ->
      tele_ass (record_params Rd) ->
      (forall Δ0 σ0, R Δ0 σ0 ⋅ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (record_ty Rd)[σ0] : Typeω@i[σ0]) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx Rd (List.length (record_fields Rd)) ++ record_params Rd ->
      (forall Δ0 σ0, R Δ0 σ0 (record_params Rd) -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵤ (record_sort Rd)[σ0]) ->
      (forall k f T, List.nth_error (record_fields Rd) k = Some (f, T) ->
         forall Δ0 σ0, R Δ0 σ0 (record_fctx Rd k ++ record_params Rd) ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] : ((record_sort Rd)[wk_shiftn k]ʷ)[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_record p)[σ] ≈ (a_record p)[σ] : (record_ty Rd)[σ].
  Proof.
    intros * R_id Hl Hnd Hass Hty Hc Hs Hf HR.
    destruct (mv_record_premises _ _ _ _ _ R_id Hty Hc Hs Hf HR) as (Hty' & Hs' & Hf').
    rewrite (record_ty_sub _ _ (mv_record_closed _ _ _ _ _ HR Hl)); cbn.
    eapply wf_exp_eq_record_cong; eauto.
  Qed.

  Lemma mv_tuple_case : forall T p Ns Rd fs i Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] : Typeω@i[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] ≈ (apps_exp (a_record p) Ns)[σ0] : Typeω@i[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_record p)[σ0] : (record_ty Rd)[σ0]) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.length Ns = List.length (record_params Rd) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params Rd) Id Ns) k = Some A ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : A[σ0]) ->
      List.map fst fs = List.map fst (record_fields Rd) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields Rd) k = Some (f, U) ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : (U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))])[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_tuple T fs)[σ] : T[σ].
  Proof.
    intros * IHTy IHT IHr Hl Hn IHN Hnames IHf HR.
    pose proof (mv_record_closed _ _ _ _ _ HR Hl) as HRd.
    cbn [exp_sub].
    eapply wf_tuple with (Ns := List.map (fun N => N[σ]) Ns).
    - exact (IHTy _ _ HR).
    - pose proof (IHT _ _ HR) as H; rewrite apps_exp_sub in H; exact H.
    - pose proof (IHr _ _ HR) as H; rewrite record_ty_sub in H by exact HRd; exact H.
    - exact Hl.
    - rewrite List.length_map; exact Hn.
    - eapply mv_record_params; eassumption.
    - rewrite tuple_names_sub; exact Hnames.
    - intros k f M' U HM' HU.
      apply nth_error_map_inv in HM' as ([f0 M] & HM & [= -> ->]); cbn.
      pose proof (IHf _ _ _ _ HM HU _ _ HR) as H.
      rewrite (record_field_sub _ _ _ _ _ _ _ HRd HU Hn) in H.
      + rewrite tuple_values_sub in H; exact H.
      + rewrite List.length_firstn, List.length_map; pose proof (nth_error_lt_length _ _ _ HM); lia.
  Qed.

  Lemma mv_proj_case : forall M p Ns Rd k f U i Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : (apps_exp (a_record p) Ns)[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_record p)[σ0] : (record_ty Rd)[σ0]) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.length Ns = List.length (record_params Rd) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params Rd) Id Ns) k = Some A ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : A[σ0]) ->
      List.nth_error (record_fields Rd) k = Some (f, U) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (U[sb_of_list Id (Ns ++ record_pre Rd k M)])[σ0] : Typeω@i[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_proj f M)[σ] : (U[sb_of_list Id (Ns ++ record_pre Rd k M)])[σ].
  Proof.
    intros * IHM IHr Hl Hn IHN HU IHU HR.
    pose proof (mv_record_closed _ _ _ _ _ HR Hl) as HRd.
    assert (HL : List.length (record_pre Rd k M) = k)
      by (apply length_record_pre; pose proof (nth_error_lt_length _ _ _ HU); lia).
    pose proof (IHU _ _ HR) as HUσ.
    rewrite (record_field_sub _ _ _ _ _ _ _ HRd HU Hn HL), record_pre_sub in HUσ |- *.
    cbn [exp_sub].
    eapply wf_proj.
    - pose proof (IHM _ _ HR) as H; rewrite apps_exp_sub in H; exact H.
    - pose proof (IHr _ _ HR) as H; rewrite record_ty_sub in H by exact HRd; exact H.
    - exact Hl.
    - rewrite List.length_map; exact Hn.
    - eapply mv_record_params; eassumption.
    - exact HU.
    - exact HUσ.
  Qed.

  Lemma mv_proj_cong_case : forall M M' p Ns Rd k f U i Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] ≈ M'[σ0] : (apps_exp (a_record p) Ns)[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_record p)[σ0] : (record_ty Rd)[σ0]) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.length Ns = List.length (record_params Rd) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params Rd) Id Ns) k = Some A ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : A[σ0]) ->
      List.nth_error (record_fields Rd) k = Some (f, U) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (U[sb_of_list Id (Ns ++ record_pre Rd k M)])[σ0] : Typeω@i[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_proj f M')[σ0] : (U[sb_of_list Id (Ns ++ record_pre Rd k M)])[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_proj f M)[σ] ≈ (a_proj f M')[σ] : (U[sb_of_list Id (Ns ++ record_pre Rd k M)])[σ].
  Proof.
    intros * IHM IHr Hl Hn IHN HU IHU IH2 HR.
    pose proof (mv_record_closed _ _ _ _ _ HR Hl) as HRd.
    assert (HL : List.length (record_pre Rd k M) = k)
      by (apply length_record_pre; pose proof (nth_error_lt_length _ _ _ HU); lia).
    pose proof (IHU _ _ HR) as HUσ.
    pose proof (IH2 _ _ HR) as Hr2.
    rewrite (record_field_sub _ _ _ _ _ _ _ HRd HU Hn HL), record_pre_sub in HUσ, Hr2 |- *.
    cbn [exp_sub] in Hr2 |- *.
    eapply wf_exp_eq_proj_cong.
    - pose proof (IHM _ _ HR) as H; rewrite apps_exp_sub in H; exact H.
    - pose proof (IHr _ _ HR) as H; rewrite record_ty_sub in H by exact HRd; exact H.
    - exact Hl.
    - rewrite List.length_map; exact Hn.
    - eapply mv_record_params; eassumption.
    - exact HU.
    - exact HUσ.
    - exact Hr2.
  Qed.

  Lemma mv_tuple_cong_case : forall T T' fs fs' p Ns Rd i Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_tuple T fs)[σ0] : T[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] ≈ T'[σ0] : Typeω@i[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ T[σ0] ≈ (apps_exp (a_record p) Ns)[σ0] : Typeω@i[σ0]) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.length Ns = List.length (record_params Rd) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params Rd) Id Ns) k = Some A ->
         forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : A[σ0]) ->
      List.map fst fs = List.map fst (record_fields Rd) ->
      List.map fst fs' = List.map fst fs ->
      (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
         List.nth_error (record_fields Rd) k = Some (f, U) ->
         forall Δ0 σ0, R Δ0 σ0 Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] ≈ M'[σ0] : (U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))])[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_tuple T' fs')[σ0] : T[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_tuple T fs)[σ] ≈ (a_tuple T' fs')[σ] : T[σ].
  Proof.
    intros * IH1 IHT IHT' Hl Hn IHN Hnames0 Hnames IHf IH2 HR.
    pose proof (mv_record_closed _ _ _ _ _ HR Hl) as HRd.
    eapply wf_exp_eq_tuple_cong with (Ns := List.map (fun N => N[σ]) Ns).
    - exact (IH1 _ _ HR).
    - exact (IHT _ _ HR).
    - pose proof (IHT' _ _ HR) as H; rewrite apps_exp_sub in H; exact H.
    - exact Hl.
    - rewrite List.length_map; exact Hn.
    - eapply mv_record_params; eassumption.
    - rewrite tuple_names_sub; exact Hnames0.
    - cbn [exp_sub]; rewrite !tuple_names_sub; exact Hnames.
    - intros k f M0 M0' U HM0 HM0' HU.
      apply nth_error_map_inv in HM0 as ([f0 M] & HM & [= -> ->]).
      apply nth_error_map_inv in HM0' as ([f1 M'] & HM' & [= -> ->]); cbn.
      pose proof (IHf _ _ _ _ _ HM HM' HU _ _ HR) as H.
      rewrite (record_field_sub _ _ _ _ _ _ _ HRd HU Hn) in H.
      + rewrite tuple_values_sub in H; exact H.
      + rewrite List.length_firstn, List.length_map; pose proof (nth_error_lt_length _ _ _ HM); lia.
    - exact (IH2 _ _ HR).
  Qed.

  Lemma mv_field_beta_case : forall T fs f M A Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_tuple T fs)[σ0] : T[σ0]) ->
      field_lookup fs f = Some M ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_proj f (a_tuple T fs))[σ0] : A[σ0]) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : A[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_proj f (a_tuple T fs))[σ] ≈ M[σ] : A[σ].
  Proof.
    intros * IH1 Hk IH2 IH3 HR.
    eapply wf_exp_eq_field_beta; [ exact (IH1 _ _ HR) | | exact (IH2 _ _ HR) | exact (IH3 _ _ HR) ].
    cbn [exp_sub]; rewrite (field_lookup_map (fun N => N[σ])), Hk; reflexivity.
  Qed.

  Lemma mv_record_eta_case : forall M p Ns Rd Γ Δ σ,
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : (apps_exp (a_record p) Ns)[σ0]) ->
      record_lookup Θ Ξ p = Some Rd ->
      List.length Ns = List.length (record_params Rd) ->
      (forall Δ0 σ0, R Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_tuple (apps_exp (a_record p) Ns) (record_eta_fields Rd M))[σ0]
                                       : (apps_exp (a_record p) Ns)[σ0]) ->
      R Δ σ Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ M[σ] ≈ (a_tuple (apps_exp (a_record p) Ns) (record_eta_fields Rd M))[σ] : (apps_exp (a_record p) Ns)[σ].
  Proof.
    intros * IHM Hl Hn IHt HR.
    pose proof (IHM _ _ HR) as H1; pose proof (IHt _ _ HR) as H2.
    cbn [exp_sub] in H2 |- *; rewrite apps_exp_sub in H1, H2 |- *; rewrite record_eta_fields_sub in H2 |- *.
    eapply wf_exp_eq_record_eta; [ exact H1 | exact Hl | rewrite List.length_map; exact Hn | exact H2 ].
  Qed.
End RecordMove.

(** A weakening, seen as the substitution it is. *)
Definition wk_as_sub (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (σ : sub) (Γ : ctx) : Prop :=
  exists φ, sb_eq σ (ι φ) /\ Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ.

Lemma wk_as_sub_dom : forall Θ Ξ Δ σ Γ, wk_as_sub Θ Ξ Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ.
Proof. intros * (φ & _ & Hφ); exact (wf_wk_dom _ _ _ _ _ Hφ). Qed.

Lemma wk_as_sub_ext : forall Θ Ξ Ψ Γ Δ σ, wk_as_sub Θ Ξ Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    wk_as_sub Θ Ξ (tele_sub Ψ σ ++ Δ) (sb_qn (length Ψ) σ) (Ψ ++ Γ).
Proof.
  intros * (φ & Heq & Hφ) HΔ HΓ; rewrite (tele_sub_sb_eq _ _ _ Heq), tele_sub_of_wk in HΔ |- *.
  exists (wk_qn (length Ψ) φ); split; [| apply wf_wk_ext; assumption ].
  intros x; symmetry; exact (sb_qn_of_wk_ext _ _ _ (fun y => eq_sym (Heq y)) x).
Qed.

Lemma wk_as_sub_of : forall Θ Ξ Δ φ Γ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> wk_as_sub Θ Ξ Δ (ι φ) Γ.
Proof. intros * Hφ; exists φ; split; [ reflexivity | exact Hφ ]. Qed.

(** The identity is a weakening. *)
Lemma wk_as_sub_id : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> wk_as_sub Θ Ξ Γ Id Γ.
Proof. intros * HΓ; exists wk_id; split; [ symmetry; exact sb_of_wk_id | apply wf_wk_id; exact HΓ ]. Qed.

(** An induction hypothesis about weakenings, read about [wk_as_sub]. *)
Lemma exp_sub_wk_as : forall M σ φ, sb_eq σ (ι φ) -> M[σ] = M[φ]ʷ.
Proof. intros * Heq; rewrite (exp_sub_sb_eq _ _ _ Heq); apply exp_sub_of_wk. Qed.

Lemma tele_sub_wk_as : forall Ψ σ φ, sb_eq σ (ι φ) -> tele_sub Ψ σ = tele_wk Ψ φ.
Proof. intros * Heq; rewrite (tele_sub_sb_eq _ _ _ Heq); apply tele_sub_of_wk. Qed.

Ltac wk_as_sub_ih :=
  repeat intro;
  match goal with
  | H : wk_as_sub _ _ _ ?σ _ |- _ =>
      let φ := fresh "φ" in let Heq := fresh "Heq" in let Hφ := fresh "Hφ" in
      destruct H as (φ & Heq & Hφ);
      repeat match goal with
      | |- context [ exp_sub ?X σ ] => rewrite (exp_sub_wk_as X σ φ Heq)
      | |- context [ tele_sub ?X σ ] => rewrite (tele_sub_wk_as X σ φ Heq)
      end;
      eauto
  end.

(** The eliminator's cases of [wk_preserves_wf]: seen through
    [wk_as_sub]. *)
Ltac wk_elim_case :=
  rewrite <- ?exp_sub_of_wk;
  first [ eapply (mv_elim_case _ _ _ (wk_as_sub_dom _ _) (wk_as_sub_ext _ _))
        | eapply (mv_elim_cong_case _ _ _ (wk_as_sub_dom _ _) (wk_as_sub_ext _ _))
        | eapply (mv_elim_iota_case _ _ _ (wk_as_sub_dom _ _) (wk_as_sub_ext _ _))
        | eapply (mv_elim_view_case _ _ _ (wk_as_sub_dom _ _) (wk_as_sub_ext _ _))
        | eapply (mv_record_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_record_cong_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_tuple_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_proj_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_proj_cong_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_tuple_cong_case _ _ _ (wk_as_sub_dom _ _))
        | eapply (mv_field_beta_case _ _ (wk_as_sub _ _))
        | eapply (mv_record_eta_case _ _ (wk_as_sub _ _)) ];
  first [ eassumption | apply wk_as_sub_of; eassumption | exact (wk_as_sub_id _ _) | wk_as_sub_ih ].





(** ** Bodies with Local Opens *)

Lemma wf_ctx_app_tail : forall Θ Ξ Ψ Γ, ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof. induction Ψ; intros * H; cbn in *; [ assumption | apply IHΨ; eapply ctx_decomp_tail; exact H ]. Qed.

Lemma body_shape_binders : forall Φ Φ', body_shape Φ Φ' -> gm_binders Φ = gm_binders Φ'.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c its]; intros [| Φ' y' E' | Φ' c' its'] Hs; cbn in *; try contradiction; auto.
  - destruct Hs as (Hs & _ & _); f_equal; auto.
  - destruct Hs as (Hs & ->); f_equal; auto.
Qed.

(** The opens of two bodies of the same shape stand after prefixes binding
    as many indices. *)
Lemma body_opens_lengths : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall Γ' Φ' Φx' k Ψ H Ψ' H', body_xp Θ Ξ Γ' Φ' Φx' -> body_shape Φ Φ' ->
    List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') ->
    length Ψ = length Ψ'.
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H0 its R T gs Hx IH _ _ Hg]; intros * Hx' Hs Hk Hk'.
  - destruct k; discriminate.
  - destruct Φ' as [| Φ1 x1 E1 | Φ1 Hm1 its1]; cbn in Hs; try contradiction; destruct Hs as (Hs & _ & _).
    inversion Hx'; subst; cbn [body_opens gm_dropn] in Hk, Hk'; eauto.
  - destruct Φ' as [| Φ1 x1 E1 | Φ1 Hm1 its1]; cbn in Hs; try contradiction; destruct Hs as (Hs & <-).
    inversion Hx'; subst.
    rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg) in Hk.
    match goal with Hg' : items_gen _ _ _ _ _ its _ |- _ => rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg') in Hk' end.
    destruct k as [| k]; cbn in Hk, Hk'; [| eauto ].
    injection Hk as <- <-; injection Hk' as <- <-.
    rewrite !length_body_ctx, (body_xp_binders _ _ _ _ _ Hx).
    match goal with Hx1 : body_xp _ _ _ Φ1 _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx1) end.
    apply body_shape_binders; assumption.
Qed.

(** A body unit moved along a substitution, from the moved premises: the
    entries of the moved body, filled in, are the filled-in entries moved
    under the parameters. *)
Lemma unit_body_moved : forall Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Δ σ σ',
    body_xp Θ Ξ (tele_sub Δu σ ++ Δ) (gmod_sub Φ (sb_qn (length Δu) σ)) (gmod_sub Φx (sb_qn (length Δu) σ)) ->
    body_xp Θ Ξ (tele_sub Δu' σ' ++ Δ) (gmod_sub Φ' (sb_qn (length Δu') σ')) (gmod_sub Φx' (sb_qn (length Δu') σ')) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub Δu σ ≈ tele_sub Δu' σ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (body_ctx Φx ++ Δu) σ ≈ tele_sub (body_ctx Φx ++ Δu) σ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (body_ctx Φx' ++ Δu') σ' ≈ tele_sub (body_ctx Φx' ++ Δu') σ' ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ A[σf][sb_qn (length Δu) σ] : Typeω@(lv y) /\
        Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ A[σf][sb_qn (length Δu) σ] ≈ A'[σf'][sb_qn (length Δu) σ'] : Typeω@(lv y) /\
        Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ M[σf][sb_qn (length Δu) σ] : A[σf][sb_qn (length Δu) σ] /\
        Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ M[σf][sb_qn (length Δu) σ] ≈ M'[σf'][sb_qn (length Δu) σ'] : A[σf][sb_qn (length Δu) σ]) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ᵘ U[σf]ᵘ[sb_qn (length Δu) σ]ᵘ ≈ U'[σf']ᵘ[sb_qn (length Δu) σ']ᵘ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ tele_sub Δu' σ' ++ Δ ⊢ A'[σf'][sb_qn (length Δu') σ'] : Typeω@(lv y) /\
        Θ ⍮ Ξ ⍮ tele_sub Δu' σ' ++ Δ ⊢ M'[σf'][sb_qn (length Δu') σ'] : A'[σf'][sb_qn (length Δu') σ']) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ tele_sub Δu' σ' ++ Δ ⊢ᵘ U'[σf']ᵘ[sb_qn (length Δu') σ']ᵘ ≈ U'[σf']ᵘ[sb_qn (length Δu') σ']ᵘ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) σ ++ Δ ⊢ᵐ H[sb_qn (length (Ψ ++ Δu)) σ]ᵐ ≈ H[sb_qn (length (Ψ ++ Δu)) σ]ᵐ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ' Φx') k = Some (Ψ, H) ->
       Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu') σ' ++ Δ ⊢ᵐ H[sb_qn (length (Ψ ++ Δu')) σ']ᵐ ≈ H[sb_qn (length (Ψ ++ Δu')) σ']ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ᵐ H[σf]ᵐ[sb_qn (length Δu) σ]ᵐ ≈ H'[σf']ᵐ[sb_qn (length Δu') σ']ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       Θ ⍮ Ξ ⍮ tele_sub Δu' σ' ++ Δ ⊢ᵐ H'[σf']ᵐ[sb_qn (length Δu') σ']ᵐ ≈ H'[σf']ᵐ[sb_qn (length Δu') σ']ᵐ) ->
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx -> body_xp Θ Ξ (Δu' ++ Γ) Φ' Φx' ->
    tele_ass Δu -> tele_ass Δu' -> length Δu = length Δu' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ (gu_open Δu Φ)[σ]ᵘ ≈ (gu_open Δu' Φ')[σ']ᵘ.
Proof.
  intros * Hbσ Hbσ' HΔσ Hxσ Hxσ' HD HU HDr HUr Ho Ho' HOo HOr Hb Hb' Ha Ha' Hl Hs Hsx Hn.
  rewrite !gunit_sub_mk; cbn [moddef_sub].
  eapply wf_unit_eq_body with (lv := lv); [ exact Hbσ | exact Hbσ' | .. ].
  (* the definitions, each filled in, then substituted *)
  all: try (intros y Φ0w b pv Aw Mw Φ0w' b' pv' Aw' Mw' σw σw' Hp Hp' Hfw Hfw';
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E & Hp0 & -> & HE);
    destruct E as [b0 pv0 A [M |] | | | | ]; cbn in HE; try discriminate; injection HE as ? ? ? ?; subst;
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp') as (Φ0' & E' & Hp0' & -> & HE');
    destruct E' as [b0' pv0' A' [M' |] | | | | ]; cbn in HE'; try discriminate; injection HE' as ? ? ? ?; subst;
    destruct (gm_fill Φ0) as [σf |] eqn:Hf0; [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δu) σ))) in Hf0; congruence ];
    destruct (gm_fill Φ0') as [σf' |] eqn:Hf0'; [| apply (proj2 (gm_fill_sub_none Φ0' (sb_qn (length Δu') σ'))) in Hf0'; congruence ];
    destruct (gm_fill_sub Φ0 (length Δu) σ σf Hf0) as (τ & Hτ & Heq); rewrite Hτ in Hfw; injection Hfw as <-;
    destruct (gm_fill_sub Φ0' (length Δu') σ' σf' Hf0') as (τ' & Hτ' & Heq'); rewrite Hτ' in Hfw'; injection Hfw' as <-;
    repeat (rewrite (fill_sub_exp _ _ _ _ _ _ Heq)); repeat (rewrite (fill_sub_exp _ _ _ _ _ _ Heq'));
    destruct (HD _ _ _ _ _ _ _ _ _ _ _ _ _ Hp0 Hp0' Hf0 Hf0') as (H1 & H2 & H3 & H4);
    destruct (HDr _ _ _ _ _ _ _ _ _ _ _ _ _ Hp0 Hp0' Hf0 Hf0') as (H5 & H6);
    first [ exact H5 | exact H6 | rewrite <- ?Hl; first [ exact H1 | exact H2 | exact H3 | exact H4 ] ]).
  - exact HΔσ.
  - rewrite body_ctx_sub, <- tele_sub_app; exact Hxσ.
  - rewrite body_ctx_sub, <- tele_sub_app; exact Hxσ'.
  - (* the modules, each filled in, then substituted *)
    intros y Φ0w pv Uw Φ0w' pv' Uw' σw σw' Hp Hp' Hfw Hfw'.
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E & Hp0 & -> & HE).
    destruct E as [| pv0 U | | | ]; cbn in HE; try discriminate; injection HE as ? ?; subst.
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp') as (Φ0' & E' & Hp0' & -> & HE').
    destruct E' as [| pv0' U' | | | ]; cbn in HE'; try discriminate; injection HE' as ? ?; subst.
    destruct (gm_fill Φ0) as [σf |] eqn:Hf0; [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δu) σ))) in Hf0; congruence ].
    destruct (gm_fill Φ0') as [σf' |] eqn:Hf0'; [| apply (proj2 (gm_fill_sub_none Φ0' (sb_qn (length Δu') σ'))) in Hf0'; congruence ].
    destruct (gm_fill_sub Φ0 (length Δu) σ σf Hf0) as (τ & Hτ & Heq); rewrite Hτ in Hfw; injection Hfw as <-.
    destruct (gm_fill_sub Φ0' (length Δu') σ' σf' Hf0') as (τ' & Hτ' & Heq'); rewrite Hτ' in Hfw'; injection Hfw' as <-.
    rewrite (fill_sub_unit _ _ _ _ _ _ Heq), (fill_sub_unit _ _ _ _ _ _ Heq'), <- Hl.
    exact (HU _ _ _ _ _ _ _ _ _ Hp0 Hp0' Hf0 Hf0').
  - (* the modules of the right side, each filled in, then substituted *)
    intros y Φ0w pv Uw Φ0w' pv' Uw' σw σw' Hp Hp' Hfw Hfw'.
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E & Hp0 & -> & HE).
    destruct E as [| pv0 U | | | ]; cbn in HE; try discriminate; injection HE as ? ?; subst.
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp') as (Φ0' & E' & Hp0' & -> & HE').
    destruct E' as [| pv0' U' | | | ]; cbn in HE'; try discriminate; injection HE' as ? ?; subst.
    destruct (gm_fill Φ0) as [σf |] eqn:Hf0; [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δu) σ))) in Hf0; congruence ].
    destruct (gm_fill Φ0') as [σf' |] eqn:Hf0'; [| apply (proj2 (gm_fill_sub_none Φ0' (sb_qn (length Δu') σ'))) in Hf0'; congruence ].
    destruct (gm_fill_sub Φ0' (length Δu') σ' σf' Hf0') as (τ' & Hτ' & Heq'); rewrite Hτ' in Hfw'; injection Hfw' as <-.
    rewrite (fill_sub_unit _ _ _ _ _ _ Heq').
    exact (HUr _ _ _ _ _ _ _ _ _ Hp0 Hp0' Hf0 Hf0').
  - (* the opens, left *)
    intros k Ψw Hw Hk.
    rewrite (body_opens_sub _ _ _ _ _ Hb), List.nth_error_map in Hk.
    destruct (List.nth_error (body_opens Φ Φx) k) as [[Ψ H] |] eqn:Ek; [| discriminate ].
    cbn in Hk; injection Hk as <- <-.
    pose proof (Ho _ _ _ Ek) as HH.
    rewrite tele_sub_app, <- List.app_assoc, List.length_app in HH.
    rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)); exact HH.
  - (* the opens, right *)
    intros k Ψw Hw Hk.
    rewrite (body_opens_sub _ _ _ _ _ Hb'), List.nth_error_map in Hk.
    destruct (List.nth_error (body_opens Φ' Φx') k) as [[Ψ H] |] eqn:Ek; [| discriminate ].
    cbn in Hk; injection Hk as <- <-.
    pose proof (Ho' _ _ _ Ek) as HH.
    rewrite tele_sub_app, <- List.app_assoc, List.length_app in HH.
    rewrite (modexp_sub_sb_eq H _ _ (sb_qn_add _ _ _)); exact HH.
  - (* the opens pairwise, each filled in, then substituted *)
    intros k Φ0w Hw Φ0w' Hw' σw σw' Hk Hk' Hfw Hfw'.
    rewrite (body_opens_at_sub _ _ _ _ _ Hb), List.nth_error_map in Hk.
    rewrite (body_opens_at_sub _ _ _ _ _ Hb'), List.nth_error_map in Hk'.
    destruct (List.nth_error (body_opens_at Φ Φx) k) as [[Φ0 H] |] eqn:Ek; [| discriminate ].
    destruct (List.nth_error (body_opens_at Φ' Φx') k) as [[Φ0' H'] |] eqn:Ek'; [| discriminate ].
    cbn in Hk, Hk'; injection Hk as <- <-; injection Hk' as <- <-.
    destruct (gm_fill Φ0) as [σf |] eqn:Hf0; [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δu) σ))) in Hf0; congruence ].
    destruct (gm_fill Φ0') as [σf' |] eqn:Hf0'; [| apply (proj2 (gm_fill_sub_none Φ0' (sb_qn (length Δu') σ'))) in Hf0'; congruence ].
    destruct (gm_fill_sub Φ0 (length Δu) σ σf Hf0) as (τ & Hτ & Heq); rewrite Hτ in Hfw; injection Hfw as <-.
    destruct (gm_fill_sub Φ0' (length Δu') σ' σf' Hf0') as (τ' & Hτ' & Heq'); rewrite Hτ' in Hfw'; injection Hfw' as <-.
    rewrite (fill_sub_modexp _ _ _ _ _ _ Heq), (fill_sub_modexp _ _ _ _ _ _ Heq').
    exact (HOo _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0').
  - (* the opens of the right side, each filled in, then substituted *)
    intros k Φ0w Hw Φ0w' Hw' σw σw' Hk Hk' Hfw Hfw'.
    rewrite (body_opens_at_sub _ _ _ _ _ Hb), List.nth_error_map in Hk.
    rewrite (body_opens_at_sub _ _ _ _ _ Hb'), List.nth_error_map in Hk'.
    destruct (List.nth_error (body_opens_at Φ Φx) k) as [[Φ0 H] |] eqn:Ek; [| discriminate ].
    destruct (List.nth_error (body_opens_at Φ' Φx') k) as [[Φ0' H'] |] eqn:Ek'; [| discriminate ].
    cbn in Hk, Hk'; injection Hk as <- <-; injection Hk' as <- <-.
    destruct (gm_fill Φ0) as [σf |] eqn:Hf0; [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δu) σ))) in Hf0; congruence ].
    destruct (gm_fill Φ0') as [σf' |] eqn:Hf0'; [| apply (proj2 (gm_fill_sub_none Φ0' (sb_qn (length Δu') σ'))) in Hf0'; congruence ].
    destruct (gm_fill_sub Φ0' (length Δu') σ' σf' Hf0') as (τ' & Hτ' & Heq'); rewrite Hτ' in Hfw'; injection Hfw' as <-.
    rewrite (fill_sub_modexp _ _ _ _ _ _ Heq').
    exact (HOr _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0').
  - apply tele_ass_sub; assumption.
  - apply tele_ass_sub; assumption.
  - rewrite !length_tele_sub; assumption.
  - apply body_shape_sub; assumption.
  - apply body_shape_sub; assumption.
  - rewrite gm_names_sub; assumption.
Qed.

(** The case of a body unit under a weakening, with the induction
    hypotheses as premises. *)
Lemma wk_unit_body_case : forall Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Δ φ,
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx ->
    body_xp Θ Ξ (Δu' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δu ≈ Δu' ->
    (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_wk Δu φ0 ≈ tele_wk Δu' φ0) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δu ≈ body_ctx Φx ++ Δu ->
    (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_wk (body_ctx Φx ++ Δu) φ0 ≈ tele_wk (body_ctx Φx ++ Δu) φ0) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δu' ≈ body_ctx Φx' ++ Δu' ->
    (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_wk (body_ctx Φx' ++ Δu') φ0 ≈ tele_wk (body_ctx Φx' ++ Δu') φ0) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[σf][φ0]ʷ : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[σf][φ0]ʷ ≈ A'[σf'][φ0]ʷ : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σf][φ0]ʷ : A[σf][φ0]ʷ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σf][φ0]ʷ ≈ M'[σf'][φ0]ʷ : A[σf][φ0]ʷ) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ gunit_wk U[σf]ᵘ φ0 ≈ gunit_wk U'[σf']ᵘ φ0) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A'[σf'][φ0]ʷ : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M'[σf'][φ0]ʷ : A'[σf'][φ0]ʷ) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ gunit_wk U'[σf']ᵘ φ0 ≈ gunit_wk U'[σf']ᵘ φ0) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δu ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Ψ ++ Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H φ0 ≈ modexp_wk H φ0) ->
    (forall k Ψ' H', List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δu' ++ Γ ⊢ᵐ H' ≈ H') ->
    (forall k Ψ' H', List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') ->
       forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Ψ' ++ Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H' φ0 ≈ modexp_wk H' φ0) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H[σf]ᵐ φ0 ≈ modexp_wk H'[σf']ᵐ φ0) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H'[σf']ᵐ φ0 ≈ modexp_wk H'[σf']ᵐ φ0) ->
    tele_ass Δu -> tele_ass Δu' -> length Δu = length Δu' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    (* the premises as the rule takes them, for the scoping of the unit *)
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu' Φ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk (gu_open Δu Φ) φ ≈ gunit_wk (gu_open Δu' Φ') φ.
Proof.
  intros * Hb Hb' HΔ IHΔ Hx IHx Hx' IHx' IHA IHAA IHM IHMM IHU IHAr IHMr IHUr Ho IHo Ho' IHo' IHOo IHOr
           Ha Ha' Hl Hs Hsx Hn HU0 Hφ.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eapply ext_eq_ctx_left; exact HΔ).
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU0) as (HΓs & HUs & HUs').
  rewrite gunit_scoped_mk in HUs, HUs'; destruct HUs as [HΔs [_ HΦs]]; destruct HUs' as [HΔs' [_ HΦs']].
  pose proof (IHΔ _ _ Hφ) as HΔφ.
  assert (Hq : Θ ⍮ Ξ ⍮ tele_wk Δu φ ++ Δ ⊢ʷ wk_qn (length Δu) φ : Δu ++ Γ)
    by (apply wf_wk_ext; [ exact Hφ | exact (ext_eq_ctx_left _ _ _ _ _ HΔφ) | exact (ext_eq_ctx_left _ _ _ _ _ HΔ) ]).
  assert (Hq' : Θ ⍮ Ξ ⍮ tele_wk Δu' φ ++ Δ ⊢ʷ wk_qn (length Δu') φ : Δu' ++ Γ)
    by (apply wf_wk_ext; [ exact Hφ | exact (ext_eq_ctx_right _ _ _ _ _ HΔφ) | exact (ext_eq_ctx_right _ _ _ _ _ HΔ) ]).
  assert (Hqn : forall n, sb_eq (ι (wk_qn n φ)) (sb_qn n (ι φ))) by (intros; apply sb_qn_of_wk_ext; reflexivity).
  rewrite <- !gunit_sub_of_wk.
  eapply (unit_body_moved Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Δ (ι φ) (ι φ));
    [ | | | | | | | | | | | | | exact Hb | exact Hb' | exact Ha | exact Ha' | exact Hl | exact Hs | exact Hsx | exact Hn ];
    rewrite ?tele_sub_of_wk.
  - rewrite !(gmod_sub_of_wk_ext _ _ _ (Hqn _)).
    eapply body_xp_wk; [ exact Hc | exact Hb | apply ctx_scoped_app_iff; split; assumption | rewrite List.length_app; exact HΦs
                       | apply wk_mod_compat_ext; eauto using wf_wk_mod_compat ].
  - rewrite !(gmod_sub_of_wk_ext _ _ _ (Hqn _)).
    eapply body_xp_wk; [ exact Hc | exact Hb' | apply ctx_scoped_app_iff; split; assumption
                       | rewrite List.length_app; exact HΦs' | apply wk_mod_compat_ext; eauto using wf_wk_mod_compat ].
  - exact HΔφ.
  - exact (IHx _ _ Hφ).
  - exact (IHx' _ _ Hφ).
  - intros * Hp Hp' Hf0 Hf0'; rewrite ?tele_sub_of_wk, !(exp_sub_of_wk_ext _ _ _ (Hqn _)).
    split; [| split; [| split ] ];
      [ exact (IHA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHAA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHMM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq) ].
  - intros * Hp Hp' Hf0 Hf0'; rewrite ?tele_sub_of_wk, !(gunit_sub_of_wk_ext _ _ _ (Hqn _)).
    exact (IHU _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq).
  - intros * Hp Hp' Hf0 Hf0'; rewrite ?tele_sub_of_wk, !(exp_sub_of_wk_ext _ _ _ (Hqn _)).
    split; [ exact (IHAr _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq') | exact (IHMr _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq') ].
  - intros * Hp Hp' Hf0 Hf0'; rewrite ?tele_sub_of_wk, !(gunit_sub_of_wk_ext _ _ _ (Hqn _)).
    exact (IHUr _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq').
  - intros k Ψ H Ek; rewrite ?tele_sub_of_wk, (modexp_sub_of_wk_ext _ _ _ (Hqn _)).
    destruct (body_opens_prefix _ _ _ _ _ Hb _ _ _ Ek) as [Ψr HΨr].
    pose proof (IHx _ _ Hφ) as Hxφ.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_wk (Ψ ++ Δu) φ ++ Δ).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxφ) as HC; rewrite HΨr, <- List.app_assoc, tele_wk_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_wk_ext _ _ (Ψ ++ Δu) _ _ _ Hφ HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho _ _ _ Ek)))) as Hφe.
    rewrite <- List.app_assoc in Hφe; exact (IHo _ _ _ Ek _ _ Hφe).
  - intros k Ψ H Ek; rewrite ?tele_sub_of_wk, (modexp_sub_of_wk_ext _ _ _ (Hqn _)).
    destruct (body_opens_prefix _ _ _ _ _ Hb' _ _ _ Ek) as [Ψr HΨr].
    pose proof (IHx' _ _ Hφ) as Hxφ.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_wk (Ψ ++ Δu') φ ++ Δ).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxφ) as HC; rewrite HΨr, <- List.app_assoc, tele_wk_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_wk_ext _ _ (Ψ ++ Δu') _ _ _ Hφ HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho' _ _ _ Ek)))) as Hφe.
    rewrite <- List.app_assoc in Hφe; exact (IHo' _ _ _ Ek _ _ Hφe).
  - intros * Ek Ek' Hf0 Hf0'; rewrite ?tele_sub_of_wk, <- Hl, !(modexp_sub_of_wk_ext _ _ _ (Hqn _)).
    exact (IHOo _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0' _ _ Hq).
  - intros * Ek Ek' Hf0 Hf0'; rewrite ?tele_sub_of_wk, !(modexp_sub_of_wk_ext _ _ _ (Hqn _)).
    exact (IHOr _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0' _ _ Hq').
Qed.


(** [β] for a literal at any open definition. *)
Definition md_open (D : moddef) : Prop :=
  match D with
  | md_body sm _ => sm = sm_open
  | md_alias _ => True
  end.

Lemma md_open_sub : forall D σ, md_open D -> md_open (moddef_sub D σ).
Proof. intros [] σ HD; cbn in *; auto. Qed.

Lemma wf_me_beta : forall Θ Ξ Γ Δ X D N,
    md_open D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) D ≈ gu_mk (Δ ++ ce_ass X :: nil) D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N ≈ me_lit (gu_mk Δ D)[Id,,N]ᵘ.
Proof.
  intros * HD HU HN; rewrite gunit_sub_mk; destruct D as [sm Φ | E]; cbn in HD |- *;
    [ subst; apply wf_me_beta_body | apply wf_me_beta_alias ]; assumption.
Qed.

Lemma gunit_sub_last : forall Δ X D σ,
    (gu_mk (Δ ++ ce_ass X :: nil) D)[σ]ᵘ = gu_mk (tele_sub Δ (q σ) ++ ce_ass X[σ] :: nil) (moddef_sub D (sb_qn (length Δ) (q σ))).
Proof.
  intros; rewrite gunit_sub_mk, tele_sub_app, List.length_app, sb_qn_plus; cbn; reflexivity.
Qed.

Lemma gunit_sub_beta : forall Δ D N σ,
    ((gu_mk Δ D)[Id,,N]ᵘ)[σ]ᵘ = (gu_mk (tele_sub Δ (q σ)) (moddef_sub D (sb_qn (length Δ) (q σ))))[Id,,N[σ]]ᵘ.
Proof.
  intros; rewrite <- gunit_sub_mk, !gunit_sub_sub; apply gunit_sub_sb_eq.
  rewrite sb_q_compose_extend, sb_extend_compose, sb_compose_id_left, sb_compose_id_right; reflexivity.
Qed.

Lemma sub_beta_gen : forall Θ Ξ Δ0 σ Δ X D N,
    md_open D ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ (gu_mk (Δ ++ ce_ass X :: nil) D)[σ]ᵘ ≈ (gu_mk (Δ ++ ce_ass X :: nil) D)[σ]ᵘ ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ] : X[σ] ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N)[σ]ᵐ ≈ (me_lit (gu_mk Δ D)[Id,,N]ᵘ)[σ]ᵐ.
Proof.
  intros * HD HU HN; cbn [modexp_sub]; rewrite gunit_sub_last in *; rewrite gunit_sub_beta.
  apply wf_me_beta; [ apply md_open_sub; exact HD | exact HU | exact HN ].
Qed.

Lemma wk_beta_gen : forall Θ Ξ Δ0 φ Δ X D N,
    md_open D ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ gunit_wk (gu_mk (Δ ++ ce_ass X :: nil) D) φ ≈ gunit_wk (gu_mk (Δ ++ ce_ass X :: nil) D) φ ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ N[φ]ʷ : X[φ]ʷ ->
    Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) φ ≈ modexp_wk (me_lit (gu_mk Δ D)[Id,,N]ᵘ) φ.
Proof.
  intros * HD HU HN; rewrite <- !modexp_sub_of_wk; rewrite <- gunit_sub_of_wk in HU; rewrite <- !exp_sub_of_wk in HN.
  apply sub_beta_gen; assumption.
Qed.

Lemma me_apps_wk : forall Ns H φ, modexp_wk (me_apps H Ns) φ = me_apps (modexp_wk H φ) (List.map (fun M => M[φ]ʷ) Ns).
Proof. induction Ns as [| N Ns IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The member rules, weakened. *)
Section WkMem.
  Context (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (φ : wk).

  Lemma wk_mem_case : forall H x R A i,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H φ0 ≈ modexp_wk H φ0) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[φ0]ʷ : (Typeω@i)[φ0]ʷ) ->
      (forall M, ds_red R = Some M -> forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[φ0]ʷ : A[φ0]ʷ) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[φ]ʷ : A[φ]ʷ.
  Proof.
    intros * HH IH Hm Ht IHA IHM Hφ; cbn; eapply wf_mem;
      [ exact (IH _ _ Hφ) | eapply wf_wk_mdenote_mem; eassumption
      | eapply ds_ty_wk; [ exact (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) | exact Ht ] | exact (IHA _ _ Hφ) |].
    intros M' HM'; destruct (ds_red_wk_inv _ _ _ HM') as (M0 & HM0 & ->); exact (IHM _ HM0 _ _ Hφ).
  Qed.

  Lemma wk_mem_cong_case : forall H H' x R A R' A',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H φ0 ≈ modexp_wk H' φ0) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
      mdenote Θ Ξ Γ (me_mem H' x) R' -> ds_ty Θ Ξ R' = Some A' ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_mem H' x)[φ0]ʷ : A[φ0]ʷ) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[φ]ʷ ≈ (a_mem H' x)[φ]ʷ : A[φ]ʷ.
  Proof.
    intros * HH IHH Hm Ht Hm' Ht' IHM Hφ; cbn.
    pose proof (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) as Hc.
    eapply wf_exp_eq_mem_cong;
      [ exact (IHH _ _ Hφ) | eapply wf_wk_mdenote_mem; eassumption | eapply ds_ty_wk; eassumption
      | eapply wf_wk_mdenote_mem; [ exact (wf_modexp_eq_refl_right HH) | eassumption | eassumption ]
      | eapply ds_ty_wk; eassumption | exact (IHM _ _ Hφ) ].
  Qed.

  Lemma wk_mem_delta_case : forall H x R A M,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk H φ0 ≈ modexp_wk H φ0) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A -> ds_red R = Some M -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[φ]ʷ ≈ M[φ]ʷ : A[φ]ʷ.
  Proof.
    intros * HH IH Hm Ht Hr Hφ; cbn.
    pose proof (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) as Hc.
    eapply wf_exp_eq_mem_delta;
      [ exact (IH _ _ Hφ) | eapply wf_wk_mdenote_mem; eassumption | eapply ds_ty_wk; eassumption | apply ds_red_wk; exact Hr ].
  Qed.

  Lemma wk_me_delta_sel_case : forall H y R Rm,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ modexp_wk (me_mem H y) φ0 ≈ modexp_wk (me_mem H y) φ0) ->
      mdenote Θ Ξ Γ (me_mem H y) R -> ds_mod Θ Ξ R = Some Rm -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk (me_mem H y) φ ≈ modexp_wk (ds_unit Rm) φ.
  Proof.
    intros * HH IH Hm Hd Hφ.
    rewrite <- (modexp_sub_of_wk (ds_unit Rm) φ), <- ds_unit_sub; cbn.
    eapply wf_me_delta_sel; [ exact (IH _ _ Hφ) | | apply ds_mod_sub; exact Hd ].
    pose proof (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
    exact (mdenote_wk _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) _ _ _ Hm HΓ HHs _ _ (wf_wk_mod_compat _ _ _ _ _ Hφ)).
  Qed.

  Lemma wk_me_unit_case : forall fp TΦ,
      gc_unit Θ Ξ (me_unit fp) = Some TΦ -> Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk (me_unit fp) φ ≈ modexp_wk (me_unit fp) φ.
  Proof.
    intros * Hu Hφ; cbn; eapply wf_me_unit; [ exact (wf_wk_dom _ _ _ _ _ Hφ) | exact Hu ].
  Qed.

  Lemma wk_me_beta_body_case : forall Δu X Φ N,
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ gunit_wk (gu_open (Δu ++ ce_ass X :: nil) Φ) φ0 ≈ gunit_wk (gu_open (Δu ++ ce_ass X :: nil) Φ) φ0) ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[φ0]ʷ : X[φ0]ʷ) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk (me_app (me_lit (gu_open (Δu ++ ce_ass X :: nil) Φ)) N) φ
        ≈ modexp_wk (me_lit (gu_open (tele_sub Δu (Id,,N)) (gmod_sub Φ (sb_qn (length Δu) (Id,,N))))) φ.
  Proof.
    intros * IHU IHN Hφ.
    replace (gu_open (tele_sub Δu (Id,,N)) (gmod_sub Φ (sb_qn (length Δu) (Id,,N))))
      with ((gu_open Δu Φ)[Id,,N]ᵘ) by (rewrite gunit_sub_mk; reflexivity).
    apply wk_beta_gen; [ reflexivity | exact (IHU _ _ Hφ) | exact (IHN _ _ Hφ) ].
  Qed.

  Lemma wk_me_beta_alias_case : forall Δu X E N,
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ gunit_wk (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E)) φ0 ≈ gunit_wk (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E)) φ0) ->
      (forall Δ0 φ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ʷ φ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[φ0]ʷ : X[φ0]ʷ) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk (me_app (me_lit (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E))) N) φ
        ≈ modexp_wk (me_lit (gu_mk (tele_sub Δu (Id,,N)) (md_alias E[sb_qn (length Δu) (Id,,N)]ᵐ))) φ.
  Proof.
    intros * IHU IHN Hφ.
    replace (gu_mk (tele_sub Δu (Id,,N)) (md_alias E[sb_qn (length Δu) (Id,,N)]ᵐ))
      with ((gu_mk Δu (md_alias E))[Id,,N]ᵘ) by (rewrite gunit_sub_mk; reflexivity).
    apply wk_beta_gen; [ exact I | exact (IHU _ _ Hφ) | exact (IHN _ _ Hφ) ].
  Qed.
End WkMem.
(** ** Weakening Preserves the Judgments ([wk_preserves_wf]) *)

Lemma wk_preserves_wf :
  (forall Θ Ξ Γ A M,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ) /\
  (forall Θ Ξ Γ A M M',
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ) /\
  (forall Θ Ξ Γ A A',
      Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ) /\
  (forall Θ Ξ Γ U,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ᵤ U[φ]ʷ) /\
  (forall Θ Ξ Γ Ψ Ψ',
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ) /\
  (forall Θ Ξ Γ U U',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U' φ) /\
  (forall Θ Ξ Γ H H',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      forall Δ φ, Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ -> Θ ⍮ Ξ ⍮ Δ ⊢ᵐ modexp_wk H φ ≈ modexp_wk H' φ).
Proof.
  apply syntactic_wf_mut_ind'; intros; destruct_let_ann;
    try solve [ wk_elim_case ];
    try solve [ first [ eapply wk_mem_case; eassumption | eapply wk_mem_cong_case; eassumption
                      | eapply wk_mem_delta_case; eassumption
                      | eapply wk_me_delta_sel_case; eassumption
                      | eapply wk_me_unit_case; eassumption
                      | eapply wk_me_beta_body_case; eassumption | eapply wk_me_beta_alias_case; eassumption ] ];
    saturate_wk; push_wk; lift_wk.
  (** The cases of globals: the recorded type is closed, so the operation on it
      disappears, and the rule applies at the type the induction hypothesis
      gives. *)
  all: try solve [ push_closed; mauto 3 ].
  (** With the weakenings pushed in and the lifted ones in the context, most
      cases are the corresponding rule applied to the induction hypotheses. *)
  all: try solve [ mauto 4 ].
  (** For the wider rules the rule application itself is what [eauto] does not
      reach in time, so we take that step by hand. *)
  all: try solve [ econstructor; mauto 3 ].
  (** The module rules. *)
  all: try solve [ rewrite ?exp_wk_sub_extend_mod; eapply wf_let_mod; eauto 6 using wf_wk_q_mod, wf_unit_eq_refl_left ].
  all: try solve [ rewrite !exp_wk_sub_extend_mod; eapply wf_exp_eq_let_mod_zeta; eauto using wf_wk_q_mod ].
  all: try solve [ rewrite exp_wk_sub_extend_mod; eapply wf_exp_eq_let_mod_cong;
                   [ eauto | eauto 6 using wf_wk_q_mod, wf_unit_eq_refl_left | rewrite <- exp_wk_sub_extend_mod; eauto ] ].
  all: try solve [ cbn [tele_wk]; first [ eapply wf_ext_eq_ass | eapply wf_ext_eq_def | eapply wf_ext_eq_mod ];
                   eauto 7 using wf_wk_ext, ext_eq_ctx_left, ext_eq_ctx_right, presup_exp_ctx, presup_exp_eq_ctx, presup_unit_eq_ctx ].
  all: try solve [ eapply wf_me_var; [ eauto | eapply wf_wk_lookup_mod; eauto ] ].
  all: try solve [ eapply wf_me_delta_slot; [ eauto | eapply wf_wk_lookup_mod; eauto ] ].
  all: try solve [ eapply wf_me_mem;
                   [ eauto
                   | eapply wf_wk_mdenote_mem; eassumption | eapply wf_wk_ds_mtele_mem; eassumption
                   | eapply wf_wk_mdenote_mem; [ apply wf_me_sym | ..]; eassumption
                   | eapply wf_wk_ds_mtele_mem; [ apply wf_me_sym | ..]; eassumption ] ].
  all: try solve [ eapply wf_me_app;
                   [ eauto
                   | eapply wf_wk_mdenote; eassumption | eapply wf_wk_ds_mtele; eassumption
                   | eapply tele_view_wk_some; eassumption | eauto | eauto | eauto
                   | eapply wf_wk_mdenote; [ apply wf_me_sym | ..]; eassumption
                   | eapply wf_wk_ds_mtele; [ apply wf_me_sym | ..]; eassumption
                   | eapply tele_view_wk_some; eassumption | eauto | eauto ] ].
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
  all: try solve [ eapply wk_unit_body_case; (eassumption || (eapply wf_unit_eq_body; eassumption)) ].
  (** An alias of a literal, flattened: the literal moves by the weakening
      lifted over the alias's parameters. *)
  all: try solve [
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?Δ ?Δ, IHx : forall _ _, wf_wk _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_wk ?Δ _) (tele_wk ?Δ _),
      IHU : forall _ _, wf_wk _ _ _ (?Δ ++ ?Γ) _ -> wf_unit_eq _ _ _ (gunit_wk (gu_mk ?Δ' ?D) _) _,
      Hφ : wf_wk _ _ _ ?Γ ?φ |- wf_unit_eq _ _ _ _ (gunit_wk (gu_mk (?Δ' ++ ?Δ) ?D) _) =>
        destruct (wf_wk_ext_of_ext _ _ _ _ _ _ _ Hφ Hx (IHx _ _ Hφ)) as [Hl _];
        change (gu_mk (Δ' ++ Δ) D) with (gunit_abs Δ (gu_mk Δ' D)); rewrite gunit_abs_wk, gunit_wk_mk;
        cbn [moddef_wk modexp_wk];
        pose proof (IHU _ _ Hl) as HU'; revert HU';
        destruct (gunit_wk (gu_mk Δ' D) (wk_qn (length Δ) φ)) as [Δw Dw]; intros HU'; cbn [gunit_abs];
        eapply wf_unit_eq_flatten; [ exact (IHx _ _ Hφ) | apply tele_ass_wk; assumption | exact HU' ]
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
  (** The small [Π]: the domain is moved into a large universe by its level,
      and the codomain's universe, the weakened level, commutes with the
      lifted weakening. *)
  all: try solve [
    match goal with
    | HL : forall Δ0 φ0, wf_wk ?T ?X Δ0 ?Γ φ0 -> wf_exp ?T ?X Δ0 (a_level ?n) ?L[φ0]ʷ,
      HA : wf_exp ?T ?X ?Γ (a_univ ?L) ?A,
      Hφ : wf_wk ?T ?X ?Δ ?Γ ?φ,
      HL0 : wf_exp ?T ?X ?Γ (a_level ?n) ?L |- _ =>
        assert (T ⍮ X ⍮ Γ ⊢ A : a_typ 0) by (eapply wf_exp_suniv_large; eassumption);
        assert (T ⍮ X ⍮ Δ ⊢ A[φ]ʷ : a_typ 0) by (eapply wf_exp_suniv_large; eauto);
        assert (T ⍮ X ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A) by (eapply wf_wk_q; eassumption);
        first [ eapply wf_pi_lvl | eapply wf_exp_eq_pi_cong_lvl ];
        rewrite <- ?exp_wk_shift_wk_q; eauto
    end ].
  (** [Π]: the domain is a type of a large universe, so the weakening lifts
      over it, and the codomain's universe commutes with the lift. *)
  all: try solve [
    match goal with
    | HU : wf_is_univ ?T ?X ?Γ ?U, HA : wf_exp ?T ?X ?Γ ?U ?A, Hφ : wf_wk ?T ?X ?Δ ?Γ ?φ |- wf_exp _ _ _ _ (a_pi _ _) =>
        assert (T ⍮ X ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A) by (eapply wf_wk_q_univ; eauto);
        eapply wf_pi; [ eauto | eauto | rewrite <- exp_wk_shift_wk_q; eauto ]
    end ].
  all: try solve [
    match goal with
    | HU : wf_is_univ ?T ?X ?Γ ?U, HA : wf_exp ?T ?X ?Γ ?U ?A, Hφ : wf_wk ?T ?X ?Δ ?Γ ?φ |- wf_exp_eq _ _ _ _ (a_pi _ _) _ =>
        assert (T ⍮ X ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A) by (eapply wf_wk_q_univ; eauto);
        eapply wf_exp_eq_pi_cong; [ eauto | eauto | eauto | rewrite <- exp_wk_shift_wk_q; eauto ]
    end ].
  (** The type former and the constructors: their types are closed. *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, Hφ : wf_wk _ _ _ _ _ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_wk_dom _ _ _ _ _ Hφ) | exact Hl ]);
        try (erewrite (ind_ty_wk D) by eassumption); try (erewrite (con_ty_wk _ D) by eassumption);
        first [ eapply wf_ind | eapply wf_con | eapply wf_exp_eq_ind_cong | eapply wf_exp_eq_con_cong ]; eauto
    end ].
  (** A constructor of a view at the uniform parameters: the view's
      arguments there move with them ([im_pre_wk]). *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HM : ind_member ?D _ = Some ?Mj, HU : List.length ?Us = ind_nu ?D,
      IH1 : forall Δ0 φ0, wf_wk _ _ Δ0 _ φ0 -> wf_exp _ _ Δ0 _ (apps_exp (a_con _ _ _) (?Us ++ _))[φ0]ʷ,
      IH2 : forall Δ0 φ0, wf_wk _ _ Δ0 _ φ0 -> wf_exp _ _ Δ0 _ (apps_exp (a_con _ _ _) (im_pre ?Mj ?Us ++ _))[φ0]ʷ,
      Hφ : wf_wk _ _ _ _ _ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_wk_dom _ _ _ _ _ Hφ) | exact Hl ]);
        pose proof (IH1 _ _ Hφ) as E1; pose proof (IH2 _ _ Hφ) as E2;
        rewrite apps_exp_wk, List.map_app in E1, E2; rewrite !apps_exp_wk, !List.map_app;
        cbn in E1, E2 |- *;
        rewrite (im_pre_wk D _ Mj Us) in E2 |- * by eassumption;
        eapply wf_exp_eq_con_view; [ eassumption | eassumption | eassumption | rewrite List.length_map; exact HU
                                   | exact E1 | exact E2 ]
    end ].
Qed.

Corollary wk_preserves_exp : forall Θ Ξ Γ Δ A M φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ : A[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_exp_eq : forall Θ Ξ Γ Δ A M M' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_subtyp : forall Θ Ξ Γ Δ A A' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_ext : forall Θ Ξ Γ Δ Ψ Ψ' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_wk Ψ φ ≈ tele_wk Ψ' φ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_unit : forall Θ Ξ Γ Δ U U' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ gunit_wk U φ ≈ gunit_wk U' φ.
Proof.
  intros; pose proof wk_preserves_wf; destruct_all; eauto.
Qed.

Corollary wk_preserves_modexp : forall Θ Ξ Γ Δ H H' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
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
  (** The eliminator: its branches at the same position are the same. *)
  all: try solve [ eapply wf_exp_eq_elim_cong; eauto;
                   intros; repeat match goal with H1 : List.nth_error ?l ?k = Some _, H2 : List.nth_error ?l ?k = Some _ |- _ =>
                                             rewrite H1 in H2; injection H2 as <- end;
                   eauto using List.nth_error_In ].
  (** A record type former: its own congruence. *)
  all: try solve [ eapply wf_exp_eq_record_cong; eassumption ].
  (** A tuple: its fields, each equal to itself; [T ≈ T] through the record
      type it is equal to. *)
  all: try match goal with
         | H : _ ⍮ _ ⍮ _ ⊢ ?T ≈ apps_exp (a_record _) _ : _ |- _ ⍮ _ ⍮ _ ⊢ a_tuple ?T ?fs ≈ a_tuple ?T ?fs : ?T =>
             let Ht := fresh "Ht" in
             assert (Ht : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T) by (eapply wf_tuple; eassumption);
             eapply wf_exp_eq_tuple_cong;
             [ exact Ht | eapply wf_exp_eq_trans; [ exact H | eapply wf_exp_eq_sym; exact H ] | exact H
             | eassumption | eassumption | eassumption | eassumption | reflexivity | | exact Ht ];
             let HM := fresh "HM" in let HM' := fresh "HM'" in
             intros * HM HM' ?; rewrite HM in HM'; injection HM' as <-; eauto
         end.
  (** A projection: its own congruence. *)
  all: try solve [ eapply wf_exp_eq_proj_cong; try eassumption; eapply wf_proj; eassumption ].
  all: first [ eapply wf_exp_eq_let_mod_cong; mauto 3
             | (* a member: its own congruence *)
               eapply wf_exp_eq_mem_cong;
               [ eassumption | eassumption | eassumption | eassumption | eassumption
               | eapply wf_mem; eassumption ] ].
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
Lemma wf_subtyp_refl_typ : forall Θ Ξ Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros; eapply wf_subtyp_refl; mauto 2.
Qed.

#[export]
Hint Resolve wf_subtyp_refl_typ : mctt.

(** ** Substitution Typing *)

(** A weakening is a substitution.  [Wk] is [ι ↑], so every rule whose type
    mentions [Wk] needs this bridge. *)
Lemma wf_sub_of_wk : forall Θ Ξ Γ Δ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ʷ φ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ (ι φ) : Δ.
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

Corollary wf_sub_id : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id : Γ.
Proof.
  intros; rewrite <- sb_of_wk_id; mauto 3.
Qed.

Corollary wf_sub_shift : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Θ ⍮ Ξ ⍮ e :: Γ ⊢ˢ Wk : Γ.
Proof.
  intros; rewrite <- sb_of_wk_shift; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id wf_sub_shift : mctt.

(** Extension of a substitution: the image of every binding of the tail is
    unchanged, so only the head is checked. *)
Lemma wf_sub_extend_gen : forall Θ Ξ Γ Δ σ e en,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Δ ->
    (forall A, e :: Δ ∋ #0 : A -> Θ ⍮ Ξ ⍮ Γ ⊢ sentry_exp en : A[sb_extend σ en]) ->
    (forall A M, e :: Δ ∋ #0 ≔ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ sentry_exp en ≈ M[sb_extend σ en] : A[sb_extend σ en]) ->
    (forall U, e :: Δ ∋ #0 ≔ₘ U -> (en = se_mod (me_lit U[sb_extend σ en]ᵘ) /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[sb_extend σ en]ᵘ ≈ U[sb_extend σ en]ᵘ) \/
                                 exists y, en = se_var y /\ Γ ∋ #y ≔ₘ U[sb_extend σ en]ᵘ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_extend σ en : e :: Δ.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ,,M : Δ ▹ A.
Proof.
  intros * Hσ ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn.
  rewrite exp_sub_shift_extend; assumption.
Qed.

(** Extension into a definition: the new image must equal the substituted
    body. *)
Lemma wf_sub_extend_def : forall Θ Ξ Γ Δ σ A M N i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ,,N : Δ ▸ A ≔ M.
Proof.
  intros * Hσ ? ? ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn; rewrite ?exp_sub_shift_extend; assumption.
Qed.

(** Extension into a module slot, by the literal of its unit.  The
    transported unit is taken well formed; [sub_preserves_unit] supplies it. *)
Lemma wf_sub_extend_mod : forall Θ Ξ Γ Δ σ U,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ,,ₘ me_lit U[σ]ᵘ : Δ ▹ₘ U.
Proof.
  intros * Hσ ? ?; apply wf_sub_extend_gen; [ assumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; cbn.
  left; rewrite gunit_sub_shift_extend; split; [ reflexivity | assumption ].
Qed.

(** [wf_sub_single] *)
Corollary wf_sub_single : forall Θ Ξ Γ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M : Γ ▹ A.
Proof.
  intros.
  eapply wf_sub_extend; [ mauto 3 | eassumption | rewrite exp_sub_id; eassumption ].
Qed.

Corollary wf_sub_single_def : forall Θ Ξ Γ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M : Γ ▸ A ≔ M.
Proof.
  intros.
  eapply wf_sub_extend_def; [ mauto 3 | eassumption | eassumption | rewrite exp_sub_id; eassumption |].
  rewrite !exp_sub_id; mauto 2.
Qed.

Corollary wf_sub_single_mod : forall Θ Ξ Γ U,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id ,,ₘ me_lit U : Γ ▹ₘ U.
Proof.
  intros; rewrite <- (gunit_sub_id U) at 2; apply wf_sub_extend_mod; rewrite ?gunit_sub_id; mauto 3.
Qed.

(** [wf_sub_wk] *)
Lemma wf_sub_wk : forall Θ Ξ Γ Γ' Δ σ φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ (sb_wk σ φ) : Δ.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    ⊢ Θ ⍮ Ξ ⍮ centry_sub e σ :: Γ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Δ ->
    Θ ⍮ Ξ ⍮ centry_sub e σ :: Γ ⊢ˢ q σ : e :: Δ.
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
      match goal with Hl : _ ∋ # _ ≔ₘ _ |- _ => destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hl) as [[-> HUσ] | (y & -> & Hy)] end.
      * left; split; [ reflexivity | eapply wk_preserves_unit; [ eassumption | mauto 2 ] ].
      * right; exists (S y); split; [ reflexivity | constructor; assumption ].
Qed.

(** [wf_sub_q].

    As in [wf_wk_q], the premise [Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i] is taken explicitly.  It
    could be dropped once [sub_preserves_wf] is available; we keep it, because
    it is exactly what the induction hypothesis of [sub_preserves_wf] supplies
    at each binder, and dropping it would make [wf_sub_q] depend on
    [sub_preserves_wf], which depends on [wf_sub_q]. *)
Lemma wf_sub_q : forall Θ Ξ Γ Δ σ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢ˢ q σ : Δ ▹ A.
Proof.
  intros * Hσ ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_ass A)); mauto 2.
Qed.

(** The same over a type of a universe. *)
Lemma wf_sub_q_univ : forall Θ Ξ Γ Δ σ A U U',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Δ ⊢ A : U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : U' ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢ˢ q σ : Δ ▹ A.
Proof.
  intros * Hσ HU HA HU' HA'.
  destruct (wf_exp_is_univ_large HU HA), (wf_exp_is_univ_large HU' HA').
  apply (wf_sub_q_gen _ _ _ _ _ (ce_ass A)); [ assumption | eapply wf_ctx_extend; eassumption.. ].
Qed.

(** The lifted substitution over a definition: its head [#0] is the substituted
    body by δ. *)
Lemma wf_sub_q_def : forall Θ Ξ Γ Δ σ A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢ˢ q σ : Δ ▸ A ≔ M.
Proof.
  intros * Hσ ? ? ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_def A M)); mauto 2.
Qed.

(** The lifted substitution over a module slot. *)
Lemma wf_sub_q_mod : forall Θ Ξ Γ Δ σ U,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U[σ]ᵘ ⊢ˢ q σ : Δ ▹ₘ U.
Proof.
  intros * Hσ ? ?; apply (wf_sub_q_gen _ _ _ _ _ (ce_mod U)); mauto 2.
Qed.

(** Lifting over a whole extension, given that both extended contexts are
    well formed. *)
Lemma wf_sub_ext : forall Θ Ξ Ψ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ⊢ˢ sb_qn (length Ψ) σ : Ψ ++ Γ.
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hσ HΔ HΓ; cbn in *; [ assumption |].
  apply wf_sub_q_gen; [ apply IH; eauto using ctx_decomp_tail | assumption | assumption ].
Qed.

#[export]
Hint Resolve wf_sub_extend wf_sub_extend_def wf_sub_extend_mod wf_sub_single wf_sub_single_def
  wf_sub_single_mod wf_sub_wk wf_sub_q wf_sub_q_def wf_sub_q_mod : mctt.


Corollary wf_sub_q_False : forall Θ Ξ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ˢ q σ : Δ ▹ ⊥.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] : A[σ].
Proof.
  intros; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_eq : forall Θ Ξ Γ Δ σ x A,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ #x[σ] : A[σ].
Proof.
  intros; apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
Qed.

Lemma sub_preserves_vlookup_def : forall Θ Ξ Γ Δ σ x A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
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

Ltac lift_sub_False :=
  match goal with
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Δ) (a_typ _) _, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass a_False) Γ ⊢ˢ sb_q σ : cons (ce_ass a_False) Δ) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_q_False; exact Hσ)
  end.

Ltac lift_sub_step :=
  match goal with
  | Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ,
    IH : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_sub A σ)) Γ ⊢ˢ sb_q σ : cons (ce_ass A) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_q; [ exact Hσ | | exact (IH _ _ Hσ) ]; mauto 2)
  | Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ,
    IH : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (a_univ _) (exp_sub ?A _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_sub A σ)) Γ ⊢ˢ sb_q σ : cons (ce_ass A) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply (wf_sub_q _ _ _ _ _ _ 0); [ exact Hσ | | exact (wf_exp_small_large (IH _ _ Hσ)) ];
                   eapply wf_exp_small_large; eassumption)
  end.

Ltac lift_sub_def :=
  match goal with
  | Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ,
    _ : forall _ _, wf_sub ?Θ ?Ξ _ (cons (ce_def ?A ?M) ?Δ) _ -> _,
    IHA : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _),
    IHM : forall _ _, wf_sub ?Θ ?Ξ _ ?Δ _ -> wf_exp ?Θ ?Ξ _ (exp_sub ?A _) (exp_sub ?M _) |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_def (exp_sub A σ) (exp_sub M σ)) Γ ⊢ˢ sb_q σ : cons (ce_def A M) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_q_def; [ exact Hσ | | | exact (IHA _ _ Hσ) | exact (IHM _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub := repeat first [ lift_sub_False | lift_sub_step | lift_sub_def ].

Lemma me_apps_slot_root : forall Ns Γ H, me_slot_root Γ (me_apps H Ns) <-> me_slot_root Γ H.
Proof. induction Ns as [| N Ns IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma ds_unit_slot_root : forall Γ R, me_slot_root Γ (ds_unit R).
Proof.
  intros Γ [A om | Δ Φ | [| e Θ] p T Φ Ns | Θ p Ns | Θ p Ns]; cbn; try exact I.
  apply me_apps_slot_root; eapply mod_qname_slot_root, qname_mod_qname.
Qed.

Lemma gc_unit_slot_root : forall Θ Ξ Γ H TΦ, gc_unit Θ Ξ H = Some TΦ -> me_slot_root Γ H.
Proof. intros * Hu; unfold gc_unit in Hu; destruct (mod_qname H) eqn:E; [ eapply mod_qname_slot_root; exact E | discriminate ]. Qed.

(** The root of a well-formed module expression, if a slot, is a module slot. *)
Lemma modexp_eq_slot_root : forall Θ Ξ Γ H H',
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> me_slot_root Γ H /\ me_slot_root Γ H'.
Proof.
  induction 1; cbn; destruct_all; eauto 6 using mod_qname_slot_root, ds_unit_slot_root, gc_unit_slot_root.
Qed.

Lemma wf_sub_ext_of_ext : forall Θ Ξ Γ Ψ Ψ' Δ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ ->
    Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ ⊢ˢ sb_qn (length Ψ) σ : Ψ ++ Γ /\
    Θ ⍮ Ξ ⍮ tele_sub Ψ' σ ++ Δ ⊢ˢ sb_qn (length Ψ') σ : Ψ' ++ Γ.
Proof.
  intros * Hσ HΨ HΨσ; split; apply wf_sub_ext; eauto using ext_eq_ctx_left, ext_eq_ctx_right.
Qed.

(** ** Substituting into the Eliminator

    The same cases as for weakenings ([wk_elim_case] and the next two).
    The declaration is closed, so the types of the parameters and arguments
    move with the terms they are instantiated at; the motive and the branches
    move under the binders their contexts add, which are well formed by the
    telescope premises. *)


(** The eliminator's cases of [sub_preserves_wf]. *)
Definition sub_as_sub (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (σ : sub) (Γ : ctx) : Prop := Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ.

Lemma sub_as_sub_dom : forall Θ Ξ Δ σ Γ, sub_as_sub Θ Ξ Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ.
Proof. intros * Hσ; exact (wf_sub_dom _ _ _ _ _ Hσ). Qed.

Lemma sub_as_sub_ext : forall Θ Ξ Ψ Γ Δ σ, sub_as_sub Θ Ξ Δ σ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Δ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    sub_as_sub Θ Ξ (tele_sub Ψ σ ++ Δ) (sb_qn (length Ψ) σ) (Ψ ++ Γ).
Proof. intros; apply wf_sub_ext; assumption. Qed.

Ltac sub_elim_case :=
  first [ eapply (mv_elim_case _ _ _ (sub_as_sub_dom _ _) (sub_as_sub_ext _ _))
        | eapply (mv_elim_cong_case _ _ _ (sub_as_sub_dom _ _) (sub_as_sub_ext _ _))
        | eapply (mv_elim_iota_case _ _ _ (sub_as_sub_dom _ _) (sub_as_sub_ext _ _))
        | eapply (mv_elim_view_case _ _ _ (sub_as_sub_dom _ _) (sub_as_sub_ext _ _))
        | eapply (mv_record_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_record_cong_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_tuple_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_proj_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_proj_cong_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_tuple_cong_case _ _ _ (sub_as_sub_dom _ _))
        | eapply (mv_field_beta_case _ _ (sub_as_sub _ _))
        | eapply (mv_record_eta_case _ _ (sub_as_sub _ _)) ];
  unfold sub_as_sub; first [ eassumption | exact (wf_sub_id _ _) ].

(** ** Substitution Preserves the Judgments ([sub_preserves_wf]) *)

(** The case of a body unit under a substitution, with the induction
    hypotheses as premises. *)
Lemma sub_unit_body_case : forall Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Δ σ,
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx ->
    body_xp Θ Ξ (Δu' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δu ≈ Δu' ->
    (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub Δu σ0 ≈ tele_sub Δu' σ0) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δu ≈ body_ctx Φx ++ Δu ->
    (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (body_ctx Φx ++ Δu) σ0 ≈ tele_sub (body_ctx Φx ++ Δu) σ0) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δu' ≈ body_ctx Φx' ++ Δu' ->
    (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (body_ctx Φx' ++ Δu') σ0 ≈ tele_sub (body_ctx Φx' ++ Δu') σ0) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[σf][σ0] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[σf][σ0] ≈ A'[σf'][σ0] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σf][σ0] : A[σf][σ0]) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σf][σ0] ≈ M'[σf'][σ0] : A[σf][σ0]) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ U[σf]ᵘ[σ0]ᵘ ≈ U'[σf']ᵘ[σ0]ᵘ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A'[σf'][σ0] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M'[σf'][σ0] : A'[σf'][σ0]) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ U'[σf']ᵘ[σ0]ᵘ ≈ U'[σf']ᵘ[σ0]ᵘ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δu ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Ψ ++ Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H[σ0]ᵐ ≈ H[σ0]ᵐ) ->
    (forall k Ψ' H', List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δu' ++ Γ ⊢ᵐ H' ≈ H') ->
    (forall k Ψ' H', List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') ->
       forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Ψ' ++ Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H'[σ0]ᵐ ≈ H'[σ0]ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H[σf]ᵐ[σ0]ᵐ ≈ H'[σf']ᵐ[σ0]ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
       List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
       forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H'[σf']ᵐ[σ0]ᵐ ≈ H'[σf']ᵐ[σ0]ᵐ) ->
    tele_ass Δu -> tele_ass Δu' -> length Δu = length Δu' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    (* the premises as the rule takes them, for the scoping of the unit *)
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu' Φ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ (gu_open Δu Φ)[σ]ᵘ ≈ (gu_open Δu' Φ')[σ]ᵘ.
Proof.
  intros * Hb Hb' HΔ IHΔ Hx IHx Hx' IHx' IHA IHAA IHM IHMM IHU IHAr IHMr IHUr Ho IHo Ho' IHo' IHOo IHOr
           Ha Ha' Hl Hs Hsx Hn HU0 Hσ.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eapply ext_eq_ctx_left; exact HΔ).
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU0) as (HΓs & HUs & HUs').
  rewrite gunit_scoped_mk in HUs, HUs'; destruct HUs as [HΔs [_ HΦs]]; destruct HUs' as [HΔs' [_ HΦs']].
  pose proof (IHΔ _ _ Hσ) as HΔσ.
  assert (Hq : Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Δ ⊢ˢ sb_qn (length Δu) σ : Δu ++ Γ)
    by (apply wf_sub_ext; [ exact Hσ | exact (ext_eq_ctx_left _ _ _ _ _ HΔσ) | exact (ext_eq_ctx_left _ _ _ _ _ HΔ) ]).
  assert (Hq' : Θ ⍮ Ξ ⍮ tele_sub Δu' σ ++ Δ ⊢ˢ sb_qn (length Δu') σ : Δu' ++ Γ)
    by (apply wf_sub_ext; [ exact Hσ | exact (ext_eq_ctx_right _ _ _ _ _ HΔσ) | exact (ext_eq_ctx_right _ _ _ _ _ HΔ) ]).
  eapply (unit_body_moved Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Δ σ σ);
    [ | | | | | | | | | | | | | exact Hb | exact Hb' | exact Ha | exact Ha' | exact Hl | exact Hs | exact Hsx | exact Hn ].
  - eapply body_xp_sub; [ exact Hc | exact Hb | apply ctx_scoped_app_iff; split; assumption | rewrite List.length_app; exact HΦs
                        | apply sub_mod_compat_ext; eauto using wf_sub_mod_compat ].
  - eapply body_xp_sub; [ exact Hc | exact Hb' | apply ctx_scoped_app_iff; split; assumption
                        | rewrite List.length_app; exact HΦs' | apply sub_mod_compat_ext; eauto using wf_sub_mod_compat ].
  - exact HΔσ.
  - exact (IHx _ _ Hσ).
  - exact (IHx' _ _ Hσ).
  - intros * Hp Hp' Hf0 Hf0'.
    split; [| split; [| split ] ];
      [ exact (IHA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHAA _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq)
      | exact (IHMM _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq) ].
  - intros * Hp Hp' Hf0 Hf0'; exact (IHU _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq).
  - intros * Hp Hp' Hf0 Hf0'.
    split; [ exact (IHAr _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq') | exact (IHMr _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq') ].
  - intros * Hp Hp' Hf0 Hf0'; exact (IHUr _ _ _ _ _ _ _ _ _ Hp Hp' Hf0 Hf0' _ _ Hq').
  - intros k Ψ H Ek.
    destruct (body_opens_prefix _ _ _ _ _ Hb _ _ _ Ek) as [Ψr HΨr].
    pose proof (IHx _ _ Hσ) as Hxσ.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) σ ++ Δ).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxσ) as HC; rewrite HΨr, <- List.app_assoc, tele_sub_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_sub_ext _ _ (Ψ ++ Δu) _ _ _ Hσ HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho _ _ _ Ek)))) as Hσe.
    rewrite <- List.app_assoc in Hσe; exact (IHo _ _ _ Ek _ _ Hσe).
  - intros k Ψ H Ek.
    destruct (body_opens_prefix _ _ _ _ _ Hb' _ _ _ Ek) as [Ψr HΨr].
    pose proof (IHx' _ _ Hσ) as Hxσ.
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu') σ ++ Δ).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxσ) as HC; rewrite HΨr, <- List.app_assoc, tele_sub_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_sub_ext _ _ (Ψ ++ Δu') _ _ _ Hσ HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho' _ _ _ Ek)))) as Hσe.
    rewrite <- List.app_assoc in Hσe; exact (IHo' _ _ _ Ek _ _ Hσe).
  - intros * Ek Ek' Hf0 Hf0'; rewrite <- Hl; exact (IHOo _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0' _ _ Hq).
  - intros * Ek Ek' Hf0 Hf0'; exact (IHOr _ _ _ _ _ _ _ Ek Ek' Hf0 Hf0' _ _ Hq').
Qed.

(** The member rules, substituted. *)
Section SubMem.
  Context (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ : sub).

  Lemma sub_mem_case : forall H x R A i,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H[σ0]ᵐ ≈ H[σ0]ᵐ) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ A[σ0] : (Typeω@i)[σ0]) ->
      (forall M, ds_red R = Some M -> forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[σ0] : A[σ0]) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[σ] : A[σ].
  Proof.
    intros * HH IH Hm Ht IHA IHM Hσ; cbn; eapply wf_mem;
      [ exact (IH _ _ Hσ) | eapply wf_sub_mdenote_mem; eassumption
      | eapply ds_ty_sub; [ exact (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) | exact Ht ] | exact (IHA _ _ Hσ) |].
    intros M' HM'; destruct (ds_red_sub_inv _ _ _ HM') as (M0 & HM0 & ->); exact (IHM _ HM0 _ _ Hσ).
  Qed.

  Lemma sub_mem_cong_case : forall H H' x R A R' A',
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H[σ0]ᵐ ≈ H'[σ0]ᵐ) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A ->
      mdenote Θ Ξ Γ (me_mem H' x) R' -> ds_ty Θ Ξ R' = Some A' ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ (a_mem H' x)[σ0] : A[σ0]) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[σ] ≈ (a_mem H' x)[σ] : A[σ].
  Proof.
    intros * HH IHH Hm Ht Hm' Ht' IHM Hσ; cbn.
    pose proof (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) as Hc.
    eapply wf_exp_eq_mem_cong;
      [ exact (IHH _ _ Hσ) | eapply wf_sub_mdenote_mem; eassumption | eapply ds_ty_sub; eassumption
      | eapply wf_sub_mdenote_mem; [ exact (wf_modexp_eq_refl_right HH) | eassumption | eassumption ]
      | eapply ds_ty_sub; eassumption | exact (IHM _ _ Hσ) ].
  Qed.

  Lemma sub_mem_delta_case : forall H x R A M,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ H[σ0]ᵐ ≈ H[σ0]ᵐ) ->
      mdenote Θ Ξ Γ (me_mem H x) R -> ds_ty Θ Ξ R = Some A -> ds_red R = Some M -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ (a_mem H x)[σ] ≈ M[σ] : A[σ].
  Proof.
    intros * HH IH Hm Ht Hr Hσ; cbn.
    pose proof (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) as Hc.
    eapply wf_exp_eq_mem_delta;
      [ exact (IH _ _ Hσ) | eapply wf_sub_mdenote_mem; eassumption | eapply ds_ty_sub; eassumption | apply ds_red_sub; exact Hr ].
  Qed.

  Lemma sub_me_delta_sel_case : forall H y R Rm,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ᵐ (me_mem H y)[σ0]ᵐ ≈ (me_mem H y)[σ0]ᵐ) ->
      mdenote Θ Ξ Γ (me_mem H y) R -> ds_mod Θ Ξ R = Some Rm -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ (me_mem H y)[σ]ᵐ ≈ (ds_unit Rm)[σ]ᵐ.
  Proof.
    intros * HH IH Hm Hd Hσ.
    rewrite <- ds_unit_sub; cbn.
    eapply wf_me_delta_sel; [ exact (IH _ _ Hσ) | | apply ds_mod_sub; exact Hd ].
    pose proof (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
    exact (mdenote_sub _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) _ _ _ Hm HΓ HHs _ _ (wf_sub_mod_compat _ _ _ _ _ Hσ)).
  Qed.

  Lemma sub_me_unit_case : forall fp TΦ,
      gc_unit Θ Ξ (me_unit fp) = Some TΦ -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ (me_unit fp)[σ]ᵐ ≈ (me_unit fp)[σ]ᵐ.
  Proof.
    intros * Hu Hσ; cbn; eapply wf_me_unit; [ exact (wf_sub_dom _ _ _ _ _ Hσ) | exact Hu ].
  Qed.

  Lemma sub_me_beta_body_case : forall Δu X Φ N,
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ (gu_open (Δu ++ ce_ass X :: nil) Φ)[σ0]ᵘ ≈ (gu_open (Δu ++ ce_ass X :: nil) Φ)[σ0]ᵘ) ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : X[σ0]) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ (me_app (me_lit (gu_open (Δu ++ ce_ass X :: nil) Φ)) N)[σ]ᵐ
        ≈ (me_lit (gu_open (tele_sub Δu (Id,,N)) (gmod_sub Φ (sb_qn (length Δu) (Id,,N)))))[σ]ᵐ.
  Proof.
    intros * IHU IHN Hσ.
    replace (gu_open (tele_sub Δu (Id,,N)) (gmod_sub Φ (sb_qn (length Δu) (Id,,N))))
      with ((gu_open Δu Φ)[Id,,N]ᵘ) by (rewrite gunit_sub_mk; reflexivity).
    apply sub_beta_gen; [ reflexivity | exact (IHU _ _ Hσ) | exact (IHN _ _ Hσ) ].
  Qed.

  Lemma sub_me_beta_alias_case : forall Δu X E N,
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ᵘ (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E))[σ0]ᵘ ≈ (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E))[σ0]ᵘ) ->
      (forall Δ0 σ0, Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ σ0 : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ N[σ0] : X[σ0]) ->
      Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ (me_app (me_lit (gu_mk (Δu ++ ce_ass X :: nil) (md_alias E))) N)[σ]ᵐ
        ≈ (me_lit (gu_mk (tele_sub Δu (Id,,N)) (md_alias E[sb_qn (length Δu) (Id,,N)]ᵐ)))[σ]ᵐ.
  Proof.
    intros * IHU IHN Hσ.
    replace (gu_mk (tele_sub Δu (Id,,N)) (md_alias E[sb_qn (length Δu) (Id,,N)]ᵐ))
      with ((gu_mk Δu (md_alias E))[Id,,N]ᵘ) by (rewrite gunit_sub_mk; reflexivity).
    apply sub_beta_gen; [ exact I | exact (IHU _ _ Hσ) | exact (IHN _ _ Hσ) ].
  Qed.
  Lemma sub_me_delta_slot_case : forall x U,
      Γ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ (me_var x)[σ]ᵐ ≈ (me_lit U)[σ]ᵐ.
  Proof.
    intros * Hx Hσ; cbn.
    destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hx) as [[-> HUσ] | (y & -> & Hy)]; cbn;
      [ apply wf_me_lit; exact HUσ | eapply wf_me_delta_slot; [ exact (wf_sub_dom _ _ _ _ _ Hσ) | exact Hy ] ].
  Qed.
End SubMem.

Lemma sub_preserves_wf :
  (forall Θ Ξ Δ A M,
      Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ]) /\
  (forall Θ Ξ Δ A M M',
      Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ] : A[σ]) /\
  (forall Θ Ξ Δ A A',
      Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ]) /\
  (forall Θ Ξ Δ U,
      Θ ⍮ Ξ ⍮ Δ ⊢ᵤ U ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U[σ]) /\
  (forall Θ Ξ Δ Ψ Ψ',
      Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ) /\
  (forall Θ Ξ Δ U U',
      Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ]ᵘ) /\
  (forall Θ Ξ Δ H H',
      Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
      forall Γ σ, Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H[σ]ᵐ ≈ H'[σ]ᵐ).
Proof.
  apply syntactic_wf_mut_ind'; intros; destruct_let_ann;
    try solve [ sub_elim_case ];
    try solve [ first [ eapply sub_mem_case; eassumption | eapply sub_mem_cong_case; eassumption
                      | eapply sub_mem_delta_case; eassumption
                      | eapply sub_me_delta_sel_case; eassumption
                      | eapply sub_me_unit_case; eassumption | eapply sub_me_delta_slot_case; eassumption
                      | eapply sub_me_beta_body_case; eassumption | eapply sub_me_beta_alias_case; eassumption ] ];
    saturate_sub; push_sub; lift_sub.
  all: try solve [ push_closed; mauto 3 ].
  all: try solve [ mauto 4 ].
  all: try solve [ econstructor; mauto 3 ].
  (** The module rules.  A local module is lifted over by [q σ] at the
      transported unit. *)
  all: try solve [ rewrite ?exp_sub_sub_extend_mod; eapply wf_let_mod; eauto 6 using wf_sub_q_mod, wf_unit_eq_refl_left ].
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
  all: try solve [ eapply sub_unit_body_case; (eassumption || (eapply wf_unit_eq_body; eassumption)) ].
  (** An alias of a literal, flattened: the literal moves by the
      substitution lifted over the alias's parameters. *)
  all: try solve [
    match goal with
    | Hx : wf_ext_eq _ _ ?Γ ?Δ ?Δ, IHx : forall _ _, wf_sub _ _ _ ?Γ _ -> wf_ext_eq _ _ _ (tele_sub ?Δ _) (tele_sub ?Δ _),
      IHU : forall _ _, wf_sub _ _ _ (?Δ ++ ?Γ) _ -> wf_unit_eq _ _ _ (gunit_sub (gu_mk ?Δ' ?D) _) _,
      Hσ : wf_sub _ _ _ ?Γ ?σ |- wf_unit_eq _ _ _ _ (gunit_sub (gu_mk (?Δ' ++ ?Δ) ?D) _) =>
        destruct (wf_sub_ext_of_ext _ _ _ _ _ _ _ Hσ Hx (IHx _ _ Hσ)) as [Hl _];
        change (gu_mk (Δ' ++ Δ) D) with (gunit_abs Δ (gu_mk Δ' D)); rewrite gunit_abs_sub, gunit_sub_mk;
        cbn [moddef_sub modexp_sub];
        pose proof (IHU _ _ Hl) as HU'; revert HU';
        destruct (gunit_sub (gu_mk Δ' D) (sb_qn (length Δ) σ)) as [Δw Dw]; intros HU'; cbn [gunit_abs];
        eapply wf_unit_eq_flatten; [ exact (IHx _ _ Hσ) | apply tele_ass_sub; assumption | exact HU' ]
    end ].
  (** Module expressions. *)
  all: try solve [
    match goal with
    | Hx : _ ∋ #?x ≔ₘ _, Hσ : wf_sub _ _ _ _ ?σ |- wf_modexp_eq _ _ _ (sentry_modexp (?σ ?x)) _ =>
        destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hx) as [[-> HUσ] | (y & -> & Hy)]; cbn;
        [ apply wf_me_lit; exact HUσ | eapply wf_me_var; eauto ]
    end ].
  all: try solve [ eapply wf_me_mem;
                   [ eauto
                   | eapply wf_sub_mdenote_mem; eassumption | eapply wf_sub_ds_mtele_mem; eassumption
                   | eapply wf_sub_mdenote_mem; [ apply wf_me_sym | ..]; eassumption
                   | eapply wf_sub_ds_mtele_mem; [ apply wf_me_sym | ..]; eassumption ] ].
  all: try solve [ eapply wf_me_app;
                   [ eauto
                   | eapply wf_sub_mdenote; eassumption | eapply wf_sub_ds_mtele; eassumption
                   | eapply tele_view_sub_some; eassumption | eauto | eauto | eauto
                   | eapply wf_sub_mdenote; [ apply wf_me_sym | ..]; eassumption
                   | eapply wf_sub_ds_mtele; [ apply wf_me_sym | ..]; eassumption
                   | eapply tele_view_sub_some; eassumption | eauto | eauto ] ].
  (** [Π], as for weakening. *)
  all: try solve [
    match goal with
    | HU : wf_is_univ ?T ?X ?Δ ?U, HA : wf_exp ?T ?X ?Δ ?U ?A, Hσ : wf_sub ?T ?X ?Γ ?Δ ?σ |- wf_exp _ _ _ _ (a_pi _ _) =>
        assert (T ⍮ X ⍮ Γ ▹ A[σ] ⊢ˢ q σ : Δ ▹ A) by (eapply wf_sub_q_univ; eauto);
        eapply wf_pi; [ eauto | eauto | rewrite <- exp_wk_shift_sub_q; eauto ]
    end ].
  all: try solve [
    match goal with
    | HU : wf_is_univ ?T ?X ?Δ ?U, HA : wf_exp ?T ?X ?Δ ?U ?A, Hσ : wf_sub ?T ?X ?Γ ?Δ ?σ |- wf_exp_eq _ _ _ _ (a_pi _ _) _ =>
        assert (T ⍮ X ⍮ Γ ▹ A[σ] ⊢ˢ q σ : Δ ▹ A) by (eapply wf_sub_q_univ; eauto);
        eapply wf_exp_eq_pi_cong; [ eauto | eauto | eauto | rewrite <- exp_wk_shift_sub_q; eauto ]
    end ].
  (** The type former and the constructors: their types are closed. *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, Hσ : wf_sub _ _ _ _ _ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ) | exact Hl ]);
        try (erewrite (ind_ty_sub D) by eassumption); try (erewrite (con_ty_sub _ D) by eassumption);
        first [ eapply wf_ind | eapply wf_con | eapply wf_exp_eq_ind_cong | eapply wf_exp_eq_con_cong ]; eauto
    end ].
  (** A constructor of a view at the uniform parameters, as for
      weakening ([im_pre_sub]). *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, HM : ind_member ?D _ = Some ?Mj, HU : List.length ?Us = ind_nu ?D,
      IH1 : forall Γ0 σ0, wf_sub _ _ Γ0 _ σ0 -> wf_exp _ _ Γ0 _ (apps_exp (a_con _ _ _) (?Us ++ _))[σ0],
      IH2 : forall Γ0 σ0, wf_sub _ _ Γ0 _ σ0 -> wf_exp _ _ Γ0 _ (apps_exp (a_con _ _ _) (im_pre ?Mj ?Us ++ _))[σ0],
      Hσ : wf_sub _ _ _ _ _ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ) | exact Hl ]);
        pose proof (IH1 _ _ Hσ) as E1; pose proof (IH2 _ _ Hσ) as E2;
        rewrite apps_exp_sub, List.map_app in E1, E2; rewrite !apps_exp_sub, !List.map_app;
        cbn in E1, E2 |- *;
        rewrite (im_pre_sub D _ Mj Us) in E2 |- * by eassumption;
        eapply wf_exp_eq_con_view; [ eassumption | eassumption | eassumption | rewrite List.length_map; exact HU
                                   | exact E1 | exact E2 ]
    end ].
Qed.

Corollary sub_preserves_exp : forall Θ Ξ Γ Δ A M σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_exp_eq : forall Θ Ξ Γ Δ A M M' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M'[σ] : A[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_subtyp : forall Θ Ξ Γ Δ A A' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ⊆ A'[σ].
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_ext : forall Θ Ξ Γ Δ Ψ Ψ' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ' σ.
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_unit : forall Θ Ξ Γ Δ U U' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ]ᵘ.
Proof.
  intros; pose proof sub_preserves_wf; destruct_all; eauto.
Qed.

Corollary sub_preserves_modexp : forall Θ Ξ Γ Δ H H' σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ ⨟ τ : Δ.
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
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) as [i ?] by mauto 3.
  eapply sub_preserves_exp; [ eassumption | eapply wf_sub_single; eassumption ].
Qed.

Corollary exp_eq_sub_single : forall Θ Ξ Γ A B M M' N,
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[Id,,N] ≈ M'[Id,,N] : B[Id,,N].
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i) as [i ?] by mauto 3.
  eapply sub_preserves_exp_eq; [ eassumption | eapply wf_sub_single; eassumption ].
Qed.

#[export]
Hint Resolve exp_sub_single exp_eq_sub_single : mctt.

(** The substitution [Id ,, M] at which the [⊥]-eliminator is typed. *)
Corollary wf_sub_False_single : forall Θ Ξ Γ M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M : Γ ▹ ⊥.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Typeω@0) by mauto 3.
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

    So [Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ] is read "[Δ] refines [Γ]"; [wf_sub_id] is its
    reflexivity and [wf_sub_compose] its transitivity. *)

Corollary ctxsub_vlookup : forall Θ Ξ Γ Δ x A,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Γ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #x : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ #x[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_vlookup_def : forall Θ Ξ Γ Δ x A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Γ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ #x ≈ M : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ #x[Id] ≈ M[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

(** A refinement keeps every module slot. *)
Corollary ctxsub_lookup_mod : forall Θ Ξ Γ Δ x U,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Γ ∋ #x ≔ₘ U ->
    Δ ∋ #x ≔ₘ U.
Proof.
  intros * H HU; destruct (wf_sub_apply_mod _ _ _ _ _ H _ _ HU) as [[[=] _] | (y & [= <-] & Hy)].
  rewrite gunit_sub_id in Hy; exact Hy.
Qed.

(** Extending a refinement by one binding on each side: the bindings below the
    heads are those of the refinement, weakened, so only the heads are left to
    the caller. *)
Lemma wf_sub_id_extend_gen : forall Θ Ξ Γ Δ e e',
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ e' :: Δ ->
    ⊢ Θ ⍮ Ξ ⍮ e :: Γ ->
    (forall B, e :: Γ ∋ #0 : B -> Θ ⍮ Ξ ⍮ e' :: Δ ⊢ #0 : B) ->
    (forall B N, e :: Γ ∋ #0 ≔ N : B -> Θ ⍮ Ξ ⍮ e' :: Δ ⊢ #0 ≈ N : B) ->
    (forall U, e :: Γ ∋ #0 ≔ₘ U -> e' :: Δ ∋ #0 ≔ₘ U) ->
    Θ ⍮ Ξ ⍮ e' :: Δ ⊢ˢ Id : e :: Γ.
Proof.
  intros * HId ? ? Hhd Hhdd Hhdm; saturate_sub.
  assert (Θ ⍮ Ξ ⍮ e' :: Δ ⊢ʷ ↑ : Δ) by mauto 2.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢ˢ Id : Γ ▹ A.
Proof.
  intros * HId ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▹ A') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▹ A' ⊢ʷ ↑ : Δ) by mauto 2.
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst.
  (** The top binding: [#0] has type [A'[↑]ʷ] there and [A'[↑]ʷ ⊆ A[↑]ʷ] by
      weakening the given subtyping. *)
  eapply wf_exp_subtyp'; [ mauto 2 | ].
  eapply wk_preserves_subtyp; eassumption.
Qed.

(** A definition refines a definition of a supertype with an equal body. *)
Lemma wf_sub_id_extend_def : forall Θ Ξ Γ Δ A A' M M' i,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' ≈ M : A ->
    Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢ˢ Id : Γ ▸ A ≔ M.
Proof.
  intros * HId ? ? ? ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢ʷ ↑ : Δ) by mauto 2.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A' ⊆ A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢ˢ Id : Γ ▹ A.
Proof.
  intros * HId ? ? ? ?; saturate_sub.
  assert (⊢ Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M') by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Δ ▸ A' ≔ M' ⊢ʷ ↑ : Δ) by mauto 2.
  eapply wf_sub_id_extend_gen; [ eassumption | eassumption | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst.
  eapply wf_exp_subtyp'; [ mauto 2 | ].
  eapply wk_preserves_subtyp; eassumption.
Qed.

(** A module slot refines a slot of the same unit. *)
Lemma wf_sub_id_extend_mod : forall Θ Ξ Γ Δ U,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Δ ▹ₘ U ⊢ˢ Id : Γ ▹ₘ U.
Proof.
  intros * HId ? ?; saturate_sub.
  eapply wf_sub_id_extend_gen; [ eassumption | mauto 2 | mauto 2 | | |];
    intros * Hlk; inversion Hlk; subst; constructor.
Qed.

(** Equal types give refinements in both directions; this is the instance
    [wf_sub_eq] and the presupposition lemma need. *)
Corollary wf_sub_id_extend_eq : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ˢ Id : Γ ▹ A.
Proof.
  intros.
  eapply wf_sub_id_extend; mauto 3.
Qed.

(** The same for definitions, with equal bodies. *)
Corollary wf_sub_id_extend_def_eq : forall Θ Ξ Γ A A' M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A' ≔ M' ⊢ˢ Id : Γ ▸ A ≔ M.
Proof.
  intros.
  eapply wf_sub_id_extend_def; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_id_extend wf_sub_id_extend_eq wf_sub_id_extend_def wf_sub_id_forget
             wf_sub_id_extend_def_eq wf_sub_id_extend_mod : mctt.

Corollary ctxsub_exp : forall Θ Ξ Γ Δ A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ M[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_exp_eq : forall Θ Ξ Γ Δ A M M',
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ M[Id] ≈ M'[Id] : A[Id]) as H' by mauto 2.
  rewrite !exp_sub_id in H'; assumption.
Qed.

Corollary ctxsub_subtyp : forall Θ Ξ Γ Δ A A',
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ Id : Γ ->
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

    [Typeω@i] is closed, so [Typeω@i[φ]ʷ] and [Typeω@i[σ]] are [Typeω@i] — but only
    up to conversion, and [eauto]'s [simple apply] does not reduce.  These four
    spell it out; every "and the type is still a type" step below goes through
    one of them. *)

Corollary wk_preserves_typ : forall Θ Ξ Γ Δ A φ i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Typeω@i.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ exp_wk A φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary wk_preserves_typ_eq : forall Θ Ξ Γ Δ A A' φ i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@i.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ exp_wk A φ ≈ exp_wk A' φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ : forall Θ Ξ Γ Δ A σ i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ : exp_sub (a_typ i) σ) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_typ_eq : forall Θ Ξ Γ Δ A A' σ i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A'[σ] : Typeω@i.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ ≈ exp_sub A' σ : exp_sub (a_typ i) σ) by mauto 2.
  assumption.
Qed.

(** The same four for a small universe [Type⟨𝕃ᵒ n⟩], also closed. *)

Corollary wk_preserves_styp : forall Θ Ξ Γ Δ A φ n,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ : Type⟨𝕃ᵒ n⟩.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ exp_wk A φ : exp_wk (Type⟨𝕃ᵒ n⟩) φ) by mauto 2.
  assumption.
Qed.

Corollary wk_preserves_styp_eq : forall Θ Ξ Γ Δ A A' φ n,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Type⟨𝕃ᵒ n⟩.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Δ ⊢ exp_wk A φ ≈ exp_wk A' φ : exp_wk (Type⟨𝕃ᵒ n⟩) φ) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_styp : forall Θ Ξ Γ Δ A σ n,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type⟨𝕃ᵒ n⟩.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ : exp_sub (Type⟨𝕃ᵒ n⟩) σ) by mauto 2.
  assumption.
Qed.

Corollary sub_preserves_styp_eq : forall Θ Ξ Γ Δ A A' σ n,
    Θ ⍮ Ξ ⍮ Δ ⊢ A ≈ A' : Type⟨𝕃ᵒ n⟩ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A'[σ] : Type⟨𝕃ᵒ n⟩.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ ≈ exp_sub A' σ : exp_sub (Type⟨𝕃ᵒ n⟩) σ) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve wk_preserves_typ wk_preserves_typ_eq
             sub_preserves_typ sub_preserves_typ_eq : mctt.
#[export]
Hint Resolve wk_preserves_styp wk_preserves_styp_eq
             sub_preserves_styp sub_preserves_styp_eq : mctt.

(** ** Lifting without the Extra Premise

    Given [wk_preserves_wf] and [sub_preserves_wf], the transported type
    premise of [wf_wk_q] and [wf_sub_q] is redundant: it is the conclusion of
    [wk_preserves_typ], respectively [sub_preserves_typ] (see the remark on
    [wf_sub_q]).  These versions replace [wf_wk_q] and [wf_sub_q] as hints, as
    [Definitions] does for the subtyping rules. *)

Corollary wf_wk_q' : forall Θ Ξ Γ Δ φ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ▹ A[φ]ʷ ⊢ʷ wk_q φ : Γ ▹ A.
Proof.
  intros; eapply wf_wk_q; mauto 2.
Qed.

Corollary wf_sub_q' : forall Θ Ξ Γ Δ σ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢ˢ q σ : Δ ▹ A.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(S i).
Proof.
  intros; eapply wf_exp_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

Lemma wf_exp_eq_cumu : forall Θ Ξ Γ A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(S i).
Proof.
  intros; eapply wf_exp_eq_subtyp'; [ eassumption | ].
  apply wf_subtyp_univ; [ mauto 2 | lia ].
Qed.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_subtyp_ge : forall {Θ Ξ Γ i j},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ Typeω@j.
Proof.
  induction 2; mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma lift_exp_ge : forall Θ Ξ Γ A i j,
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma lift_exp_eq_ge : forall Θ Ξ Γ A A' i j,
    i <= j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@j.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
Hint Resolve lift_exp_ge lift_exp_eq_ge : mctt.

(** The same along the order of universe indices, where a universe is written
    as the term [ulvl_tm u]: inside a tier it is the order on levels, and from
    the small tier to the large one it is [wf_subtyp_small_large]. *)
Lemma lift_exp_uidx : forall Θ Ξ Γ A u v,
    uidx_le u v ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : ulvl_tm v.
Proof.
  intros * Hle HA; destruct u as [n | n], v as [m | m]; cbn in Hle, HA |- *;
    [ eapply wf_exp_subtyp'; [ eassumption | apply wf_subtyp_suniv_ole; [ mauto 2 | assumption ] ]
    | eapply wf_exp_small_large; eassumption
    | contradiction
    | eapply lift_exp_ge; eassumption ].
Qed.

Lemma lift_exp_eq_uidx : forall Θ Ξ Γ A A' u v,
    uidx_le u v ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm u ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : ulvl_tm v.
Proof.
  intros * Hle HA; destruct u as [n | n], v as [m | m]; cbn in Hle, HA |- *;
    [ eapply wf_exp_eq_subtyp'; [ eassumption | apply wf_subtyp_suniv_ole; [ mauto 2 | assumption ] ]
    | eapply wf_exp_eq_small_large; eassumption
    | contradiction
    | eapply lift_exp_eq_ge; eassumption ].
Qed.

#[export]
Hint Resolve lift_exp_uidx lift_exp_eq_uidx : mctt.

(** The closed small types are types of every universe, small or large: their
    rules give them [Type@0], which [uidx_le_least] lifts anywhere. *)
Lemma wf_level_univ : forall {Θ Ξ Γ n} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : ulvl_tm u.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_level; assumption ]. Qed.

Lemma wf_True_univ : forall {Θ Ξ Γ} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : ulvl_tm u.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_True; assumption ]. Qed.

Lemma wf_False_univ : forall {Θ Ξ Γ} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : ulvl_tm u.
Proof. intros; eapply (lift_exp_uidx _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_False; assumption ]. Qed.

Lemma wf_exp_eq_level_cong_univ : forall {Θ Ξ Γ n} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ≈ Level@n : ulvl_tm u.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_exp_eq_level_cong; assumption ]. Qed.

Lemma wf_exp_eq_True_cong_univ : forall {Θ Ξ Γ} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : ulvl_tm u.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_exp_eq_True_cong; assumption ]. Qed.

Lemma wf_exp_eq_False_cong_univ : forall {Θ Ξ Γ} {u : uidx}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : ulvl_tm u.
Proof. intros; eapply (lift_exp_eq_uidx _ _ _ _ _ (us oz)); [ apply uidx_le_least | apply wf_exp_eq_False_cong; assumption ]. Qed.

(** Not hints: they would fire on a goal whose type is still an evar and
    leave the index open.  Apply them by name. *)

(** The order on indices is subtyping of the universes. *)
Lemma wf_subtyp_uidx : forall {Θ Ξ Γ} {u v : uidx},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    uidx_le u v ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ulvl_tm u ⊆ ulvl_tm v.
Proof.
  intros * HΓ Hle; destruct u as [n | n], v as [m | m]; cbn in Hle |- *;
    [ apply wf_subtyp_suniv_ole; assumption
    | eapply wf_subtyp_small_large; mauto 3
    | contradiction
    | apply wf_subtyp_ge; assumption ].
Qed.

(** The same from a type of any universe, large or small. *)
Lemma wf_subtyp_refl_univ : forall Θ Ξ Γ A u, Θ ⍮ Ξ ⍮ Γ ⊢ A : ulvl_tm u -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros * HA; eapply wf_subtyp_refl_typ, (lift_exp_uidx _ _ _ _ u (ulvl u));
    [ apply uidx_le_ulvl | exact HA ].
Qed.

#[export]
Hint Resolve wf_subtyp_refl_univ : mctt.



Corollary lift_exp_max_left : forall Θ Ξ Γ A i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(max i j).
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_max_right : forall Θ Ξ Γ A i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(max i j).
Proof.
  intros; eapply lift_exp_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_left : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(max i j).
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

Corollary lift_exp_eq_max_right : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(max i j).
Proof.
  intros; eapply lift_exp_eq_ge; [ | eassumption ]; lia.
Qed.

(** Transitivity across two different levels. *)
Lemma exp_eq_trans_typ_max : forall {Θ Ξ Γ i i' A A' A''},
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ A'' : Typeω@i' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A'' : Typeω@(max i i').
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@(max i i')) by eauto using lift_exp_eq_max_left.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A' ≈ A'' : Typeω@(max i i')) by eauto using lift_exp_eq_max_right; mautosolve 4.
Qed.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

(** Two types are always types at a common level.  Stating it in this form —
    with the level existentially quantified rather than spelled [max i j] — is
    what lets a proof reach it with [eapply] and leave both levels to
    unification, which is the only way to use cumulativity in a case whose level
    variables the induction named for us. *)
Corollary lift_exp_common : forall Θ Ξ Γ A A' i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@j ->
    exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@k /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@k.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** [wf_pi_large] checks the domain and the codomain at the same level, which is
    almost never how they arrive: the domain's level comes from its own premise
    and the codomain's from presupposition.  This is the form that takes them as
    they come.  It is a hint, and the level it produces is a [max] of two evars,
    so it only fires where the level of the [Π]-type is still open — which is
    exactly where the strict [wf_pi_large] cannot fire at all. *)
Corollary wf_pi_max : forall Θ Ξ Γ A B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@(max i j).
Proof.
  intros.
  eapply wf_pi_large; [ eapply lift_exp_max_left | eapply lift_exp_max_right ]; eassumption.
Qed.

#[export]
Hint Resolve wf_pi_max : mctt.

(** [lift_exp_common] for the two components of a [Π]-type, which do not live in
    the same context and so are not two instances of it.  Every rule that
    mentions a [Π]-type checks both components at one level, and this is what
    supplies that level when they arrive at two. *)
Corollary lift_exp_pi_common : forall Θ Ξ Γ A B i j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@j ->
    exists k, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@k /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@k.
Proof.
  intros.
  exists (max i j); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

(** ** Types in a Well-formed Context

    Every binding of a well-formed context is a type in that context: the
    weakening carried by [ctx_lookup] is exactly what makes this so. *)

(** What the global context guarantees about the parameters in scope: popping a
    frame leaves a well-formed context, whose parameters are well formed.  The
    parameters checked one frame out are those of [frame_params]: all of them
    but a record module's value, which is typed inside the record's frame
    ([wf_gs_tele] gives the whole telescope there). *)

Lemma wf_gmod_ctx : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> ⊢ Θ ⍮ Ξ ⍮ frame_params K Δ ++ gs_tele Ξ.
Proof.
  induction 1; cbn [frame_params List.tl]; assumption.
Qed.

Lemma ctx_wf_gctx : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ᵍ Θ ⍮ Ξ.
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
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros * HΓ Hlk; gen HΓ; induction Hlk; intros HΓ;
    assert (Θ ⍮ Ξ ⍮ _ ⊢ʷ ↑ : Γ) by (eapply wf_wk_shift; exact HΓ);
    [ destruct (ctx_decomp_right HΓ) as [k ?]
    | destruct (ctx_decomp_def_typ HΓ) as [k ?]
    | destruct IHHlk as [k ?]; [ mauto 2 |] ];
    exists k; change (Typeω@k) with (Typeω@k[↑]ʷ); mauto 2.
Qed.

(** The body of a definition entry is typed at its type, both weakened. *)
Lemma ctx_lookup_def_wf : forall Ξ Θ Γ x A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Γ ∋ #x ≔ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ Hlk; gen HΓ; induction Hlk; intros HΓ;
    assert (Θ ⍮ Ξ ⍮ _ ⊢ʷ ↑ : Γ) by (eapply wf_wk_shift; exact HΓ);
    [ pose proof (ctx_decomp_def_body HΓ) | pose proof (IHHlk ltac:(mauto 2)) ];
    mauto 2.
Qed.

#[export]
Hint Resolve ctx_lookup_wf ctx_lookup_def_wf : mctt.
