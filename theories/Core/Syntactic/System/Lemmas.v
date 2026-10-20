(** * Properties of the Judgments, continued

    Everything here uses presupposition, which [Global/Presup.v] proves by a mutual
    induction over all the judgments; the structural properties it relies on
    are in [Structural]. *)

From Stdlib Require Import Lia Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export Presup.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Presupposition for Typing

    [presup_exp_typ] is proved in [Global/Presup.v], from the mutual theorem. *)

Corollary presup_exp : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros; split; mauto 2 using presup_exp_typ.
Qed.

(** ** Context Conversion of Substitutions

    [Θ ⍮ Ξ ⍮ Γ' ⊢ˢ Id : Γ] transports substitutions too: compose with the inclusion and
    cancel the identity.  Which side it goes on is what distinguishes the two:
    [ctxsub_sub] refines the domain, [ctxsub_sub_cod] coarsens the codomain. *)

Corollary ctxsub_sub : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Δ.
Proof.
  intros.
  rewrite <- (sb_compose_id_right σ); mauto 2.
Qed.

Corollary ctxsub_sub_cod : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id : Γ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ : Γ'.
Proof.
  intros.
  rewrite <- (sb_compose_id_left σ); mauto 2.
Qed.

#[export]
Hint Resolve ctxsub_sub : mctt.

(** * Substitution Equivalence

    The closure properties below are the [wf_sub_eq] counterparts of
    [wf_sub_id]–[wf_sub_q].  [Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ] equates the images at
    [A[σ]], so symmetry and transitivity need [A[σ]] and [A[σ']] to be equal
    types.  That is [sub_eq_preserves_exp], which therefore comes first, and
    the [PER] instance last. *)

Lemma sentry_modexp_wk : forall e φ, sentry_modexp (sentry_wk e φ) = modexp_wk (sentry_modexp e) φ.
Proof. intros [] φ; reflexivity. Qed.

Lemma sentry_modexp_sub : forall e τ, sentry_modexp (sentry_sub e τ) = (sentry_modexp e)[τ]ᵐ.
Proof. intros [] τ; reflexivity. Qed.

(** What a well-typed substitution sends a module slot to is a well-formed
    module expression. *)
Lemma wf_sub_mod_image : forall Θ Ξ Γ Δ σ x U,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Δ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ sentry_modexp (σ x) ≈ sentry_modexp (σ x).
Proof.
  intros * Hσ Hl; destruct (wf_sub_apply_mod _ _ _ _ _ Hσ _ _ Hl) as [[-> HU] | (y & -> & Hy)]; cbn.
  - apply wf_me_lit; exact HU.
  - eapply wf_me_var; [ exact (wf_sub_dom _ _ _ _ _ Hσ) | exact Hy ].
Qed.

Lemma wf_sub_eq_refl : forall Θ Ξ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ : Δ.
Proof.
  intros; econstructor; [ mauto 2 | mauto 2 | mauto 2 | intros; eapply wf_sub_mod_image; eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_refl : mctt.

Lemma sub_eq_preserves_vlookup : forall Θ Ξ Γ Δ σ σ' x A,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Δ ∋ #x : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ #x[σ'] : A[σ].
Proof.
  intros; eapply wf_sub_eq_apply; eassumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_vlookup : mctt.

(** [saturate_sub_eq] plays the role [saturate_sub] does for [sub_preserves_wf]: it
    injects the two typing components of every substitution equivalence in
    context, so that all the [mauto] calls below can reach them. *)

Ltac saturate_sub_eq :=
  match_by_head wf_sub_eq ltac:(fun H => pose proof (wf_sub_eq_left _ _ _ _ _ _ H);
                                         pose proof (wf_sub_eq_right _ _ _ _ _ _ H));
  clear_dups;
  saturate_sub.

Corollary ctxsub_sub_eq : forall Θ Ξ Γ Γ' Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ ≈ σ' : Δ.
Proof.
  intros * ? H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A ?.
    eapply ctxsub_exp_eq; mauto 2.
  - intros x U Hl; rewrite <- (modexp_sub_id (sentry_modexp (σ x))), <- (modexp_sub_id (sentry_modexp (σ' x))).
    eapply sub_preserves_modexp; [ eapply wf_sub_eq_apply_mod; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve ctxsub_sub_eq : mctt.

(** The tempting justification of the second component is
    "[sub_preserves_exp_eq] applied to reflexivity", which does not give it:
    [sub_preserves_wf] transports along a single substitution and so only
    yields [A[σ] ≈ A[σ]].  The equation really comes from [sub_eq_preserves_exp],
    which is proved by an induction that appeals to this lemma.  We break the
    cycle by taking the equation as a premise; that is precisely what the
    induction hypothesis for the domain supplies at every use site. *)

Lemma wf_sub_eq_q : forall Θ Ξ Γ Δ σ σ' A i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢ˢ q σ ≈ q σ' : Δ ▹ A.
Proof.
  intros * H ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Typeω@i) by mauto 2.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢ʷ ↑ : Γ) by mauto 2.
  econstructor; [ mauto 2 | | |].
  - eapply ctxsub_sub; [ eapply wf_sub_id_extend_eq; mauto 2 | mauto 2 ].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 3 | ].
    rewrite <- !sentry_exp_wk; fold (exp_sub (a_var n) σ) (exp_sub (a_var n) σ').
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
  - intros x U Hlk; inversion Hlk; subst;
    match goal with Hl0 : _ ∋ # ?n ≔ₘ _ |- _ =>
      change (sb_q σ (S n)) with (sentry_wk (σ n) wk_shift); change (sb_q σ' (S n)) with (sentry_wk (σ' n) wk_shift);
      rewrite !sentry_modexp_wk; eapply wk_preserves_modexp; [ eapply wf_sub_eq_apply_mod; eassumption | eassumption ] end.
Qed.

(** The same over a definition, with the substituted bodies equal as a
    premise for the same reason. *)
Lemma wf_sub_eq_q_def : forall Θ Ξ Γ Δ σ σ' A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢ˢ q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * H ? ? ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ'] : A[σ']) by mauto 2.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢ʷ ↑ : Γ) by mauto 2.
  econstructor; [ mauto 2 | | |].
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] ≈ A[σ] : Typeω@i) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ'] ≈ M[σ] : A[σ']) by
      (eapply wf_exp_eq_subtyp'; [ symmetry; eassumption | eapply wf_subtyp_refl; eassumption ]).
    eapply ctxsub_sub; [ eapply wf_sub_id_extend_def_eq; eassumption | mauto 2 ].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 3 | ].
    rewrite <- !sentry_exp_wk; fold (exp_sub (a_var n) σ) (exp_sub (a_var n) σ').
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
  - intros x U Hlk; inversion Hlk; subst;
    match goal with Hl0 : _ ∋ # ?n ≔ₘ _ |- _ =>
      change (sb_q σ (S n)) with (sentry_wk (σ n) wk_shift); change (sb_q σ' (S n)) with (sentry_wk (σ' n) wk_shift);
      rewrite !sentry_modexp_wk; eapply wk_preserves_modexp; [ eapply wf_sub_eq_apply_mod; eassumption | eassumption ] end.
Qed.

#[export]
Hint Resolve wf_sub_eq_q wf_sub_eq_q_def : mctt.

Corollary wf_sub_eq_q_False : forall Θ Ξ Γ Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ˢ q σ ≈ q σ' : Δ ▹ ⊥.
Proof.
  intros * H; saturate_sub_eq.
  apply (wf_sub_eq_q Θ Ξ Γ Δ σ σ' ⊥ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_False : mctt.

Lemma wf_sub_eq_extend : forall Θ Ξ Γ Δ σ σ' A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ,,M ≈ σ',,M' : Δ ▹ A.
Proof.
  intros * H ? ? ? ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
      [ assumption | eapply wf_sub_eq_apply; eassumption ].
  - intros x U Hlk; inversion Hlk; subst; cbn; eapply wf_sub_eq_apply_mod; eassumption.
Qed.

(** The instance every elimination rule needs: two single substitutions of
    equal terms.  Stating it separately is what keeps [exp_sub_id] out of the
    call sites, which would otherwise have to rewrite [A[Id]] to [A] three
    times over. *)
Corollary wf_sub_eq_id_extend : forall Θ Ξ Γ A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M ≈ Id,,M' : Γ ▹ A.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  apply (wf_sub_eq_extend Θ Ξ Γ Γ sb_id sb_id A M M' i);
    [ mauto 3 | assumption
    | rewrite exp_sub_id; assumption
    | rewrite exp_sub_id; assumption
    | rewrite exp_sub_id; assumption ].
Qed.

Lemma wf_sub_eq_extend_def : forall Θ Ξ Γ Δ σ σ' A M N N' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N' : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N' ≈ M[σ'] : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ,,N ≈ σ',,N' : Δ ▸ A ≔ M.
Proof.
  intros * H ? ? ? ? ? ? ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
      [ assumption | eapply wf_sub_eq_apply; eassumption ].
  - intros x U Hlk; inversion Hlk; subst; cbn; eapply wf_sub_eq_apply_mod; eassumption.
Qed.

Corollary wf_sub_eq_id_extend_def : forall Θ Ξ Γ A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id,,M ≈ Id,,M' : Γ ▸ A ≔ M.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  apply (wf_sub_eq_extend_def Θ Ξ Γ Γ sb_id sb_id A M M M' i);
    rewrite ?exp_sub_id; mauto 3.
Qed.

Lemma wf_sub_eq_wk : forall Θ Ξ Γ Γ' Δ σ σ' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ʷ φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ (sb_wk σ φ) ≈ (sb_wk σ' φ) : Δ.
Proof.
  intros * H ?; saturate_wk; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A ?; reduce_index; rewrite <- exp_wk_sub, <- !sentry_exp_wk; fold (exp_sub (a_var x) σ) (exp_sub (a_var x) σ').
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
  - intros x U Hl; cbn [sb_wk]; rewrite !sentry_modexp_wk.
    eapply wk_preserves_modexp; [ eapply wf_sub_eq_apply_mod; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_extend wf_sub_eq_id_extend wf_sub_eq_extend_def wf_sub_eq_id_extend_def
             wf_sub_eq_wk : mctt.

(** Extending equivalent substitutions into a module slot, each by the literal
    of its own transported unit, the two transported units being equal. *)
Lemma wf_sub_eq_extend_mod : forall Θ Ξ Γ Δ σ σ' U,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ']ᵘ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ,,ₘ me_lit U[σ]ᵘ ≈ σ' ,,ₘ me_lit U[σ']ᵘ : Δ ▹ₘ U.
Proof.
  intros * H ? HUσ; saturate_sub_eq.
  econstructor; [ apply wf_sub_extend_mod; eauto using sub_preserves_unit
                | apply wf_sub_extend_mod; eauto using sub_preserves_unit | |].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend; eapply wf_sub_eq_apply; eassumption.
  - intros x U0 Hlk; inversion Hlk; subst; cbn; [ apply wf_me_lit; exact HUσ | eapply wf_sub_eq_apply_mod; eassumption ].
Qed.

(** Two sides reduced to equal terms, at types that are equal. *)
Lemma wf_exp_eq_meet : forall Θ Ξ Γ L N N' L' T T' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ L ≈ N : T ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T ->
    Θ ⍮ Ξ ⍮ Γ ⊢ L' ≈ N' : T' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ T' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ L ≈ L' : T.
Proof.
  intros.
  eapply wf_exp_eq_trans; [ eassumption |].
  eapply wf_exp_eq_trans; [ eassumption |].
  eapply wf_exp_eq_sym, wf_exp_eq_subtyp'; [ eassumption |].
  eapply wf_subtyp_refl; [ eassumption | eapply wf_exp_eq_sym; eassumption ].
Qed.

(** ** Equivalent Substitutions Preserve Typing

    This is about typing derivations only, so it is a plain induction on
    [wf_exp]: the subtyping premise of [wf_exp_subtyp] is discharged by
    [sub_preserves_subtyp] rather than by an induction hypothesis.  Because
    [wf_exp_eq_elim_cong] lets the motive vary, the presupposition lemma
    needs to move a type along an equivalence of substitutions, that is, it
    needs this lemma.  Its counterparts for equality and
    subtyping ([sub_eq_preserves_exp_eq], [sub_eq_preserves_subtyp]) in turn
    need presupposition for the symmetry case, and so come after it, in
    [Core.Syntactic.SubEq]. *)

Ltac lift_sub_eq_False :=
  match goal with
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Δ) (a_typ _) _, Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ' |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass a_False) Γ ⊢ˢ sb_q σ ≈ sb_q σ' : cons (ce_ass a_False) Δ) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_eq_q_False; exact Hσ)
  end.

Ltac lift_sub_eq_step :=
  match goal with
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    IH : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_sub A σ)) Γ ⊢ˢ sb_q σ ≈ sb_q σ' : cons (ce_ass A) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_eq_q; [ exact Hσ | | exact (IH _ _ _ Hσ) ]; mauto 2)
  (** A domain in a small universe, at a level it is given to be one: both are
      moved into the least large universe. *)
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    HL : wf_exp ?Θ ?Ξ ?Δ (a_level ?n) ?L,
    HA : wf_exp ?Θ ?Ξ ?Δ (a_univ ?L) ?A,
    IH : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_univ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_ass (exp_sub A σ)) Γ ⊢ˢ sb_q σ ≈ sb_q σ' : cons (ce_ass A) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply (wf_sub_eq_q _ _ _ _ _ _ _ 0);
                   [ exact Hσ | exact (wf_exp_suniv_large HL HA)
                   | eapply wf_exp_eq_suniv_large; [| exact (IH _ _ _ Hσ) ];
                     let HLs := fresh "HLs" in
                     pose proof (sub_preserves_exp _ _ _ _ _ _ _ HL (wf_sub_eq_left _ _ _ _ _ _ Hσ)) as HLs;
                     exact HLs ])
  end.

Ltac lift_sub_eq_def :=
  match goal with
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    _ : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ (cons (ce_def ?A ?M) ?Δ) _ _ -> _,
    IHA : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _) _,
    IHM : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (exp_sub ?A _) (exp_sub ?M _) _ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ cons (ce_def (exp_sub A σ) (exp_sub M σ)) Γ ⊢ˢ sb_q σ ≈ sb_q σ' : cons (ce_def A M) Δ) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_eq_q_def; [ exact Hσ | | | exact (IHA _ _ _ Hσ) | exact (IHM _ _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub_eq := repeat first [ lift_sub_eq_False | lift_sub_eq_step | lift_sub_eq_def ].

(** [saturate_sub_typ] and [saturate_sub_eq_IH] are the counterparts of
    [push_sub]/[lift_sub] for the equivalence induction: the first transports
    every type premise along every substitution in context, the second
    instantiates every induction hypothesis at every substitution equivalence in
    context.  Together they leave all the premises of the congruence rule
    literally in the context, so that the search never has to guess a domain
    type through an evar. *)

Ltac saturate_sub_typ :=
  repeat match goal with
  | H : wf_exp ?Θ ?Ξ ?Δ (a_typ ?i) ?A, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ : a_typ i) in
      assert_fails (assert T by assumption);
      assert T by (eapply sub_preserves_typ; eassumption)
  | H : wf_exp ?Θ ?Ξ ?Δ (a_univ ?i) ?A, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ : a_univ i) in
      assert_fails (assert T by assumption);
      assert T by (eapply sub_preserves_styp; eassumption)
  end.

Ltac saturate_sub_eq_IH :=
  repeat match goal with
  | IH : forall _ _ _, wf_sub_eq _ _ _ ?Δ _ _ -> _, Hσ : wf_sub_eq _ _ _ ?Δ _ _ |- _ =>
      let T := type of (IH _ _ _ Hσ) in
      assert_fails (assert T by assumption);
      pose proof (IH _ _ _ Hσ)
  end.

(** The head of an equation of telescopes of assumptions. *)
Lemma ext_eq_ass_inv : forall Θ Ξ Γ Ψ Ψ' A A', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' /\ Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i /\
      Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i.
Proof. intros * H; inversion H; subst; eexists; eauto. Qed.

(** An annotated motive context [T ▹ Z] equal to [T' ▹ Z'] and to the
    motive's context [T ▹ H]: [T ▹ Z'] is equal to the motive's context
    too. *)
Lemma ann_ctx_trans : forall Θ Ξ Δ T T' Z Z' H,
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ T ▹ Z ≈ T' ▹ Z' -> Θ ⍮ Ξ ⍮ Δ ⊢ˣ T ▹ Z ≈ T ▹ H -> tele_ass T ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˣ T ▹ Z' ≈ T ▹ H.
Proof.
  intros * Ha Hb HT.
  destruct (ext_eq_ass_inv _ _ _ _ _ _ _ Ha) as (i & HTT' & HZ & HZZ' & HZ').
  destruct (ext_eq_ass_inv _ _ _ _ _ _ _ Hb) as (j & HTT & _ & HZH & HH).
  pose proof (ctxsub_exp _ _ _ _ _ _ (ctxsub_ext_rev _ _ _ _ _ HTT' HT) HZ') as HZ'l.
  eapply wf_ext_eq_ass with (i := max i j);
    [ exact HTT | eapply lift_exp_max_left; exact HZ'l
    | eapply wf_exp_eq_trans; [ eapply wf_exp_eq_sym, lift_exp_eq_max_left; exact HZZ' | eapply lift_exp_eq_max_right; exact HZH ]
    | eapply lift_exp_max_right; exact HH ].
Qed.

(** The eliminator: the scrutinee, the motives, the annotations and the
    branches move under the equivalent substitutions lifted over their
    contexts, which the induction hypotheses of the telescope premises
    give; the annotations of the second side by the equations of the
    annotated contexts. *)
Lemma sub_eq_elim_case : forall Θ Ξ Γ Δ σ σ' p D oq Us m Mm Bks bm Ps M i,
    ind_lookup Θ Ξ p = Some D ->
    elim_grp D oq p m ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = List.length (ind_members D) ->
    List.length Ps = im_np D Mm ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[τ] ≈ P[τ'] : T[τ]) ->
    (forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ M[τ] ≈ M[τ'] : (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[τ]) ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : Γ ->
       (tele_ass (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) ->
         Θ ⍮ Ξ ⍮ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z)) τ
            ≈ sb_qn (List.length (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z)) τ'
           : (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) τ
           ≈ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) τ') /\
       (tele_ass (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ'
           : elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ
           ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ')) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[τ] ≈ (eb_motive b)[τ'] : Typeω@i[τ]) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : Γ ->
       (tele_ass (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ'
           : elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ
           ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ') /\
       (tele_ass (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) τ'
           : elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ
           ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) τ')) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : Γ ->
       (tele_ass (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) τ'
           : elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ
           ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ') /\
       (tele_ass (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢ˢ sb_qn (List.length (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) τ'
           : elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ /\
         Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ
           ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) τ')) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢ˢ τ ≈ τ' : elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ B[τ] ≈ B[τ'] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[τ]) ->
    Θ ⍮ Ξ ⍮ Δ ⊢ˢ σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim oq Us m Bks M)[σ] ≈ (a_elim oq Us m Bks M)[σ']
      : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[σ].
Proof.
  intros * Hl Hg HMm Hbm HlB HlP HPs IHPs IHM Hann Hnm HZ IHZ HA IHA HΨ IHΨ Hn HΨB IHΨB Hk HB IHB Hσ.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hs; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hs'.
  assert (HD : decl_closed D) by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hs) | exact Hl ]).
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
  (* the premises at one substitution *)
  assert (HPs1 : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ P[σ0] : T[σ0])
    by (intros; eapply sub_preserves_exp; eauto).
  assert (HZ1 : forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z) σ0
                          ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (HA1 : forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ (eb_motive b)[σ0] : Typeω@i[σ0])
    by (intros; eapply sub_preserves_exp; eauto).
  assert (HΨ1 : forall k Mk, ind_member D k = Some Mk -> forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0
                          ≈ tele_sub (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (HΨB1 : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 Γ ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ˣ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0
                          ≈ tele_sub (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) σ0)
    by (intros; eapply sub_preserves_ext; eauto).
  assert (HB1 : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
             ind_con Mk c = Some gs -> List.In (c, n, B) (eb_brs b) ->
             forall Δ0 σ0, sub_as_sub Θ Ξ Δ0 σ0 (elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) ->
             Θ ⍮ Ξ ⍮ Δ0 ⊢ B[σ0] : (elim_bty p k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[σ0])
    by (intros; eapply sub_preserves_exp; eauto).
  pose proof (sub_as_sub_dom Θ Ξ) as Rd; pose proof (sub_as_sub_ext Θ Ξ) as Re.
  rewrite !exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
  eapply wf_exp_eq_elim_cong;
    [ exact Hl | exact Hg | exact Hg | exact HMm | rewrite nth_error_blocks_sub, Hbm; reflexivity
    | rewrite length_blocks_sub; exact HlB | rewrite length_blocks_sub; exact HlB | rewrite List.length_map; exact HlP | .. ].
  - eapply mv_elim_params with (R := sub_as_sub Θ Ξ); eassumption.
  - rewrite List.length_map; exact HlP.
  - intros j0 P0 P0' T0 HP HP' HT; erewrite <- params_insts_sub in HT by eassumption.
    apply nth_error_map_inv in HP as (P & HP & ->); apply nth_error_map_inv in HP' as (P2 & HP' & ->).
    rewrite HP in HP'; injection HP' as <-; apply nth_error_map_inv in HT as (T & HT & ->).
    exact (IHPs _ _ _ HP HT _ _ _ Hσ).
  - rewrite <- ind_mty_split_sub by (try assumption; unfold im_np in HlP; lia); exact (IHM _ _ _ Hσ).
  - apply mv_elim_ups; exact Hann.
  - apply mv_elim_ups; exact Hann.
  - apply blocks_nm_ok_sub; exact Hnm.
  - apply blocks_nm_ok_sub; exact Hnm.
  - rewrite List.firstn_map; eapply mv_blocks_ann with (R := sub_as_sub Θ Ξ); eassumption.
  - (* the annotations at the second substitution, at the parameters at the
       first: equal to those at the first *)
    intros k Mk b Z HMk Hb HZb.
    rewrite nth_error_blocks_sub in Hb; destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb; [| discriminate ].
    injection Hb as <-; destruct b0 as [nm oZ A0 Bs0]; cbn in HZb; destruct oZ as [Z0 |]; [| discriminate ].
    injection HZb as <-.
    pose proof (Hnm _ _ _ HMk Hb0) as Enm; cbn in Enm; subst nm.
    replace (S (im_nn Mk) - 1) with (im_nn Mk) by lia.
    assert (Hlft : Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.map (fun U => U[σ]) (List.firstn (ind_nu D) Ps)))
                                  ▹ Z0[sb_qn (im_nn Mk) σ]
                                ≈ elim_mctx p D k Mk (List.map (fun U => U[σ]) (List.firstn (ind_nu D) Ps))).
    { eapply mv_blocks_ann with (R := sub_as_sub Θ Ξ) (k := k) (b := eblock_sub (eb_mk (S (im_nn Mk)) (Some Z0) A0 Bs0) σ);
        first [ eassumption | rewrite nth_error_blocks_sub, Hb0; reflexivity | cbn [eblock_sub eb_ann option_map]; replace (S (im_nn Mk) - 1) with (im_nn Mk) by lia; reflexivity ]. }
    assert (HtZ : tele_ass (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z0))
      by (constructor; [ eauto | apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption ]).
    destruct (proj1 (IHZ _ _ _ _ HMk Hb0 eq_refl _ _ _ Hσ) HtZ) as [_ HZσ].
    cbn [tele_sub centry_sub] in HZσ; rewrite length_tele_sub in HZσ; fold (im_nn Mk) in HZσ.
    erewrite !nparams_sub in HZσ by eassumption.
    rewrite List.firstn_map; unfold elim_mctx in Hlft |- *; eapply ann_ctx_trans; [ exact HZσ | exact Hlft |].
    apply tele_ass_sub; eapply decl_closed_nparams_ass; eassumption.
  - rewrite List.firstn_map; eapply mv_blocks_motive with (R := sub_as_sub Θ Ξ); eassumption.
  - (* the motives at the two substitutions *)
    intros k Mk b b' HMk Hb Hb'.
    rewrite !nth_error_blocks_sub in Hb, Hb'; destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb, Hb'; [| discriminate ].
    injection Hb as <-; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb0) as Enm; destruct b0 as [nm oZ A0 Bs0]; cbn in Enm |- *; subst nm.
    destruct (proj1 (IHΨ _ _ HMk _ _ _ Hσ) (elim_mctx_ass _ _ _ _ _ HD HMk)) as [Hlift _].
    rewrite length_elim_mctx in Hlift; erewrite elim_mctx_sub in Hlift by eassumption.
    rewrite List.firstn_map; exact (IHA _ _ _ HMk Hb0 _ _ _ Hlift).
  - intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption; exact (HΨ1 _ _ HMk _ _ Hs).
  - apply mv_blocks_names; exact Hn.
  - intros k b b' Hb Hb'; rewrite !nth_error_blocks_sub in Hb, Hb'.
    destruct (List.nth_error Bks k) as [[nm oZ A0 Bs0] |]; cbn in Hb, Hb'; [| discriminate ].
    injection Hb as <-; injection Hb' as <-; cbn; unfold brs_sub; rewrite !brs_fst_map; reflexivity.
  - rewrite List.firstn_map; eapply mv_blocks_bctx with (R := sub_as_sub Θ Ξ); eassumption.
  - apply mv_blocks_counts; exact Hk.
  - (* the branches at the two substitutions *)
    intros k Mk b b' i0 c gs n B1 B2 HMk Hb Hb' Hi Hi' Hc.
    rewrite !nth_error_blocks_sub in Hb, Hb'; destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb, Hb'; [| discriminate ].
    injection Hb as <-; injection Hb' as <-.
    pose proof (Hnm _ _ _ HMk Hb0) as Enm; destruct b0 as [nm oZ A0 Bs0]; cbn in Enm, Hi, Hi' |- *; subst nm.
    unfold brs_sub in Hi, Hi'.
    apply nth_error_map_inv in Hi as ([[c1 n1] B] & Hi & Heq1); cbn in Heq1; injection Heq1 as -> -> ->.
    apply nth_error_map_inv in Hi' as ([[c2 n2] B'] & Hi' & Heq2); cbn in Heq2; injection Heq2 as -> -> ->.
    rewrite Hi in Hi'; injection Hi' as <-.
    pose proof (List.nth_error_In _ _ Hi) as Hin; cbn [eb_brs] in Hin.
    pose proof (Hk _ _ _ _ _ _ _ HMk Hb0 Hc Hin) as En; cbn in En; subst n2.
    destruct (proj1 (IHΨB _ _ _ _ HMk Hc _ _ _ Hσ) (elim_bctx_ass _ _ _ _ _ _ _ HD HMk)) as [Hlift _].
    rewrite length_elim_bctx in Hlift.
    erewrite elim_bctx_sub in Hlift;
      [| eassumption | eassumption | apply cons_lookup_in; eassumption | eassumption | intros j0 Mj HMj; eapply blocks_motives_sub; eassumption ].
    rewrite List.firstn_map; erewrite <- elim_bty_sub by eassumption.
    replace (im_nn Mk + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + im_nn Mk) by lia.
    exact (IHB _ _ _ _ _ _ _ HMk Hb0 Hc Hin _ _ _ Hlift).
Qed.

(** ** The Module Cases of [sub_eq_preserves_mut]

    Equivalent substitutions move each side of a judgment about units or
    module expressions to an equal one.  A body unit's entries are compared
    with the entries before them filled in, in its parameters' context, so
    they are moved only under the lifting over the parameters, which are
    assumptions. *)

(** The entry of a body of the same shape named as one of the other's. *)
Lemma shape_prefix : forall Φ Φ' y Φ0 E, body_shape Φ Φ' -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
    exists Φ0' E', gm_prefix_upto Φ' y = Some (gm_ext Φ0' y E') /\ body_shape Φ0 Φ0' /\ entry_shape E E'.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros [| Φ' x' E0' | Φ' H' its'] * Hs Hp; cbn in Hs, Hp |- *; try contradiction; try discriminate.
  - destruct Hs as (Hs & <- & HE).
    destruct (String.eqb y x); [ injection Hp as ? ? ?; subst; do 2 eexists; split; [ reflexivity | split; assumption ] |].
    exact (IH _ _ _ _ Hs Hp).
  - destruct Hs as (Hs & <-); destruct (List.existsb _ _); [ discriminate | exact (IH _ _ _ _ Hs Hp) ].
Qed.

Lemma fill_prefix : forall Φ y Φ0 E, gm_fill Φ <> None -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
    exists σ, gm_fill Φ0 = Some σ.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hf Hp; cbn in Hf, Hp; try discriminate.
  - assert (Hf0 : gm_fill Φ <> None)
      by (destruct E0 as [? ? ? [] | | | ]; try contradiction; destruct (gm_fill Φ); cbn in Hf; congruence).
    destruct (String.eqb y x); [ injection Hp as ? ? ?; subst; destruct (gm_fill Φ0) eqn:Ef; [ eauto | contradiction ] |].
    exact (IH _ _ _ Hf0 Hp).
  - contradiction.
Qed.

Lemma body_shape_dropn : forall n Φ Φ', body_shape Φ Φ' -> body_shape (gm_dropn n Φ) (gm_dropn n Φ').
Proof.
  induction n as [| n IH]; intros [| Φ x E | Φ H its] [| Φ' x' E' | Φ' H' its'] Hs; cbn in Hs |- *; try contradiction; auto.
  apply IH, Hs.
Qed.

(** The opens of two bodies of the same shape, with expansions of the same
    shape, are paired: the expanded prefixes before them have the same shape. *)
Lemma body_opens_at_pair : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall Γ' Φ' Φx' k Φ0 H, body_xp Θ Ξ Γ' Φ' Φx' -> body_shape Φ Φ' -> body_shape Φx Φx' ->
    List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
    exists Φ0' H', List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') /\ body_shape Φ0 Φ0' /\ gm_nopens Φ0 = 0.
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H0 its R T gs Hx IH _ _ Hg]; intros * Hx' Hs Hsx Hk.
  - destruct k; discriminate.
  - destruct Φ' as [| Φ1 x1 E1 | Φ1 Hm1 its1]; cbn in Hs; try contradiction; destruct Hs as (Hs & _ & _).
    inversion Hx'; subst; cbn [body_opens_at gm_dropn] in Hk |- *.
    cbn in Hsx; destruct Hsx as (Hsx & _ & _); eauto.
  - destruct Φ' as [| Φ1 x1 E1 | Φ1 Hm1 its1]; cbn in Hs; try contradiction; destruct Hs as (Hs & <-).
    inversion Hx'; subst.
    rewrite (body_opens_at_open _ _ _ _ _ _ _ _ _ Hg) in Hk.
    match goal with Hg' : items_gen _ _ _ _ _ its ?gs' |- _ =>
      rewrite (body_opens_at_open _ _ _ _ _ _ _ _ _ Hg');
      assert (Hl : List.length gs = List.length gs')
        by (rewrite (items_gen_length _ _ _ _ _ _ _ Hg), (items_gen_length _ _ _ _ _ _ _ Hg'); reflexivity);
      pose proof (body_shape_dropn (List.length gs) _ _ Hsx) as Hsx0;
      rewrite gm_dropn_gens_append in Hsx0; rewrite Hl, gm_dropn_gens_append in Hsx0 end.
    destruct k as [| k]; cbn in Hk |- *; [| eauto ].
    injection Hk as <- <-; do 2 eexists; split; [ reflexivity | split; [ exact Hsx0 | eapply body_xp_nopens; exact Hx ] ].
Qed.

Lemma sub_eq_ext_ass_diag : forall Θ Ξ Δ Ψ A i Γ0 σ σ',
    Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ0 ⊢ˢ sb_qn (length Ψ) σ ≈ sb_qn (length Ψ) σ' : Ψ ++ Δ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ σ' ->
    ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Δ ->
    Θ ⍮ Ξ ⍮ Ψ ++ Δ ⊢ A : Typeω@i ->
    (forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Ψ ++ Δ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ A[τ] ≈ A[τ'] : Typeω@i[τ]) ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ tele_sub (Ψ ▹ A) σ ++ Γ0 ⊢ˢ sb_qn (length (Ψ ▹ A)) σ ≈ sb_qn (length (Ψ ▹ A)) σ' : Ψ ▹ A ++ Δ /\
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˣ tele_sub (Ψ ▹ A) σ ≈ tele_sub (Ψ ▹ A) σ'.
Proof.
  intros * Hl HE HΨ HA IHA Hσ.
  split.
  - cbn [tele_sub List.length sb_qn List.app]; eapply wf_sub_eq_q; [ exact Hl | exact HA | exact (IHA _ _ _ Hl) ].
  - cbn [tele_sub List.length].
    assert (Hr : Θ ⍮ Ξ ⍮ tele_sub Ψ σ' ++ Γ0 ⊢ˢ sb_qn (length Ψ) σ' : Ψ ++ Δ)
      by (apply wf_sub_ext; [ exact (wf_sub_eq_right _ _ _ _ _ _ Hσ) | exact (ext_eq_ctx_right _ _ _ _ _ HE) | exact HΨ ]).
    eapply wf_ext_eq_ass.
    + exact HE.
    + exact (sub_preserves_typ _ _ _ _ _ _ _ HA (wf_sub_eq_left _ _ _ _ _ _ Hl)).
    + exact (IHA _ _ _ Hl).
    + exact (sub_preserves_typ _ _ _ _ _ _ _ HA Hr).
Qed.

(** One side of a body unit, moved by two equivalent substitutions. *)
Lemma sub_eq_unit_self : forall Θ Ξ Γ Δu Φ Φx lv Γ0 σ σ',
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Γ0 ⊢ˢ sb_qn (length Δu) σ ≈ sb_qn (length Δu) σ' : Δu ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˣ tele_sub Δu σ ≈ tele_sub Δu σ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δu ≈ body_ctx Φx ++ Δu ->
    (forall y Φ0 b pv A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σf ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ A[σf] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σf ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ A[σf][τ] ≈ A[σf][τ'] : Typeω@(lv y)[τ]) ->
    (forall y Φ0 b pv A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σf ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ M[σf] : A[σf]) ->
    (forall y Φ0 b pv A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) -> gm_fill Φ0 = Some σf ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ M[σf][τ] ≈ M[σf][τ'] : A[σf][τ]) ->
    (forall y Φ0 pv U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) -> gm_fill Φ0 = Some σf ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵘ U[σf]ᵘ ≈ U[σf]ᵘ) ->
    (forall y Φ0 pv U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) -> gm_fill Φ0 = Some σf ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U[σf]ᵘ[τ]ᵘ ≈ U[σf]ᵘ[τ']ᵘ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δu ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H[σf]ᵐ[τ]ᵐ ≈ H[σf]ᵐ[τ']ᵐ) ->
    tele_ass Δu -> body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu Φ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_open Δu Φ)[σ]ᵘ ≈ (gu_open Δu Φ)[σ']ᵘ.
Proof.
  intros * Hb Hσ L HΔσ Hx HA IHA HM IHM HU IHU Ho IHo Ha Hs Hsx Hn HU0.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hs0; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hs1.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eapply ext_eq_ctx_left; exact Hx).
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU0) as (HΓs & HUs & _).
  rewrite gunit_scoped_mk in HUs; destruct HUs as [HΔs [_ HΦs]].
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ Hx Hs0) as Hxσ.
  pose proof (sub_preserves_ext _ _ _ _ _ _ _ Hx Hs1) as Hxσ'.
  assert (HΔΓ : ⊢ Θ ⍮ Ξ ⍮ Δu ++ Γ) by (pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as HC; rewrite <- List.app_assoc in HC; eapply wf_ctx_app_tail; exact HC).
  assert (R : Θ ⍮ Ξ ⍮ tele_sub Δu σ' ++ Γ0 ⊢ˢ sb_qn (length Δu) σ' : Δu ++ Γ)
    by (apply wf_sub_ext; [ exact Hs1 | exact (ext_eq_ctx_right _ _ _ _ _ HΔσ) | exact HΔΓ ]).
  (* both prefixes of a self-pair are the same *)
  assert (Hsame : forall y X X', gm_prefix_upto Φx y = Some X -> gm_prefix_upto Φx y = Some X' -> X = X')
    by (intros * E1 E2; rewrite E1 in E2; injection E2 as ->; reflexivity).
  eapply (unit_body_moved Θ Ξ Γ Δu Δu Φ Φ Φx Φx lv Γ0 σ σ');
    [ | | exact HΔσ | exact Hxσ | exact Hxσ' | | | | | | | | | exact Hb | exact Hb | exact Ha | exact Ha
    | reflexivity | exact Hs | exact Hsx | exact Hn ].
  - eapply body_xp_sub; [ exact Hc | exact Hb | apply ctx_scoped_app_iff; split; assumption | rewrite List.length_app; exact HΦs
                        | apply sub_mod_compat_ext; eauto using wf_sub_mod_compat ].
  - eapply body_xp_sub; [ exact Hc | exact Hb | apply ctx_scoped_app_iff; split; assumption | rewrite List.length_app; exact HΦs
                        | apply sub_mod_compat_ext; eauto using wf_sub_mod_compat ].
  - intros * Hp Hp' Hf0 Hf0'.
    pose proof (Hsame _ _ _ Hp Hp') as E; injection E as <- -> -> -> ->; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    pose proof (IHA _ _ _ _ _ _ _ Hp Hf0 _ _ _ L) as HAσ; cbn in HAσ.
    pose proof (sub_preserves_typ _ _ _ _ _ _ _ (HA _ _ _ _ _ _ _ Hp Hf0) (wf_sub_eq_left _ _ _ _ _ _ L)) as HAl.
    split; [ exact HAl | split; [ exact HAσ | split ] ].
    + exact (sub_preserves_exp _ _ _ _ _ _ _ (HM _ _ _ _ _ _ _ Hp Hf0) (wf_sub_eq_left _ _ _ _ _ _ L)).
    + exact (IHM _ _ _ _ _ _ _ Hp Hf0 _ _ _ L).
  - intros * Hp Hp' Hf0 Hf0'.
    pose proof (Hsame _ _ _ Hp Hp') as E; injection E as <- -> ->; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (IHU _ _ _ _ _ Hp Hf0 _ _ _ L).
  - intros * Hp Hp' Hf0 Hf0'.
    pose proof (Hsame _ _ _ Hp Hp') as E; injection E as <- -> -> -> ->; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    split; [ exact (sub_preserves_typ _ _ _ _ _ _ _ (HA _ _ _ _ _ _ _ Hp Hf0) R)
           | exact (sub_preserves_exp _ _ _ _ _ _ _ (HM _ _ _ _ _ _ _ Hp Hf0) R) ].
  - intros * Hp Hp' Hf0 Hf0'.
    pose proof (Hsame _ _ _ Hp Hp') as E; injection E as <- -> ->; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (sub_preserves_unit _ _ _ _ _ _ _ (HU _ _ _ _ _ Hp Hf0) R).
  - intros k Ψ H Ek.
    destruct (body_opens_prefix _ _ _ _ _ Hb _ _ _ Ek) as [Ψr HΨr].
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) σ ++ Γ0).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxσ) as HC; rewrite HΨr, <- List.app_assoc, tele_sub_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_sub_ext _ _ (Ψ ++ Δu) _ _ _ Hs0 HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho _ _ _ Ek)))) as Hσe.
    rewrite <- List.app_assoc in Hσe; exact (sub_preserves_modexp _ _ _ _ _ _ _ (Ho _ _ _ Ek) Hσe).
  - intros k Ψ H Ek.
    destruct (body_opens_prefix _ _ _ _ _ Hb _ _ _ Ek) as [Ψr HΨr].
    assert (HΔ0 : ⊢ Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) σ' ++ Γ0).
    { pose proof (ext_eq_ctx_left _ _ _ _ _ Hxσ') as HC; rewrite HΨr, <- List.app_assoc, tele_sub_app, <- List.app_assoc in HC.
      eapply wf_ctx_app_tail; exact HC. }
    pose proof (wf_sub_ext _ _ (Ψ ++ Δu) _ _ _ Hs1 HΔ0 ltac:(rewrite <- List.app_assoc; exact (presup_modexp_eq_ctx (Ho _ _ _ Ek)))) as Hσe.
    rewrite <- List.app_assoc in Hσe; exact (sub_preserves_modexp _ _ _ _ _ _ _ (Ho _ _ _ Ek) Hσe).
  - intros k Φ0 H Φ0' H' σf σf' Ek Ek' Hf0 Hf0'.
    rewrite Ek in Ek'; injection Ek' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (IHo _ _ _ _ Ek Hf0 _ _ _ L).
  - intros k Φ0 H Φ0' H' σf σf' Ek Ek' Hf0 Hf0'.
    rewrite Ek in Ek'; injection Ek' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    pose proof (Ho _ _ _ (body_opens_at_nth _ _ _ _ _ Ek)) as HH0.
    pose proof (sub_preserves_modexp _ _ _ _ _ _ _ HH0 (wf_gm_fill _ _ _ _ _ (presup_modexp_eq_ctx HH0) Hf0)) as HH1.
    exact (sub_preserves_modexp _ _ _ _ _ _ _ HH1 R).
Qed.

Lemma sub_eq_unit_alias_self : forall Θ Ξ Γ Δu E Γ0 σ σ',
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ tele_sub Δu σ ++ Γ0 ⊢ˢ sb_qn (length Δu) σ ≈ sb_qn (length Δu) σ' : Δu ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˣ tele_sub Δu σ ≈ tele_sub Δu σ' ->
    tele_ass Δu ->
    Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵐ E ≈ E ->
    (forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ E[τ]ᵐ ≈ E[τ']ᵐ) ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_mk Δu (md_alias E))[σ]ᵘ ≈ (gu_mk Δu (md_alias E))[σ']ᵘ.
Proof.
  intros * Hσ L HΔσ Ha HE IHE.
  rewrite !gunit_sub_mk; cbn [moddef_sub].
  eapply wf_unit_eq_alias; [ exact HΔσ | apply tele_ass_sub; exact Ha | apply tele_ass_sub; exact Ha | exact (IHE _ _ _ L) |].
  eapply sub_preserves_modexp; [ exact HE |].
  apply wf_sub_ext; [ exact (wf_sub_eq_right _ _ _ _ _ _ Hσ) | exact (ext_eq_ctx_right _ _ _ _ _ HΔσ) | exact (presup_modexp_eq_ctx HE) ].
Qed.

(** Both sides of a flattened alias of a literal: the alias by congruence,
    the merged literal through the alias by flattening on either side. *)
Lemma sub_eq_unit_flatten_case : forall Θ Ξ Γ Δ Δ' D Γ0 σ σ',
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ0 ⊢ˢ sb_qn (length Δ) σ ≈ sb_qn (length Δ) σ' : Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˣ tele_sub Δ σ ≈ tele_sub Δ σ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ ->
    tele_ass Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
    (forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δ ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ (gu_mk Δ' D)[τ]ᵘ ≈ (gu_mk Δ' D)[τ']ᵘ) ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[σ]ᵘ ≈ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[σ']ᵘ /\
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_mk (Δ' ++ Δ) D)[σ]ᵘ ≈ (gu_mk (Δ' ++ Δ) D)[σ']ᵘ.
Proof.
  intros * Hσ L HΔσ HΔ Ha HU IHU.
  assert (HL : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[σ]ᵘ ≈ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[σ']ᵘ).
  { eapply sub_eq_unit_alias_self; [ exact Hσ | exact L | exact HΔσ | exact Ha | apply wf_me_lit; exact HU |].
    intros * Hτ; cbn [modexp_sub]; apply wf_me_lit, IHU; exact Hτ. }
  split; [ exact HL |].
  assert (Hflat : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ s : Γ ->
             Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[s]ᵘ ≈ (gu_mk (Δ' ++ Δ) D)[s]ᵘ).
  { intros s Hs.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HΔ Hs) as HΔs.
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs (ext_eq_ctx_left _ _ _ _ _ HΔs) (presup_unit_eq_ctx HU)) as Hq.
    pose proof (sub_preserves_unit _ _ _ _ _ _ _ HU Hq) as HUs.
    change (gu_mk (Δ' ++ Δ) D) with (gunit_abs Δ (gu_mk Δ' D)); rewrite gunit_abs_sub, gunit_sub_mk; cbn [moddef_sub modexp_sub].
    revert HUs; destruct ((gu_mk Δ' D)[sb_qn (length Δ) s]ᵘ) as [Δw Dw]; intros HUs; cbn [gunit_abs].
    eapply wf_unit_eq_flatten; [ exact HΔs | apply tele_ass_sub; exact Ha | exact HUs ]. }
  eapply wf_unit_eq_trans; [ apply wf_unit_eq_sym, Hflat, (wf_sub_eq_left _ _ _ _ _ _ Hσ) |].
  eapply wf_unit_eq_trans; [ exact HL | apply Hflat, (wf_sub_eq_right _ _ _ _ _ _ Hσ) ].
Qed.

(** Both sides of a body unit, from the rule's premises. *)
Lemma sub_eq_unit_body_case : forall Θ Ξ Γ Δu Δu' Φ Φ' Φx Φx' lv Γ0 σ σ',
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx ->
    body_xp Θ Ξ (Δu' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δu ≈ Δu' ->
    (forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Γ ->
       (tele_ass Δu -> Θ ⍮ Ξ ⍮ tele_sub Δu τ ++ Γ1 ⊢ˢ sb_qn (length Δu) τ ≈ sb_qn (length Δu) τ' : Δu ++ Γ /\
                        Θ ⍮ Ξ ⍮ Γ1 ⊢ˣ tele_sub Δu τ ≈ tele_sub Δu τ') /\
       (tele_ass Δu' -> Θ ⍮ Ξ ⍮ tele_sub Δu' τ ++ Γ1 ⊢ˢ sb_qn (length Δu') τ ≈ sb_qn (length Δu') τ' : Δu' ++ Γ /\
                        Θ ⍮ Ξ ⍮ Γ1 ⊢ˣ tele_sub Δu' τ ≈ tele_sub Δu' τ')) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δu ≈ body_ctx Φx ++ Δu ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δu' ≈ body_ctx Φx' ++ Δu' ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ A[σf] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ A[σf][τ] ≈ A[σf][τ'] : Typeω@(lv y)[τ]) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ A[σf] ≈ A'[σf'] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ M[σf] : A[σf]) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ M[σf][τ] ≈ M[σf][τ'] : A[σf][τ]) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ M[σf] ≈ M'[σf'] : A[σf]) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵘ U[σf]ᵘ ≈ U'[σf']ᵘ) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ ->
          Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U[σf]ᵘ[τ]ᵘ ≈ U[σf]ᵘ[τ']ᵘ /\ Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U'[σf']ᵘ[τ]ᵘ ≈ U'[σf']ᵘ[τ']ᵘ) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu' ++ Γ ⊢ A'[σf'] : Typeω@(lv y)) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ A'[σf'][τ] ≈ A'[σf'][τ'] : Typeω@(lv y)[τ]) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu' ++ Γ ⊢ M'[σf'] : A'[σf']) ->
    (forall y Φ0 b pv A M Φ0' b' pv' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_def b pv A (Some M))) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_def b' pv' A' (Some M'))) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu' ++ Γ -> Θ ⍮ Ξ ⍮ Γ1 ⊢ M'[σf'][τ] ≈ M'[σf'][τ'] : A'[σf'][τ]) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu' ++ Γ ⊢ᵘ U'[σf']ᵘ ≈ U'[σf']ᵘ) ->
    (forall y Φ0 pv U Φ0' pv' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y (ge_mod pv' U')) ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu' ++ Γ ->
          Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U'[σf']ᵘ[τ]ᵘ ≈ U'[σf']ᵘ[τ']ᵘ /\ Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U'[σf']ᵘ[τ]ᵘ ≈ U'[σf']ᵘ[τ']ᵘ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δu ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Ψ' H', List.nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δu' ++ Γ ⊢ᵐ H' ≈ H') ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵐ H[σf]ᵐ ≈ H'[σf']ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu ++ Γ ->
          Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H[σf]ᵐ[τ]ᵐ ≈ H[σf]ᵐ[τ']ᵐ /\ Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H'[σf']ᵐ[τ]ᵐ ≈ H'[σf']ᵐ[τ']ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        Θ ⍮ Ξ ⍮ Δu' ++ Γ ⊢ᵐ H'[σf']ᵐ ≈ H'[σf']ᵐ) ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' ->
        forall Γ1 τ τ', Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ τ ≈ τ' : Δu' ++ Γ ->
          Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H'[σf']ᵐ[τ]ᵐ ≈ H'[σf']ᵐ[τ']ᵐ /\ Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H'[σf']ᵐ[τ]ᵐ ≈ H'[σf']ᵐ[τ']ᵐ) ->
    tele_ass Δu -> tele_ass Δu' -> length Δu = length Δu' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_open Δu Φ)[σ]ᵘ ≈ (gu_open Δu Φ)[σ']ᵘ /\
    Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ (gu_open Δu' Φ')[σ]ᵘ ≈ (gu_open Δu' Φ')[σ']ᵘ.
Proof.
  intros * Hb Hb' HΔ IHΔ Hx Hx' HA IHA HAA HM IHM HMM HU IHU HAr IHAr HMr IHMr HUr IHUr Ho Ho' HOO IHOO HOR IHOR
           Ha Ha' Hl Hs Hsx Hn Hσ.
  (* an open of one side has its counterpart on the other, filled in *)
  assert (Hopair : forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf ->
            exists Φ0' H' σf', List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') /\ gm_fill Φ0' = Some σf').
  { intros * Ek Hf0; destruct (body_opens_at_pair _ _ _ _ _ Hb _ _ _ _ _ _ Hb' Hs Hsx Ek) as (Φ0' & H' & Ek' & Hs0 & Hn0).
    destruct (body_shape_fill _ _ Hn0 Hs0) as [_ Hf0'].
    destruct (gm_fill Φ0') as [σf' |] eqn:E'; [ do 3 eexists; split; [ exact Ek' | exact E' ] | contradiction ]. }
  assert (Hopair' : forall k Φ0' H' σf', List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') -> gm_fill Φ0' = Some σf' ->
            exists Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) /\ gm_fill Φ0 = Some σf).
  { intros * Ek' Hf0'.
    destruct (body_opens_at_pair _ _ _ _ _ Hb' _ _ _ _ _ _ Hb (body_shape_sym _ _ Hs) (body_shape_sym _ _ Hsx) Ek')
      as (Φ0 & H & Ek & Hs0 & Hn0).
    destruct (body_shape_fill _ _ Hn0 Hs0) as [_ Hf0].
    destruct (gm_fill Φ0) as [σf |] eqn:E; [ do 3 eexists; split; [ exact Ek | exact E ] | contradiction ]. }
  destruct (body_shape_fill _ _ (body_xp_nopens _ _ _ _ _ Hb) Hsx) as [Hf Hf'].
  destruct (IHΔ _ _ _ Hσ) as [HL HR].
  destruct (HL Ha) as [L HΔσ]; destruct (HR Ha') as [L' HΔσ'].
  destruct (body_shape_refl _ _ Hsx) as (Hsx1 & Hsx2 & Hnx).
  pose proof (body_shape_of_xp _ _ _ _ _ Hb Hsx1) as Hs1.
  pose proof (body_shape_of_xp _ _ _ _ _ Hb' Hsx2) as Hs2.
  assert (Hnames : gm_names Φ = gm_names Φ')
    by (rewrite <- (body_xp_names _ _ _ _ _ Hb), <- (body_xp_names _ _ _ _ _ Hb'); exact Hnx).
  (* a definition or a module of one side has its counterpart on the other *)
  assert (Hpair : forall y Φ0 E, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) ->
            exists Φ0' E' σf', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') /\ entry_shape E E' /\ gm_fill Φ0' = Some σf').
  { intros * Hp; destruct (shape_prefix _ _ _ _ _ Hsx Hp) as (Φ0' & E' & Hp' & _ & HE).
    destruct (fill_prefix _ _ _ _ Hf' Hp') as (σf' & Hf0'); eauto 6. }
  assert (Hpair' : forall y Φ0' E', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') ->
            exists Φ0 E σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) /\ entry_shape E E' /\ gm_fill Φ0 = Some σf).
  { intros * Hp'; destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hsx) Hp') as (Φ0 & E & Hp & _ & HE).
    destruct (fill_prefix _ _ _ _ Hf Hp) as (σf & Hf0).
    destruct E' as [? ? ? [] | | | ], E as [? ? ? [] | | | ]; cbn in HE; try contradiction; do 3 eexists;
      (split; [ exact Hp | split; [| exact Hf0 ] ]); cbn; intuition. }
  assert (HU0 : Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu' Φ')
    by (eapply wf_unit_eq_body; eassumption).
  split.
  - eapply sub_eq_unit_self; [ exact Hb | exact Hσ | exact L | exact HΔσ | exact Hx | | | | | | | exact Ho |
                             | exact Ha | exact Hs1 | exact Hsx1 | exact Hn | eapply wf_unit_eq_trans; [ exact HU0 | apply wf_unit_eq_sym; exact HU0 ] ].
    7: intros k Φ0 H σf Ek Hf0; destruct (Hopair _ _ _ _ Ek Hf0) as (Φ0' & H' & σf' & Ek' & Hf0');
         intros; eapply proj1; eapply IHOO; eassumption.
    + intros y Φ0 b pv A M σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply HA; eassumption.
    + intros y Φ0 b pv A M σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply IHA; eassumption.
    + intros y Φ0 b pv A M σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply HM; eassumption.
    + intros y Φ0 b pv A M σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply IHM; eassumption.
    + intros y Φ0 pv U σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | ? ? | | ]; cbn in HE; try contradiction;
        eapply wf_unit_eq_trans; [ eapply HU; eassumption | apply wf_unit_eq_sym; eapply HU; eassumption ].
    + intros y Φ0 pv U σf Hp Hf0; destruct (Hpair _ _ _ Hp) as (Φ0' & E' & σf' & Hp' & HE & Hf0');
        destruct E' as [? ? ? [] | ? ? | | ]; cbn in HE; try contradiction; intros; eapply proj1; eapply IHU; eassumption.
  - eapply sub_eq_unit_self; [ exact Hb' | exact Hσ | exact L' | exact HΔσ' | exact Hx' | | | | | | | exact Ho' |
                             | exact Ha' | exact Hs2 | exact Hsx2 | rewrite <- Hnames; exact Hn
                             | eapply wf_unit_eq_trans; [ apply wf_unit_eq_sym; exact HU0 | exact HU0 ] ].
    7: intros k Φ0' H' σf' Ek' Hf0'; destruct (Hopair' _ _ _ _ Ek' Hf0') as (Φ0 & H & σf & Ek & Hf0);
         intros; eapply proj1; eapply IHOR; [ exact Ek | exact Ek' | exact Hf0 | exact Hf0' | eassumption ].
    + intros y Φ0' b' pv' A' M' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply HAr; eassumption.
    + intros y Φ0' b' pv' A' M' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply IHAr; eassumption.
    + intros y Φ0' b' pv' A' M' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply HMr; eassumption.
    + intros y Φ0' b' pv' A' M' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | | | ]; cbn in HE; try contradiction; eapply IHMr; eassumption.
    + intros y Φ0' pv' U' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | ? ? | | ]; cbn in HE; try contradiction; eapply HUr; eassumption.
    + intros y Φ0' pv' U' σf' Hp' Hf0'; destruct (Hpair' _ _ _ Hp') as (Φ0 & E & σf & Hp & HE & Hf0);
        destruct E as [? ? ? [] | ? ? | | ]; cbn in HE; try contradiction; intros; eapply proj1; eapply IHUr; eassumption.
Qed.

(** A literal given its outermost parameter, both sides moved. *)
Lemma lit_app_cong : forall Θ Ξ Γ Δ1 X1 D1 Δ2 X2 D2 N1 N2,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ1 ++ ce_ass X1 :: nil) D1 ≈ gu_mk (Δ2 ++ ce_ass X2 :: nil) D2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N1 : X1 -> Θ ⍮ Ξ ⍮ Γ ⊢ N1 ≈ N2 : X1 -> Θ ⍮ Ξ ⍮ Γ ⊢ N2 : X2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ1 ++ ce_ass X1 :: nil) D1)) N1 ≈ me_app (me_lit (gu_mk (Δ2 ++ ce_ass X2 :: nil) D2)) N2.
Proof.
  intros * HU HN1 HN HN2.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU))) as Hv.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HH.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HH) as (_ & (R1 & _ & HR1 & _) & (R2 & _ & HR2 & _)).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH Hv) as (_ & HK1 & HK2).
  assert (Ht : forall Δ X D R, mdenote Θ Ξ Γ (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) R -> desc_ok Θ Ξ Γ R ->
            exists T1, ds_mtele Θ Ξ R = Some (T1 ++ ce_ass X :: nil)).
  { intros * Hm Hok; inversion Hm; subst; [ unfold gc_unit in *; cbn in *; discriminate |].
    match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
      destruct (udenote_last _ _ _ _ _ _ _ Hu) as (R0 & Hu0 & ->);
      exact (desc_ok_mtele_last _ _ _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu0) Hok) end. }
  destruct (Ht _ _ _ _ HR1 (HK1 _ HR1)) as (T1 & HT1).
  destruct (Ht _ _ _ _ HR2 (HK2 _ HR2)) as (T2 & HT2).
  destruct (presup_exp_typ HN1) as [i HX1].
  destruct (presup_exp_typ HN2) as [j HX2].
  eapply wf_me_app; [ exact HH | exact HR1 | exact HT1 | apply tele_view_last | exact HX1 | exact HN1 | exact HN
                    | exact HR2 | exact HT2 | apply tele_view_last | exact HX2 | exact HN2 ].
Qed.

Lemma sub_eq_preserves_mut :
  (forall Θ Ξ Δ A M, Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ]) /\
  (forall Θ Ξ Δ A M M', Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Δ A A', Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Δ U, Θ ⍮ Ξ ⍮ Δ ⊢ᵤ U -> True) /\
  (forall Θ Ξ Δ Ψ Ψ', Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
       (tele_ass Ψ -> Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢ˢ sb_qn (length Ψ) σ ≈ sb_qn (length Ψ) σ' : Ψ ++ Δ /\
                       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ σ ≈ tele_sub Ψ σ') /\
       (tele_ass Ψ' -> Θ ⍮ Ξ ⍮ tele_sub Ψ' σ ++ Γ ⊢ˢ sb_qn (length Ψ') σ ≈ sb_qn (length Ψ') σ' : Ψ' ++ Δ /\
                        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub Ψ' σ ≈ tele_sub Ψ' σ')) /\
  (forall Θ Ξ Δ U U', Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ']ᵘ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U'[σ]ᵘ ≈ U'[σ']ᵘ) /\
  (forall Θ Ξ Δ H H', Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H[σ]ᵐ ≈ H[σ']ᵐ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H'[σ]ᵐ ≈ H'[σ']ᵐ).
Proof.
  apply syntactic_wf_mut_ind'; intros; try exact I.
  (** Units: a body by its filled-in entries, an alias by its target. *)
  all: try solve [ eapply sub_eq_unit_body_case; eassumption ].
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HΔ : wf_ext_eq _ _ _ ?Δu ?Δu',
      IHΔ : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> (tele_ass ?Δu -> _) /\ (tele_ass ?Δu' -> _),
      Ha : tele_ass ?Δu, Ha' : tele_ass ?Δu', HE : wf_modexp_eq _ _ _ ?E ?E', HE' : wf_modexp_eq _ _ _ ?E' ?E',
      IHE : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?E _) _ /\ _,
      IHE' : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?E' _) _ /\ _
      |- wf_unit_eq _ _ _ (gunit_sub (gu_mk ?Δu (md_alias ?E)) ?σ) _ /\ _ =>
        destruct (IHΔ _ _ _ Hσ) as [HL HR]; destruct (HL Ha) as [L HΔσ]; destruct (HR Ha') as [L' HΔσ'];
        split; [ eapply sub_eq_unit_alias_self; [ exact Hσ | exact L | exact HΔσ | exact Ha | eapply wf_modexp_eq_refl_left; exact HE
                                                | intros; exact (proj1 (IHE _ _ _ ltac:(eassumption))) ]
               | eapply sub_eq_unit_alias_self; [ exact Hσ | exact L' | exact HΔσ' | exact Ha' | exact HE'
                                                | intros; exact (proj1 (IHE' _ _ _ ltac:(eassumption))) ] ]
    end ].
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HΔ : wf_ext_eq _ _ _ ?Δ ?Δ,
      IHΔ : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> (tele_ass ?Δ -> _) /\ _,
      Ha : tele_ass ?Δ, HU : wf_unit_eq _ _ (?Δ ++ _) (gu_mk ?Δ' ?D) _,
      IHU : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_unit_eq _ _ _ (gunit_sub (gu_mk ?Δ' ?D) _) _ /\ _
      |- wf_unit_eq _ _ _ (gunit_sub (gu_mk ?Δ (md_alias (me_lit (gu_mk ?Δ' ?D)))) ?σ) _ /\ _ =>
        destruct (IHΔ _ _ _ Hσ) as [HL _]; destruct (HL Ha) as [L HΔσ];
        eapply sub_eq_unit_flatten_case;
        [ exact Hσ | exact L | exact HΔσ | exact HΔ | exact Ha | exact HU | intros; exact (proj1 (IHU _ _ _ ltac:(eassumption))) ]
    end ].
  (** Symmetry and transitivity: each side as the induction hypotheses give
      it. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', IH : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_unit_eq _ _ _ (gunit_sub ?U _) _ /\ wf_unit_eq _ _ _ (gunit_sub ?U' _) _
      |- wf_unit_eq _ _ _ (gunit_sub ?U' ?σ) _ /\ wf_unit_eq _ _ _ (gunit_sub ?U ?σ) _ =>
        destruct (IH _ _ _ Hσ); split; assumption
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', IH : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?H _) _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H' _) _
      |- wf_modexp_eq _ _ _ (modexp_sub ?H' ?σ) _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H ?σ) _ =>
        destruct (IH _ _ _ Hσ); split; assumption
    end ].
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ',
      IH1 : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_unit_eq _ _ _ (gunit_sub ?U _) _ /\ _,
      IH2 : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> _ /\ wf_unit_eq _ _ _ (gunit_sub ?U'' _) _
      |- wf_unit_eq _ _ _ (gunit_sub ?U ?σ) _ /\ wf_unit_eq _ _ _ (gunit_sub ?U'' ?σ) _ =>
        split; [ exact (proj1 (IH1 _ _ _ Hσ)) | exact (proj2 (IH2 _ _ _ Hσ)) ]
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ',
      IH1 : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?H _) _ /\ _,
      IH2 : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H'' _) _
      |- wf_modexp_eq _ _ _ (modexp_sub ?H ?σ) _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H'' ?σ) _ =>
        split; [ exact (proj1 (IH1 _ _ _ Hσ)) | exact (proj2 (IH2 _ _ _ Hσ)) ]
    end ].
  (** Module expressions. *)
  all: try solve [ cbn; split; eapply wf_me_unit; first [ eapply wf_sub_eq_left; eassumption | eassumption ] ].
  all: try solve [
    match goal with Hσ : wf_sub_eq _ _ _ _ _ _, Hx : _ ∋ #?x ≔ₘ _ |- wf_modexp_eq _ _ _ (modexp_sub (me_var ?x) _) _ /\ _ =>
      cbn; split; eapply wf_sub_eq_apply_mod; eassumption end ].
  all: try solve [ cbn; match goal with IH : forall _ _ _, _ -> wf_unit_eq _ _ _ _ _ /\ wf_unit_eq _ _ _ _ _, Hσ : wf_sub_eq _ _ _ _ _ _ |- _ =>
                     destruct (IH _ _ _ Hσ); split; apply wf_me_lit; assumption end ].
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HH : wf_modexp_eq _ _ _ ?H ?H',
      IH : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?H _) _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H' _) _,
      Hm : mdenote _ _ _ (me_mem ?H ?y) _, Hm' : mdenote _ _ _ (me_mem ?H' ?y) _
      |- wf_modexp_eq _ _ _ (modexp_sub (me_mem ?H ?y) ?σ) _ /\ _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        pose proof (wf_modexp_eq_refl_left HH) as HHl; pose proof (wf_modexp_eq_refl_right HH) as HHr;
        destruct (IH _ _ _ Hσ) as [IH1 IH2]; cbn; split; eapply wf_me_mem;
        first [ exact IH1 | exact IH2
              | eapply wf_sub_mdenote_mem; [ exact HHl | exact Hm | eassumption ]
              | eapply wf_sub_mdenote_mem; [ exact HHr | exact Hm' | eassumption ]
              | eapply wf_sub_ds_mtele_mem; [ exact HHl | exact Hm | eassumption | eassumption ]
              | eapply wf_sub_ds_mtele_mem; [ exact HHr | exact Hm' | eassumption | eassumption ] ]
    end ].
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HH : wf_modexp_eq _ _ _ ?H ?H',
      IH : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?H _) _ /\ wf_modexp_eq _ _ _ (modexp_sub ?H' _) _,
      HB : wf_exp _ _ _ (a_typ _) ?B, IHB : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?B _) _,
      HN : wf_exp _ _ _ ?B ?N, IHN : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?N _) _,
      HB' : wf_exp _ _ _ (a_typ _) ?B', IHB' : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?B' _) _,
      HN' : wf_exp _ _ _ ?B' ?N', IHN' : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?N' _) _,
      Hm : mdenote _ _ _ ?H ?R, HT : ds_mtele _ _ ?R = Some _, Hv : tele_view _ = Some (?B, _),
      Hm' : mdenote _ _ _ ?H' ?R', HT' : ds_mtele _ _ ?R' = Some _, Hv' : tele_view _ = Some (?B', _)
      |- wf_modexp_eq _ _ _ (modexp_sub (me_app ?H ?N) ?σ) _ /\ _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        pose proof (wf_modexp_eq_refl_left HH) as HHl; pose proof (wf_modexp_eq_refl_right HH) as HHr;
        destruct (IH _ _ _ Hσ) as [IH1 IH2]; cbn; split; eapply wf_me_app;
        [ exact IH1
        | eapply wf_sub_mdenote; [ exact HHl | exact Hm | exact Hl ]
        | eapply wf_sub_ds_mtele; [ exact HHl | exact Hm | exact HT | exact Hl ]
        | eapply tele_view_sub_some; exact Hv
        | eapply sub_preserves_typ; [ exact HB | exact Hl ]
        | eapply sub_preserves_exp; [ exact HN | exact Hl ]
        | exact (IHN _ _ _ Hσ)
        | eapply wf_sub_mdenote; [ exact HHl | exact Hm | exact Hr ]
        | eapply wf_sub_ds_mtele; [ exact HHl | exact Hm | exact HT | exact Hr ]
        | eapply tele_view_sub_some; exact Hv
        | eapply sub_preserves_typ; [ exact HB | exact Hr ]
        | eapply sub_preserves_exp; [ exact HN | exact Hr ]
        | exact IH2
        | eapply wf_sub_mdenote; [ exact HHr | exact Hm' | exact Hl ]
        | eapply wf_sub_ds_mtele; [ exact HHr | exact Hm' | exact HT' | exact Hl ]
        | eapply tele_view_sub_some; exact Hv'
        | eapply sub_preserves_typ; [ exact HB' | exact Hl ]
        | eapply sub_preserves_exp; [ exact HN' | exact Hl ]
        | exact (IHN' _ _ _ Hσ)
        | eapply wf_sub_mdenote; [ exact HHr | exact Hm' | exact Hr ]
        | eapply wf_sub_ds_mtele; [ exact HHr | exact Hm' | exact HT' | exact Hr ]
        | eapply tele_view_sub_some; exact Hv'
        | eapply sub_preserves_typ; [ exact HB' | exact Hr ]
        | eapply sub_preserves_exp; [ exact HN' | exact Hr ] ]
    end ].
  (** [δ] for a slot: the slot's two images, each its unit. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq ?T ?X ?G0 ?G ?σ ?σ', Hx : _ ∋ #?x ≔ₘ ?U |- wf_modexp_eq _ _ _ (modexp_sub (me_var ?x) _) _ /\ wf_modexp_eq _ _ _ (modexp_sub (me_lit ?U) _) _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        assert (Hlit : forall s, T ⍮ X ⍮ G0 ⊢ˢ s : G -> T ⍮ X ⍮ G0 ⊢ᵐ sentry_modexp (s x) ≈ me_lit U[s]ᵘ)
          by (intros s Hs; destruct (wf_sub_apply_mod _ _ _ _ _ Hs _ _ Hx) as [[-> HUσ] | (y & -> & Hy)]; cbn;
              [ apply wf_me_lit; exact HUσ | eapply wf_me_delta_slot; [ eapply wf_sub_dom; exact Hs | exact Hy ] ]);
        cbn; split; [ eapply wf_sub_eq_apply_mod; eassumption |];
        eapply wf_me_trans; [ apply wf_me_sym; exact (Hlit _ Hl) |];
        eapply wf_me_trans; [ eapply wf_sub_eq_apply_mod; eassumption | exact (Hlit _ Hr) ]
    end ].
  (** [δ] for a selection: the unit side through the selection, each image
      its unit. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HH : wf_modexp_eq _ _ _ (me_mem ?H ?y) (me_mem ?H ?y),
      Hm : mdenote _ _ _ (me_mem ?H ?y) ?R, Hd : ds_mod _ _ ?R = Some ?Rm,
      IHs : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub (me_mem ?H ?y) _) _ /\ _
      |- wf_modexp_eq _ _ _ (modexp_sub (me_mem ?H ?y) ?σ) _ /\ wf_modexp_eq _ _ _ (modexp_sub (ds_unit ?Rm) _) _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        pose proof (wf_me_delta_sel _ _ _ _ _ _ _ HH Hm Hd) as Hδ;
        split; [ exact (proj1 (IHs _ _ _ Hσ)) |];
        eapply wf_me_trans; [ apply wf_me_sym; eapply sub_preserves_modexp; [ exact Hδ | exact Hl ] |];
        eapply wf_me_trans; [ exact (proj1 (IHs _ _ _ Hσ)) | eapply sub_preserves_modexp; [ exact Hδ | exact Hr ] ]
    end ].
  (** [β]: the redex from one substitution to the other, the reduct through
      it. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HU : wf_unit_eq _ _ _ (gu_mk (?Δ ++ ce_ass ?X :: nil) ?D) _,
      IHU : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_unit_eq _ _ _ (gunit_sub (gu_mk (?Δ ++ ce_ass ?X :: nil) ?D) _) _ /\ _,
      HN : wf_exp _ _ _ ?X ?N, IHN : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?N _) _ |- _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        assert (Hred : _ ⍮ _ ⍮ _ ⊢ᵐ modexp_sub (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) σ
                                    ≈ modexp_sub (me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) D)) N) σ')
          by (cbn [modexp_sub]; pose proof (proj1 (IHU _ _ _ Hσ)) as HUσ; rewrite !gunit_sub_last in HUσ |- *;
              eapply lit_app_cong; [ exact HUσ | eapply sub_preserves_exp; [ exact HN | exact Hl ] | exact (IHN _ _ _ Hσ)
                                   | eapply sub_preserves_exp; [ exact HN | exact Hr ] ]);
        split; [ exact Hred |];
        eapply wf_me_trans; [ apply wf_me_sym; eapply sub_preserves_modexp; [ first [ eapply wf_me_beta_body | eapply wf_me_beta_alias ]; eassumption | exact Hl ] |];
        eapply wf_me_trans; [ exact Hred | eapply sub_preserves_modexp; [ first [ eapply wf_me_beta_body | eapply wf_me_beta_alias ]; eassumption | exact Hr ] ]
    end ].
  (** An alias with no parameter: its target through it. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HE : wf_modexp_eq _ _ _ ?E ?E,
      IHE : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?E _) _ /\ _
      |- wf_modexp_eq _ _ _ (modexp_sub (me_lit (gu_mk nil (md_alias ?E))) ?σ) _ /\ _ =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        split; [| exact (proj1 (IHE _ _ _ Hσ)) ];
        eapply wf_me_trans; [ eapply sub_preserves_modexp; [ eapply wf_me_beta_alias0; exact HE | exact Hl ] |];
        eapply wf_me_trans; [ exact (proj1 (IHE _ _ _ Hσ)) |];
        apply wf_me_sym; eapply sub_preserves_modexp; [ eapply wf_me_beta_alias0; exact HE | exact Hr ]
    end ].
  (** A member: the module expression from one substitution to the other;
      the right-hand side typed at the left one's type by the equation of
      the type the premise gives. *)
  all: try solve [
    match goal with
    | Hσ : wf_sub_eq _ _ _ _ ?σ ?σ', HH : wf_modexp_eq _ _ _ ?H ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) ?R,
      Ht : ds_ty _ _ ?R = Some ?A, HA : wf_exp _ _ _ (a_typ _) ?A,
      HMr : forall _, ds_red ?R = Some _ -> wf_exp _ _ _ ?A _,
      IHA : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?A _) _,
      IH : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_modexp_eq _ _ _ (modexp_sub ?H _) _ /\ _
      |- wf_exp_eq _ _ _ (exp_sub ?A ?σ) (exp_sub (a_mem ?H ?x) ?σ) (exp_sub (a_mem ?H ?x) ?σ') =>
        pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hl; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hσ) as Hr;
        let Hc := fresh "Hc" in
        pose proof (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)) as Hc;
        pose proof (IHA _ _ _ Hσ) as HAσ; cbn [exp_sub] in HAσ;
        cbn [exp_sub]; eapply wf_exp_eq_mem_cong;
        [ exact (proj1 (IH _ _ _ Hσ))
        | eapply wf_sub_mdenote_mem; [ exact HH | exact Hm | exact Hl ]
        | eapply ds_ty_sub; [ exact Hc | exact Ht ]
        | eapply wf_sub_mdenote_mem; [ exact HH | exact Hm | exact Hr ]
        | eapply ds_ty_sub; [ exact Hc | exact Ht ]
        | eapply wf_exp_subtyp;
          [ eapply wf_mem; [ eapply sub_preserves_modexp; [ exact HH | exact Hr ]
                           | eapply wf_sub_mdenote_mem; [ exact HH | exact Hm | exact Hr ]
                           | eapply ds_ty_sub; [ exact Hc | exact Ht ]
                           | eapply sub_preserves_typ; [ exact HA | exact Hr ]
                           | let HM' := fresh "HM'" in
                             intros ? HM'; destruct (ds_red_sub_inv _ _ _ HM') as (? & ? & ->);
                             eapply sub_preserves_exp; [ eapply HMr; eassumption | exact Hr ] ]
          | eapply sub_preserves_typ; [ exact HA | exact Hl ]
          | eapply wf_subtyp_refl; [ eapply sub_preserves_typ; [ exact HA | exact Hl ] | apply wf_exp_eq_sym; exact HAσ ] ] ]
    end ].
  (** [Π]: by the kind of its universe. *)
  all: repeat match goal with Hu : wf_is_univ _ _ _ _ |- _ => inversion Hu; subst; clear Hu end.
  (** Telescopes of assumptions: the substitutions are lifted entry by
      entry, at the equation of the entry's type the induction hypothesis
      gives. *)
  all: try solve [ cbn; split; intros _; (split; [ assumption | apply wf_ext_eq_nil; eapply wf_sub_dom, wf_sub_eq_left; eassumption ]) ].
  all: try solve [ split; intros Hass; inversion Hass as [| ? ? [? Heq] ? ]; discriminate ].
  all: try solve [
    match goal with
    | HΨ : wf_ext_eq _ _ ?Δ ?Ψ ?Ψ', IHx : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> (tele_ass ?Ψ -> _) /\ (tele_ass ?Ψ' -> _),
      HA : wf_exp _ _ (?Ψ ++ ?Δ) (a_typ ?i) ?A,
      IHA : forall _ _ _, wf_sub_eq _ _ _ (?Ψ ++ ?Δ) _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?A _) _,
      HA' : wf_exp _ _ (?Ψ' ++ ?Δ) (a_typ ?i) ?A',
      IHA' : forall _ _ _, wf_sub_eq _ _ _ (?Ψ' ++ ?Δ) _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?A' _) _,
      Hσ : wf_sub_eq _ _ ?Γ ?Δ ?σ ?σ' |- _ =>
        destruct (IHx _ _ _ Hσ) as [IHl IHr];
        split; intros Hass; inversion_clear Hass as [| ? ? _ Hass'];
        [ destruct (IHl Hass') as [Hl HE];
          exact (sub_eq_ext_ass_diag _ _ _ _ _ _ _ _ _ Hl HE (ext_eq_ctx_left _ _ _ _ _ HΨ) HA IHA Hσ)
        | destruct (IHr Hass') as [Hl HE];
          exact (sub_eq_ext_ass_diag _ _ _ _ _ _ _ _ _ Hl HE (ext_eq_ctx_right _ _ _ _ _ HΨ) HA' IHA' Hσ) ]
    end ].
  (** The eliminator. *)
  all: try solve [ eapply sub_eq_elim_case; eassumption ].
  all: destruct_let_ann; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
    saturate_sub_typ; saturate_sub_eq_IH.
  (** In the [a_glob] case the recorded type reaches [Γ] only through
      [saturate_sub_typ], i.e. after [push_sub] has run. *)
  all: try solve [ push_closed; mauto 3 ].
  (** The type former and the constructors: their types are closed. *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, Hσ : wf_sub _ _ _ _ _ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ) | exact Hl ]);
        try (erewrite (ind_ty_sub D) by eassumption); try (erewrite (con_ty_sub _ D) by eassumption);
        first [ eapply wf_exp_eq_ind_cong | eapply wf_exp_eq_con_cong ]; eauto using wf_sub_dom
    end ].
  (** The module of an inductive type as a term: its chain is closed, and
      both sides unfold to the type former. *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, Hp : mod_qname _ = Some _, Hσ : wf_sub _ _ _ _ ?σ |- _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hσ) | exact Hl ]);
        rewrite (ind_ty_sub D _ HD); cbn [exp_sub]; rewrite !(mod_qname_sub _ _ _ Hp);
        eapply wf_exp_eq_trans;
        [ eapply wf_exp_eq_mem_glob_ind_unfold | eapply wf_exp_eq_sym, wf_exp_eq_mem_glob_ind_unfold ];
        eauto using wf_sub_dom
    end ].
  all: try solve [ mauto 3 ].
  (** The small [Π]: the codomain's universe, the weakened level, commutes
      with the lifted substitution. *)
  all: try solve [
    match goal with
    | HL : wf_exp _ _ ?Δ (a_level ?n) ?L, HA : wf_exp _ _ ?Δ (a_univ ?L) ?A, Hσ : wf_sub_eq _ _ ?Γ ?Δ ?σ ?σ',
      Hs : wf_sub _ _ ?Γ ?Δ ?σ, IHA : forall _ _ _, wf_sub_eq _ _ _ ?Δ _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?A _) _,
      IHB : forall _ _ _, wf_sub_eq _ _ _ (cons (ce_ass ?A) ?Δ) _ _ -> _,
      Hq : wf_sub_eq _ _ _ (cons (ce_ass ?A) ?Δ) (sb_q ?σ) (sb_q ?σ') |- _ =>
        eapply wf_exp_eq_pi_cong_lvl;
        [ let H' := fresh in pose proof (sub_preserves_exp _ _ _ _ _ _ _ HL Hs) as H'; exact H'
        | let H' := fresh in pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hs) as H'; exact H'
        | exact (IHA _ _ _ Hσ)
        | rewrite <- exp_wk_shift_sub_q; exact (IHB _ _ _ Hq) ]
    end ].
  (** A local module: both sides are reduced by [ζ] and meet at the body
      under the two extended substitutions, at the body's type. *)
  1: { match goal with
    | h1 : wf_sub_eq _ _ ?Γ0 ?Γ ?σ ?σ', h2 : wf_unit_eq _ _ ?Γ ?U ?U,
      h3 : wf_exp _ _ (ce_mod ?U :: ?Γ) (a_typ _) ?C, h4 : wf_exp _ _ (ce_mod ?U :: ?Γ) ?C ?B,
      h5 : wf_sub _ _ ?Γ0 ?Γ ?σ, h6 : wf_sub _ _ ?Γ0 ?Γ ?σ',
      h7 : forall _ _ _, wf_sub_eq _ _ _ (ce_mod ?U :: ?Γ) _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?C _) _,
      h8 : forall _ _ _, wf_sub_eq _ _ _ (ce_mod ?U :: ?Γ) _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?B _) _ |- _ =>
        rename h1 into Hσ, h2 into HU, h3 into HC, h4 into HB, h5 into Hl, h6 into Hr, h7 into IHC, h8 into IHB
    end.
match goal with IHU : forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> wf_unit_eq _ _ _ (gunit_sub U _) (gunit_sub U _) /\ _ |- _ =>
      pose proof (wf_sub_eq_extend_mod _ _ _ _ _ _ _ Hσ HU (proj1 (IHU _ _ _ Hσ))) as Hτ end.
    assert (HUl : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (HUr : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ']ᵘ ≈ U[σ']ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (Hz : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ s : Γ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[s]ᵘ ≈ U[s]ᵘ ->
                   Θ ⍮ Ξ ⍮ Γ0 ⊢ ℓₘ U[s]ᵘ in B[q s] ≈ B[s ,,ₘ me_lit U[s]ᵘ] : C[s ,,ₘ me_lit U[s]ᵘ]).
    { intros s Hs HUs; rewrite <- (exp_sub_q_extend_mod B), <- (exp_sub_q_extend_mod C).
      eapply wf_exp_eq_let_mod_zeta;
      [ exact HUs
      | eapply sub_preserves_typ; [ exact HC | apply wf_sub_q_mod; assumption ]
      | eapply sub_preserves_exp; [ exact HB | apply wf_sub_q_mod; assumption ] ]. }
    rewrite exp_sub_extend_mod_sub.
    eapply wf_exp_eq_meet;
        [ exact (Hz _ Hl HUl) | exact (IHB _ _ _ Hτ) | exact (Hz _ Hr HUr)
        | eapply sub_preserves_typ; [ exact HC | eapply wf_sub_eq_left; exact Hτ ]
        | exact (IHC _ _ _ Hτ) ]. }
Qed.


Corollary sub_eq_preserves_exp : forall Θ Ξ Δ A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ].
Proof. exact (proj1 sub_eq_preserves_mut). Qed.

#[export]
Hint Resolve sub_eq_preserves_exp : mctt.

(** Equivalent substitutions move a well-formed module expression and a
    well-formed unit to equal ones. *)
Corollary sub_eq_preserves_modexp : forall Θ Ξ Δ H H',
    Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' ->
    forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H[σ]ᵐ ≈ H[σ']ᵐ.
Proof.
  intros * HH * Hσ; destruct sub_eq_preserves_mut as (_ & _ & _ & _ & _ & _ & HM).
  exact (proj1 (HM _ _ _ _ _ HH _ _ _ Hσ)).
Qed.

Corollary sub_eq_preserves_unit : forall Θ Ξ Δ U U',
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' ->
    forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ']ᵘ.
Proof.
  intros * HU * Hσ; destruct sub_eq_preserves_mut as (_ & _ & _ & _ & _ & HUU & _).
  exact (proj1 (HUU _ _ _ _ _ HU _ _ _ Hσ)).
Qed.

Corollary sub_eq_preserves_typ : forall Θ Ξ Γ Δ A σ σ' i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ exp_sub A σ ≈ exp_sub A σ' : exp_sub (a_typ i) σ) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve sub_eq_preserves_typ : mctt.

(** ** Substitution Equivalence is a PER

    Both directions need to move an image from [A[σ]] to [A[σ']], which is what
    [sub_eq_preserves_typ] and [ctx_lookup_wf] together provide. *)

Lemma wf_sub_eq_sym : forall Θ Ξ Γ Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ' ≈ σ : Δ.
Proof.
  intros * H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A Hlk.
    assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i) as [i ?] by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i) by mauto 2.
    eapply wf_exp_eq_subtyp';
      [ symmetry; eapply wf_sub_eq_apply; eassumption | mauto 3 ].
  - intros x U Hl; apply wf_me_sym; eapply wf_sub_eq_apply_mod; eassumption.
Qed.

Lemma wf_sub_eq_trans : forall Θ Ξ Γ Δ σ σ' σ'',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ' ≈ σ'' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ'' : Δ.
Proof.
  intros * H1 H2; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A Hlk.
    assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i) as [i ?] by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ'] ≈ #x[σ''] : A[σ]) by
      (eapply wf_exp_eq_subtyp'; [ eapply wf_sub_eq_apply; eassumption | mauto 4 ]).
    etransitivity; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
  - intros x U Hl; eapply wf_me_trans; eapply wf_sub_eq_apply_mod; eassumption.
Qed.

#[export]
Instance wf_sub_eq_PER Θ Ξ Γ Δ : PER (wf_sub_eq Θ Ξ Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_per_elem Θ Ξ Γ Δ : PERElem _ (wf_sub Θ Ξ Γ Δ) (wf_sub_eq Θ Ξ Γ Δ).
Proof.
  intros ? ?; mauto 2.
Qed.

(** [sb_eq] is not a Leibniz equality, so a pointwise rearrangement of a
    substitution — [sb_compose_assoc] and its kin — has to be turned into a
    judgmental one before it can be used on a judgment that is not [Proper] for
    it, such as a gluing predicate. *)
Lemma wf_sub_eq_of_sb_eq : forall Θ Ξ Γ Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    sb_eq σ σ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ.
Proof.
  intros * ? Heq.
  econstructor; [ eassumption | now rewrite <- Heq | |].
  - intros x A ?; change (exp_sub (a_var x) σ') with (sentry_exp (σ' x)); rewrite <- (Heq x); mauto 2.
  - intros x U Hl; rewrite <- (Heq x); eapply wf_sub_mod_image; eassumption.
Qed.

(** ** Composition of Equivalent Substitutions

    The two one-sided halves are [sub_preserves_exp_eq] and
    [sub_eq_preserves_exp] respectively; the full congruence is their
    composite. *)

Lemma wf_sub_eq_compose_left : forall Θ Ξ Γ Γ' Δ σ σ' τ,
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ ⨟ τ ≈ σ' ⨟ τ : Δ.
Proof.
  intros * H ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A ?; reduce_index; rewrite <- exp_sub_sub, <- !sentry_exp_sub; fold (exp_sub (a_var x) σ) (exp_sub (a_var x) σ').
    eapply sub_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
  - intros x U Hl; cbn [sb_compose]; rewrite !sentry_modexp_sub.
    eapply sub_preserves_modexp; [ eapply wf_sub_eq_apply_mod; eassumption | eassumption ].
Qed.

Lemma wf_sub_eq_compose_right : forall Θ Ξ Γ Γ' Δ σ τ τ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ ≈ τ' : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ ⨟ τ ≈ σ ⨟ τ' : Δ.
Proof.
  intros * ? H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | |].
  - intros x A ?; reduce_index; rewrite <- exp_sub_sub, <- !sentry_exp_sub; fold (exp_sub (a_var x) σ).
    eapply sub_eq_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
  - intros x U Hl; cbn [sb_compose]; rewrite !sentry_modexp_sub.
    eapply sub_eq_preserves_modexp; [ eapply wf_sub_mod_image; eassumption | eassumption ].
Qed.

Corollary wf_sub_eq_compose : forall Θ Ξ Γ Γ' Δ σ σ' τ τ',
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ ≈ τ' : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ ⨟ τ ≈ σ' ⨟ τ' : Δ.
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
    descriptions of a weakened [Π]-type: [(Π A B)[↑]ʷ] is [Π A[↑]ʷ B[q ↑]ʷ], but
    only by computation, so [eauto] cannot see it and the step is taken by hand.
    The application's type is [B[q ↑]ʷ[Id ,, #0]], which is [B] by
    [exp_wk_q_shift_single]: lifting a weakening and then substituting the top
    variable for it is the identity. *)

(** [Id ,, #0] and its variable form [sb_extend Id (se_var 0)] substitute the
    same terms, though not the same module expressions; on a well-typed term
    they agree judgmentally. *)
Lemma wf_sub_eq_var_zero : forall Θ Ξ Γ A i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ˢ Id,,#0 ≈ sb_extend Id (se_var 0) : Γ ▹ A ▹ A[↑]ʷ.
Proof.
  intros * HA.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
  assert (HA' : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; eassumption).
  assert (Hv : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #0 : A[↑]ʷ) by mauto 3.
  assert (Hl : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ˢ Id,,#0 : Γ ▹ A ▹ A[↑]ʷ) by (eapply wf_sub_single; eassumption).
  assert (Hr : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ˢ sb_extend Id (se_var 0) : Γ ▹ A ▹ A[↑]ʷ).
  { apply wf_sub_extend_gen; [ mauto 3 | mauto 3 | | |]; intros * Hlk; inversion Hlk; subst; cbn.
    rewrite exp_sub_shift_extend, exp_sub_id; exact Hv. }
  econstructor; [ exact Hl | exact Hr | |].
  - intros x B Hlk.
    replace (exp_sub (a_var x) (sb_extend Id (se_var 0))) with (exp_sub (a_var x) (Id,,#0)) by (destruct x; reflexivity).
    apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
  - intros x U Hlk; inversion Hlk; subst; cbn; eapply wf_me_var; [ mauto 2 | eassumption ].
Qed.

Lemma wf_fn_eta_expand : forall Θ Ξ Γ A B M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk M ↑ : exp_wk (Π A B) ↑) as H'
      by (eapply wk_preserves_exp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ : Π A[↑]ʷ B[wk_q ↑]ʷ) by exact H'.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #0 : A[↑]ʷ) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ▹ A[↑]ʷ ⊢ B[wk_q ↑]ʷ : Typeω@i)
      by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : B[wk_q ↑]ʷ[Id,,#0]) by (eapply wf_app; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B[wk_q ↑]ʷ[Id,,#0] ≈ B : Typeω@i).
  { rewrite <- (exp_wk_q_shift_single B) at 2.
    eapply (sub_eq_preserves_typ _ _ _ _ _ _ _ i); [ eassumption | eapply wf_sub_eq_var_zero; eassumption ]. }
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : B).
  { eapply wf_exp_subtyp'; [ eassumption |].
    eapply wf_subtyp_refl; [ eassumption | eassumption ]. }
  mauto 2.
Qed.

#[export]
Hint Resolve wf_fn_eta_expand : mctt.

(** ** Closed Neutrals

    A neutral with no global or parameter at its head has a variable there, and
    the empty context has none. *)

Lemma no_closed_neutral : forall {Θ Ξ A} {W : ne},
    ne_clean W ->
    ~ Θ ⍮ Ξ ⍮ ⋅ ⊢ W : A.
Proof.
  intros * HW H.
  dependent induction H;
    (* subsumption: the same neutral *)
    try solve [ eapply IHwf_exp1; [ exact HW | reflexivity | reflexivity ] ];
    destruct W; try (simpl in *; congruence);
    autoinjections; cbn in *; destruct_all;
    eauto.
  inversion_by_head ctx_lookup.
Qed.

#[export]
Hint Resolve no_closed_neutral : mctt.

(** ** Conversion

    Subsumption specialised to an equation.  They come last because, registered as hints,
    they let [eauto] change the type of a goal at will — which is what the
    presupposition proof needs on almost every case, and what the proofs above
    are deliberately kept free of. *)

Lemma wf_conv : forall Θ Ξ Γ M A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros; mauto 3.
Qed.

Lemma wf_exp_eq_conv : forall Θ Ξ Γ M M' A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros; mauto 3.
Qed.

#[export]
Hint Resolve wf_conv wf_exp_eq_conv : mctt.

(** ** The Global Context

    Presupposition of what each judgment is relative to, and the canonicity that
    resolution's determinism is stated with.  That resolution lands in a
    well-typed entry is [presup_global]. *)

(** The stack presupposes the filed units with no frame open.  This needs
    nothing from [Presup]. *)

Lemma wf_gstack_deps : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ nil.
Proof.
  induction 1; [ constructor | apply wf_gstack_file; assumption | assumption ].
Qed.

#[export]
Hint Resolve wf_gstack_deps : mctt.

Lemma wf_gentry_gctx : forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> ⊢ᵍ Θ ⍮ Ξ.
Proof.
  induction 1; subst; eauto using ctx_wf_gctx, presup_exp_ctx, presup_ext_eq_ctx, wf_gmod_ctx.
Qed.

Lemma wf_gunit_ctx : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢ᵍᵘ U -> ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ.
Proof. eauto using wf_gmod_ctx, wf_gunit_mod. Qed.

Corollary wf_gunit_gctx : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢ᵍᵘ U -> ⊢ᵍ Θ ⍮ Ξ.
Proof. eauto using ctx_wf_gctx, wf_gunit_ctx. Qed.

Corollary wf_gmod_gctx : forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> ⊢ᵍ Θ ⍮ Ξ.
Proof. eauto using ctx_wf_gctx, wf_gmod_ctx. Qed.

(** Each judgment presupposes what it is relative to: a term judgment its
    context, a context the global context, an entry or a unit the global
    context it is checked against, a module its telescope, the stack the filed
    units with no frame open. *)
Theorem presup_ambient :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ᵍ Θ ⍮ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> ⊢ᵍ Θ ⍮ Ξ) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢ᵍᵐ Φ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ) /\
  (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢ᵍᵘ U -> ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ) /\
  (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ nil).
Proof.
  refine (conj ctx_wf_gctx (conj _ (conj _ (conj _ (conj wf_gentry_gctx (conj wf_gmod_ctx
    (conj wf_gunit_ctx wf_gstack_deps)))))));
    intros * H; eauto using presup_exp_ctx, presup_exp_eq_ctx, presup_subtyp_ctx.
Qed.
