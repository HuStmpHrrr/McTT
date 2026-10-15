(** * Properties of the Judgments, continued

    Everything here uses presupposition, which [GlobalPresup] proves by a mutual
    induction over all the judgments; the structural properties it relies on
    are in [Structural]. *)

From Stdlib Require Import Lia Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export GlobalPresup.
Import Syntax_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** Presupposition for Typing

    [presup_exp_typ] is proved in [GlobalPresup], from the mutual theorem. *)

Corollary presup_exp : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
Proof.
  intros; split; mauto 2 using presup_exp_typ.
Qed.

(** ** Context Conversion of Substitutions

    [Θ ⍮ Ξ ⍮ Γ' ⊢s Id : Γ] transports substitutions too: compose with the inclusion and
    cancel the identity.  Which side it goes on is what distinguishes the two:
    [ctxsub_sub] refines the domain, [ctxsub_sub_cod] coarsens the codomain. *)

Corollary ctxsub_sub : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ : Δ.
Proof.
  intros.
  rewrite <- (sb_compose_id_right σ); mauto 2.
Qed.

Corollary ctxsub_sub_cod : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢s Id : Γ' ->
    Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢s σ : Γ'.
Proof.
  intros.
  rewrite <- (sb_compose_id_left σ); mauto 2.
Qed.

#[export]
Hint Resolve ctxsub_sub : mctt.

(** * Substitution Equivalence

    The closure properties below are the [wf_sub_eq] counterparts of
    [wf_sub_id]–[wf_sub_q].  [Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ] equates the images at
    [A[σ]], so symmetry and transitivity need [A[σ]] and [A[σ']] to be equal
    types.  That is [sub_eq_preserves_exp], which therefore comes first, and
    the [PER] instance last. *)

Lemma wf_sub_eq_refl : forall Θ Ξ Γ Δ σ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ : Δ.
Proof.
  intros; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_refl : mctt.

Lemma sub_eq_preserves_vlookup : forall Θ Ξ Γ Δ σ σ' x A,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
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
    Θ ⍮ Ξ ⍮ Γ' ⊢s Id : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ ≈ σ' : Δ.
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
    [sub_preserves_wf] transports along a single substitution and so only
    yields [A[σ] ≈ A[σ]].  The equation really comes from [sub_eq_preserves_exp],
    which is proved by an induction that appeals to this lemma.  We break the
    cycle by taking the equation as a premise; that is precisely what the
    induction hypothesis for the domain supplies at every use site. *)

Lemma wf_sub_eq_q : forall Θ Ξ Γ Δ σ σ' A i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢s q σ ≈ q σ' : Δ ▹ A.
Proof.
  intros * H ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Typeω@i) by mauto 2.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢w ↑ : Γ) by mauto 2.
  econstructor; [ mauto 2 | | ].
  - eapply ctxsub_sub; [ eapply wf_sub_id_extend_eq; mauto 2 | mauto 2 ].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 3 | ].
    rewrite <- !sentry_exp_wk; fold (exp_sub (a_var n) σ) (exp_sub (a_var n) σ').
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

(** The same over a definition, with the substituted bodies equal as a
    premise for the same reason. *)
Lemma wf_sub_eq_q_def : forall Θ Ξ Γ Δ σ σ' A M i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢s q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * H ? ? ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ'] : A[σ']) by mauto 2.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢w ↑ : Γ) by mauto 2.
  econstructor; [ mauto 2 | | ].
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] ≈ A[σ] : Typeω@i) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ'] ≈ M[σ] : A[σ']) by
      (eapply wf_exp_eq_subtyp'; [ symmetry; eassumption | eapply wf_subtyp_refl; eassumption ]).
    eapply ctxsub_sub; [ eapply wf_sub_id_extend_def_eq; eassumption | mauto 2 ].
  - intros x B Hlk.
    inversion Hlk; subst; reduce_index; rewrite exp_wk_shift_sub_q; [ mauto 3 | ].
    rewrite <- !sentry_exp_wk; fold (exp_sub (a_var n) σ) (exp_sub (a_var n) σ').
    eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_q wf_sub_eq_q_def : mctt.

Corollary wf_sub_eq_q_nat : forall Θ Ξ Γ Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ℕ ⊢s q σ ≈ q σ' : Δ ▹ ℕ.
Proof.
  intros * H; saturate_sub_eq.
  apply (wf_sub_eq_q Θ Ξ Γ Δ σ σ' ℕ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_nat : mctt.

Corollary wf_sub_eq_q_False : forall Θ Ξ Γ Δ σ σ',
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢s q σ ≈ q σ' : Δ ▹ ⊥.
Proof.
  intros * H; saturate_sub_eq.
  apply (wf_sub_eq_q Θ Ξ Γ Δ σ σ' ⊥ 0); simpl; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_False : mctt.

Lemma wf_sub_eq_extend : forall Θ Ξ Γ Δ σ σ' A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ,,M ≈ σ',,M' : Δ ▹ A.
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
Corollary wf_sub_eq_id_extend : forall Θ Ξ Γ A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M ≈ Id,,M' : Γ ▹ A.
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
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N' : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ M[σ] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N' ≈ M[σ'] : A[σ'] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ,,N ≈ σ',,N' : Δ ▸ A ≔ M.
Proof.
  intros * H ? ? ? ? ? ? ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x B Hlk.
  inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend;
    [ assumption | eapply wf_sub_eq_apply; eassumption ].
Qed.

Corollary wf_sub_eq_id_extend_def : forall Θ Ξ Γ A M M' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢s Id,,M ≈ Id,,M' : Γ ▸ A ≔ M.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ) by mauto 2.
  apply (wf_sub_eq_extend_def Θ Ξ Γ Γ sb_id sb_id A M M M' i);
    rewrite ?exp_sub_id; mauto 3.
Qed.

Lemma wf_sub_eq_wk : forall Θ Ξ Γ Γ' Δ σ σ' φ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢w φ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s (sb_wk σ φ) ≈ (sb_wk σ' φ) : Δ.
Proof.
  intros * H ?; saturate_wk; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_wk_sub, <- !sentry_exp_wk; fold (exp_sub (a_var x) σ) (exp_sub (a_var x) σ').
  eapply wk_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve wf_sub_eq_extend wf_sub_eq_id_extend wf_sub_eq_extend_def wf_sub_eq_id_extend_def
             wf_sub_eq_wk : mctt.

(** Extending equivalent substitutions into a module slot, each by the literal
    of its own transported unit.  The two units need not be related: the
    judgment equates term images only. *)
Lemma wf_sub_eq_extend_mod : forall Θ Ξ Γ Δ σ σ' U,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ,,ₘ me_lit U[σ]ᵘ ≈ σ' ,,ₘ me_lit U[σ']ᵘ : Δ ▹ₘ U.
Proof.
  intros * H ?; saturate_sub_eq.
  econstructor; [ apply wf_sub_extend_mod; eauto using sub_preserves_unit
                | apply wf_sub_extend_mod; eauto using sub_preserves_unit | ].
  intros x B Hlk.
  inversion Hlk; subst; reduce_index; rewrite exp_sub_shift_extend; eapply wf_sub_eq_apply; eassumption.
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
    [wf_exp_eq_natrec_cong] lets the motive vary, the presupposition lemma
    needs to move a type along an equivalence of substitutions, that is, it
    needs this lemma.  Its counterparts for equality and
    subtyping ([sub_eq_preserves_exp_eq], [sub_eq_preserves_subtyp]) in turn
    need presupposition for the symmetry case, and so come after it, in
    [Core.Syntactic.SubEq]. *)

Ltac lift_sub_eq_nat :=
  match goal with
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_nat) ?Δ) (a_typ _) _, Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ' |- _ =>
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_ass a_nat) Γ) (cons (ce_ass a_nat) Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_eq_q_nat; exact Hσ)
  | _ : wf_exp ?Θ ?Ξ (cons (ce_ass a_False) ?Δ) (a_typ _) _, Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ' |- _ =>
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_ass a_False) Γ) (cons (ce_ass a_False) Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (apply wf_sub_eq_q_False; exact Hσ)
  end.

Ltac lift_sub_eq_step :=
  match goal with
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    IH : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_typ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_ass (exp_sub A σ)) Γ) (cons (ce_ass A) Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_eq_q; [ exact Hσ | | exact (IH _ _ _ Hσ) ]; mauto 2)
  (** A domain in a small universe, at a level it is given to be one: both are
      moved into the least large universe. *)
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    HL : wf_exp ?Θ ?Ξ ?Δ (a_level ?n) ?L,
    HA : wf_exp ?Θ ?Ξ ?Δ (a_univ ?L) ?A,
    IH : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_univ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_ass (exp_sub A σ)) Γ) (cons (ce_ass A) Δ) (sb_q σ) (sb_q σ')) in
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
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_def (exp_sub A σ) (exp_sub M σ)) Γ) (cons (ce_def A M) Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (eapply wf_sub_eq_q_def; [ exact Hσ | | | exact (IHA _ _ _ Hσ) | exact (IHM _ _ _ Hσ) ]; mauto 2)
  end.

Ltac lift_sub_eq := repeat first [ lift_sub_eq_nat | lift_sub_eq_step | lift_sub_eq_def ].

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
      let T := constr:(wf_exp Θ Ξ Γ (a_typ i) (exp_sub A σ)) in
      assert_fails (assert T by assumption);
      assert T by (eapply sub_preserves_typ; eassumption)
  | H : wf_exp ?Θ ?Ξ ?Δ (a_univ ?i) ?A, Hσ : wf_sub ?Θ ?Ξ ?Γ ?Δ ?σ |- _ =>
      let T := constr:(wf_exp Θ Ξ Γ (a_univ i) (exp_sub A σ)) in
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

(** [exp_sub_sub_natrec] cannot join the [push_sub] set — it rewrites in the
    opposite direction from [exp_sub_extend_comm] and the two together would
    loop.  It is applied once, at the end, to the instantiated hypotheses. *)

Ltac reduce_sub_natrec :=
  (on_all_hyp: (fun H => try setoid_rewrite exp_sub_sub_natrec in H)).

(** The eliminator: the motive and the branches move under the equivalent
    substitutions lifted over their contexts, which the induction
    hypotheses of the telescope premises give. *)
Lemma sub_eq_elim_case : forall Θ Ξ Γ Δ σ σ' p D Ps M nm i A Bs,
    ind_lookup Θ Ξ p = Some D -> List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    (forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢s τ ≈ τ' : Γ -> Θ ⍮ Ξ ⍮ Δ0 ⊢ M[τ] ≈ M[τ'] : (apps (a_ind p) Ps)[τ]) ->
    nm = S (ind_nn D) ->
    Θ ⍮ Ξ ⍮ elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    (forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢s τ ≈ τ' : elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ->
       Θ ⍮ Ξ ⍮ Δ0 ⊢ A[τ] ≈ A[τ'] : Typeω@i[τ]) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    (tele_ass (elim_mctx p D (List.firstn (ind_nu D) Ps)) ->
     forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢s τ ≈ τ' : Γ ->
       Θ ⍮ Ξ ⍮ tele_sub (elim_mctx p D (List.firstn (ind_nu D) Ps)) τ ++ Δ0
         ⊢s sb_qn (List.length (elim_mctx p D (List.firstn (ind_nu D) Ps))) τ
          ≈ sb_qn (List.length (elim_mctx p D (List.firstn (ind_nu D) Ps))) τ'
         : elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ) ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs, ind_con D c = Some gs ->
       tele_ass (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢s τ ≈ τ' : Γ ->
         Θ ⍮ Ξ ⍮ tele_sub (elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) τ ++ Δ0
           ⊢s sb_qn (List.length (elim_bctx p D gs A (List.firstn (ind_nu D) Ps))) τ
            ≈ sb_qn (List.length (elim_bctx p D gs A (List.firstn (ind_nu D) Ps))) τ'
           : elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ) ->
    (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
       forall Δ0 τ τ', Θ ⍮ Ξ ⍮ Δ0 ⊢s τ ≈ τ' : elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ->
         Θ ⍮ Ξ ⍮ Δ0 ⊢ B[τ] ≈ B[τ'] : (elim_bty p D c gs A (List.firstn (ind_nu D) Ps))[τ]) ->
    Θ ⍮ Ξ ⍮ Δ ⊢s σ ≈ σ' : Γ ->
    Θ ⍮ Ξ ⍮ Δ ⊢ (a_elim nm A Bs M)[σ] ≈ (a_elim nm A Bs M)[σ'] : (A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[σ].
Proof.
  intros * Hl HPl HPs HM Hnm HA HAA HΨ HΨl Hn HΨB HΨBl Hk HBB Hσ.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hσ) as Hs.
  assert (HD : decl_closed D) by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hs) | exact Hl ]).
  pose proof (wk_firstn_length D Ps HD HPl) as HUl.
  rewrite (sub_elim_type D Ps A M nm σ HPl Hnm); cbn [exp_sub]; subst nm.
  assert (HΨσ : Θ ⍮ Ξ ⍮ Δ ⊢ˣ tele_sub (elim_mctx p D (List.firstn (ind_nu D) Ps)) σ
                  ≈ tele_sub (elim_mctx p D (List.firstn (ind_nu D) Ps)) σ)
    by (eapply sub_preserves_ext; eassumption).
  pose proof (sub_elim_motive_ctx _ _ _ _ _ _ _ _ HD HUl Hs HΨ HΨσ) as Hq.
  pose proof (HΨl (elim_mctx_ass _ _ _ HD) _ _ _ Hσ) as Hlift.
  rewrite length_elim_mctx, elim_mctx_sub in Hlift by assumption.
  eapply wf_exp_eq_elim_cong with (Ps := List.map (fun P => P[σ]) Ps).
  - exact Hl.
  - rewrite List.length_map; exact HPl.
  - eapply sub_elim_params; [ exact HD | | exact Hs ].
    intros * HP HT ? ? Hs0; eapply sub_preserves_exp; [ eapply HPs; eassumption | exact Hs0 ].
  - rewrite <- sub_apps_ind; apply HM; exact Hσ.
  - reflexivity.
  - rewrite List.firstn_map; exact (sub_preserves_exp _ _ _ _ _ _ _ HA Hq).
  - rewrite List.firstn_map, <- elim_mctx_sub by assumption; exact HΨσ.
  - rewrite List.firstn_map; exact (HAA _ _ _ Hlift).
  - apply brs_names_map; exact Hn.
  - intros c gs Hc; rewrite List.firstn_map, <- (elim_bctx_sub p D c gs A _ σ HD (cons_lookup_in _ _ _ Hc) HUl).
    eapply sub_preserves_ext; [ apply (HΨB c gs Hc) | exact Hs ].
  - rewrite !brs_fst_map; reflexivity.
  - intros c gs n B' Hc Hin; apply brs_in_map in Hin as (B & Hin & ->); eapply Hk; eassumption.
  - intros k c gs n B1 B2 Hk1 Hk2 Hc.
    apply nth_error_map_inv in Hk1 as ([[c1 n1] B] & Hk1 & Heq1); cbn in Heq1; injection Heq1 as E1 E2 E3; subst.
    apply nth_error_map_inv in Hk2 as ([[c2 n2] B'] & Hk2 & Heq2); cbn in Heq2; injection Heq2 as E4 E5 E6; subst.
    rewrite Hk1 in Hk2; injection Hk2 as <-.
    cbn [fst snd]; pose proof (List.nth_error_In _ _ Hk1) as Hin.
    rewrite List.firstn_map, <- elim_bty_sub, (Hk _ _ _ _ Hc Hin).
    apply (HBB _ gs _ B Hc Hin).
    pose proof (HΨBl _ gs Hc (elim_bctx_ass _ _ _ _ _ HD) _ _ _ Hσ) as HlB.
    rewrite length_elim_bctx, (elim_bctx_sub p D _ gs A _ σ HD (cons_lookup_in _ _ _ Hc) HUl) in HlB.
    replace (ind_nn D + List.length gs + cargs_nrec gs) with (cargs_nrec gs + List.length gs + ind_nn D) by lia.
    exact HlB.
Qed.

Lemma sub_eq_preserves_mut :
  (forall Θ Ξ Δ A M, Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ]) /\
  (forall Θ Ξ Δ A M M', Θ ⍮ Ξ ⍮ Δ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Δ A A', Θ ⍮ Ξ ⍮ Δ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Δ Ψ Ψ', Θ ⍮ Ξ ⍮ Δ ⊢ˣ Ψ ≈ Ψ' -> tele_ass Ψ ->
     forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
       Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ ⊢s sb_qn (length Ψ) σ ≈ sb_qn (length Ψ) σ' : Ψ ++ Δ) /\
  (forall Θ Ξ Δ U U', Θ ⍮ Ξ ⍮ Δ ⊢ᵘ U ≈ U' -> True) /\
  (forall Θ Ξ Δ H H', Θ ⍮ Ξ ⍮ Δ ⊢ᵐ H ≈ H' -> True).
Proof.
  apply syntactic_wf_mut_ind'; intros; try exact I.
  (** Telescopes of assumptions: the substitutions are lifted entry by
      entry, at the equation of the entry's type the induction hypothesis
      gives. *)
  all: try solve [ cbn; assumption ].
  all: try solve [
    match goal with
    | Hass : tele_ass (_ :: _) |- _ =>
        inversion Hass as [| ? ? [? Heq] ? ]; discriminate
    end ].
  all: try solve [
    match goal with
    | Hass : tele_ass (ce_ass ?A :: ?Ψ), IHx : tele_ass ?Ψ -> forall _ _ _, wf_sub_eq _ _ _ _ _ _ -> _,
      HA : wf_exp _ _ (?Ψ ++ ?Δ) (a_typ ?i) ?A,
      IHA : forall _ _ _, wf_sub_eq _ _ _ (?Ψ ++ ?Δ) _ _ -> wf_exp_eq _ _ _ _ (exp_sub ?A _) _,
      Hσ : wf_sub_eq _ _ ?Γ ?Δ ?σ ?σ' |- _ =>
        inversion_clear Hass as [| ? ? _ Hass'];
        pose proof (IHx Hass' _ _ _ Hσ) as Hl;
        cbn [tele_sub List.length sb_qn List.app];
        eapply wf_sub_eq_q; [ exact Hl | exact HA | exact (IHA _ _ _ Hl) ]
    end ].
  (** The eliminator. *)
  all: try solve [ eapply sub_eq_elim_case; eassumption ].
  all: destruct_let_ann; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
    saturate_sub_typ; saturate_sub_eq_IH; reduce_sub_natrec.
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
        try rewrite (ind_ty_sub D _ HD); try (erewrite (con_ty_sub _ D _ _ _ HD) by eassumption);
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
        eapply wf_exp_eq_pi_cong_small;
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
pose proof (wf_sub_eq_extend_mod _ _ _ _ _ _ _ Hσ HU) as Hτ.
    assert (HUl : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (HUr : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ']ᵘ ≈ U[σ']ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (Hz : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[s]ᵘ ≈ U[s]ᵘ ->
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
  (** A member: both sides are reduced by [δ] and meet at the reduct. *)
  1: { match goal with
    | h1 : wf_modexp_eq _ _ ?Γ ?H ?H, h2 : me_noargs ?H, h3 : wf_sub_eq _ _ ?Γ0 ?Γ ?σ ?σ',
      h4 : wf_sub _ _ ?Γ0 ?Γ ?σ, h5 : wf_sub _ _ ?Γ0 ?Γ ?σ' |- _ =>
        rename h1 into HH, h4 into Hl, h5 into Hr
    end.
assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eassumption).
    pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ HH)) as Hroot.
    assert (Hd : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ a_mem H[s]ᵐ x ≈ M[s] : A[s]).
    { intros s Hs; pose proof (wf_sub_mod_compat _ _ _ _ _ Hs) as Hcm.
      eapply wf_exp_eq_mem_delta;
        [ eapply me_noargs_sub; eassumption | eapply sub_preserves_modexp; eassumption
        | eapply (member_type_sub_term _ _ Hc); eassumption
        | eapply sub_preserves_typ; eassumption
        | unfold member_unfold in *; eapply member_unfold_sub; eassumption
        | eapply sub_preserves_exp; eassumption ]. }
    eapply wf_exp_eq_meet; [ exact (Hd _ Hl) | eassumption | exact (Hd _ Hr) | eassumption | eassumption ]. }
  (** A member of an applied module: both sides commute the arguments out. *)
  1: { match goal with
    | h1 : wf_modexp_eq _ _ ?Γ ?H ?H, h2 : modexp_spine ?H = _, h3 : _ <> nil, h4 : wf_sub_eq _ _ ?Γ0 ?Γ ?σ ?σ',
      h5 : wf_sub _ _ ?Γ0 ?Γ ?σ, h6 : wf_sub _ _ ?Γ0 ?Γ ?σ' |- _ =>
        rename h1 into HH, h3 into Hne, h5 into Hl, h6 into Hr
    end.
pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ HH)) as Hroot.
    assert (Hd : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ ->
               Θ ⍮ Ξ ⍮ Γ0 ⊢ a_mem H[s]ᵐ x ≈ (apps (member_ref R (pre ++ x :: nil)) args)[s] : A[s]).
    { intros s Hs; pose proof (wf_sub_mod_compat _ _ _ _ _ Hs) as Hcm.
      rewrite apps_sub, member_ref_sub.
      eapply wf_exp_eq_mem_app;
        [ eapply sub_preserves_modexp; eassumption | eapply modexp_spine_sub; eassumption
        | destruct args; [ contradiction Hne; reflexivity | discriminate ]
        | eapply sub_preserves_typ; eassumption
        | rewrite <- member_ref_sub, <- apps_sub; eapply sub_preserves_exp; eassumption ]. }
    eapply wf_exp_eq_meet; [ exact (Hd _ Hl) | eassumption | exact (Hd _ Hr) | eassumption | eassumption ]. }
Qed.

Corollary sub_eq_preserves_exp : forall Θ Ξ Δ A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ].
Proof. exact (proj1 sub_eq_preserves_mut). Qed.

#[export]
Hint Resolve sub_eq_preserves_exp : mctt.

Corollary sub_eq_preserves_typ : forall Θ Ξ Γ Δ A σ σ' i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ' ≈ σ : Δ.
Proof.
  intros * H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A Hlk.
  assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i) as [i ?] by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i) by mauto 2.
  eapply wf_exp_eq_subtyp';
    [ symmetry; eapply wf_sub_eq_apply; eassumption | mauto 3 ].
Qed.

Lemma wf_sub_eq_trans : forall Θ Ξ Γ Δ σ σ' σ'',
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ' ≈ σ'' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ'' : Δ.
Proof.
  intros * H1 H2; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A Hlk.
  assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i) as [i ?] by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Typeω@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ'] ≈ #x[σ''] : A[σ]) by
    (eapply wf_exp_eq_subtyp'; [ eapply wf_sub_eq_apply; eassumption | mauto 4 ]).
  etransitivity; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
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
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    sb_eq σ σ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ.
Proof.
  intros * ? Heq.
  econstructor; [ eassumption | now rewrite <- Heq | ].
  intros x A ?; change (exp_sub (a_var x) σ') with (sentry_exp (σ' x)); rewrite <- (Heq x); mauto 2.
Qed.

(** ** Composition of Equivalent Substitutions

    The two one-sided halves are [sub_preserves_exp_eq] and
    [sub_eq_preserves_exp] respectively; the full congruence is their
    composite. *)

Lemma wf_sub_eq_compose_left : forall Θ Ξ Γ Γ' Δ σ σ' τ,
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s τ : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ ⨟ τ ≈ σ' ⨟ τ : Δ.
Proof.
  intros * H ?; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_sub_sub, <- !sentry_exp_sub; fold (exp_sub (a_var x) σ) (exp_sub (a_var x) σ').
  eapply sub_preserves_exp_eq; [ eapply wf_sub_eq_apply; eassumption | eassumption ].
Qed.

Lemma wf_sub_eq_compose_right : forall Θ Ξ Γ Γ' Δ σ τ τ',
    Θ ⍮ Ξ ⍮ Γ ⊢s σ : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s τ ≈ τ' : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ ⨟ τ ≈ σ ⨟ τ' : Δ.
Proof.
  intros * ? H; saturate_sub_eq.
  econstructor; [ mauto 2 | mauto 2 | ].
  intros x A ?; reduce_index; rewrite <- exp_sub_sub, <- !sentry_exp_sub; fold (exp_sub (a_var x) σ).
  eapply sub_eq_preserves_exp; [ eapply wf_sub_apply; eassumption | eassumption ].
Qed.

Corollary wf_sub_eq_compose : forall Θ Ξ Γ Γ' Δ σ σ' τ τ',
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s τ ≈ τ' : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢s σ ⨟ τ ≈ σ' ⨟ τ' : Δ.
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
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s Id,,#0 ≈ sb_extend Id (se_var 0) : Γ ▹ A ▹ A[↑]ʷ.
Proof.
  intros * HA.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (HA' : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Typeω@i) by (eapply wk_preserves_typ; eassumption).
  assert (Hv : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #0 : A[↑]ʷ) by mauto 3.
  assert (Hl : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s Id,,#0 : Γ ▹ A ▹ A[↑]ʷ) by (eapply wf_sub_single; eassumption).
  assert (Hr : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s sb_extend Id (se_var 0) : Γ ▹ A ▹ A[↑]ʷ).
  { apply wf_sub_extend_gen; [ mauto 3 | mauto 3 | | |]; intros * Hlk; inversion Hlk; subst; cbn.
    rewrite exp_sub_shift_extend, exp_sub_id; exact Hv. }
  econstructor; [ exact Hl | exact Hr |].
  intros x B Hlk.
  replace (exp_sub (a_var x) (sb_extend Id (se_var 0))) with (exp_sub (a_var x) (Id,,#0)) by (destruct x; reflexivity).
  apply wf_exp_eq_refl; eapply wf_sub_apply; eassumption.
Qed.

Lemma wf_fn_eta_expand : forall Θ Ξ Γ A B M i,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
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

Lemma wf_gstack_deps : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢g Θ ⍮ nil.
Proof.
  induction 1; [ constructor | apply wf_gstack_file; assumption | assumption ].
Qed.

#[export]
Hint Resolve wf_gstack_deps : mctt.

Lemma wf_gentry_gctx : forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> ⊢g Θ ⍮ Ξ.
Proof.
  induction 1; subst; eauto using ctx_wf_gctx, presup_exp_ctx, presup_ext_eq_ctx, wf_gmod_ctx.
Qed.

Lemma wf_gunit_ctx : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ.
Proof. eauto using wf_gmod_ctx, wf_gunit_mod. Qed.

Corollary wf_gunit_gctx : forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> ⊢g Θ ⍮ Ξ.
Proof. eauto using ctx_wf_gctx, wf_gunit_ctx. Qed.

Corollary wf_gmod_gctx : forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> ⊢g Θ ⍮ Ξ.
Proof. eauto using ctx_wf_gctx, wf_gmod_ctx. Qed.

(** Each judgment presupposes what it is relative to: a term judgment its
    context, a context the global context, an entry or a unit the global
    context it is checked against, a module its telescope, the stack the filed
    units with no frame open. *)
Theorem presup_ambient :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢g Θ ⍮ Ξ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> ⊢ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> ⊢g Θ ⍮ Ξ) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ) /\
  (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> ⊢ Θ ⍮ Ξ ⍮ gu_params U ++ gs_tele Ξ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢g Θ ⍮ nil).
Proof.
  refine (conj ctx_wf_gctx (conj _ (conj _ (conj _ (conj wf_gentry_gctx (conj wf_gmod_ctx
    (conj wf_gunit_ctx wf_gstack_deps)))))));
    intros * H; eauto using presup_exp_ctx, presup_exp_eq_ctx, presup_subtyp_ctx.
Qed.
