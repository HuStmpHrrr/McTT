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
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A[σ] ⊢s q σ ≈ q σ' : Δ ▹ A.
Proof.
  intros * H ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Type@i) by mauto 2.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ] ->
    Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢s q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * H ? ? ? ?; saturate_sub_eq.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] : Type@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] : Type@i) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] : A[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ M[σ'] : A[σ']) by mauto 2.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ]) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▸ A[σ] ≔ M[σ] ⊢w ↑ : Γ) by mauto 2.
  econstructor; [ mauto 2 | | ].
  - assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ'] ≈ A[σ] : Type@i) by mauto 2.
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
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
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
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
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
    Θ ⍮ Ξ ⍮ Γ ⊢ T : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ T' : Type@i ->
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
  | Hσ : wf_sub_eq ?Θ ?Ξ ?Γ ?Δ ?σ ?σ',
    IH : forall _ _ _, wf_sub_eq ?Θ ?Ξ _ ?Δ _ _ -> wf_exp_eq ?Θ ?Ξ _ (a_univ _) (exp_sub ?A _) _ |- _ =>
      let T := constr:(wf_sub_eq Θ Ξ (cons (ce_ass (exp_sub A σ)) Γ) (cons (ce_ass A) Δ) (sb_q σ) (sb_q σ')) in
      assert_fails (assert T by assumption);
      assert T by (eapply (wf_sub_eq_q _ _ _ _ _ _ _ 0); [ exact Hσ | | exact (wf_exp_eq_small_large (IH _ _ _ Hσ)) ];
                   eapply wf_exp_small_large; eassumption)
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

Lemma sub_eq_preserves_exp : forall Θ Ξ Δ A M,
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    forall Γ σ σ', Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ M[σ] ≈ M[σ'] : A[σ].
Proof.
  induction 1; intros; destruct_let_ann; saturate_sub_eq; push_sub; lift_sub_eq; saturate_sub_eq;
    saturate_sub_typ; saturate_sub_eq_IH; reduce_sub_natrec.
  (** In the [a_glob] case the recorded type reaches [Γ] only through
      [saturate_sub_typ], i.e. after [push_sub] has run. *)
  all: try solve [ push_closed; mauto 3 ].
  all: try solve [ mauto 3 ].
  (** A local module: both sides are reduced by [ζ] and meet at the body
      under the two extended substitutions, at the body's type. *)
  1: { pose proof (wf_sub_eq_extend_mod _ _ _ _ _ _ _ H2 H) as Hτ.
    assert (HUl : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (HUr : Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[σ']ᵘ ≈ U[σ']ᵘ) by (eapply sub_preserves_unit; eassumption).
    assert (Hz : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ᵘ U[s]ᵘ ≈ U[s]ᵘ ->
                   Θ ⍮ Ξ ⍮ Γ0 ⊢ ℓₘ U[s]ᵘ in B[q s] ≈ B[s ,,ₘ me_lit U[s]ᵘ] : C[s ,,ₘ me_lit U[s]ᵘ]).
    { intros s Hs HUs; rewrite <- (exp_sub_q_extend_mod B), <- (exp_sub_q_extend_mod C).
      eapply wf_exp_eq_let_mod_zeta;
      [ exact HUs
      | eapply sub_preserves_typ; [ exact H0 | apply wf_sub_q_mod; assumption ]
      | eapply sub_preserves_exp; [ exact H1 | apply wf_sub_q_mod; assumption ] ]. }
    rewrite exp_sub_extend_mod_sub.
    eapply wf_exp_eq_meet;
        [ exact (Hz _ H5 HUl) | exact (IHwf_exp2 _ _ _ Hτ) | exact (Hz _ H6 HUr)
        | eapply sub_preserves_typ; [ exact H0 | eapply wf_sub_eq_left; exact Hτ ]
        | exact (IHwf_exp1 _ _ _ Hτ) ]. }
  (** A member: both sides are reduced by [δ] and meet at the reduct. *)
  1: { assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; eassumption).
    pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ H1)) as Hroot.
    assert (Hd : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ a_mem H[s]ᵐ x ≈ M[s] : A[s]).
    { intros s Hs; pose proof (wf_sub_mod_compat _ _ _ _ _ Hs) as Hcm.
      eapply wf_exp_eq_mem_delta;
        [ eapply me_noargs_sub; eassumption | eapply sub_preserves_modexp; eassumption
        | eapply (member_type_sub_term _ _ Hc); eassumption
        | eapply sub_preserves_typ; eassumption
        | unfold member_unfold in *; eapply member_unfold_sub; eassumption
        | eapply sub_preserves_exp; eassumption ]. }
    eapply wf_exp_eq_meet; [ exact (Hd _ H14) | exact H11 | exact (Hd _ H15) | exact H8 | exact H12 ]. }
  (** A member of an applied module: both sides commute the arguments out. *)
  1: { pose proof (proj1 (modexp_eq_slot_root _ _ _ _ _ H0)) as Hroot.
    assert (Hd : forall s, Θ ⍮ Ξ ⍮ Γ0 ⊢s s : Γ ->
               Θ ⍮ Ξ ⍮ Γ0 ⊢ a_mem H[s]ᵐ x ≈ (apps (member_ref R (pre ++ x :: nil)) args)[s] : A[s]).
    { intros s Hs; pose proof (wf_sub_mod_compat _ _ _ _ _ Hs) as Hcm.
      rewrite apps_sub, member_ref_sub.
      eapply wf_exp_eq_mem_app;
        [ eapply sub_preserves_modexp; eassumption | eapply modexp_spine_sub; eassumption
        | destruct args; [ contradiction H2; reflexivity | discriminate ]
        | eapply sub_preserves_typ; eassumption
        | rewrite <- member_ref_sub, <- apps_sub; eapply sub_preserves_exp; eassumption ]. }
    eapply wf_exp_eq_meet; [ exact (Hd _ H13) | exact H10 | exact (Hd _ H14) | exact H7 | exact H11 ]. }
Qed.

#[export]
Hint Resolve sub_eq_preserves_exp : mctt.

Corollary sub_eq_preserves_typ : forall Θ Ξ Γ Δ A σ σ' i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢s σ ≈ σ' : Δ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Type@i.
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
  assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i) as [i ?] by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Type@i) by mauto 2.
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
  assert (exists i, Θ ⍮ Ξ ⍮ Δ ⊢ A : Type@i) as [i ?] by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ A[σ] ≈ A[σ'] : Type@i) by mauto 2.
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢s Id,,#0 ≈ sb_extend Id (se_var 0) : Γ ▹ A ▹ A[↑]ʷ.
Proof.
  intros * HA.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (HA' : Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Type@i) by (eapply wk_preserves_typ; eassumption).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M[↑]ʷ $ #0 : Π A B.
Proof.
  intros.
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢w ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk M ↑ : exp_wk (Π A B) ↑) as H'
      by (eapply wk_preserves_exp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ : Π A[↑]ʷ B[wk_q ↑]ʷ) by exact H'.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ A[↑]ʷ : Type@i) by (eapply wk_preserves_typ; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ #0 : A[↑]ʷ) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ▹ A[↑]ʷ ⊢ B[wk_q ↑]ʷ : Type@i)
      by (eapply wk_preserves_typ; [ eassumption | eapply wf_wk_q'; eassumption ]).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M[↑]ʷ $ #0 : B[wk_q ↑]ʷ[Id,,#0]) by (eapply wf_app; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B[wk_q ↑]ʷ[Id,,#0] ≈ B : Type@i).
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
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros; mauto 3.
Qed.

Lemma wf_exp_eq_conv : forall Θ Ξ Γ M M' A A' i,
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : Type@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type@i ->
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
  inversion 1; subst; eauto using ctx_wf_gctx, presup_exp_ctx, presup_ext_eq_ctx, wf_gmod_ctx.
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
