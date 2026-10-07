From Stdlib Require Import Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export CtxSub SystemOpt.
From Mctt.Core.Soundness.Weakening Require Export Definitions.
Import Syntax_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A Kripke weakening is a substitution, in the form the gluing proofs use.
    It is not [Γ ⊢w φ : Δ]; see [Definitions]. *)
Lemma kripke_escape : forall Γ Δ φ,
    Γ ⊢k φ : Δ ->
    Γ ⊢s (ι φ) : Δ.
Proof.
  intros * H; induction H;
    saturate_ctx_sub;
    match goal with H : wk_eq _ _ |- _ => rewrite H end.
  - rewrite sb_of_wk_id; eassumption.
  - rewrite sb_of_wk_compose, sb_of_wk_shift.
    saturate_sub.
    rewrite <- (sb_compose_id_left (Wk ⨟ (ι ψ))).
    mauto 4.
Qed.

End Fixed_GCtx.

Ltac saturate_kripke_escape :=
  match_by_head wk_kripke ltac:(fun H => pose proof (kripke_escape _ _ _ H));
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma kripke_id : forall Γ, ⊢ Γ -> Γ ⊢k wk_id : Γ.
Proof. intros; eapply kwk_id; [ mauto 2 | reflexivity ]. Qed.

Lemma kripke_shift : forall Γ A, ⊢ Γ ▹ A -> Γ ▹ A ⊢k ↑ : Γ.
Proof.
  intros * H; eapply kwk_shift;
    [ apply kripke_id; eassumption
    | mauto 3
    | symmetry; apply wk_compose_id_right ].
Qed.

(** Past a definition entry, by forgetting the definition. *)
Lemma kripke_shift_def : forall Γ A M, ⊢ Γ ▸ A ≔ M -> Γ ▸ A ≔ M ⊢k ↑ : Γ.
Proof.
  intros * H; eapply kwk_shift;
    [ apply kripke_id; eassumption
    | mauto 3
    | symmetry; apply wk_compose_id_right ].
Qed.

(** Past a module slot. *)
Lemma kripke_shift_mod : forall Γ U, ⊢ Γ ▹ₘ U -> Γ ▹ₘ U ⊢k ↑ : Γ.
Proof.
  intros * H; eapply kwk_shift;
    [ apply kripke_id; eassumption
    | mauto 3
    | symmetry; apply wk_compose_id_right ].
Qed.

Hint Resolve kripke_id kripke_shift kripke_shift_def kripke_shift_mod : mctt.

(** The codomain may always be coarsened: this is the closure property the
    subtyping cases need, and the reason for the refinement premise. *)
Lemma kripke_ctxsub : forall Γ Δ Δ' φ,
    Γ ⊢k φ : Δ ->
    Δ ⊆ Δ' ->
    Γ ⊢k φ : Δ'.
Proof.
  intros * H ?; destruct H.
  - eapply kwk_id; [ etransitivity; eassumption | eassumption ].
  - eapply kwk_shift; [ eassumption | etransitivity; eassumption | eassumption ].
Qed.

Hint Resolve kripke_ctxsub : mctt.

Lemma kripke_compose : forall Γ Δ Θ φ ψ,
    Γ ⊢k ψ : Δ ->
    Δ ⊢k φ : Θ ->
    Γ ⊢k φ ⊙ ψ : Θ.
Proof.
  intros * Hψ Hφ; revert Γ ψ Hψ.
  induction Hφ; intros ? ? Hψ;
    match goal with H : wk_eq _ _ |- _ => rewrite H end.
  - rewrite wk_compose_id_left.
    eapply kripke_ctxsub; eassumption.
  - rewrite wk_compose_assoc.
    eapply kwk_shift; [ | eassumption | reflexivity ].
    eauto.
Qed.

Hint Resolve kripke_compose : mctt.

(** Every Kripke weakening is [⇑^n], where [n] is the difference of the two
    lengths. The gluing model needs this because readback turns a de Bruijn
    level into an index by counting from the length of the target context. *)
Lemma kripke_shiftn : forall Γ Δ φ,
    Γ ⊢k φ : Δ ->
    length Δ <= length Γ /\ wk_eq φ (wk_shiftn (length Γ - length Δ)).
Proof.
  intros * H; induction H as [ | ? ? ? ? ? ? ? [Hle Hψ] ];
    match goal with H : ctx_sub _ _ _ _ |- _ => pose proof (ctx_sub_length _ _ _ _ H) end;
    match goal with H : wk_eq _ _ |- _ => rewrite H end;
    unfold_ops; simpl in *;
    (split; [ lia | intro x ]).
  - lia.
  - rewrite Hψ; lia.
Qed.

Corollary kripke_preserves_exp : forall Γ Δ A M φ,
    Δ ⊢ M : A ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ : A[φ]ʷ.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk M φ), <- (exp_sub_of_wk A φ); mauto 2.
Qed.

Corollary kripke_preserves_exp_eq : forall Γ Δ A M M' φ,
    Δ ⊢ M ≈ M' : A ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk M φ), <- (exp_sub_of_wk M' φ), <- (exp_sub_of_wk A φ); mauto 2.
Qed.

Corollary kripke_preserves_subtyp : forall Γ Δ A A' φ,
    Δ ⊢ A ⊆ A' ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk A φ), <- (exp_sub_of_wk A' φ); mauto 2.
Qed.

Hint Resolve kripke_preserves_exp kripke_preserves_exp_eq kripke_preserves_subtyp : mctt.

(** [Typeω@i] and [ℕ] are closed, so transporting them is the identity, but
    only up to reduction, which the [simple apply] of [eauto] does not
    perform. Compare [wk_preserves_typ] in [System.Lemmas]. *)

Corollary kripke_preserves_typ : forall Γ Δ A φ i,
    Δ ⊢ A : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq : forall Γ Δ A A' φ i,
    Δ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk A' φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_nat : forall Γ Δ M φ,
    Δ ⊢ M : ℕ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ : ℕ.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ : exp_wk a_nat φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_nat_eq : forall Γ Δ M M' φ,
    Δ ⊢ M ≈ M' : ℕ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : ℕ.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ ≈ exp_wk M' φ : exp_wk a_nat φ) by mauto 2.
  assumption.
Qed.

(** The same for [Level], whose elements the gluing predicate relates by
    readback. *)

Corollary kripke_preserves_level : forall Γ Δ M φ,
    Δ ⊢ M : Level ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ : Level.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ : exp_wk a_level φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_level_eq : forall Γ Δ M M' φ,
    Δ ⊢ M ≈ M' : Level ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : Level.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ ≈ exp_wk M' φ : exp_wk a_level φ) by mauto 2.
  assumption.
Qed.

(** The same for [⊤] and [⊥]. *)

Corollary kripke_preserves_True : forall Γ Δ M φ,
    Δ ⊢ M : ⊤ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ : ⊤.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ : exp_wk a_True φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_False : forall Γ Δ M φ,
    Δ ⊢ M : ⊥ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ : ⊥.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ : exp_wk a_False φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_False_eq : forall Γ Δ M M' φ,
    Δ ⊢ M ≈ M' : ⊥ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ M[φ]ʷ ≈ M'[φ]ʷ : ⊥.
Proof.
  intros.
  assert (Γ ⊢ exp_wk M φ ≈ exp_wk M' φ : exp_wk a_False φ) by mauto 2.
  assumption.
Qed.

(** A universe, as the term [ulvl_tm u], is closed, so it is its own
    transport: the gluing predicates state every equation in it. *)
Fact exp_wk_ulvl_tm : forall u φ, (ulvl_tm u)[φ]ʷ = ulvl_tm u.
Proof. intros [] ?; reflexivity. Qed.

Corollary kripke_preserves_exp_univ : forall Γ Δ A φ u,
    Δ ⊢ A : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ : ulvl_tm u.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ : exp_wk (ulvl_tm u) φ) by mauto 2.
  rewrite exp_wk_ulvl_tm in *; assumption.
Qed.

Corollary kripke_preserves_exp_eq_univ : forall Γ Δ A A' φ u,
    Δ ⊢ A ≈ A' : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : ulvl_tm u.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk A' φ : exp_wk (ulvl_tm u) φ) by mauto 2.
  rewrite exp_wk_ulvl_tm in *; assumption.
Qed.

Hint Resolve kripke_preserves_exp_univ kripke_preserves_exp_eq_univ : mctt.

(** The shapes the gluing predicates state a type in, each in the ambient
    universe of its index: the right-hand sides are closed, so they are their
    own transports — again invisible to [eauto]. *)
Corollary kripke_preserves_univ_eq_nat : forall Γ Δ A φ u,
    Δ ⊢ A ≈ ℕ : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ℕ : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (ℕ : exp)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Corollary kripke_preserves_univ_eq_True : forall Γ Δ A φ u,
    Δ ⊢ A ≈ ⊤ : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ⊤ : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (⊤ : exp)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Corollary kripke_preserves_univ_eq_False : forall Γ Δ A φ u,
    Δ ⊢ A ≈ ⊥ : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ⊥ : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (⊥ : exp)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Corollary kripke_preserves_univ_eq_typ : forall Γ Δ A φ u j,
    Δ ⊢ A ≈ Typeω@j : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Typeω@j : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (Typeω@j)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Corollary kripke_preserves_univ_eq_suniv : forall Γ Δ A φ u t,
    Δ ⊢ A ≈ Type⟨t⟩ : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Type⟨t[φ]ʷ⟩ : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (Type⟨t⟩)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Corollary kripke_preserves_univ_eq_level : forall Γ Δ A φ u,
    Δ ⊢ A ≈ Level : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Level : ulvl_tm u.
Proof.
  intros; assert (Γ ⊢ A[φ]ʷ ≈ (Level : exp)[φ]ʷ : ulvl_tm u) by mauto 2; assumption.
Qed.

Hint Resolve kripke_preserves_univ_eq_nat kripke_preserves_univ_eq_True
             kripke_preserves_univ_eq_False kripke_preserves_univ_eq_typ
             kripke_preserves_univ_eq_suniv kripke_preserves_univ_eq_level : mctt.

(** The two shapes the gluing predicates state a type in: [A ≈ Typeω@j] for the
    universe and [A ≈ ℕ] for [ℕ].  Both right-hand sides are closed, so they are
    their own transports — again invisible to [eauto]. *)

Corollary kripke_preserves_typ_eq_typ : forall Γ Δ A φ i j,
    Δ ⊢ A ≈ Typeω@j : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Typeω@j : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk (a_typ j) φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_suniv : forall Γ Δ A φ i t,
    Δ ⊢ A ≈ Type⟨t⟩ : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Type⟨t[φ]ʷ⟩ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk (a_univ t) φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

(** The readback clause of a type in a small universe, whose equation is at the
    small universe itself. *)
Corollary kripke_preserves_exp_eq_suniv : forall Γ Δ A A' φ t,
    Δ ⊢ A ≈ A' : Type⟨t⟩ ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ A'[φ]ʷ : Type⟨t[φ]ʷ⟩.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk A' φ : exp_wk (a_univ t) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_nat : forall Γ Δ A φ i,
    Δ ⊢ A ≈ ℕ : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ℕ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk a_nat φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_level : forall Γ Δ A φ i,
    Δ ⊢ A ≈ Level : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ Level : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk a_level φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_True : forall Γ Δ A φ i,
    Δ ⊢ A ≈ ⊤ : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ⊤ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk a_True φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_False : forall Γ Δ A φ i,
    Δ ⊢ A ≈ ⊥ : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ⊢ A[φ]ʷ ≈ ⊥ : Typeω@i.
Proof.
  intros.
  assert (Γ ⊢ exp_wk A φ ≈ exp_wk a_False φ : exp_wk (a_typ i) φ) by mauto 2.
  assumption.
Qed.

Hint Resolve kripke_preserves_typ kripke_preserves_typ_eq
             kripke_preserves_nat kripke_preserves_nat_eq
             kripke_preserves_level kripke_preserves_level_eq
             kripke_preserves_True kripke_preserves_False kripke_preserves_False_eq
             kripke_preserves_typ_eq_typ kripke_preserves_typ_eq_nat
             kripke_preserves_typ_eq_suniv kripke_preserves_exp_eq_suniv
             kripke_preserves_typ_eq_True kripke_preserves_typ_eq_False
             kripke_preserves_typ_eq_level : mctt.

(** [q φ] is not a Kripke weakening, since it is not a shift. It is still a
    substitution, which is all the [Π] clauses of the gluing model need to type
    a codomain in the extended context. *)

Corollary kripke_q_escape : forall Γ Δ A φ i,
    Δ ⊢ A : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢s (ι (wk_q φ)) : Δ ▹ A.
Proof.
  intros * ? ?%kripke_escape.
  rewrite sb_q_of_wk, <- (exp_sub_of_wk A φ); mauto 3.
Qed.

Corollary kripke_preserves_exp_q : forall Γ Δ A B M φ i,
    Δ ▹ A ⊢ M : B ->
    Δ ⊢ A : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢ M[wk_q φ]ʷ : B[wk_q φ]ʷ.
Proof.
  intros.
  rewrite <- (exp_sub_of_wk M), <- (exp_sub_of_wk B).
  eauto using kripke_q_escape, sub_preserves_exp.
Qed.

Corollary kripke_preserves_typ_q : forall Γ Δ A B φ i j,
    Δ ▹ A ⊢ B : Typeω@j ->
    Δ ⊢ A : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢ B[wk_q φ]ʷ : Typeω@j.
Proof.
  intros.
  assert (Γ ▹ A[φ]ʷ ⊢ exp_wk B (wk_q φ) : exp_wk (a_typ j) (wk_q φ))
    by (eapply kripke_preserves_exp_q; eassumption).
  assumption.
Qed.

(** The same in any universe: the codomain of a glued [Π] is typed in the
    ambient universe of the index. *)
Corollary kripke_preserves_univ_q : forall Γ Δ A B φ u v,
    Δ ▹ A ⊢ B : ulvl_tm v ->
    Δ ⊢ A : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢ B[wk_q φ]ʷ : ulvl_tm v.
Proof.
  intros * HB HA Hφ.
  assert (Δ ⊢ A : Typeω@(ulvl u))
    by (eapply (lift_exp_uidx _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | exact HA ]).
  assert (Γ ▹ A[φ]ʷ ⊢ exp_wk B (wk_q φ) : exp_wk (ulvl_tm v) (wk_q φ))
    by (eapply kripke_preserves_exp_q; eassumption).
  rewrite exp_wk_ulvl_tm in *; assumption.
Qed.

Hint Resolve kripke_preserves_exp_q kripke_preserves_typ_q kripke_preserves_univ_q : mctt.

(** Extending by the new variable as a term, rather than by the variable
    entry of [q φ]: the two agree on every term, and a type of the extended
    context mentions no slot at the new position. *)
Corollary kripke_q_var_eq : forall Γ Δ A B M φ i,
    Δ ▹ A ⊢ M : B ->
    Δ ⊢ A : Typeω@i ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢ M[ι (φ ⊙ ↑),,#0] ≈ M[wk_q φ]ʷ : B[wk_q φ]ʷ.
Proof.
  intros * HM HA Hφ.
  rewrite <- (exp_sub_of_wk M), <- (exp_sub_of_wk B).
  apply wf_exp_eq_sym.
  pose proof (kripke_q_escape _ _ _ _ _ HA Hφ) as Hq.
  pose proof (wf_sub_dom _ _ _ _ _ Hq) as HC.
  assert (Hk : Γ ▹ A[φ]ʷ ⊢k φ ⊙ ↑ : Δ) by mauto 3.
  pose proof (kripke_escape _ _ _ Hk) as Hs.
  assert (Hs' : Γ ▹ A[φ]ʷ ⊢s ι (φ ⊙ ↑),,#0 : Δ ▹ A).
  { eapply wf_sub_extend; [ exact Hs | exact HA |].
    rewrite exp_sub_of_wk, <- exp_wk_wk; mauto 3. }
  eapply sub_eq_preserves_exp; [ exact HM |].
  constructor; [ exact Hq | exact Hs' |].
  intros x C Hx.
  replace (#x[ι (φ ⊙ ↑),,#0]) with (#x[ι wk_q φ]) by (destruct x; reflexivity).
  apply wf_exp_eq_refl.
  exact (wf_sub_apply _ _ _ _ _ Hq _ _ Hx).
Qed.

(** The same with the domain in any universe. *)
Corollary kripke_q_var_eq_univ : forall Γ Δ A B M φ u,
    Δ ▹ A ⊢ M : B ->
    Δ ⊢ A : ulvl_tm u ->
    Γ ⊢k φ : Δ ->
    Γ ▹ A[φ]ʷ ⊢ M[ι (φ ⊙ ↑),,#0] ≈ M[wk_q φ]ʷ : B[wk_q φ]ʷ.
Proof.
  intros * HM HA Hφ.
  assert (Δ ⊢ A : Typeω@(ulvl u))
    by (eapply (lift_exp_uidx _ _ _ _ u (ulvl u)); [ apply uidx_le_ulvl | exact HA ]).
  eapply kripke_q_var_eq; eassumption.
Qed.

Corollary shift_var_eq : forall Δ A B M u,
    Δ ▹ A ⊢ M : B ->
    Δ ⊢ A : ulvl_tm u ->
    Δ ▹ A ⊢ M[ι ↑,,#0] ≈ M : B.
Proof.
  intros * HM HA.
  assert (Hk : Δ ⊢k wk_id : Δ) by (apply kripke_id; mauto 2).
  pose proof (kripke_q_var_eq_univ _ _ _ _ _ _ _ HM HA Hk) as H.
  rewrite exp_wk_id, !(exp_wk_id_ext _ _ wk_q_id) in H.
  replace (M[ι ↑,,#0]) with (M[ι (wk_id ⊙ ↑),,#0]); [ exact H |].
  apply exp_sub_sb_eq; intros [| x]; reflexivity.
Qed.

(** Both presuppositions, as [saturate_sub] supplies them for [wf_sub]: not
    hints, or [eauto] would cycle against the context introduction rules. *)
Corollary kripke_dom : forall Γ Δ φ, Γ ⊢k φ : Δ -> ⊢ Γ.
Proof. intros * ?%kripke_escape; eapply wf_sub_dom; eassumption. Qed.

Corollary kripke_cod : forall Γ Δ φ, Γ ⊢k φ : Δ -> ⊢ Δ.
Proof. intros * ?%kripke_escape; eapply wf_sub_cod; eassumption. Qed.

End Fixed_GCtx.

#[export]
Hint Resolve kripke_id kripke_shift kripke_shift_def kripke_shift_mod : mctt.
#[export]
Hint Resolve kripke_ctxsub : mctt.
#[export]
Hint Resolve kripke_compose : mctt.
#[export]
Hint Resolve kripke_preserves_exp kripke_preserves_exp_eq kripke_preserves_subtyp : mctt.
#[export]
Hint Resolve kripke_preserves_typ kripke_preserves_typ_eq
kripke_preserves_nat kripke_preserves_nat_eq
kripke_preserves_level kripke_preserves_level_eq
kripke_preserves_typ_eq_typ kripke_preserves_typ_eq_nat
kripke_preserves_typ_eq_suniv kripke_preserves_exp_eq_suniv : mctt.
#[export]
Hint Resolve kripke_preserves_exp_univ kripke_preserves_exp_eq_univ
kripke_preserves_univ_eq_nat kripke_preserves_univ_eq_True
kripke_preserves_univ_eq_False kripke_preserves_univ_eq_typ
kripke_preserves_univ_eq_suniv kripke_preserves_univ_eq_level : mctt.
#[export]
Hint Resolve kripke_preserves_True kripke_preserves_False kripke_preserves_False_eq
kripke_preserves_typ_eq_True kripke_preserves_typ_eq_False
kripke_preserves_typ_eq_level : mctt.
#[export]
Hint Resolve kripke_preserves_exp_q kripke_preserves_typ_q kripke_preserves_univ_q : mctt.
Ltac saturate_kripke :=
  match_by_head wk_kripke ltac:(fun H => pose proof (kripke_dom _ _ _ H);
                                         pose proof (kripke_cod _ _ _ H));
  clear_dups.

