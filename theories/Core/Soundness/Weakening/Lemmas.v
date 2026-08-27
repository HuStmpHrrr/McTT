From Stdlib Require Import Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Export CtxSub SystemOpt.
From Mctt.Core.Soundness.Weakening Require Export Definitions.
Import Syntax_Notations Wk_Notations.

(** In the form the gluing proofs use it: a Kripke weakening is a substitution.  Not [Γ ⊢w φ : Δ] — see [Definitions]. *)
Lemma kripke_escape : forall Γ Δ φ,
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢s ^(ι φ) : Δ }}.
Proof.
  intros * H; induction H;
    saturate_ctx_sub;
    match goal with H : wk_eq _ _ |- _ => rewrite H end.
  - rewrite sb_of_wk_id; eassumption.
  - rewrite sb_of_wk_compose, sb_of_wk_shift.
    saturate_sub.
    rewrite <- (sb_compose_id_left {{{ Wk ⨟ ^(ι ψ) }}}).
    mauto 4.
Qed.

Ltac saturate_kripke_escape :=
  match_by_head wk_kripke ltac:(fun H => pose proof (kripke_escape _ _ _ H));
  clear_dups.

Lemma kripke_id : forall Γ, {{ ⊢ Γ }} -> {{ Γ ⊢k wk_id : Γ }}.
Proof. intros; eapply kwk_id; [ mauto 2 | reflexivity ]. Qed.

Lemma kripke_shift : forall Γ A, {{ ⊢ Γ , A }} -> {{ Γ , A ⊢k ↑ : Γ }}.
Proof.
  intros * H; eapply kwk_shift;
    [ apply kripke_id; eassumption
    | mauto 3
    | symmetry; apply wk_compose_id_right ].
Qed.

#[export]
Hint Resolve kripke_id kripke_shift : mctt.

(** The codomain may always be coarsened: this is the closure property the
    subtyping cases need, and the reason for the refinement premise. *)
Lemma kripke_ctxsub : forall Γ Δ Δ' φ,
    {{ Γ ⊢k φ : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢k φ : Δ' }}.
Proof.
  intros * H ?; destruct H.
  - eapply kwk_id; [ etransitivity; eassumption | eassumption ].
  - eapply kwk_shift; [ eassumption | etransitivity; eassumption | eassumption ].
Qed.

#[export]
Hint Resolve kripke_ctxsub : mctt.

Lemma kripke_compose : forall Γ Δ Θ φ ψ,
    {{ Γ ⊢k ψ : Δ }} ->
    {{ Δ ⊢k φ : Θ }} ->
    {{ Γ ⊢k φ ⊙ ψ : Θ }}.
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

#[export]
Hint Resolve kripke_compose : mctt.

(** Equivalently: every Kripke weakening is [⇑^n], and
    [n] is the difference of the two lengths.  The gluing model needs this
    because a readback turns a de Bruijn *level* into an index by counting from
    the length of the context it lands in. *)
Lemma kripke_shiftn : forall Γ Δ φ,
    {{ Γ ⊢k φ : Δ }} ->
    length Δ <= length Γ /\ wk_eq φ (wk_shiftn (length Γ - length Δ)).
Proof.
  intros * H; induction H as [ | ? ? ? ? ? ? ? [Hle Hψ] ];
    match goal with H : ctx_sub _ _ |- _ => pose proof (ctx_sub_length _ _ H) end;
    match goal with H : wk_eq _ _ |- _ => rewrite H end;
    unfold_ops; simpl in *;
    (split; [ lia | intro x ]).
  - lia.
  - rewrite Hψ; lia.
Qed.

Corollary kripke_preserves_exp : forall Γ Δ A M φ,
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ M⟨φ⟩ : A⟨φ⟩ }}.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk M φ), <- (exp_sub_of_wk A φ); mauto 2.
Qed.

Corollary kripke_preserves_exp_eq : forall Γ Δ A M M' φ,
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }}.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk M φ), <- (exp_sub_of_wk M' φ), <- (exp_sub_of_wk A φ); mauto 2.
Qed.

Corollary kripke_preserves_subtyp : forall Γ Δ A A' φ,
    {{ Δ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ A⟨φ⟩ ⊆ A'⟨φ⟩ }}.
Proof.
  intros * ? ?%kripke_escape.
  rewrite <- (exp_sub_of_wk A φ), <- (exp_sub_of_wk A' φ); mauto 2.
Qed.

#[export]
Hint Resolve kripke_preserves_exp kripke_preserves_exp_eq kripke_preserves_subtyp : mctt.

(** [Type@i] and [ℕ] are closed, so transporting them is the identity — but
    only up to reduction, which [eauto]'s [simple apply] does not do.  Compare
    [wk_preserves_typ] in [System.Lemmas]. *)

Corollary kripke_preserves_typ : forall Γ Δ A φ i,
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ A⟨φ⟩ : Type@i }}.
Proof.
  intros.
  assert (wf_exp Γ (exp_wk (a_typ i) φ) (exp_wk A φ)) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq : forall Γ Δ A A' φ i,
    {{ Δ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_wk (a_typ i) φ) (exp_wk A φ) (exp_wk A' φ)) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_nat : forall Γ Δ M φ,
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ M⟨φ⟩ : ℕ }}.
Proof.
  intros.
  assert (wf_exp Γ (exp_wk a_nat φ) (exp_wk M φ)) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_nat_eq : forall Γ Δ M M' φ,
    {{ Δ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : ℕ }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_wk a_nat φ) (exp_wk M φ) (exp_wk M' φ)) by mauto 2.
  assumption.
Qed.

(** The two shapes the gluing predicates state a type in: [A ≈ Type@j] for the
    universe and [A ≈ ℕ] for [ℕ].  Both right-hand sides are closed, so they are
    their own transports — again invisible to [eauto]. *)

Corollary kripke_preserves_typ_eq_typ : forall Γ Δ A φ i j,
    {{ Δ ⊢ A ≈ Type@j : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ A⟨φ⟩ ≈ Type@j : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_wk (a_typ i) φ) (exp_wk A φ) (exp_wk (a_typ j) φ)) by mauto 2.
  assumption.
Qed.

Corollary kripke_preserves_typ_eq_nat : forall Γ Δ A φ i,
    {{ Δ ⊢ A ≈ ℕ : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ ⊢ A⟨φ⟩ ≈ ℕ : Type@i }}.
Proof.
  intros.
  assert (wf_exp_eq Γ (exp_wk (a_typ i) φ) (exp_wk A φ) (exp_wk a_nat φ)) by mauto 2.
  assumption.
Qed.

#[export]
Hint Resolve kripke_preserves_typ kripke_preserves_typ_eq
             kripke_preserves_nat kripke_preserves_nat_eq
             kripke_preserves_typ_eq_typ kripke_preserves_typ_eq_nat : mctt.

(** [q φ] is *not* a Kripke weakening — it is not a shift.  It is still a
    substitution, though, and that is all the [Π] clauses of the gluing model
    need in order to type a codomain in the extended context. *)

Corollary kripke_q_escape : forall Γ Δ A φ i,
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ , A⟨φ⟩ ⊢s ^(ι (wk_q φ)) : Δ , A }}.
Proof.
  intros * ? ?%kripke_escape.
  rewrite sb_q_of_wk, <- (exp_sub_of_wk A φ); mauto 3.
Qed.

Corollary kripke_preserves_exp_q : forall Γ Δ A B M φ i,
    {{ Δ , A ⊢ M : B }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ , A⟨φ⟩ ⊢ M⟨wk_q φ⟩ : B⟨wk_q φ⟩ }}.
Proof.
  intros.
  rewrite <- (exp_sub_of_wk M), <- (exp_sub_of_wk B).
  eauto using kripke_q_escape, sub_preserves_exp.
Qed.

Corollary kripke_preserves_typ_q : forall Γ Δ A B φ i j,
    {{ Δ , A ⊢ B : Type@j }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢k φ : Δ }} ->
    {{ Γ , A⟨φ⟩ ⊢ B⟨wk_q φ⟩ : Type@j }}.
Proof.
  intros.
  assert (wf_exp {{{ Γ , A⟨φ⟩ }}} (exp_wk (a_typ j) (wk_q φ)) (exp_wk B (wk_q φ)))
    by (eapply kripke_preserves_exp_q; eassumption).
  assumption.
Qed.

#[export]
Hint Resolve kripke_preserves_exp_q kripke_preserves_typ_q : mctt.

(** Both presuppositions, as [saturate_sub] supplies them for [wf_sub]: not
    hints, or [eauto] would cycle against the context introduction rules. *)
Corollary kripke_dom : forall Γ Δ φ, {{ Γ ⊢k φ : Δ }} -> {{ ⊢ Γ }}.
Proof. intros * ?%kripke_escape; eapply wf_sub_dom; eassumption. Qed.

Corollary kripke_cod : forall Γ Δ φ, {{ Γ ⊢k φ : Δ }} -> {{ ⊢ Δ }}.
Proof. intros * ?%kripke_escape; eapply wf_sub_cod; eassumption. Qed.

Ltac saturate_kripke :=
  match_by_head wk_kripke ltac:(fun H => pose proof (kripke_dom _ _ _ H);
                                         pose proof (kripke_cod _ _ _ H));
  clear_dups.
