From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Domain Evaluation Readback.
From Mctt.Core.Syntactic Require Export System.
Import Domain_Notations.

Generalizable All Variables.

(** The initial environment of a context: every variable in scope is a
    neutral at its own level. *)
Inductive initial_env (Θ : gdeps) (Ξ : gstack) : ctx -> env -> Prop :=
| initial_env_nil : initial_env Θ Ξ nil nil
| initial_env_cons :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ me_top ⍮ ρ ↘ a ->
     initial_env Θ Ξ (A :: Γ) (ρ ↦ ⇑! a (length Γ))).

#[export]
Hint Constructors initial_env : mctt.

Lemma functional_initial_env : forall {Θ Ξ} Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall ρ',
      initial_env Θ Ξ Γ ρ' ->
      ρ = ρ'.
Proof.
  induction 1; intros ? Hother; inversion_clear Hother; eauto.
  erewrite IHinitial_env in *; try eassumption;
    functional_eval_rewrite_clear;
    eauto.
Qed.

#[export]
Hint Resolve functional_initial_env : mctt.

Lemma initial_env_spec : forall {Θ Ξ} x Γ ρ A,
    initial_env Θ Ξ Γ ρ ->
    Γ ∋ #x : A ->
    exists a, ρ x = ⇑! a (length Γ - x - 1).
Proof.
  induction x; intros * Hinit Hlookup;
    dependent destruction Hlookup; dependent destruction Hinit; simpl.
  - eexists; cbn; repeat f_equal; lia.
  - destruct (IHx _ _ _ Hinit Hlookup) as [a' Ha']; exists a'.
    cbn; unfold env_var in *; rewrite Ha'; repeat f_equal; lia.
Qed.

#[export]
Hint Resolve initial_env_spec : mctt.

Ltac functional_initial_env_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_initial_env equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : initial_env ?T ?X ?G ?ρ, H2 : initial_env ?T ?X ?G ?ρ' |- _ =>
      clean replace ρ' with ρ by first [solve [mauto 2] | tactic_error ρ' ρ]; clear H2
  end.
Ltac functional_initial_env_rewrite_clear := repeat functional_initial_env_rewrite_clear1.

(** NbE in [Θ ⍮ Ξ ⍮ Γ]: only [Γ] has variables; parameters and globals are
    evaluated through [Θ ⍮ Ξ]. *)
Inductive nbe (Θ : gdeps) (Ξ : gstack) : ctx -> exp -> typ -> nf -> Prop :=
| nbe_run :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ me_top ⍮ ρ ↘ a ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ me_top ⍮ ρ ↘ m ->
     Rnf ⇓ a m in Θ ⍮ Ξ ⍮ length Γ ↘ w ->
     nbe Θ Ξ Γ M A w ).

#[export]
Hint Constructors nbe : mctt.

Lemma functional_nbe : forall {Θ Ξ} Γ M A w w',
    nbe Θ Ξ Γ M A w ->
    nbe Θ Ξ Γ M A w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

#[export]
Hint Resolve functional_nbe : mctt.

Lemma nbe_cumu : forall {Θ Ξ Γ A i W},
    nbe Θ Ξ Γ A Type@i W ->
    nbe Θ Ξ Γ A Type@(S i) W.
Proof.
  inversion_clear 1.
  simplify_evals.
  inversion_clear_by_head read_nf.
  mauto.
Qed.

Lemma lift_nbe_ge : forall {Θ Ξ Γ A i j W},
    i <= j ->
    nbe Θ Ξ Γ A Type@i W ->
    nbe Θ Ξ Γ A Type@j W.
Proof.
  induction 1; mauto using nbe_cumu.
Qed.

Lemma lift_nbe_max_left : forall {Θ Ξ Γ A i i' W},
    nbe Θ Ξ Γ A Type@i W ->
    nbe Θ Ξ Γ A Type@(max i i') W.
Proof.
  intros.
  assert (i <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

Lemma lift_nbe_max_right : forall {Θ Ξ Γ A i i' W},
    nbe Θ Ξ Γ A Type@i' W ->
    nbe Θ Ξ Γ A Type@(max i i') W.
Proof.
  intros.
  assert (i' <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

#[export]
Hint Resolve lift_nbe_max_left lift_nbe_max_right : mctt.

Lemma functional_nbe_of_typ : forall {Θ Ξ} Γ A i j W W',
    nbe Θ Ξ Γ A Type@i W ->
    nbe Θ Ξ Γ A Type@j W' ->
    W = W'.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_of_typ : mctt.


Inductive nbe_ty (Θ : gdeps) (Ξ : gstack) : ctx -> typ -> nf -> Prop :=
| nbe_ty_run :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ me_top ⍮ ρ ↘ m ->
     Rtyp m in Θ ⍮ Ξ ⍮ length Γ ↘ W ->
     nbe_ty Θ Ξ Γ M W ).

#[export]
Hint Constructors nbe_ty : mctt.

Lemma functional_nbe_ty : forall {Θ Ξ} Γ M w w',
    nbe_ty Θ Ξ Γ M w ->
    nbe_ty Θ Ξ Γ M w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

Lemma nbe_type_to_nbe_ty : forall {Θ Ξ} Γ M i w,
    nbe Θ Ξ Γ M Type@i w ->
    nbe_ty Θ Ξ Γ M w.
Proof.
  intros. progressive_inversion.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_ty nbe_type_to_nbe_ty : mctt.

Ltac functional_nbe_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_nbe equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : nbe ?T ?X ?G ?M ?A ?W, H2 : nbe ?T ?X ?G ?M ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?T ?X ?G ?A Type@?i ?W, H2 : nbe ?T ?X ?G ?A Type@?j ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]
  | H1 : nbe_ty ?T ?X ?G ?M ?W, H2 : nbe_ty ?T ?X ?G ?M ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  end.
Ltac functional_nbe_rewrite_clear := repeat functional_nbe_rewrite_clear1.
