From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Domain Evaluation Readback.
From Mctt.Core.Syntactic Require Export System.
Import Domain_Notations.

Generalizable All Variables.

(** The initial environment of a context: each assumption in scope is a
    neutral at its own de Bruijn level, each definition is the value of its
    body, each module slot is the closure of its unit, and each definition
    with a module part is both.  The level of a definition or a slot is
    never given to a neutral.  An assumption or a definition of a
    proposition is the proof [⋆ᵈ], as relevance-directed evaluation has
    it. *)
Inductive initial_env (Θ : gdeps) (Ξ : gstack) : ctx -> env -> Prop :=
| initial_env_nil : initial_env Θ Ξ nil nil
(** An assumption: a fresh variable of its type, the proof [⋆ᵈ] at a
    proposition *)
| initial_env_cons :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     initial_env Θ Ξ (Γ ▹ A) (ρ ↦ relevant_value a (⇑! a (length Γ))))
(** A definition of a relevant type: the value of its body *)
| initial_env_cons_def :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = relevant ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     initial_env Θ Ξ (Γ ▸ A ≔ M) (ρ ↦ m))
(** A definition of a proposition: the proof [⋆ᵈ], its body not
    evaluated *)
| initial_env_cons_def_proof :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_relevance a = propositional ->
     initial_env Θ Ξ (Γ ▸ A ≔ M) (ρ ↦ ⋆ᵈ))
| initial_env_cons_mod :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     initial_env Θ Ξ (Γ ▹ₘ U) (ρ ↦ᵐ h))
(** A definition with a module part: the value of its term and the closure
    of its unit *)
| initial_env_cons_dm :
  `( initial_env Θ Ξ Γ ρ ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ me_lit U ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     initial_env Θ Ξ (Γ ▸ₘ A ≔ M ‖ U) (ρ ↦ᵈ m ‖ h)).

#[export]
Hint Constructors initial_env : mctt.

Lemma functional_initial_env : forall {Θ Ξ} Γ ρ,
    initial_env Θ Ξ Γ ρ ->
    forall ρ',
      initial_env Θ Ξ Γ ρ' ->
      ρ = ρ'.
Proof.
  induction 1; intros ? Hother; inversion_clear Hother; eauto.
  all: erewrite IHinitial_env in *; try eassumption;
    functional_eval_rewrite_clear;
    try congruence;
    eauto.
Qed.

#[export]
Hint Resolve functional_initial_env : mctt.

(** Only an assumption is a neutral in the initial environment, the proof
    [⋆ᵈ] at a proposition; a definition is the value of its body. *)
Lemma initial_env_spec : forall {Θ Ξ} x Γ ρ A,
    initial_env Θ Ξ Γ ρ ->
    List.nth_error Γ x = Some (ce_ass A) ->
    exists a, ρ x = relevant_value a (⇑! a (length Γ - x - 1)).
Proof.
  induction x; intros * Hinit Hlookup;
    dependent destruction Hinit; simpl in *; try discriminate.
  1: eexists; cbn; repeat f_equal; lia.
  all: destruct (IHx _ _ _ Hinit Hlookup) as [a' Ha']; exists a';
    rewrite env_var_cons_succ, Ha'; repeat f_equal; lia.
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

(** The normal form of a term [M] at the value [a] of its type, in the
    environment [ρ] of [s] variables, relevance-directed: a proof is never
    evaluated. *)
Inductive nbe_term (Θ : gdeps) (Ξ : gstack) (s : nat) (ρ : env) (M : exp) (a : domain) : nf -> Prop :=
(** At a proposition: the proof [⋆ⁿ], the term not evaluated *)
| nbe_term_proof :
    domain_relevance a = propositional ->
    nbe_term Θ Ξ s ρ M a ⋆ⁿ
(** At a relevant type: the value of the term, read back at the type *)
| nbe_term_relevant : forall m w,
    domain_relevance a = relevant ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ s ↘ w ->
    nbe_term Θ Ξ s ρ M a w.

#[export]
Hint Constructors nbe_term : mctt.

(** NbE in [Θ ⍮ Ξ ⍮ Γ]: evaluate the type in the initial environment of
    [Γ], then, at a relevant type, the term, and read it back
    ([nbe_term]).  Only [Γ] contributes variables; globals are resolved in
    [Θ ⍮ Ξ]. *)
#[warnings="-cannot-define-projection"]
Record nbe (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M : exp) (A : typ) (w : nf) : Prop := nbe_run
  { (** The initial environment of [Γ] *)
    ρ : env
    (** The value of the type *)
  ; a : domain
  ; nbe_init : initial_env Θ Ξ Γ ρ
  ; nbe_eval_typ : ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a
    (** The normal form of the term at it *)
  ; nbe_result : nbe_term Θ Ξ (length Γ) ρ M a w }.

#[export]
Hint Constructors nbe : mctt.

(** The normal form at a type is unique. *)
Lemma functional_nbe_term : forall {Θ Ξ} s ρ M a w w',
    nbe_term Θ Ξ s ρ M a w ->
    nbe_term Θ Ξ s ρ M a w' ->
    w = w'.
Proof.
  intros * H H'; destruct H; destruct H'; try congruence.
  functional_eval_rewrite_clear; functional_read_rewrite_clear; reflexivity.
Qed.

#[export]
Hint Resolve functional_nbe_term : mctt.

Lemma functional_nbe : forall {Θ Ξ} Γ M A w w',
    nbe Θ Ξ Γ M A w ->
    nbe Θ Ξ Γ M A w' ->
    w = w'.
Proof.
  intros * [ρ a Hi Ha Hw] [ρ' a' Hi' Ha' Hw'].
  functional_initial_env_rewrite_clear; functional_eval_rewrite_clear.
  exact (functional_nbe_term _ _ _ _ _ _ Hw Hw').
Qed.

(** NbE at a relevant type: the term evaluated and read back. *)
Lemma nbe_relevant_inv : forall {Θ Ξ Γ M A w},
    nbe Θ Ξ Γ M A w ->
    forall ρ a, initial_env Θ Ξ Γ ρ -> ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> domain_relevance a = relevant ->
    exists m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m /\ Rnf ⇓ a m in Θ ⍮ Ξ ⍮ length Γ ↘ w.
Proof.
  intros * [ρ0 a0 Hi Ha Hw] ρ a Hi' Ha' Hr.
  functional_initial_env_rewrite_clear; functional_eval_rewrite_clear.
  destruct Hw as [Hp | m w Hr' Hm Hw]; [ congruence | exists m; split; assumption ].
Qed.

(** NbE at a relevant type, from its steps: the environment, the type's
    value, the term's value and its readback, at a relevant type. *)
Lemma nbe_relevant_intro : forall {Θ Ξ Γ M A w ρ a m},
    initial_env Θ Ξ Γ ρ -> ⟦ A ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a -> ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m ->
    Rnf ⇓ a m in Θ ⍮ Ξ ⍮ length Γ ↘ w -> domain_relevance a = relevant ->
    nbe Θ Ξ Γ M A w.
Proof. intros * Hi Ha Hm Hw Hr; econstructor; [ exact Hi | exact Ha | eapply nbe_term_relevant; eassumption ]. Qed.

(** Split every [nbe_term] into its two cases: a proof, discarded when the
    type's value is relevant, and a term evaluated and read back. *)
Ltac invert_nbe_term :=
  repeat match goal with
    | H : nbe_term _ _ _ _ _ _ _ |- _ =>
        let Hp := fresh "Hp" in
        inversion H as [Hp | ? ? Hp ? ?]; subst; clear H; try (cbn in Hp; discriminate)
    end.

#[export]
Hint Resolve functional_nbe : mctt.

Lemma nbe_cumu : forall {Θ Ξ Γ A i W},
    nbe Θ Ξ Γ A Typeω@i W ->
    nbe Θ Ξ Γ A Typeω@(S i) W.
Proof.
  intros * [ρ a Hi Ha Hw].
  simplify_evals.
  (** A universe is no proposition: only the case of a type is left. *)
  destruct Hw as [Hp | m w Hr Hm Hw]; [ cbn in Hp; discriminate |].
  inversion_clear_by_head read_nf; try (cbn in *; discriminate).
  all: econstructor; [ eassumption | mauto | eapply nbe_term_relevant; [ reflexivity | eassumption | mauto ] ].
Qed.

Lemma lift_nbe_ge : forall {Θ Ξ Γ A i j W},
    i <= j ->
    nbe Θ Ξ Γ A Typeω@i W ->
    nbe Θ Ξ Γ A Typeω@j W.
Proof.
  induction 1; mauto using nbe_cumu.
Qed.

Lemma lift_nbe_max_left : forall {Θ Ξ Γ A i i' W},
    nbe Θ Ξ Γ A Typeω@i W ->
    nbe Θ Ξ Γ A Typeω@(max i i') W.
Proof.
  intros.
  assert (i <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

Lemma lift_nbe_max_right : forall {Θ Ξ Γ A i i' W},
    nbe Θ Ξ Γ A Typeω@i' W ->
    nbe Θ Ξ Γ A Typeω@(max i i') W.
Proof.
  intros.
  assert (i' <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

#[export]
Hint Resolve lift_nbe_max_left lift_nbe_max_right : mctt.

Lemma functional_nbe_of_typ : forall {Θ Ξ} Γ A i j W W',
    nbe Θ Ξ Γ A Typeω@i W ->
    nbe Θ Ξ Γ A Typeω@j W' ->
    W = W'.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_of_typ : mctt.


#[warnings="-cannot-define-projection"]
Record nbe_ty (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M : typ) (W : nf) : Prop := nbe_ty_run
  { ρ : env
  ; m : domain
  ; nbe_ty_init : initial_env Θ Ξ Γ ρ
  ; nbe_ty_eval : ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m
  ; nbe_ty_read : Rtyp m in Θ ⍮ Ξ ⍮ length Γ ↘ W }.

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
    nbe Θ Ξ Γ M Typeω@i w ->
    nbe_ty Θ Ξ Γ M w.
Proof.
  intros * [ρ a Hi Ha Hw].
  simplify_evals.
  destruct Hw as [Hp | m w' Hr Hm Hw]; [ cbn in Hp; discriminate |].
  inversion_clear_by_head read_nf; try (cbn in *; discriminate); mauto.
Qed.

#[export]
Hint Resolve functional_nbe_ty nbe_type_to_nbe_ty : mctt.

Ltac functional_nbe_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_nbe equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : nbe ?T ?X ?G ?M ?A ?W, H2 : nbe ?T ?X ?G ?M ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?T ?X ?G ?A Typeω@?i ?W, H2 : nbe ?T ?X ?G ?A Typeω@?j ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]
  | H1 : nbe_ty ?T ?X ?G ?M ?W, H2 : nbe_ty ?T ?X ?G ?M ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  end.
Ltac functional_nbe_rewrite_clear := repeat functional_nbe_rewrite_clear1.
