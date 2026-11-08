(** * The Reference Normalizer

    The normalization relations of [Core.Semantic.NbE] implemented
    literally, by the reference evaluator and readback
    ([Reference.Evaluation], [Reference.Readback]): one function per
    relation, one match branch per rule.  None of these relations is
    recursive but the initial environment, on its context: their orders are
    the existence of the Core result ([Extraction.NbE]), from which the
    orders of the evaluations and readbacks they make follow
    ([eval_exp_order_sound], [read_nf_order_sound], ...). *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Reference Require Import Evaluation Readback.
From Mctt.Extraction Require Import NbE.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** The normal form of a term at a value of its type exists. *)
Definition nbe_term_order (Θ : gdeps) (Ξ : gstack) (s : nat) (ρ : env) (M : exp) (a : domain) : Prop :=
  exists w, nbe_term Θ Ξ s ρ M a w.

Lemma nbe_term_order_sound : forall Θ Ξ s ρ M a w, nbe_term Θ Ξ s ρ M a w -> nbe_term_order Θ Ξ s ρ M a.
Proof. intros * H; exists w; exact H. Qed.

#[local]
Hint Resolve initial_env_order_sound nbe_order_sound nbe_ty_order_sound nbe_term_order_sound : mctt.

(** The existence orders, taken apart to the Core derivations they hold,
    at the results computed already *)
#[local]
Ltac nbe_obligation_open :=
  intros; cbv beta in *;
  unfold initial_env_order, nbe_order, nbe_ty_order, nbe_term_order in *;
  repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : nbe _ _ _ _ _ _ |- _ => destruct H
    | H : nbe_ty _ _ _ _ _ |- _ => destruct H
    | H : initial_env _ _ (_ :: _) _ |- _ => inversion H; subst; clear H
    end;
  functional_initial_env_rewrite_clear; functional_eval_rewrite_clear.

#[local]
Ltac nbe_obligation :=
  nbe_obligation_open;
  first [ solve [ eauto with mctt ]
        | solve [ exfalso; eapply evaluated_kind_not_propositional; eassumption ]
        | solve [ invert_nbe_term; functional_eval_rewrite_clear;
                  first [ solve [ eauto with mctt ]
                        | exfalso; eapply evaluated_kind_not_propositional; eassumption ] ]
        | solve [ econstructor; eauto with mctt ]
        | solve [ eapply initial_env_cons_def_proof; eassumption ]
        | solve [ eapply initial_env_cons_def; eassumption ]
        | idtac ].

Section InitialEnvImpl.
  Variables (Θ : gdeps) (Ξ : gstack).

  #[tactic="nbe_obligation",derive(equations=no,eliminator=no)]
  Equations initial_env_impl (G : ctx) (H : initial_env_order Θ Ξ G) : { ρ | initial_env Θ Ξ G ρ } by struct G :=
  | nil, H => exist _ nil _
  (** An assumption: a fresh variable of its type *)
  | ce_ass κ A :: G, H =>
      let (p, Hp) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      exist _ (p ↦ ⇑! a (List.length G) ⦂ entry_type_value a) _
  (** A definition, by the kind of its type *)
  | ce_def A M :: G, H with initial_env_impl G (initial_env_order_tail _ _ _ _ H) := {
    | exist _ p Hp with eval_exp_impl Θ Ξ A p _ := {
      | exist _ a Ha with evaluated_kind_decide (domain_kind a) := {
        | left Hk =>
            let (m, Hm) := eval_exp_impl Θ Ξ M p _ in
            exist _ (p ↦ m ⦂ entry_type_value a) _
        (** A definition of a proposition: its body kept *)
        | right Hk => exist _ (p ↦ ⋆ᵈ⟨M, p⟩ ⦂ entry_type_value a) _ } } }
  | ce_mod U :: G, H =>
      let (p, Hp) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (h, Hh) := eval_modexp_impl Θ Ξ (me_lit U) p _ in
      exist _ (p ↦ᵐ h ⦂ U) _
  | ce_dm A M U :: G, H =>
      let (p, Hp) := initial_env_impl G (initial_env_order_tail _ _ _ _ H) in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (m, Hm) := eval_exp_impl Θ Ξ M p _ in
      let (h, Hh) := eval_modexp_impl Θ Ξ (me_lit U) p _ in
      exist _ (p ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U) _.

  (** The normal form of a term at a value of its type, by its kind *)
  #[tactic="nbe_obligation",derive(equations=no,eliminator=no)]
  Equations nbe_term_impl s ρ M a (H : nbe_term_order Θ Ξ s ρ M a) : { w | nbe_term Θ Ξ s ρ M a w } :=
  | s, ρ, M, a, H with evaluated_kind_decide (domain_kind a) := {
    (** At a proposition: the term kept, read back *)
    | right Hk =>
        let (w, Hw) := read_nf_impl Θ Ξ s ⇓ a ⋆ᵈ⟨M, ρ⟩ _ in
        exist _ w _
    (** At a type of a universe or of levels: its value, read back *)
    | left Hk =>
        let (m, Hm) := eval_exp_impl Θ Ξ M ρ _ in
        let (w, Hw) := read_nf_impl Θ Ξ s ⇓ a m _ in
        exist _ w _ }.

  (** NbE of a term: the initial environment, the type's value, then the
      term's normal form at it *)
  #[tactic="nbe_obligation",derive(equations=no,eliminator=no)]
  Equations nbe_impl G M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } :=
  | G, M, A, H =>
      let (p, Hp) := initial_env_impl G (nbe_order_init _ _ _ _ _ H) in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (w, Hw) := nbe_term_impl (List.length G) p M a _ in
      exist _ w (nbe_run _ _ _ _ _ _ p a Hp Ha Hw).

  (** NbE of a type: the initial environment, the type's value, read back
      as a type *)
  #[tactic="nbe_obligation",derive(equations=no,eliminator=no)]
  Equations nbe_ty_impl G A (H : nbe_ty_order Θ Ξ G A) : { w | nbe_ty Θ Ξ G A w } :=
  | G, A, H =>
      let (p, Hp) := initial_env_impl G (nbe_ty_order_init _ _ _ _ H) in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (w, Hw) := read_typ_impl Θ Ξ (List.length G) a _ in
      exist _ w (nbe_ty_run _ _ _ _ _ p a Hp Ha Hw).
End InitialEnvImpl.

(** The implementations compute the Core results: they are sound by
    construction, and the results are unique. *)

Lemma initial_env_impl_complete : forall Θ Ξ G ρ (H : initial_env_order Θ Ξ G),
    initial_env Θ Ξ G ρ -> proj1_sig (initial_env_impl Θ Ξ G H) = ρ.
Proof.
  intros * Hi; destruct (initial_env_impl Θ Ξ G H) as [ρ' Hi']; cbn.
  exact (functional_initial_env _ _ Hi' _ Hi).
Qed.

Lemma nbe_impl_complete : forall Θ Ξ G M A w (H : nbe_order Θ Ξ G M A),
    nbe Θ Ξ G M A w -> proj1_sig (nbe_impl Θ Ξ G M A H) = w.
Proof.
  intros * Hn; destruct (nbe_impl Θ Ξ G M A H) as [w' Hn']; cbn.
  exact (functional_nbe _ _ _ _ _ Hn' Hn).
Qed.

Lemma nbe_ty_impl_complete : forall Θ Ξ G A w (H : nbe_ty_order Θ Ξ G A),
    nbe_ty Θ Ξ G A w -> proj1_sig (nbe_ty_impl Θ Ξ G A H) = w.
Proof.
  intros * Hn; destruct (nbe_ty_impl Θ Ξ G A H) as [w' Hn']; cbn.
  exact (functional_nbe_ty _ _ _ _ Hn' Hn).
Qed.
