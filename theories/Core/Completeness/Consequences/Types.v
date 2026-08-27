(** * Consequences of Completeness: types are rigid

    Distinct type constructors are never judgmentally equal, and [Type@i ≈ Type@j]
    forces [i = j].  Each proof reads the judgment at the initial environment and
    inverts the resulting [per_univ]; only the variable-against-variable case needs
    work, since there the values are neutrals whose levels must be turned back
    into indices. *)

From Stdlib Require Import Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

(** A variable of a context evaluates, in that context's initial environment, to
    the neutral at its own level. *)
Lemma eval_var_at_initial_env : forall {Γ x i ρ a},
    initial_env Γ ρ ->
    {{ ⟦ #x ⟧ ρ ↘ a }} ->
    {{ Γ ⊢ #x : Type@i }} ->
    x < length Γ /\ exists b, a = d{{{ ⇑! b (length Γ - x - 1) }}}.
Proof.
  intros * Hρ Hev Hx.
  destruct (wf_vlookup_inversion Hx) as [A [Hlookup _]].
  pose proof (initial_env_spec _ _ _ _ Hρ Hlookup) as [b Heq].
  split; [ mauto 2 |].
  exists b.
  eapply functional_eval_exp; [ exact Hev | apply eval_exp_var_eq; exact Heq ].
Qed.

Lemma exp_eq_typ_implies_eq_level : forall {Γ i j k},
    {{ Γ ⊢ Type@i ≈ Type@j : Type@k }} ->
    i = j.
Proof.
  intros * H%completeness_fundamental_exp_eq.
  destruct (rel_typ_under_ctx_at_initial_env H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a = d{{{ 𝕌@i }}}) as ->
      by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ]).
  assert (a' = d{{{ 𝕌@j }}}) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  invert_per_univ_elem HR; congruence.
Qed.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level : mctt.

Inductive is_typ_constr : typ -> Prop :=
| typ_is_typ_constr : forall i, is_typ_constr {{{ Type@i }}}
| nat_is_typ_constr : is_typ_constr {{{ ℕ }}}
| pi_is_typ_constr : forall A B, is_typ_constr {{{ Π A B }}}
| var_is_typ_constr : forall x, is_typ_constr {{{ #x }}}
.
#[export]
Hint Constructors is_typ_constr : mctt.

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var : forall Γ A x i,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ #x : Type@i }} ->
    A = {{{ #x }}}.
Proof.
  intros * Histyp H.
  assert {{ Γ ⊢ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢ #x : Type@i }} by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct (eval_var_at_initial_env Hρ Ha' ltac:(eassumption)) as [Hxlt [b ->]].
  (** Only the variable case survives: [⇑! b _] has no other constructor to be
      related to. *)
  destruct Histyp;
    [ assert (a = d{{{ 𝕌@i0 }}}) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = d{{{ ℕ }}}) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | idtac
    | destruct (eval_var_at_initial_env Hρ Ha ltac:(eassumption)) as [? [? ->]] ];
    invert_per_univ_elem HR.
  - (** [Π A B] evaluates to a [Π]-value once its domain does. *)
    match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
  - (** Two neutral variables related in [per_bot]: read both back at
        [length Γ] and compare the indices they produce. *)
    f_equal.
    enough (length Γ - x0 - 1 = length Γ - x - 1) by lia.
    match_by_head1 per_bot ltac:(fun H => destruct (H (length Γ)) as [? []]).
    match_by_head read_ne ltac:(fun H => directed dependent destruction H).
    lia.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mctt.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ : forall Γ A i j,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ Type@i : Type@j }} ->
    A = {{{ Type@i }}}.
Proof.
  intros * Histyp H.
  assert {{ Γ ⊢ A : Type@j }} by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = d{{{ 𝕌@i }}}) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_typ ]).
  destruct Histyp;
    [ assert (a = d{{{ 𝕌@i0 }}}) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | assert (a = d{{{ ℕ }}}) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_nat ])
    | idtac
    | destruct (eval_var_at_initial_env Hρ Ha ltac:(eassumption)) as [? [? ->]] ];
    invert_per_univ_elem HR.
  - congruence.
  - match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mctt.

Theorem is_typ_constr_and_exp_eq_nat_implies_eq_nat : forall Γ A j,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ ℕ : Type@j }} ->
    A = {{{ ℕ }}}.
Proof.
  intros * Histyp H.
  assert {{ Γ ⊢ A : Type@j }} by mauto 2.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ H) as Hsem.
  destruct (rel_typ_under_ctx_at_initial_env Hsem)
    as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  assert (a' = d{{{ ℕ }}}) as ->
      by (eapply functional_eval_exp; [ exact Ha' | apply eval_exp_nat ]).
  destruct Histyp;
    [ assert (a = d{{{ 𝕌@i }}}) as ->
        by (eapply functional_eval_exp; [ exact Ha | apply eval_exp_typ ])
    | reflexivity
    | idtac
    | destruct (eval_var_at_initial_env Hρ Ha ltac:(eassumption)) as [? [? ->]] ];
    invert_per_univ_elem HR.
  match_by_head eval_exp ltac:(fun H => directed dependent destruction H).
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mctt.
