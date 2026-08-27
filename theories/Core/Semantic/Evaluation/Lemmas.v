From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

Section functional_eval.
  Lemma functional_eval :
    (forall M ρ m1,
        {{ ⟦ M ⟧ ρ ↘ m1 }} ->
        forall m2,
          {{ ⟦ M ⟧ ρ ↘ m2 }} ->
          m1 = m2) /\
      (forall A MZ MS m ρ r1,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r1 }} ->
          forall r2,
            {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r2 }} ->
            r1 = r2) /\
      (forall m n r1,
          {{ $| m & n |↘ r1 }} ->
          forall r2,
            {{ $| m & n |↘ r2 }} ->
            r1 = r2).
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    apply eval_mut_ind; intros;
      progressive_inversion; do 2 f_equal; try reflexivity...
  Qed.

  Corollary functional_eval_exp : forall M ρ m1 m2,
      {{ ⟦ M ⟧ ρ ↘ m1 }} ->
      {{ ⟦ M ⟧ ρ ↘ m2 }} ->
      m1 = m2.
  Proof.
    pose proof functional_eval; firstorder.
  Qed.

  Corollary functional_eval_natrec : forall A MZ MS m ρ r1 r2,
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r1 }} ->
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r2 }} ->
      r1 = r2.
  Proof.
    pose proof functional_eval; intuition.
  Qed.

  Corollary functional_eval_app : forall m n r1 r2,
      {{ $| m & n |↘ r1 }} ->
      {{ $| m & n |↘ r2 }} ->
      r1 = r2.
  Proof.
    pose proof functional_eval; intuition.
  Qed.

  (** Determinism says nothing about substitutions, and the omission is forced
      rather than incidental: [eval_sub] is defined pointwise, so determinism
      delivers only [env_eq], and turning that into [eq] would need functional
      extensionality, which this development does without.  So this is where the
      chain of [=]-rewriting stops — see [functional_eval_rewrite_clear1]
      below. *)
  Corollary functional_eval_sub : forall σ ρ ρσ1 ρσ2,
      {{ ⟦ σ ⟧s ρ ↘ ρσ1 }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ2 }} ->
      env_eq ρσ1 ρσ2.
  Proof.
    intros * ? ? x.
    eapply functional_eval_exp; eapply eval_sub_index; eassumption.
  Qed.
End functional_eval.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub : mctt.

Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m1 }}, H2 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m2 }} |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : {{ $| ^?m & ^?n |↘ ^?r1 }}, H2 : {{ $| ^?m & ^?n |↘ ^?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?r1 }}, H2 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is deliberately no [eval_sub] case: [functional_eval_sub] yields
    [env_eq], not [eq], so there is nothing to [replace].  Two evaluations of one
    substitution are reconciled in the PER model instead. *)
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.

(** * Inversion

    [simplify_evals] takes evaluation hypotheses apart wholesale, which is what
    the cases with no substitutions left in them want.  The [ℕ]-[β] rule for
    [succ] wants one hypothesis inverted and the rest left alone: its recursive
    call arrives as an evaluation of the *eliminator*, and what the rule's own
    evaluation needs is the [eval_natrec] inside it.  Naming that inversion keeps
    the rest of the context — six other evaluations, at environments a global
    [cbn] would rewrite — untouched. *)
Proposition eval_exp_natrec_inversion : forall A MZ MS M ρ r,
    {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r }} ->
    exists m,
      {{ ⟦ M ⟧ ρ ↘ m }} /\
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }}.
Proof.
  intros * H.
  dependent destruction H.
  eexists; split; eassumption.
Qed.
