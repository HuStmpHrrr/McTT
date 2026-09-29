From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval : forall Θ Ξ,
    (forall M ρ m1,
        ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall A MZ MS m ρ r1,
          ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2,
            ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
            r1 = r2) /\
      (forall m n r1,
          $| m & n | Θ ⍮ Ξ ↘ r1 ->
          forall r2,
            $| m & n | Θ ⍮ Ξ ↘ r2 ->
            r1 = r2).
  Proof.
    intros Θ Ξ; apply eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global agree *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : GlobalCtx.gc_resolve Θ Ξ ?p = Some _, H2 : GlobalCtx.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ => specialize (IH _ H); subst
        end;
      try congruence; intuition congruence.
  Qed.

  Corollary functional_eval_exp : forall Θ Ξ M ρ m1 m2,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (functional_eval Θ Ξ); firstorder.
  Qed.

  Corollary functional_eval_natrec : forall Θ Ξ A MZ MS m ρ r1 r2,
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_app : forall Θ Ξ m n r1 r2,
      $| m & n | Θ ⍮ Ξ ↘ r1 ->
      $| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (functional_eval Θ Ξ); intuition.
  Qed.

  (** An evaluated substitution is determined at every variable both results
      have: [eval_sub] fixes the values, [per_ctx] the number of them. *)
  Corollary functional_eval_sub : forall Θ Ξ σ ρ ρσ1 ρσ2 x m1 m2,
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ1 ->
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ2 ->
      env_var ρσ1 x = Some m1 ->
      env_var ρσ2 x = Some m2 ->
      m1 = m2.
  Proof.
    intros * H1 H2 Hx1 Hx2.
    eapply functional_eval_exp; [ apply H1 | apply H2 ]; eassumption.
  Qed.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub : mctt.



Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is deliberately no [eval_sub] case: [functional_eval_sub] is
    pointwise, so there is nothing to [replace]. *)
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.

(** * Inversion

    [simplify_evals] takes evaluation hypotheses apart wholesale, which is what
    the cases with no substitutions left in them want.  The [ℕ]-[β] rule for
    [succ] wants one hypothesis inverted and the rest left alone: its recursive
    call arrives as an evaluation of the *eliminator*, and what the rule's own
    evaluation needs is the [eval_natrec] inside it.  Naming that inversion keeps
    the rest of the context — six other evaluations, at environments a global
    [cbn] would rewrite — untouched. *)
Proposition eval_exp_natrec_inversion : forall Θ Ξ A MZ MS M ρ r,
    ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    exists m,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m /\
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
Proof.
  intros * H.
  dependent destruction H.
  eexists; split; eassumption.
Qed.
