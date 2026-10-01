From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval : forall {Θ Ξ},
    (forall κ M ρ m1,
        ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall κ A MZ MS m ρ r1,
          ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r1 ->
          forall r2,
            ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r2 ->
            r1 = r2) /\
      (forall m n r1,
          $| m & n | Θ ⍮ Ξ ↘ r1 ->
          forall r2,
            $| m & n | Θ ⍮ Ξ ↘ r2 ->
            r1 = r2) /\
      (forall κ a c args ip r1, eval_pend Θ Ξ κ a c args ip r1 ->
          forall r2, eval_pend Θ Ξ κ a c args ip r2 -> r1 = r2) /\
      (forall κ ip r1, eval_ent Θ Ξ κ ip r1 ->
          forall r2, eval_ent Θ Ξ κ ip r2 -> r1 = r2) /\
      (forall κ j c Γ ρ1, eval_ptele Θ Ξ κ j c Γ ρ1 ->
          forall ρ2, eval_ptele Θ Ξ κ j c Γ ρ2 -> ρ1 = ρ2) /\
      (forall κ n h h1, eval_gne Θ Ξ κ n h h1 ->
          forall h2, eval_gne Θ Ξ κ n h h2 -> h1 = h2) /\
      (forall κ Δ args h h1, eval_fargs Θ Ξ κ Δ args h h1 ->
          forall h2, eval_fargs Θ Ξ κ Δ args h h2 -> h1 = h2).
  Proof.
    intros Θ Ξ; apply eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         lookups it makes agree *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : ?X = Some _, H2 : ?X = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as; subst
        | H1 : ?X = me_frame _ _ _, H2 : ?X = me_frame _ _ _ |- _ =>
            rewrite H1 in H2; injection H2 as; subst
        | H1 : ?X = me_base _, H2 : ?X = me_frame _ _ _ |- _ =>
            rewrite H1 in H2; discriminate H2
        | H1 : ?X = me_frame _ _ _, H2 : ?X = me_base _ |- _ =>
            rewrite H1 in H2; discriminate H2
        | H1 : ?X = me_base _, H2 : ?X = me_base _ |- _ =>
            rewrite H1 in H2; injection H2 as; subst
        | H1 : List.length ?l < ?c, H2 : List.length ?l = ?c |- _ => exfalso; lia
        | H1 : ?n < ?n |- _ => exfalso; lia
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ => specialize (IH _ H); subst
        end;
      try congruence; intuition congruence.
  Qed.

  Corollary functional_eval_exp : forall {Θ Ξ} κ M ρ m1 m2,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); firstorder.
  Qed.

  Corollary functional_eval_natrec : forall {Θ Ξ} κ A MZ MS m ρ r1 r2,
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r1 ->
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_app : forall {Θ Ξ} m n r1 r2,
      $| m & n | Θ ⍮ Ξ ↘ r1 ->
      $| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_pend : forall {Θ Ξ} κ a c args ip r1 r2,
      eval_pend Θ Ξ κ a c args ip r1 -> eval_pend Θ Ξ κ a c args ip r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition eauto. Qed.

  Corollary functional_eval_ent : forall {Θ Ξ} κ ip r1 r2,
      eval_ent Θ Ξ κ ip r1 -> eval_ent Θ Ξ κ ip r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition eauto. Qed.

  Corollary functional_eval_ptele : forall {Θ Ξ} κ j c Γ ρ1 ρ2,
      eval_ptele Θ Ξ κ j c Γ ρ1 -> eval_ptele Θ Ξ κ j c Γ ρ2 -> ρ1 = ρ2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition eauto. Qed.

  Corollary functional_eval_gne : forall {Θ Ξ} κ n h h1 h2,
      eval_gne Θ Ξ κ n h h1 -> eval_gne Θ Ξ κ n h h2 -> h1 = h2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition eauto. Qed.

  (** An evaluated substitution is determined pointwise. *)
  Corollary functional_eval_sub : forall {Θ Ξ} κ σ ρ ρσ1 ρσ2,
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ1 ->
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ2 ->
      env_eq ρσ1 ρσ2.
  Proof.
    intros * H1 H2 x.
    eapply functional_eval_exp; [ apply H1 | apply H2 ].
  Qed.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub
  functional_eval_pend functional_eval_ent functional_eval_ptele functional_eval_gne : mctt.



Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?κ ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?κ ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?κ ⍮ ?ρ ↘ ?r1), H2 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?κ ⍮ ?ρ ↘ ?r2) |- _ =>
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
Proposition eval_exp_natrec_inversion : forall {Θ Ξ} κ A MZ MS M ρ r,
    ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r ->
    exists m,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m /\
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r.
Proof.
  intros * H.
  dependent destruction H.
  eexists; split; eassumption.
Qed.
