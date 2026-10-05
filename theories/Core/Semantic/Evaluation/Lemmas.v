From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval : forall {Θ},
    (forall M ρ m1,
        ⟦ M ⟧ Θ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ Θ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall A MZ MS m ρ r1,
          ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r1 ->
          forall r2,
            ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r2 ->
            r1 = r2) /\
      (forall m n r1,
          $| m & n | Θ ↘ r1 ->
          forall r2,
            $| m & n | Θ ↘ r2 ->
            r1 = r2) /\
      (forall Ms ρ ms1, ⟦ Ms ⟧* Θ ⍮ ρ ↘ ms1 -> forall ms2, ⟦ Ms ⟧* Θ ⍮ ρ ↘ ms2 -> ms1 = ms2) /\
      (forall m args r1, $*| m & args | Θ ↘ r1 -> forall r2, $*| m & args | Θ ↘ r2 -> r1 = r2) /\
      (forall H ρ h1, ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h1 -> forall h2, ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐ| h & n | Θ ↘ r1 -> forall r2, $ᵐ| h & n | Θ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜ x Θ ↘ r1 -> forall r2, h ·ₜ x Θ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘ y Θ ↘ r1 -> forall r2, h ·ₘ y Θ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ* ch Θ ↘ r1 -> forall r2, h ·ₜ* ch Θ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ* ch Θ ↘ r1 -> forall r2, h ·ₘ* ch Θ ↘ r2 -> r1 = r2).
  Proof.
    intros Θ; apply eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global or a module agree, and two neutral
         scrutinees of [efq] that are equal have equal parts; an induction
         hypothesis is never spent on the premise it is about *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : GlobalCtx.gc_const Θ ?p = Some _, H2 : GlobalCtx.gc_const Θ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : GlobalCtx.gc_unit Θ ?p = Some _, H2 : GlobalCtx.gc_unit Θ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : eval_selc _ _ nil _ |- _ => inversion H
        end;
      cbn [gu_params dm_unsat] in *; try congruence; try lia; intuition (try congruence; try lia).
  Qed.

  Corollary functional_eval_exp : forall {Θ} M ρ m1 m2,
      ⟦ M ⟧ Θ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ Θ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ; pose proof (@functional_eval Θ); firstorder.
  Qed.

  Corollary functional_eval_natrec : forall {Θ} A MZ MS m ρ r1 r2,
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r1 ->
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ; pose proof (@functional_eval Θ); intuition.
  Qed.

  Corollary functional_eval_app : forall {Θ} m n r1 r2,
      $| m & n | Θ ↘ r1 ->
      $| m & n | Θ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ; pose proof (@functional_eval Θ); intuition.
  Qed.

  (** An evaluated substitution is determined pointwise. *)
  Corollary functional_eval_modexp : forall {Θ} H ρ h1 h2,
      ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h1 ->
      ⟦ H ⟧ᵐ Θ ⍮ ρ ↘ h2 ->
      h1 = h2.
  Proof.
    intros Θ; pose proof (@functional_eval Θ); intuition.
  Qed.

  Corollary functional_eval_sub : forall {Θ} σ ρ ρσ1 ρσ2,
      ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ1 ->
      ⟦ σ ⟧s Θ ⍮ ρ ↘ ρσ2 ->
      env_eq ρσ1 ρσ2.
  Proof.
    intros * H1 H2 x; specialize (H1 x); specialize (H2 x).
    destruct (σ x); cbn in H1, H2.
    - congruence.
    - destruct H1 as (m1 & -> & H1), H2 as (m2 & -> & H2); f_equal; eapply functional_eval_exp; eassumption.
    - destruct H1 as (m1 & -> & H1), H2 as (m2 & -> & H2); f_equal; eapply functional_eval_modexp; eassumption.
  Qed.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_modexp functional_eval_sub : mctt.



Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ↘ ?r1), H2 : ($| ?m & ?n | ?T ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?ρ ↘ ?r1), H2 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is no [eval_sub] case: [functional_eval_sub] gives only pointwise
    equality, so there is nothing to [replace]. *)
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.

(** * Inversion

    [simplify_evals] inverts all evaluation hypotheses at once.  The [ℕ]-[β]
    rule for [succ] needs a single one inverted: its recursive call arrives as
    an evaluation of the eliminator, and the rule needs the [eval_natrec]
    inside it.  [eval_exp_natrec_inversion] does just that and leaves the other
    hypotheses untouched. *)
Proposition eval_exp_natrec_inversion : forall {Θ} A MZ MS M ρ r,
    ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r ->
    exists m,
      ⟦ M ⟧ Θ ⍮ ρ ↘ m /\
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ ρ ↘ r.
Proof.
  intros * H.
  dependent destruction H.
  eexists; split; eassumption.
Qed.
