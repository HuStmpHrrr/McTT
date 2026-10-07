From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval : forall {Θ Ξ},
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
            r1 = r2) /\
      (forall Ms ρ ms1, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> forall ms2, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2) /\
      (forall m args r1, $*| m & args | Θ ⍮ Ξ ↘ r1 -> forall r2, $*| m & args | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall H ρ h1, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐ| h & n | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐ| h & n | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜ x Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ x Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘ y Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ y Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ* ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ* ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ* ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ* ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2).
  Proof.
    intros Θ Ξ; apply eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global or a module agree, and two neutral
         scrutinees of [efq] that are equal have equal parts; an induction
         hypothesis is never spent on the premise it is about *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : Members.gc_resolve Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _ _),
          H2 : forall U r, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U r) |- _ =>
            exfalso; exact (H2 _ _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : eval_selc _ _ _ nil _ |- _ => inversion H
        end;
      cbn [gu_params] in *; try congruence; try lia; intuition (try congruence; try lia).
  Qed.

  Corollary functional_eval_exp : forall {Θ Ξ} M ρ m1 m2,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); firstorder.
  Qed.

  Corollary functional_eval_natrec : forall {Θ Ξ} A MZ MS m ρ r1 r2,
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
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

  (** An evaluated substitution is determined pointwise. *)
  Corollary functional_eval_modexp : forall {Θ Ξ} H ρ h1 h2,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h1 ->
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h2 ->
      h1 = h2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_benv : forall {Θ Ξ} ρ Φ ρ1 ρ2,
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 ->
      ρ1 = ρ2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_sub : forall {Θ Ξ} σ ρ ρσ1 ρσ2,
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ1 ->
      ⟦ σ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ2 ->
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
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦rec ?m return ?A | zero -> ?MZ | succ -> ?MS end ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
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
Proposition eval_exp_natrec_inversion : forall {Θ Ξ} A MZ MS M ρ r,
    ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
    exists m,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m /\
      ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r.
Proof.
  intros * H.
  dependent destruction H.
  eexists; split; eassumption.
Qed.

(** The universe at an index evaluates to its value, at either tier. *)
Lemma eval_ulvl_tm : forall Θ Ξ u ρ, ⟦ ulvl_tm u ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ulvl_val u.
Proof. intros ? ? [] ?; cbn; repeat econstructor. Qed.

#[export]
Hint Resolve eval_ulvl_tm : mctt.
