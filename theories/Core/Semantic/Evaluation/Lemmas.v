From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Inductives.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

  (** Kinds are unique: a definition is no module, and a body's entry is
      found by one lookup. *)
  Lemma functional_kind : forall {Θ Ξ},
    (forall h ch k1, dkind Θ Ξ h ch k1 -> forall k2, dkind Θ Ξ h ch k2 -> k1 = k2) /\
    (forall ρ U ch k1, ukind Θ Ξ ρ U ch k1 -> forall k2, ukind Θ Ξ ρ U ch k2 -> k1 = k2) /\
    (forall ρ H ch k1, skind Θ Ξ ρ H ch k1 -> forall k2, skind Θ Ξ ρ H ch k2 -> k1 = k2) /\
    (forall ρ Φ ρ1, kenv Θ Ξ ρ Φ ρ1 -> forall ρ2, kenv Θ Ξ ρ Φ ρ2 -> ρ1 = ρ2) /\
    (forall ρ H its gs1, kgens Θ Ξ ρ H its gs1 -> forall gs2, kgens Θ Ξ ρ H its gs2 -> gs1 = gs2).
  Proof.
    intros Θ Ξ; apply kind_mut_ind; intros;
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
        | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _ _),
          H2 : forall U r, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U r) |- _ =>
            exfalso; exact (H2 _ _ H1)
        | H1 : Members.gc_resolve Θ Ξ ?p = Some (ge_def _ _ _ _),
          H2 : forall b pv A B, Members.gc_resolve Θ Ξ ?p <> Some (ge_def b pv A B) |- _ =>
            exfalso; exact (H2 _ _ _ _ H1)
        | H : dkind Θ Ξ (dm_global _ _) nil _ |- _ => inversion H; subst; clear H
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        end; try congruence.
  Qed.

  Corollary functional_kgens : forall {Θ Ξ} ρ H its gs1 gs2,
      kgens Θ Ξ ρ H its gs1 -> kgens Θ Ξ ρ H its gs2 -> gs1 = gs2.
  Proof. intros Θ Ξ; pose proof (@functional_kind Θ Ξ) as Hf; destruct_all; eauto. Qed.

  Lemma kgens_length : forall Θ Ξ ρ H its gs, kgens Θ Ξ ρ H its gs -> List.length gs = List.length its.
  Proof. induction 1; cbn; auto. Qed.

  Lemma functional_eval : forall {Θ Ξ},
    (forall M ρ m1,
        ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
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
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2) /\
      (forall ρ nm A Bs m r1,
          ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ nm A Bs gs vs r1,
          ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ nm A Bs t v r1,
          eval_ih Θ Ξ ρ nm A Bs t v r1 -> forall r2, eval_ih Θ Ξ ρ nm A Bs t v r2 -> r1 = r2) /\
      (forall p ups ρ t a1, eval_shty Θ Ξ p ups ρ t a1 -> forall a2, eval_shty Θ Ξ p ups ρ t a2 -> a1 = a2) /\
      (forall ρm A ρ t v a1, eval_ihty Θ Ξ ρm A ρ t v a1 -> forall a2, eval_ihty Θ Ξ ρm A ρ t v a2 -> a1 = a2).
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
        | H1 : ind_alias_lookup Θ Ξ ?p = Some _, H2 : ind_alias_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_alias_lookup Θ Ξ ?p = Some _ |- _ =>
            exfalso; destruct (ind_lookup_entry _ _ _ _ H1) as (? & ? & He1); rewrite ind_alias_lookup_entry, He1 in H2; discriminate H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _ _),
          H2 : forall U r, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U r) |- _ =>
            exfalso; exact (H2 _ _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite (gm_prefix_item_excl _ _ _ H1) in H2; discriminate H2
        | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : kgens Θ Ξ ?ρ ?H ?its ?g1, H2 : kgens Θ Ξ ?ρ ?H ?its ?g2 |- _ =>
            assert_fails (constr_eq g1 g2); pose proof (functional_kgens _ _ _ _ _ H1 H2); subst g2
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

  Corollary functional_eval_app : forall {Θ Ξ} m n r1 r2,
      $| m & n | Θ ⍮ Ξ ↘ r1 ->
      $| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_elim : forall {Θ Ξ} ρ nm A Bs m r1 r2,
      ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ihs : forall {Θ Ξ} ρ nm A Bs gs vs r1 r2,
      ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ih : forall {Θ Ξ} ρ nm A Bs t v r1 r2,
      eval_ih Θ Ξ ρ nm A Bs t v r1 -> eval_ih Θ Ξ ρ nm A Bs t v r2 -> r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_shty : forall {Θ Ξ} p ups ρ t a1 a2,
      eval_shty Θ Ξ p ups ρ t a1 -> eval_shty Θ Ξ p ups ρ t a2 -> a1 = a2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ihty : forall {Θ Ξ} ρm A ρ t v a1 a2,
      eval_ihty Θ Ξ ρm A ρ t v a1 -> eval_ihty Θ Ξ ρm A ρ t v a2 -> a1 = a2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
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
Hint Resolve functional_eval_exp functional_eval_elim functional_eval_ihs functional_eval_ih functional_eval_shty functional_eval_ihty functional_eval_app functional_eval_modexp functional_eval_sub : mctt.



Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦elim ?m under ?nm ?A ?Bs ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦elim ?m under ?nm ?A ?Bs ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ihs ?vs of ?gs under ?nm ?A ?Bs ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦ihs ?vs of ?gs under ?nm ?A ?Bs ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ih ?T ?X ?ρ ?nm ?A ?Bs ?t ?v ?r1, H2 : eval_ih ?T ?X ?ρ ?nm ?A ?Bs ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : eval_shty ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r1, H2 : eval_ihty ?T ?X ?ρm ?A ?ρ ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is no [eval_sub] case: [functional_eval_sub] gives only pointwise
    equality, so there is nothing to [replace]. *)
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.

(** The universe at an index evaluates to its value, at either tier. *)
Lemma eval_ulvl_tm : forall Θ Ξ u ρ, ⟦ ulvl_tm u ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ulvl_val u.
Proof. intros ? ? [] ?; cbn; repeat econstructor. Qed.

#[export]
Hint Resolve eval_ulvl_tm : mctt.

(** One recursive result per recursive argument. *)
Lemma eval_ihs_length : forall {Θ Ξ} ρ nm A Bs gs vs ihs,
    ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
    List.length vs = List.length gs /\ List.length ihs = cargs_nrec gs.
Proof. induction 1; cbn; intuition congruence. Qed.
