From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Syntactic Require Import Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval_exps : forall {Θ Ξ} Ms ρ ms1 ms2,
      ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); firstorder. Qed.

  Lemma functional_fresh_tele : forall {Θ Ξ} ρ T s vs1, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
      forall vs2, Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ reflexivity |].
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_fresh_cargs : forall {Θ Ξ} p ups ρ gs s vs1, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs1 ->
      forall vs2, Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ auto | |];
      functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_fresh_ihs : forall {Θ Ξ} ρ As ρa gs' gs vs s ihs1, Fihs vs at gs' gs under ρ As in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs1 ->
      forall ihs2, Fihs vs at gs' gs under ρ As in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs2 -> ihs1 = ihs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; auto.
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_wrap_ihs_eval : forall {Θ Ξ} ρ p ups Bks gs' gs vs ihs r1,
      ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      forall r2, ⟦wihs vs of gs' gs with ihs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; auto.
    all: functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Ltac functional_fresh_rewrite_clear :=
    repeat match goal with
      | H1 : fresh_tele ?T ?X ?ρ ?L ?s ?v1, H2 : fresh_tele ?T ?X ?ρ ?L ?s ?v2 |- _ =>
          pose proof (functional_fresh_tele _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v1, H2 : fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v2 |- _ =>
          pose proof (functional_fresh_cargs _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fresh_ihs ?T ?X ?ρ ?A ?ρa ?gs' ?gs ?vs ?s ?i1, H2 : fresh_ihs ?T ?X ?ρ ?A ?ρa ?gs' ?gs ?vs ?s ?i2 |- _ =>
          pose proof (functional_fresh_ihs _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?g' ?g ?vs ?ih ?r1, H2 : wrap_ihs_eval ?T ?X ?ρ ?p ?o ?Bks ?g' ?g ?vs ?ih ?r2 |- _ =>
          pose proof (functional_wrap_ihs_eval _ _ _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ⟦ ?Ps ⟧* ?T ⍮ ?X ⍮ ?ρ ↘ ?b1, H2 : ⟦ ?Ps ⟧* ?T ⍮ ?X ⍮ ?ρ ↘ ?b2 |- _ =>
          pose proof (functional_eval_exps _ _ _ _ H1 H2); subst; clear H2
      | H1 : eval_mref ?T ?X ?p ?ups ?j ?r1, H2 : eval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
          let E := fresh "E" in
          pose proof (functional_eval_mref _ _ _ _ _ H1 H2) as E; injection E; intros; subst; clear H2
      | H : (_, _) = (_, _) |- _ => injection H; intros; subst; clear H
      | H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : record_lookup ?T ?X ?p = Some _, H2 : record_lookup ?T ?X ?p = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; intros; subst; clear H2
      | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
          rewrite H1 in H2; injection H2; intros; subst; clear H2
      | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
          rewrite H1 in H2; injection H2 as ?; subst
      end.

  Lemma functional_read : forall {Θ Ξ},
    (forall s m M1,
        Rnf m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
        forall M2,
          Rnf m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
          M1 = M2) /\
      (forall s m M1,
          Rne m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rne m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2) /\
      (forall s m M1,
          Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
          forall M2,
            Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
            M1 = M2) /\
      (forall s xs ys1,
          Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys1 ->
          forall ys2,
            Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys2 ->
            ys1 = ys2) /\
      (forall s ρ T vs Vs1, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 -> forall Vs2, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
      (forall s p ups ρ gs vs Vs1, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs1 ->
         forall Vs2, Rcargs vs at gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Vs2 -> Vs1 = Vs2) /\
      (forall s p ups ρ t v V1, Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V1 ->
         forall V2, Rsh v at t of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ V2 -> V1 = V2) /\
      (forall s ρ p ups Bks sel i Ms NBks1, Rblks i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks1 ->
         forall NBks2, Rblks i Ms from p ups Bks sel in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ NBks2 -> NBks1 = NBks2) /\
      (forall s ρ p ups Bks Mv A Mi r cs Bs Bs1, Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs1 ->
         forall Bs2, Rbrs Bs at cs of Mi r from p ups Bks Mv A in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Bs2 -> Bs1 = Bs2) /\
      (forall s ρ fl v Fs1, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs1 -> forall Fs2, Rflds v at fl in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Fs2 -> Fs1 = Fs2).
  Proof.
    intros Θ Ξ; apply read_mut_ind; intros; progressive_inversion; functional_eval_rewrite_clear;
      functional_fresh_rewrite_clear; functional_eval_rewrite_clear.
    (** A small universe takes the canonical level that its level reads
        back as, so its case is that equality under [nf_univ_of].  The other
        level cases read back a canonical form, so the equality is under
        [nf_lvl_of (lvl_canon …)]: [repeat f_equal] reaches the atoms. *)
    all: try solve [ apply nf_univ_of_cong; eauto | repeat f_equal; solve [eauto] ].
    (** A constructor at an inductive type, read by one of two rules (a
        declared member, or a view): the other side is inverted here, the
        rules excluding each other by the member's head. *)
    all: match goal with
         | H : read_nf _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
         | H : read_ne _ _ _ _ _ |- _ = _ => inversion H; subst; clear H
         end;
      functional_fresh_rewrite_clear; functional_eval_rewrite_clear; try congruence;
      repeat match goal with
        | H1 : List.length ?v = (?a + ?g)%nat, H2 : List.length ?v = (?b + ?g)%nat |- _ =>
            assert_fails (constr_eq a b); assert (a = b) by lia; subst b
        end;
      repeat f_equal; solve [eauto].
  Qed.

  Corollary functional_read_nf : forall {Θ Ξ} s m M1 M2,
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rnf m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_read Θ Ξ); firstorder.
  Qed.

  Lemma functional_read_la : forall {Θ Ξ} s xs ys1 ys2,
      Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys1 ->
      Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys2 ->
      ys1 = ys2.
  Proof.
    intros Θ Ξ; pose proof (@functional_read Θ Ξ); firstorder.
  Qed.

  Lemma functional_read_ne : forall {Θ Ξ} s m M1 M2,
      Rne m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rne m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_read Θ Ξ); firstorder.
  Qed.

  Lemma functional_read_typ : forall {Θ Ξ} s m M1 M2,
      Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M1 ->
      Rtyp m in Θ ⍮ Ξ ⍮ s ↘ M2 ->
      M1 = M2.
  Proof.
    intros Θ Ξ; pose proof (@functional_read Θ Ξ); firstorder.
  Qed.

(** ** The Realiser of a Level and Its Readback

    Readback preserves the offset of each atom, so the realiser of a level
    value — its value when every atom is [0] — is that of the canonical form
    it reads back as.  This is what makes the realiser of a level a sound
    index for a small universe in the models: it does not depend on the
    length. *)
  Lemma read_la_max : forall {Θ Ξ} s xs ys,
      Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
      forall c, la_max c ys = dla_max c xs.
  Proof.
    intros * H; induction H; intros c; cbn; [ reflexivity | congruence ].
  Qed.

(** The readback of a level does not depend on the sort of the type it is
    read at: the two clauses for [Level] mention it nowhere.  This is what
    lets [per_lvl] be stated at one sort and used at every one. *)
  Lemma read_nf_level_sort : forall {Θ Ξ} s m n l W,
      Rnf ⇓ (Levelᵈ@m) l in Θ ⍮ Ξ ⍮ s ↘ W ->
      Rnf ⇓ (Levelᵈ@n) l in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. inversion 1; subst; econstructor; eassumption. Qed.

  Lemma read_nf_level_real : forall {Θ Ξ} s n l W,
      Rnf ⇓ (Levelᵈ@n) l in Θ ⍮ Ξ ⍮ s ↘ W ->
      exists L, W = nf_lvl_of L /\ lvl_real L = dlvl_real l.
  Proof.
    inversion 1; subst.
    - eexists; split; [ reflexivity |].
      rewrite lvl_real_canon.
      unfold lvl_real, dlvl_real; cbn.
      erewrite read_la_max by eassumption; reflexivity.
    - exists (oz, la_cons 0 (dsort a) M la_nil); split; [ reflexivity | reflexivity ].
  Qed.

#[export]
Hint Resolve functional_read_nf functional_read_ne functional_read_typ functional_read_la : mctt.

Ltac functional_read_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_read equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (Rnf ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rnf ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rne ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rne ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rtyp ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rtyp ?m in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : (Rla ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M1), H2 : (Rla ?xs in ?T ⍮ ?X ⍮ ?s ↘ ?M2) |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_read_rewrite_clear := repeat functional_read_rewrite_clear1.

(** One fresh variable per member of a telescope, per argument, and per
    recursive argument. *)
Lemma fresh_tele_length : forall {Θ Ξ} ρ T s vs,
    Ftele T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

Lemma fresh_cargs_length : forall {Θ Ξ} p ups ρ gs s vs,
    Fcargs gs of p ups in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ vs -> List.length vs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

Lemma fresh_ihs_length : forall {Θ Ξ} ρ As ρa gs' gs vs s ihs,
    Fihs vs at gs' gs under ρ As in Θ ⍮ Ξ ⍮ ρa ⍮ s ↘ ihs -> List.length ihs = cargs_nrec gs'.
Proof. induction 1; cbn; congruence. Qed.
