From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Syntactic Require Import Inductives.
From Mctt.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

  Lemma functional_eval_exps : forall {Θ Ξ} Ms ρ ms1 ms2,
      ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2.
  Proof. intros Θ Ξ; pose proof (@functional_eval Θ Ξ); firstorder. Qed.

  Lemma functional_fresh_tele : forall {Θ Ξ} ρ T s vs1, fresh_tele Θ Ξ ρ T s vs1 ->
      forall vs2, fresh_tele Θ Ξ ρ T s vs2 -> vs1 = vs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ reflexivity |].
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Lemma functional_fresh_cargs : forall {Θ Ξ} p ups ρ gs s vs1 bss1, fresh_cargs Θ Ξ p ups ρ gs s vs1 bss1 ->
      forall vs2 bss2, fresh_cargs Θ Ξ p ups ρ gs s vs2 bss2 -> vs1 = vs2 /\ bss1 = bss2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; [ auto | |].
    - functional_eval_rewrite_clear; edestruct IHfresh_cargs as [-> ->]; [ eassumption | auto ].
    - match goal with H1 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?b1, H2 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?b2 |- _ =>
        pose proof (functional_eval_exps _ _ _ _ H1 H2) as <- end.
      edestruct IHfresh_cargs as [-> ->]; [ eassumption | auto ].
  Qed.

  Lemma functional_fresh_ihs : forall {Θ Ξ} ρ A gs vs bss s ihs1, fresh_ihs Θ Ξ ρ A gs vs bss s ihs1 ->
      forall ihs2, fresh_ihs Θ Ξ ρ A gs vs bss s ihs2 -> ihs1 = ihs2.
  Proof.
    induction 1; intros * H2; inversion H2; subst; auto.
    functional_eval_rewrite_clear; f_equal; auto.
  Qed.

  Ltac functional_fresh_rewrite_clear :=
    repeat match goal with
      | H1 : fresh_tele ?T ?X ?ρ ?L ?s ?v1, H2 : fresh_tele ?T ?X ?ρ ?L ?s ?v2 |- _ =>
          pose proof (functional_fresh_tele _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v1 ?b1, H2 : fresh_cargs ?T ?X ?p ?us ?ρ ?gs ?s ?v2 ?b2 |- _ =>
          destruct (functional_fresh_cargs _ _ _ _ _ _ _ H1 _ _ H2); subst; clear H2
      | H1 : fresh_ihs ?T ?X ?ρ ?A ?gs ?vs ?bss ?s ?i1, H2 : fresh_ihs ?T ?X ?ρ ?A ?gs ?vs ?bss ?s ?i2 |- _ =>
          pose proof (functional_fresh_ihs _ _ _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ⟦ ?Ps ⟧* ?T ⍮ ?X ⍮ ?ρ ↘ ?b1, H2 : ⟦ ?Ps ⟧* ?T ⍮ ?X ⍮ ?ρ ↘ ?b2 |- _ =>
          pose proof (functional_eval_exps _ _ _ _ H1 H2); subst; clear H2
      | H1 : ind_lookup ?T ?X ?p = Some _, H2 : ind_lookup ?T ?X ?p = Some _ |- _ =>
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
      (forall s p ups ρ gs vs Vs1, read_cargs Θ Ξ s p ups ρ gs vs Vs1 ->
         forall Vs2, read_cargs Θ Ξ s p ups ρ gs vs Vs2 -> Vs1 = Vs2) /\
      (forall s ρ A p D ups cs Bs Bs1, read_brs Θ Ξ s ρ A p D ups cs Bs Bs1 ->
         forall Bs2, read_brs Θ Ξ s ρ A p D ups cs Bs Bs2 -> Bs1 = Bs2).
  Proof.
    intros Θ Ξ; apply read_mut_ind; intros; progressive_inversion; functional_eval_rewrite_clear;
      functional_fresh_rewrite_clear; functional_eval_rewrite_clear;
      first
        [ (** A small universe takes the canonical level that its level reads
              back as, so its case is that equality under [nf_univ_of]. *)
          solve [ apply nf_univ_of_cong; eauto ]
          (** The other level cases read back a canonical form, so the equality
              is under [nf_lvl_of (lvl_canon …)]: [repeat f_equal] reaches the
              atoms. *)
        | repeat f_equal; solve [eauto] ].
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
    fresh_tele Θ Ξ ρ T s vs -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

Lemma fresh_cargs_length : forall {Θ Ξ} p ups ρ gs s vs bss,
    fresh_cargs Θ Ξ p ups ρ gs s vs bss -> List.length vs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

Lemma fresh_ihs_length : forall {Θ Ξ} ρ A gs vs bss s ihs,
    fresh_ihs Θ Ξ ρ A gs vs bss s ihs -> List.length ihs = cargs_nrec gs.
Proof. induction 1; cbn; congruence. Qed.
