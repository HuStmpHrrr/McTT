From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

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
            ys1 = ys2).
  Proof.
    intros Θ Ξ; apply read_mut_ind; intros; progressive_inversion; functional_eval_rewrite_clear;
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
