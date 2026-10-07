From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions.
Import Domain_Notations Fixed_Notations.
Import ListNotations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism R0 `(R0_morphism : Proper _ ((@relation_equivalence domain) ==> (@relation_equivalence domain)) R0) A ρ A' ρ' : (rel_mod_eval R0 A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma per_bot_sym : forall m n,
    Dom m ≈ n ∈ per_bot ->
    Dom n ≈ m ∈ per_bot.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_bot_sym : mctt.

Lemma per_bot_trans : forall m n l,
    Dom m ≈ n ∈ per_bot ->
    Dom n ≈ l ∈ per_bot ->
    Dom m ≈ l ∈ per_bot.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
Qed.

Hint Resolve per_bot_trans : mctt.

#[local] Instance per_bot_PER : PER per_bot.
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot : forall {n},
    Dom #ᵈ n ≈ #ᵈ n ∈ per_bot.
Proof.
  intros ? ?. repeat econstructor.
Qed.

Hint Resolve var_per_bot : mctt.

Lemma per_top_sym : forall m n,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ m ∈ per_top.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_top_sym : mctt.

Lemma per_top_trans : forall m n l,
    Dom m ≈ n ∈ per_top ->
    Dom n ≈ l ∈ per_top ->
    Dom m ≈ l ∈ per_top.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
Qed.

Hint Resolve per_top_trans : mctt.

#[local] Instance per_top_PER : PER per_top.
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    Dom m ≈ m' ∈ per_bot ->
    Dom ⇓ (⇑ a b) (⇑ c m) ≈ ⇓ (⇑ a' b') (⇑ c' m') ∈ per_top.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

Hint Resolve per_bot_then_per_top : mctt.

Lemma per_top_typ_sym : forall m n,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ m ∈ per_top_typ.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs; solve [eauto].
Qed.

Hint Resolve per_top_typ_sym : mctt.

Lemma per_top_typ_trans : forall m n l,
    Dom m ≈ n ∈ per_top_typ ->
    Dom n ≈ l ∈ per_top_typ ->
    Dom m ≈ l ∈ per_top_typ.
Proof.
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear; solve [eauto].
Qed.

Hint Resolve per_top_typ_trans : mctt.

#[local] Instance per_top_typ_PER : PER per_top_typ.
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.

Lemma per_nat_sym : forall m n,
    Dom m ≈ n ∈ per_nat ->
    Dom n ≈ m ∈ per_nat.
Proof.
  induction 1; econstructor; mautosolve.
Qed.

Hint Resolve per_nat_sym : mctt.

Lemma per_nat_trans : forall m n l,
    Dom m ≈ n ∈ per_nat ->
    Dom n ≈ l ∈ per_nat ->
    Dom m ≈ l ∈ per_nat.
Proof.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor; mautosolve.
Qed.

Hint Resolve per_nat_trans : mctt.

#[local] Instance per_nat_PER : PER per_nat.
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
Qed.

Lemma per_ne_sym : forall m n,
    Dom m ≈ n ∈ per_ne ->
    Dom n ≈ m ∈ per_ne.
Proof.
  intros * [].
  econstructor; mautosolve.
Qed.

Hint Resolve per_ne_sym : mctt.

Lemma per_ne_trans : forall m n l,
    Dom m ≈ n ∈ per_ne ->
    Dom n ≈ l ∈ per_ne ->
    Dom m ≈ l ∈ per_ne.
Proof.
  intros * [].
  inversion_clear 1.
  econstructor; mautosolve.
Qed.

Hint Resolve per_ne_trans : mctt.

#[local] Instance per_ne_PER : PER per_ne.
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    per_univ_elem_induction Horig; basic_per_univ_elem_econstructor; eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mautosolve.
Qed.

(** The morphism in forward form.  [apply -> per_univ_elem_morphism_iff] needs
    the level to be known, which is not the case when building a context PER:
    there the level of the head relation is fixed only by the witness supplied
    for it.  Taking the witness first leaves [<~>] as the only goal, and leaves
    the target relation implicit, so the caller never spells out the
    impredicative head relation. *)
Lemma per_univ_elem_resp_iff : forall {i R R' a a'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    (R <~> R') ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R'.
Proof.
  intros * H HR.
  apply -> per_univ_elem_morphism_iff; [ eassumption | reflexivity | reflexivity | eassumption ].
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> (@relation_equivalence domain) as per_univ_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros ** a b.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism i A ρ A' ρ' : (rel_typ i A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Lemma domain_app_per : forall f f' a a',
  Dom f ≈ f' ∈ per_bot ->
  Dom a ≈ a' ∈ per_top ->
  Dom f $ᵈ a ≈ f' $ᵈ a' ∈ per_bot.
Proof.
  intros. intros s.
  destruct (H s) as [? []].
  destruct (H0 s) as [? []].
  mauto.
Qed.

End Fixed_GCtx.

#[export] Existing Instance rel_mod_eval_morphism_Proper.
#[export] Existing Instance rel_mod_app_morphism_Proper.
#[export]
Hint Resolve per_bot_sym : mctt.
#[export]
Hint Resolve per_bot_trans : mctt.
#[export] Existing Instance per_bot_PER.
#[export]
Hint Resolve var_per_bot : mctt.
#[export]
Hint Resolve per_top_sym : mctt.
#[export]
Hint Resolve per_top_trans : mctt.
#[export] Existing Instance per_top_PER.
#[export]
Hint Resolve per_bot_then_per_top : mctt.
#[export]
Hint Resolve per_top_typ_sym : mctt.
#[export]
Hint Resolve per_top_typ_trans : mctt.
#[export] Existing Instance per_top_typ_PER.
#[export]
Hint Resolve per_nat_sym : mctt.
#[export]
Hint Resolve per_nat_trans : mctt.
#[export] Existing Instance per_nat_PER.
#[export]
Hint Resolve per_ne_sym : mctt.
#[export]
Hint Resolve per_ne_trans : mctt.
#[export] Existing Instance per_ne_PER.
#[export] Existing Instance per_univ_elem_morphism_iff_Proper.
#[export] Existing Instance per_univ_elem_morphism_relation_equivalence_Proper.
#[export] Existing Instance rel_typ_morphism_Proper.
Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** Closes [R1 x y] or [R2 x y] from [R1 <~> R2] directly.
    [apply_relation_equivalence] only rewrites, and [setoid_rewrite] leaves the
    conclusion untouched when both sides of [<~>] are applications, as the head
    relations [head_rel _ _ D] of a context PER are for two witnesses [D]. *)
Ltac use_relation_equivalence :=
  match goal with
  | H : ?R1 <~> ?R2 |- ?R1 _ _ => apply H
  | H : ?R1 <~> ?R2 |- ?R2 _ _ => apply H
  end.

(** Move every hypothesis across the equivalences in context, from left to
    right, where [apply_relation_equivalence] cannot rewrite (the
    relations are applied to dependent evidence). *)
Ltac move_by_relation_equivalence :=
  repeat match goal with
    | Heq : ?R1 <~> ?R2, H : ?R1 ?x ?y |- _ => apply Heq in H
    end.

Ltac move_goal_by_relation_equivalence :=
  try match goal with
    | Heq : ?R1 <~> ?R2 |- ?R1 _ _ => apply Heq
    end.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a ≈ b' ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  per_univ_elem_induction Horig; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros.
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder;
    (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
     econstructor; intuition).
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder;
      (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear;
       econstructor; intuition).
Qed.

End Fixed_GCtx.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : (DF ?a ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ ?b' ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R /\
      (forall m m',
          Dom m ≈ m' ∈ R ->
          Dom m' ≈ m ∈ R).
Proof.
  simpl.
  per_univ_elem_induction1; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1; mautosolve.
  - split.
    + apply per_univ_elem_core_suniv'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]; mautosolve.
  - destruct_conjs.
    split.
    + basic_per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; apply_relation_equivalence]; mautosolve.
Qed.

Corollary per_univ_sym : forall i R a b,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b ≈ a ∈ per_univ_elem i ↘ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_sym' : forall i a b,
    Dom a ≈ b ∈ per_univ i ->
    Dom b ≈ a ∈ per_univ i.
Proof.
  intros * [? ?%per_univ_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m' ≈ m ∈ R.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF a' ≈ b ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    DF b' ≈ a ∈ per_univ_elem i' ↘ R' ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

End Fixed_GCtx.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF ?a ≈ _ ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF _ ≈ ?b ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?b ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : (DF ?a ≈ _ ∈ per_univ_elem ?i ↘ ?R1),
      H2 : DF _ ≈ ?a ∈ per_univ_elem ?i' ↘ ?R2 |- _ =>
      (** Order matters less here, as [H1] and [H2] cannot be exchanged. *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_univ_elem_trans : forall i R a1 a2,
    per_univ_elem i R a1 a2 ->
    (forall j a3,
        per_univ_elem j R a2 a3 ->
        per_univ_elem i R a1 a3) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof.
  per_univ_elem_induction1;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (** The univ case. *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** The small univ case. *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** The nat case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [⊤] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The [⊥] case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The pi case. *)
    destruct_conjs.
    basic_per_univ_elem_econstructor; eauto.
    + handle_per_univ_elem_irrel.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel; (basic_per_univ_elem_econstructor; mautosolve 4).
  - (** The function case. *)
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (** The neut case. *)
    idtac; (basic_per_univ_elem_econstructor; mautosolve 4).
Qed.

Corollary per_univ_trans : forall i j R a1 a2 a3,
    per_univ_elem i R a1 a2 ->
    per_univ_elem j R a2 a3 ->
    per_univ_elem i R a1 a3.
Proof.
  intros * ?%per_univ_elem_trans.
  firstorder.
Qed.

Corollary per_univ_trans' : forall i j a1 a2 a3,
    Dom a1 ≈ a2 ∈ per_univ i ->
    Dom a2 ≈ a3 ∈ per_univ j ->
    Dom a1 ≈ a3 ∈ per_univ i.
Proof.
  intros * [? ?] [? ?].
  handle_per_univ_elem_irrel.
  firstorder mauto using per_univ_trans.
Qed.

Corollary per_elem_trans : forall i R a1 a2 m1 m2 m3,
    per_univ_elem i R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_univ_elem_trans.
  firstorder.
Qed.

#[local] Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[local] Instance per_univ_PER' {i} : PER (per_univ i).
Proof.
  split.
  - auto using per_univ_sym'.
  - eauto using per_univ_trans'.
Qed.

#[local] Instance per_elem_PER {i R a b} `(H : per_univ_elem i R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** [per_elem_PER] from a chain, so that [solve_chain_PER] need not read a
    pair off it first. *)
#[local] Instance per_elem_chain_PER {i R l} `(H : rel_chain (per_univ_elem i R) l) : PER R.
Proof.
  destruct (rel_chain_shape _ _ H) as [a [b [l' ->]]].
  eapply per_elem_PER; pairwise.
Qed.

(** ** Chains of Types

    A semantic type judgment provides a chain in [per_univ i], each link with
    its own element PER.  What its consumer needs is the whole chain at one
    PER, namely the one the judgment's element chain lives in.
    [per_univ_chain_at_in] refines the chain to the PER of any one of its
    pairs; this is the only use of irrelevance in the completeness proof.

    The proof uses irrelevance twice, through the left value [x] of the given
    pair: first to the pair [(x, u)], which shares [x], then to [(u, v)],
    which shares [u]. *)
Lemma per_univ_chain_at_in : forall {i R l x y},
    rel_chain (per_univ i) l ->
    In x l ->
    In y l ->
    DF x ≈ y ∈ per_univ_elem i ↘ R ->
    rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain Hx Hy HR.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  apply rel_chain_intro; intros u v Hu Hv.
  assert (Hxu : Dom x ≈ u ∈ per_univ i) by pairwise.
  destruct Hxu as [Rxu HRxu].
  assert (HRxu' : DF x ≈ u ∈ per_univ_elem i ↘ R)
    by (eapply per_univ_elem_resp_iff; [ exact HRxu |];
        eapply per_univ_elem_right_irrel; [ exact HRxu | exact HR ]).
  assert (Huv : Dom u ≈ v ∈ per_univ i) by pairwise.
  destruct Huv as [Ruv HRuv].
  eapply per_univ_elem_resp_iff; [ exact HRuv |].
  eapply per_univ_elem_cross_irrel; [ exact HRuv | exact HRxu' ].
Qed.

(** Weak functionality of [per_univ i]: a chain in it is a chain at one
    element PER, with no anchor needed.  This is the paper's [S ⊆_R ↘ R'];
    [per_univ_chain_at_in] is the case where the caller fixes [R'].  All the
    links' PERs are equivalent, so the first is taken. *)
Corollary per_univ_chain_functional : forall {i l},
    rel_chain (per_univ i) l ->
    exists R, rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  assert (Hab : Dom a ≈ b ∈ per_univ i) by pairwise.
  destruct Hab as [R HR].
  exists R.
  eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in.
Qed.

End Fixed_GCtx.

#[export] Existing Instance per_univ_PER.
#[export] Existing Instance per_univ_PER'.
#[export] Existing Instance per_elem_PER.
#[export] Existing Instance per_elem_chain_PER.
(** Names the element PER of a chain in [per_univ i] and refines the chain to
    it, in place.  Nothing is lost: every pair of the chain remains available
    at [R] through [pairwise]. *)
Ltac functionalize_per_univ_chain H R :=
  apply per_univ_chain_functional in H; destruct H as [R H].

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** [pairwise] at a [per_univ i] goal, supplying the existential that the
    refined chain no longer carries. *)
Ltac pairwise_univ := first [ pairwise | eexists; pairwise ].

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The other half of weak functionality: the output PER is unique, so
    [S ⊆_R ↘ R'] is well defined.  One value shared with any other element of
    the universe determines [R']: the chain is at a PER, so it is reflexive at
    that value, and irrelevance then needs no second value. *)
Lemma per_univ_chain_rel_irrel : forall {i j R R' l x y},
    rel_chain (per_univ_elem i R) l ->
    DF x ≈ y ∈ per_univ_elem j ↘ R' ->
    In x l ->
    R <~> R'.
Proof.
  intros * Hchain Hanchor Hx.
  assert (Hxx : DF x ≈ x ∈ per_univ_elem i ↘ R)
    by (eapply rel_chain_refl; first [ eassumption | solve_chain_PER ]).
  eapply per_univ_elem_right_irrel; [ exact Hxx | exact Hanchor ].
Qed.

End Fixed_GCtx.

(** [retype_rel_chain Htyp Hanchor H] moves [H] between the element PER of the
    type chain [Htyp] and the one [Hanchor] names.  The two need share only
    one value.  Only [H] determines the direction, so both are tried.  [H] may
    be a [rel_chain] (rewritten through [rel_chain_Proper]) or a bare pair,
    either at the relation itself or under the [per_head] of a type the anchor
    is about. *)
Ltac retype_rel_chain Htyp Hanchor H :=
  let Hiff := fresh "Hiff" in
  pose proof (per_univ_chain_rel_irrel Htyp Hanchor ltac:(solve_in)) as Hiff;
  first [ rewrite Hiff in H | rewrite <- Hiff in H ];
  clear Hiff.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The [per_univ_elem] rule for [Π] without its PER premise. *)
Lemma per_univ_elem_pi' :
  forall i a a' ρ B ρ' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain)
    elem_rel,
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
        rel_mod_eval (per_univ_elem i) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

End Fixed_GCtx.

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Hint Resolve per_univ_elem_pi' : mctt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j a a' in_rel ρ ρ' B B' elem_rel},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem j ↘ elem_rel ->
    exists (out_rel : forall {c c'} (equiv_c_c' : Dom c ≈ c' ∈ in_rel), relation domain),
      (forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
          rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') (out_rel equiv_c_c')) /\
        (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel), rel_mod_app f c f' c' (out_rel equiv_c_c')).
Proof.
  intros * Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_mod_eval (per_univ_elem j) B (ρ ↦ c) B' (ρ' ↦ c') R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_pi' : mctt.
Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** Cumulativity, along the order of universe indices: in particular, a
    small universe is in every large one. *)
Lemma per_univ_elem_cumu_uidx : forall i a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    forall i', uidx_le i i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  simpl.
  per_univ_elem_induction1; intros; subst;
    per_univ_elem_econstructor; eauto; try solve_uidx.
  intros.
  destruct_rel_mod_eval.
  econstructor; solve [eauto].
Qed.

Lemma per_univ_elem_cumu : forall (i : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_univ_elem_cumu : mctt.

Lemma per_univ_elem_cumu_ge : forall (i i' : nat) a0 a1 R,
    i <= i' ->
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

(** A small type is a type of every large universe. *)
Lemma per_univ_elem_small_large : forall j (i : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem (us j) ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R.
Proof.
  intros; eapply per_univ_elem_cumu_uidx; [ eassumption | exact I ].
Qed.

Hint Resolve per_univ_elem_cumu_ge : mctt.

Lemma per_univ_elem_cumu_max_left : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem i ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (i <= max i j) by lia; mautosolve.
Qed.

Lemma per_univ_elem_cumu_max_right : forall (i j : nat) a0 a1 R,
    DF a0 ≈ a1 ∈ per_univ_elem j ↘ R ->
    DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R.
Proof.
  intros.
  assert (j <= max i j) by lia; mautosolve.
Qed.

Lemma per_subtyp_to_univ_elem : forall a b i,
    Sub a <: b at i ->
    exists R R',
      DF a ≈ a ∈ per_univ_elem i ↘ R /\
        DF b ≈ b ∈ per_univ_elem i ↘ R'.
Proof.
  destruct 1; do 2 eexists; mauto;
    split; per_univ_elem_econstructor; mauto;
    try apply Equivalence_Reflexive.
  all: solve_uidx.
Qed.


Lemma per_elem_subtyping : forall A B i,
    Sub A <: B at i ->
    forall R R' a b,
      DF A ≈ A ∈ per_univ_elem i ↘ R ->
      DF B ≈ B ∈ per_univ_elem i ↘ R' ->
      R a b ->
      R' a b.
Proof.
  induction 1; intros;
    handle_per_univ_elem_irrel;
    saturate_refl;
    (on_all_hyp: fun H => directed invert_per_univ_elem H);
    handle_per_univ_elem_irrel;
    clear_refl_eqs;
    trivial.
  - firstorder mauto.
  - destruct_conjs; eexists; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; lia ].
  - destruct_conjs; eexists; eapply per_univ_elem_cumu_uidx; [ eassumption | cbn; exact I ].
  - intros.
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    saturate_refl_for per_univ_elem.
    destruct_rel_mod_app.
    simplify_evals.
    econstructor; eauto.
    intuition.
Qed.

Lemma per_elem_subtyping_gen : forall a b i a' b' R R' m n,
    Sub a <: b at i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DF b ≈ b' ∈ per_univ_elem i ↘ R' ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub a <: b at i.
Proof.
  simpl; per_univ_elem_induction1;
    subst;
    mauto;
    destruct_all.
  assert (DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel)
    by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto).
  saturate_refl.
  econstructor; eauto.
  intros;
    destruct_rel_mod_eval;
    functional_eval_rewrite_clear;
    trivial.
Qed.

Hint Resolve per_subtyp_refl1 : mctt.

Lemma per_subtyp_refl2 : forall a b i R,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Sub b <: a at i.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

Hint Resolve per_subtyp_refl2 : mctt.

Lemma per_subtyp_trans : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall a3,
      Sub a2 <: a3 at i ->
      Sub a1 <: a3 at i.
Proof.
  induction 1; intros ? Hsub; simpl in *.
  1-7: progressive_inversion; mauto.
  all: try solve [ econstructor; solve [ lia | solve_uidx ] ].
  - inversion Hsub; subst; econstructor; solve [ lia | solve_uidx ].
  - dependent destruction Hsub.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    + etransitivity; eassumption.
    + intros.
      saturate_refl.
      (on_all_hyp: fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      intuition.
Qed.

Hint Resolve per_subtyp_trans : mctt.

#[local] Instance per_subtyp_trans_ins i : Transitive (per_subtyp i).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp : forall a b i a' b' R R',
    Sub a <: b at i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    DF b ≈ b' ∈ per_univ_elem i ↘ R' ->
    Sub a' <: b' at i.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_subtyp_cumu_uidx : forall a1 a2 i,
    Sub a1 <: a2 at i ->
    forall j,
      uidx_le i j ->
      Sub a1 <: a2 at j.
Proof.
  induction 1; intros; econstructor; eauto using per_univ_elem_cumu_uidx; solve_uidx.
Qed.

Lemma per_subtyp_cumu : forall a1 a2 (i : nat),
    Sub a1 <: a2 at i ->
    forall (j : nat),
      i <= j ->
      Sub a1 <: a2 at j.
Proof.
  intros; eapply per_subtyp_cumu_uidx; [ eassumption | cbn; lia ].
Qed.

Hint Resolve per_subtyp_cumu : mctt.

Lemma per_subtyp_cumu_left : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max i j.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Lemma per_subtyp_cumu_right : forall a1 a2 (i j : nat),
    Sub a1 <: a2 at i ->
    Sub a1 <: a2 at max j i.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

(** * The Module PER is a PER *)

(** ** Related Types, Seen from Either Side *)

Lemma rel_typ_sym : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R ->
    rel_typ i A' ρ' A ρ R /\ (forall m m', R m m' -> R m' m).
Proof.
  intros * [a a' Ha Ha' HR]; pose proof (per_univ_elem_sym _ _ _ _ HR) as [HR' Hs].
  split; [ econstructor; eassumption | exact Hs ].
Qed.

Lemma rel_typ_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R'},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    (R <~> R') /\ rel_typ i A1 ρ1 A3 ρ3 R /\ (forall m1 m2 m3, R m1 m2 -> R m2 m3 -> R m1 m3).
Proof.
  intros * [a1 a2 H1 H2 HR] [a2' a3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  assert (HRR' : R <~> R') by first [ symmetry; eapply per_univ_elem_cross_irrel; [ exact HR' | exact HR ]
                                     | eapply per_univ_elem_cross_irrel; [ exact HR | exact HR' ] ].
  split; [ exact HRR' | split ].
  - econstructor; [ eassumption | eassumption |].
    eapply per_univ_trans; [ exact HR |].
    eapply per_univ_elem_resp_iff; [ exact HR' | symmetry; exact HRR' ].
  - intros; eapply per_elem_trans; eassumption.
Qed.

Lemma rel_elem_sym : forall {i A ρ A' ρ' R M M'},
    rel_typ i A ρ A' ρ' R ->
    rel_elem M ρ M' ρ' R -> rel_elem M' ρ' M ρ R.
Proof.
  intros * HT [m m' Hm Hm' HR]; destruct (rel_typ_sym HT) as [_ Hs].
  econstructor; [ eassumption | eassumption | apply Hs; exact HR ].
Qed.

Lemma rel_elem_trans : forall {i j A1 ρ1 A2 ρ2 A3 ρ3 R R' M1 M2 M3},
    rel_typ i A1 ρ1 A2 ρ2 R ->
    rel_typ j A2 ρ2 A3 ρ3 R' ->
    rel_elem M1 ρ1 M2 ρ2 R -> rel_elem M2 ρ2 M3 ρ3 R' -> rel_elem M1 ρ1 M3 ρ3 R.
Proof.
  intros * HT HT' [m1 m2 H1 H2 HR] [m2' m3 H2' H3 HR'].
  functional_eval_rewrite_clear.
  destruct (rel_typ_trans HT HT') as (HRR' & _ & Ht).
  econstructor; [ eassumption | eassumption |].
  eapply Ht; [ exact HR | apply HRR'; exact HR' ].
Qed.

(** ** Symmetry *)

Lemma per_dmod_sym_all :
  (forall m m', per_dmod m m' -> per_dmod m' m) /\
  (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> per_gargs ts ρ' ρ args' args) /\
  (forall ts ρ D ts' ρ' D' args args', per_ltele ts ρ D ts' ρ' D' args args' -> per_ltele ts' ρ' D' ts ρ D args' args) /\
  (forall ρ D ρ' D', per_mdef ρ D ρ' D' -> per_mdef ρ' D' ρ D) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> per_body ρ' Φ' ρ Φ).
Proof.
  apply per_dmod_mut_ind_all; intros; try solve [ econstructor; eauto ].
  - destruct (rel_typ_sym r) as [? Hs]; econstructor; eauto.
  - destruct (rel_typ_sym r) as [? Hs]; econstructor; eauto.
  - destruct (rel_typ_sym r) as [? Hs]; econstructor; [ eassumption |].
    intros c c' Hc; apply H, Hs, Hc.
  - destruct (rel_typ_sym r) as [? Hs]; econstructor; eauto using rel_elem_sym.
Qed.

Corollary per_dmod_sym : forall m m', per_dmod m m' -> per_dmod m' m.
Proof. exact (proj1 per_dmod_sym_all). Qed.

(** ** Transitivity *)

Lemma per_dmod_trans_all :
  (forall m1 m2, per_dmod m1 m2 -> forall m3, per_dmod m2 m3 -> per_dmod m1 m3) /\
  (forall ts ρ1 ρ2 a1 a2, per_gargs ts ρ1 ρ2 a1 a2 ->
     forall ρ3 a3, per_gargs ts ρ2 ρ3 a2 a3 -> per_gargs ts ρ1 ρ3 a1 a3) /\
  (forall ts1 ρ1 D1 ts2 ρ2 D2 a1 a2, per_ltele ts1 ρ1 D1 ts2 ρ2 D2 a1 a2 ->
     forall ts3 ρ3 D3 a3, per_ltele ts2 ρ2 D2 ts3 ρ3 D3 a2 a3 -> per_ltele ts1 ρ1 D1 ts3 ρ3 D3 a1 a3) /\
  (forall ρ1 D1 ρ2 D2, per_mdef ρ1 D1 ρ2 D2 -> forall ρ3 D3, per_mdef ρ2 D2 ρ3 D3 -> per_mdef ρ1 D1 ρ3 D3) /\
  (forall ρ1 Φ1 ρ2 Φ2, per_body ρ1 Φ1 ρ2 Φ2 -> forall ρ3 Φ3, per_body ρ2 Φ2 ρ3 Φ3 -> per_body ρ1 Φ1 ρ3 Φ3).
Proof.
  apply per_dmod_mut_ind_all; intros;
    match goal with H : _ |- _ => inversion H; subst; clear H end.
  - (* global *)
    match goal with H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
      rewrite H1 in H2; injection H2 as <- end.
    econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
  - (* global arguments *)
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; [ exact HT | eapply Ht; [ eassumption | apply HRR; eassumption ] | eauto ].
  - (* a supplied parameter *)
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; [ exact HT | eapply Ht; [ eassumption | apply HRR; eassumption ] | eauto ].
  - (* a missing parameter: the middle side is quantified against itself *)
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht); destruct (rel_typ_sym H1) as [_ Hs] end.
    econstructor; [ exact HT |].
    intros c c' Hc.
    match goal with IH : forall c c', _ -> forall ts3 ρ3 D3 a3, _ -> _, H2 : forall c c', _ -> per_ltele _ _ _ _ _ _ _ _ |- _ =>
      eapply IH; [ eapply Ht; [ exact Hc | apply Hs; exact Hc ] | apply H2, HRR, Hc ] end.
  - econstructor; eauto.
  - econstructor; eauto.
  - (* an alias: the middle target is one value *)
    functional_eval_rewrite_clear.
    match goal with H1 : eval_modexp _ _ ?E ?ρ ?h1, H2 : eval_modexp _ _ ?E ?ρ ?h2 |- _ =>
      assert (h1 = h2) by (eapply functional_eval_modexp; eassumption); subst end.
    econstructor; eauto.
  - constructor.
  - (* a definition *)
    match goal with H1 : eval_benv _ _ ?ρ ?Φ ?r1, H2 : eval_benv _ _ ?ρ ?Φ ?r2 |- _ =>
      assert (r1 = r2) by (eapply functional_eval_benv; eassumption); subst end.
    match goal with H1 : rel_typ _ _ _ _ _ _, H2 : rel_typ _ _ _ _ _ _ |- _ =>
      destruct (rel_typ_trans H1 H2) as (HRR & HT & Ht) end.
    econstructor; eauto using rel_elem_trans.
  - (* a module *)
    match goal with H1 : eval_benv _ _ ?ρ ?Φ ?r1, H2 : eval_benv _ _ ?ρ ?Φ ?r2 |- _ =>
      assert (r1 = r2) by (eapply functional_eval_benv; eassumption); subst end.
    econstructor; eauto.
Qed.

Corollary per_dmod_trans : forall m1 m2 m3, per_dmod m1 m2 -> per_dmod m2 m3 -> per_dmod m1 m3.
Proof. intros; eapply (proj1 per_dmod_trans_all); eassumption. Qed.

#[export] Instance per_dmod_PER : PER per_dmod.
Proof. split; [ exact per_dmod_sym | exact per_dmod_trans ]. Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity; mautosolve.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

(** A head tied to the closure of one unit is tied to the closure of any
    unit related to it over the same tails. *)
Lemma mod_tie_move : forall (T : relation env) U U' ρ m,
    T ρ ρ ->
    (forall ρ ρ', T ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) ->
    per_dmod m (dm_local ρ U nil) -> per_dmod m (dm_local ρ U' nil).
Proof. intros * Hρ HU Hm; eapply per_dmod_trans; [ exact Hm | apply HU, Hρ ]. Qed.

Lemma mod_tie_move_sym : forall (T : relation env) U U' ρ m,
    PER T -> T ρ ρ ->
    (forall ρ ρ', T ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) ->
    per_dmod m (dm_local ρ U' nil) -> per_dmod m (dm_local ρ U nil).
Proof.
  intros * HT Hρ HU Hm; eapply per_dmod_trans; [ exact Hm |].
  apply per_dmod_sym, HU, Hρ.
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
  split; intros [].
  - assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition;
      (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  - assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition;
      (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  - (** A definition: the heads are tied to the bodies, which are related
        across the two right-hand contexts through the left body. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros [Ht ?];
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      exists Ht0; destruct_conjs;
      (** The bodies are read at each tail against itself, too. *)
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [symmetry |]; intuition);
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [symmetry |]; intuition);
      destruct_rel_typ; handle_per_univ_elem_irrel;
      match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end;
      move_by_relation_equivalence;
      repeat split; try (move_goal_by_relation_equivalence; solve_per);
      eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
  - (** A slot: the heads are tied to the closures of the left unit, which
        are related to the closures of either right unit. *)
    specialize (IHHorig _ _ equiv_Γ_Γ'0).
    intros ρ ρ'.
    split; intros (Ht & ? & ? & ? & ?);
      [ assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition
      | assert (Ht0 : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition ];
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel) by (etransitivity; [symmetry |]; intuition);
      assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel0) by (etransitivity; [| symmetry]; intuition);
      assert (Dom ρ'↯ ≈ ρ'↯ ∈ tail_rel0) by (etransitivity; [symmetry |]; intuition);
      repeat split; try assumption;
      first [ eapply mod_tie_move; [| eassumption | eassumption ]; assumption
            | eapply mod_tie_move_sym; [ | | eassumption | eassumption ]; [ typeclasses eauto | assumption ]
            | eapply mod_tie_move; [| eassumption |];
              [| eapply mod_tie_move_sym; [ | | eassumption | eassumption ]; [ typeclasses eauto | assumption ] ];
              assumption ].
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ ≈ Γ ∈ per_ctx_env ↘ R /\
      (forall ρ ρ',
          Dom ρ ≈ ρ' ∈ R ->
          Dom ρ' ≈ ρ ∈ R).
Proof.
  simpl.
  induction 1.
  1,2: split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise env).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    symmetry; solve [intuition].
  - apply_relation_equivalence.
    destruct_conjs.
    assert (tail_rel ρ'↯ ρ↯) by eauto.
    assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    eexists; symmetry; handle_per_univ_elem_irrel; intuition.
  - (** A definition.  The swapped context has the same head relation, and its
        environment relation lists the same four ties in another order. *)
    simpl in *; destruct_conjs.
    split.
    + eapply per_ctx_env_cons_def with (head_rel := head_rel); [ eassumption | eassumption | | |].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        econstructor; eauto.
        symmetry; solve [intuition].
      * intros ρ ρ' Hρ.
        assert (tail_rel ρ' ρ) by eauto.
        assert (tail_rel ρ ρ) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
        move_by_relation_equivalence.
        econstructor; try eassumption.
        move_goal_by_relation_equivalence; solve_per.
      * intros ρ ρ'; split; intros Hρ;
          [ apply H2 in Hρ | apply H2 ]; destruct Hρ as [e Hρ]; exists e; tauto.
    + intros ρ ρ' Hρ.
      apply H2 in Hρ; apply H2.
      destruct Hρ as [e ?]; destruct_conjs.
      assert (Ht : tail_rel ρ'↯ ρ↯) by eauto.
      exists Ht.
      assert (tail_rel ρ↯ ρ↯) by (etransitivity; eassumption).
      assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end.
      move_by_relation_equivalence.
      repeat split; try (move_goal_by_relation_equivalence; solve_per);
        eexists; split; try eassumption; move_goal_by_relation_equivalence; solve_per.
  - (** A slot.  The swapped context ties the heads to the same closures. *)
    simpl in *; destruct_conjs.
    match goal with
    | HU : forall ρ ρ', tail_rel ρ ρ' -> per_dmod _ _,
      HE : env_rel <~> _, Hs : forall ρ ρ', tail_rel ρ ρ' -> tail_rel ρ' ρ |- _ =>
        split;
        [ eapply per_ctx_env_cons_mod; [ eassumption | eassumption | | ];
          [ intros ρ ρ' Hρ; apply per_dmod_sym, HU, Hs, Hρ
          | intros ρ ρ'; split; intros Hρ; [ apply HE in Hρ | apply HE ]; destruct_conjs; repeat split; assumption ]
        | intros ρ ρ' Hρ; apply HE in Hρ; apply HE; destruct_conjs; repeat split; eauto ]
    end.
Qed.

Corollary per_ctx_sym : forall Γ Δ R,
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ ≈ Γ ∈ per_ctx_env ↘ R.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym : forall Γ Δ R ρ ρ',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ' ∈ R ->
    Dom ρ' ≈ ρ ∈ R.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    DF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_cumu : mctt.
#[export]
Hint Resolve per_univ_elem_cumu_ge : mctt.
#[export]
Hint Resolve per_subtyp_refl1 : mctt.
#[export]
Hint Resolve per_subtyp_refl2 : mctt.
#[export]
Hint Resolve per_subtyp_trans : mctt.
#[export] Existing Instance per_subtyp_trans_ins.
#[export]
Hint Resolve per_subtyp_cumu : mctt.
#[export] Existing Instance per_ctx_env_morphism_iff_Proper.
#[export] Existing Instance per_ctx_env_morphism_relation_equivalence_Proper.
(** The ties of a definition entry, closed from the instances of the type and
    body premises at the tails in context: the head relations of one type
    value coincide, and the ties follow by symmetry and transitivity. *)
Ltac solve_def_heads :=
  destruct_rel_typ; handle_per_univ_elem_irrel;
  match goal with H : per_univ_elem _ _ _ _ |- _ => pose proof (per_elem_PER H) end;
  move_by_relation_equivalence;
  repeat split; try (move_goal_by_relation_equivalence; solve_per);
  try (eexists; split; [ eassumption | move_goal_by_relation_equivalence; solve_per ]).

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : (DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R1),
        H2 : DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R2 |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : (DF _ ≈ ?Δ ∈ per_ctx_env ↘ ?R1),
        H2 : DF _ ≈ ?Δ ∈ per_ctx_env ↘ ?R2 |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : (DF ?Γ ≈ _ ∈ per_ctx_env ↘ ?R1),
        H2 : DF _ ≈ ?Γ ∈ per_ctx_env ↘ ?R2 |- _ =>
        (** Order matters less here, as [H1] and [H2] cannot be exchanged. *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    (forall Γ3,
        DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R ->
        DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R) /\
      (forall ρ1 ρ2 ρ3,
          Dom ρ1 ≈ ρ2 ∈ R ->
          Dom ρ2 ≈ ρ3 ∈ R ->
          Dom ρ1 ≈ ρ3 ∈ R).
Proof with solve [eauto using per_univ_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise env);
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      (** This cannot be [etransitivity], as the two levels [i] differ. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - destruct_conjs.
    assert (tail_rel ρ1↯ ρ3↯) by eauto.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    eexists.
    apply_relation_equivalence.
    etransitivity; intuition.
  - (** A definition: the right body is moved across the middle one. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    eapply per_ctx_env_cons_def with (head_rel := head_rel); [ eauto | eassumption | | |].
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      eapply per_univ_trans; [| eassumption]; eassumption.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      assert (tail_rel0 ρ ρ) by intuition.
      destruct_rel_typ; handle_per_univ_elem_irrel.
      econstructor; try eassumption.
      solve_def_heads.
    + intros ρ ρ'; split; intros [Ht ?]; destruct_conjs; exists Ht;
        assert (tail_rel ρ↯ ρ↯) by (etransitivity; [| symmetry]; eassumption);
        assert (tail_rel ρ'↯ ρ'↯) by (etransitivity; [symmetry |]; eassumption);
        assert (tail_rel0 ρ↯ ρ↯) by intuition;
        assert (tail_rel0 ρ'↯ ρ'↯) by intuition;
        assert (tail_rel0 ρ↯ ρ'↯) by intuition;
        solve_def_heads.
  - cbn beta in *; destruct_conjs.
    assert (Ht : tail_rel ρ1↯ ρ3↯) by eauto.
    exists Ht.
    assert (tail_rel ρ1↯ ρ1↯) by (etransitivity; [| symmetry]; eassumption).
    assert (tail_rel ρ3↯ ρ3↯) by (etransitivity; [symmetry |]; eassumption).
    solve_def_heads.
  - (** A slot: the closures of the first unit are related to those of the
        last through the middle unit. *)
    destruct IHper_ctx_env as [IHctx IHenv].
    match goal with
    | HU1 : forall ρ ρ', ?T ρ ρ' -> per_dmod (dm_local ρ ?U1 nil) (dm_local ρ' ?U2 nil),
      HU2 : forall ρ ρ', ?T ρ ρ' -> per_dmod (dm_local ρ ?U2 nil) (dm_local ρ' ?U3 nil),
      HE : _ <~> _, HT : PER ?T, Hc : per_ctx_env ?T ?Γ2 ?Γ3 |- per_ctx_env _ (?Γ1 ▹ₘ ?U1) (?Γ3 ▹ₘ ?U3) =>
        eapply per_ctx_env_cons_mod with (tail_rel := T);
        [ apply IHctx; exact Hc | exact HT
        | intros ρ ρ' Hρ; eapply per_dmod_trans;
          [ apply HU1, Hρ | apply HU2; etransitivity; [ symmetry |]; exact Hρ ]
        | intros ρ ρ'; split; intros Hρ;
          [ pose proof (proj2 (HE ρ ρ') Hρ) as Hρ'; destruct Hρ' as (Ht & ? & ? & ? & ?);
            destruct Hρ as (_ & ? & ? & ? & ?); repeat split; assumption
          | destruct Hρ as (Ht & ? & ? & ? & ?);
            assert (T ρ↯ ρ↯) by (etransitivity; [| symmetry ]; exact Ht);
            assert (T ρ'↯ ρ'↯) by (etransitivity; [ symmetry |]; exact Ht);
            repeat split; try assumption;
            (eapply mod_tie_move; [| exact HU1 |]; eassumption) ] ]
    end.
Qed.

Corollary per_ctx_trans : forall Γ1 Γ2 Γ3 R,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R ->
    DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans : forall Γ1 Γ2 R ρ1 ρ2 ρ3,
    DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R ->
    Dom ρ1 ≈ ρ2 ∈ R ->
    Dom ρ2 ≈ ρ3 ∈ R ->
    Dom ρ1 ≈ ρ3 ∈ R.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[local] Instance per_ctx_PER {R} : PER (per_ctx_env R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[local] Instance per_env_PER {R Γ Δ} (H : per_ctx_env R Γ Δ) : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** [per_ctx_env_cons] without its PER premise. *)
Lemma per_ctx_env_cons' : forall {Γ Γ' i A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel), relation domain)
                             env_rel,
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ tail_rel),
        rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> fun ρ ρ' =>
         exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ tail_rel),
           Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop) ->
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_rel.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

Hint Resolve per_ctx_env_cons' : mctt.

End Fixed_GCtx.

#[export] Existing Instance per_ctx_PER.
#[export] Existing Instance per_env_PER.
#[export]
Hint Resolve per_ctx_env_cons' : mctt.
Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ A A' env_relΓA},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ env_relΓA -> 
    exists i (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ), relation domain),
      (forall ρ ρ' (equiv_ρ_ρ' : Dom ρ ≈ ρ' ∈ env_relΓ),
          rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : Dom ρ↯ ≈ ρ'↯ ∈ env_relΓ),
               Dom (ρ 0) ≈ (ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop).
Proof.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ i A ρ A' ρ' R ->
                          Dom m ≈ m' ∈ R).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
  - intros ρ ρ'.
    split; intros; destruct_conjs;
      assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel) by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve eexists; intros; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; destruct H as [? [? []]])
  + (inversion H; subst).

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** A Canonical Extended Context PER

    [per_ctx_env_cons] leaves the head relation of an extended context
    existentially quantified and indexed by the evidence relating the tails.
    The completeness cases for substitutions build the context PER of
    [Δ ▹ S] and relate four environments in it, so they would have to produce
    the head evidence once per link of the chain.

    [per_head] names the head relation once, impredicatively:
    [per_head S S' ρ ρ'] relates what every [per_univ_elem] relating the
    values of [S] and [S'] in [ρ] and [ρ'] relates.  [rel_ctx_extend] makes
    the same choice.  [per_head] does not mention the tail evidence, so the
    extended PER [per_env_extend] is a conjunction rather than a dependent
    pair. *)

Definition per_head (S S' : typ) (ρ ρ' : env) : relation domain :=
  fun m m' =>
    forall i R a a',
      ⟦ S ⟧ ρ ↘ a ->
      ⟦ S' ⟧ ρ' ↘ a' ->
      DF a ≈ a' ∈ per_univ_elem i ↘ R ->
      Dom m ≈ m' ∈ R.

Definition per_env_extend (S S' : typ) (R : relation env) : relation env :=
  fun ρ ρ' =>
    Dom ρ↯ ≈ ρ'↯ ∈ R /\
      Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S' ρ↯ ρ'↯.

(** [per_head] is the PER the types denote, because evaluation is functional
    and [per_univ_elem] is irrelevant in its relation argument.  This direction
    has the content, and it is the one completeness needs: a [per_head] from
    an element PER already at hand. *)
Lemma per_head_of : forall {S S' ρ ρ' i R a a' m m'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom m ≈ m' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR Hm.
  hnf; intros * Ha0 Ha0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** The converse instantiates the universal quantification at the witness. *)
Corollary per_head_iff : forall {S S' ρ ρ' i R a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    R <~> per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR m m'; split.
  - intros Hm. eapply per_head_of; eassumption.
  - intros Hm. eapply Hm; eassumption.
Qed.

(** Hence any related pair of type values is a [per_univ_elem] at the head PER
    of the expressions they came from.  A type judgment reports a level and an
    anonymous element PER, whereas a semantic recursion needs its motive at the
    head PER; this lemma keeps the level and replaces the PER. *)
Corollary per_univ_elem_at_head : forall {S S' ρ ρ' i a a'},
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    Dom a ≈ a' ∈ per_univ i ->
    DF a ≈ a' ∈ per_univ_elem i ↘ (per_head S S' ρ ρ').
Proof.
  intros * Ha Ha' [R HR].
  eapply per_univ_elem_resp_iff; [ exact HR |].
  eapply per_head_iff; eassumption.
Qed.

(** The head PER of a type does not depend on which environments of a related
    family it is read in: any two evaluations of [S] and [S'] whose four values
    form a chain give the same relation.  This lets a judgment proved at one
    pair of environments be used at another, as in every rule whose type is an
    instantiated codomain. *)
Lemma per_head_resp : forall {S S' ρ1 ρ2 ρ3 ρ4 i a1 a2 a3 a4},
    ⟦ S ⟧ ρ1 ↘ a1 ->
    ⟦ S' ⟧ ρ2 ↘ a2 ->
    ⟦ S ⟧ ρ3 ↘ a3 ->
    ⟦ S' ⟧ ρ4 ↘ a4 ->
    rel_chain (per_univ i) ([a1; a2; a3; a4]) ->
    per_head S S' ρ1 ρ2 <~> per_head S S' ρ3 ρ4.
Proof.
  intros * Ha1 Ha2 Ha3 Ha4 Hchain.
  assert (H12 : Dom a1 ≈ a2 ∈ per_univ i) by pairwise.
  destruct H12 as [R HR].
  (** Refining the chain to [R] identifies the two head PERs: each is [R] by
      [per_head_iff], at its own pair of type values. *)
  assert (HchainR : rel_chain (per_univ_elem i R) ([a1; a2; a3; a4]))
    by (eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in).
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ R) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha1 | exact Ha2 | exact HR ] |].
  eapply per_head_iff; [ exact Ha3 | exact Ha4 | exact H34 ].
Qed.

(** [per_head_resp] for an elimination rule, where the two pairs of
    environments differ only in their heads.  There the codomain judgment is
    available at any related pair of arguments, and each link of the chain is
    an instance of it; the middle one is at the crossing pair [(u, y)].  That
    relatedness is a premise rather than derived: [RN] is a PER at every use,
    but requiring it would oblige every caller to provide the instance. *)
Lemma per_head_of_args : forall {i B ρ ρ' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      per_head B B (ρ ↦ x) (ρ' ↦ y) <~> per_head B B (ρ ↦ u) (ρ' ↦ v).
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [bx [by0 [Hbx [Hby0 Hb_xy]]]].
  destruct (Hcod _ _ Huv) as [bu [bv [Hbu [Hbv Hb_uv]]]].
  destruct (Hcod _ _ Huy) as [bu0 [by1 [Hbu0 [Hby1 Hb_uy]]]].
  assert (bu0 = bu) as -> by (eapply functional_eval_exp; eassumption).
  assert (by1 = by0) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Hbx | exact Hby0 | exact Hbu | exact Hbv |].
  apply rel_chain_4; [ exact Hb_xy | symmetry; exact Hb_uy | exact Hb_uv ].
Qed.

(** The codomain at one argument pair, as a [per_univ_elem] at the head PER of
    another pair.  This is how an element PER provided by a judgment is
    identified with the canonical one: irrelevance needs a shared type value,
    which is the codomain's value at the pair the judgment was read at, while
    the PER wanted is the one at the pair the goal names. *)
Corollary per_head_anchor : forall {i B ρ ρ' RN},
    (forall x y,
        Dom x ≈ y ∈ RN ->
        exists b b',
          ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    forall x y u v,
      Dom x ≈ y ∈ RN ->
      Dom u ≈ v ∈ RN ->
      Dom u ≈ y ∈ RN ->
      exists b b',
        ⟦ B ⟧ ρ ↦ x ↘ b /\ ⟦ B ⟧ ρ' ↦ y ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i
               ↘ (per_head B B (ρ ↦ u) (ρ' ↦ v)).
Proof.
  intros * Hcod * Hxy Huv Huy.
  destruct (Hcod _ _ Hxy) as [b [b' [Hb [Hb' [R HR]]]]].
  exists b, b'.
  do 2 (split; [ eassumption |]).
  eapply per_univ_elem_resp_iff; [ exact HR |].
  etransitivity;
    [ eapply per_head_iff; [ exact Hb | exact Hb' | exact HR ]
    | eapply per_head_of_args; eassumption ].
Qed.

(** The premise of [per_ctx_env_cons], at the canonical head relation.  Its
    own premise has the shape that [rel_exp_of_typ_inversion_simple]
    provides. *)
Lemma per_ctx_env_extend : forall {Δ Δ' S S' env_relΔ} {i : nat},
    EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a',
          ⟦ S ⟧ ρ ↘ a /\ ⟦ S' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    EF Δ ▹ S ≈ Δ' ▹ S' ∈ per_ctx_env ↘ per_env_extend S S' env_relΔ.
Proof.
  intros * HΔ HS.
  eapply (per_ctx_env_cons' (i := i) (fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S' ρ ρ'));
    [ eassumption | | ].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ'; split.
    + intros [? ?]; eexists; eassumption.
    + intros [? ?]; split; eassumption.
Qed.

(** The introduction rule of [per_env_extend].  Since the extended PER is a
    conjunction, this is [split], and it applies to any pair of environments,
    not only to literal extensions.  Completeness needs this generality: it
    places both [⟪q ψ⟫ ρ] and [⟦σ ,, M⟧s ρ] in an extended context PER, and
    only the latter is a literal [ρ ↦ m]. *)
Lemma per_env_extend_intro : forall {S S' R ρ ρ'},
    Dom ρ↯ ≈ ρ'↯ ∈ R ->
    Dom (ρ 0) ≈ (ρ' 0) ∈ per_head S S' ρ↯ ρ'↯ ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S' R.
Proof.
  intros * ? ?; split; assumption.
Qed.

(** [per_env_extend_intro] for a literal extension [ρ ↦ m].  The premises of
    the general rule mention [(ρ ↦ m) ↯] and [(ρ ↦ m) 0]; these are convertible
    to [ρ] and [m], but the tactics that discharge head obligations match
    syntactically. *)
Corollary per_env_extend_intro' : forall {S S' R ρ ρ' m m'},
    Dom ρ ≈ ρ' ∈ R ->
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    Dom ρ ↦ m ≈ ρ' ↦ m' ∈ per_env_extend S S' R.
Proof.
  intros * ? ?; apply per_env_extend_intro; assumption.
Qed.

(** ** A Canonical Context PER for a Definition Entry

    [def_tie S M ρ] says that the head of [ρ] is the value of [M] in the tail
    of [ρ], up to the head PER of [S].  Two environments are related at
    [Δ ▸ S ≔ M] when they are related at [Δ ▹ S] and each satisfies the
    tie. *)
Definition def_tie (S : typ) (M : exp) (ρ : env) : Prop :=
  exists m, ⟦ M ⟧ ρ↯ ↘ m /\ Dom m ≈ (ρ 0) ∈ per_head S S ρ↯ ρ↯.

Definition per_env_extend_def (S : typ) (M : exp) (R : relation env) : relation env :=
  fun ρ ρ' =>
    Dom ρ ≈ ρ' ∈ per_env_extend S S R /\ def_tie S M ρ /\ def_tie S M ρ'.

(** The head PER of a type is the same at any two related pairs of tails. *)
Lemma per_head_resp_simple : forall {S R i},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain R ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head S S ρ1 ρ2 <~> per_head S S ρ3 ρ4.
Proof.
  intros * HPER HS * Hchain.
  assert (H12 : Dom ρ1 ≈ ρ2 ∈ R) by pairwise.
  assert (H32 : Dom ρ3 ≈ ρ2 ∈ R) by pairwise.
  assert (H34 : Dom ρ3 ≈ ρ4 ∈ R) by pairwise.
  destruct (HS _ _ H12) as [a1 [a2 [Ha1 [Ha2 Ha12]]]].
  destruct (HS _ _ H32) as [a3 [a2' [Ha3 [Ha2' Ha32]]]].
  destruct (HS _ _ H34) as [a3' [a4 [Ha3' [Ha4 Ha34]]]].
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 |].
  apply rel_chain_4; [ exact Ha12 | symmetry; exact Ha32 | exact Ha34 ].
Qed.

(** The premise [per_ctx_env_cons_def] asks for, at the canonical relation. *)
Lemma per_ctx_env_extend_def : forall {Δ S M env_relΔ} {i : nat},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΔ ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    EF Δ ▸ S ≔ M ≈ Δ ▸ S ≔ M ∈ per_ctx_env ↘ per_env_extend_def S M env_relΔ.
Proof.
  intros * HΔ HS HM.
  assert (HPER : PER env_relΔ) by (eapply per_env_PER; eassumption).
  eapply per_ctx_env_cons_def
    with (head_rel := fun ρ ρ' (_ : Dom ρ ≈ ρ' ∈ env_relΔ) => per_head S S ρ ρ');
    [ eassumption | eassumption | | |].
  - intros ρ ρ' Hρ.
    destruct (HS _ _ Hρ) as [a [a' [Ha [Ha' [R HR]]]]].
    econstructor; try eassumption.
    eapply per_univ_elem_resp_iff; [ eassumption |].
    eapply per_head_iff; eassumption.
  - intros ρ ρ' Hρ.
    destruct (HM _ _ Hρ) as [m [m' [Hm [Hm' Hmm']]]].
    econstructor; eassumption.
  - intros ρ ρ'.
    (** A tie at a single environment and a tie read across the related pair
        are the same, since the head PER does not depend on the tails. *)
    assert (Hmove : forall ρ1 ρ2,
               Dom ρ1 ≈ ρ2 ∈ env_relΔ ->
               (per_head S S ρ1 ρ1 <~> per_head S S ρ1 ρ2) /\
                 (per_head S S ρ2 ρ2 <~> per_head S S ρ1 ρ2)).
    { intros ρ1 ρ2 H12.
      assert (H11 : Dom ρ1 ≈ ρ1 ∈ env_relΔ) by solve_per.
      assert (H22 : Dom ρ2 ≈ ρ2 ∈ env_relΔ) by solve_per.
      split; eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per. }
    split.
    + intros [[Ht Hh] [[m [Hm Htie]] [m' [Hm' Htie']]]].
      destruct (Hmove _ _ Ht) as [H1 H2].
      exists Ht.
      repeat split; try eassumption.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
    + intros [Ht [Hh [[m [Hm Htie]] [_ [[m' [Hm' Htie']] _]]]]].
      destruct (Hmove _ _ Ht) as [H1 H2].
      repeat split; try eassumption.
      * eexists; split; [ eassumption | apply H1; eassumption ].
      * eexists; split; [ eassumption | apply H2; eassumption ].
Qed.

(** The tie propagates along the relation of an assumption entry, and from a
    body to a related one.  So it is enough to establish it at one environment
    of a chain. *)
Lemma def_tie_resp : forall {S M M' R i ρ ρ'},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    Dom ρ ≈ ρ' ∈ per_env_extend S S R ->
    def_tie S M ρ ->
    def_tie S M' ρ'.
Proof.
  intros * HPER HS HM [Ht Hh] [m [Hm Htie]].
  assert (H11 : Dom ρ↯ ≈ ρ↯ ∈ R) by solve_per.
  assert (H22 : Dom ρ'↯ ≈ ρ'↯ ∈ R) by solve_per.
  destruct (HM _ _ Ht) as [m1 [m2 [Hm1 [Hm2 Hm12]]]].
  assert (m1 = m) as -> by (eapply functional_eval_exp; eassumption).
  exists m2; split; [ eassumption |].
  assert (E1 : per_head S S ρ↯ ρ↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  assert (E2 : per_head S S ρ'↯ ρ'↯ <~> per_head S S ρ↯ ρ'↯)
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  apply E2; apply E1 in Htie.
  destruct (HS _ _ Ht) as [a [a' [Ha [Ha' [R' HR']]]]].
  pose proof (per_head_iff Ha Ha' HR') as E3.
  assert (PER R') by (eapply per_elem_PER; eassumption).
  apply E3; apply E3 in Htie, Hh, Hm12.
  solve_per.
Qed.

(** Transporting a [per_head] to another pair of environments, the bridging
    step of the completeness proofs.  The two head relations are equal because
    their types are related in [per_univ]: the first two evaluations and the
    PER describe the source types, the next two evaluations the target types,
    and the last premise relates the two left types.  That suffices because
    [per_univ_elem] is irrelevant on either side. *)
Lemma per_head_bridge : forall {S S' ρ ρ' T T' u u' i R a a' b b' m m'},
    Dom m ≈ m' ∈ per_head S S' ρ ρ' ->
    ⟦ S ⟧ ρ ↘ a ->
    ⟦ S' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    ⟦ T ⟧ u ↘ b ->
    ⟦ T' ⟧ u' ↘ b' ->
    Dom a ≈ b ∈ per_univ i ->
    Dom m ≈ m' ∈ per_head T T' u u'.
Proof.
  intros * Hm Ha Ha' HR Hb Hb' [? Hab].
  assert (Hmm : Dom m ≈ m' ∈ R) by (eapply Hm; eassumption).
  hnf; intros * Hb0 Hb0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** ** A Canonical Function PER

    The same construction one level down.  [per_univ_elem_core_pi] leaves the
    codomain family [out_rel] existentially quantified and indexed by the
    evidence relating the two arguments, so a Π-value's element PER is
    determined only up to that choice.  The four-value pattern of a Π-type
    compares Π-values whose codomain expressions and environments all differ
    ([B[q σ]] at [ρ], [B] at [⟦σ⟧ρ], …), yet all its links must be at one
    element PER.

    [per_pi] names the family canonically, with [per_head] as the codomain
    relation: the PER the codomain denotes at [ρ ↦ c] and [ρ' ↦ c'] is a head
    PER.  It is independent of the evidence and of the level, so one [per_pi]
    serves every link. *)

Definition per_pi (in_rel : relation domain) (B : typ) (ρ : env) (B' : typ) (ρ' : env) : relation domain :=
  fun f f' =>
    forall c c' (equiv_c_c' : Dom c ≈ c' ∈ in_rel),
      rel_mod_app f c f' c' (per_head B B' (ρ ↦ c) (ρ' ↦ c')).

(** Building a Π-value at [per_pi].  The codomain premise has the element PER
    existentially quantified, which is the shape a four-value chain provides
    after [destruct_per_univ_chain]; [per_head_iff] turns any such PER into the
    canonical one. *)
Lemma per_univ_elem_pi_canonical : forall {i a a' in_rel ρ B ρ' B'},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b' R,
          ⟦ B ⟧ ρ ↦ c ↘ b /\
          ⟦ B' ⟧ ρ' ↦ c' ↘ b' /\
          DF b ≈ b' ∈ per_univ_elem i ↘ R) ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ').
Proof.
  intros * Ha HB.
  eapply (per_univ_elem_pi' _ _ _ _ _ _ _ in_rel
            (fun c c' (_ : Dom c ≈ c' ∈ in_rel) =>
               per_head B B' (ρ ↦ c) (ρ' ↦ c')));
    [ eassumption | | reflexivity ].
  intros c c' equiv_c_c'.
  destruct (HB _ _ equiv_c_c') as [b [b' [R [Hb [Hb' HR]]]]].
  econstructor; try eassumption.
  eapply per_univ_elem_resp_iff; [ eassumption |].
  eapply per_head_iff; eassumption.
Qed.

(** Whatever PER a Π-value carries, it is [per_pi]; this justifies
    application.  The two levels are unrelated, since [per_univ_elem]
    irrelevance is cross-level, so a Π-type from one judgment and a domain from
    another need no lifting. *)
Corollary per_pi_iff : forall {i j a a' in_rel ρ B ρ' B' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
    DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem j ↘ R ->
    R <~> per_pi in_rel B ρ B' ρ'.
Proof.
  intros * Ha HΠ.
  invert_per_univ_elem HΠ.
  rename x into out_rel; rename H into Hout; rename H0 into HR.
  (** [HR] identifies [R] with the family-indexed relation; it remains to show
      the family is pointwise the canonical head PER.  Transitivity of
      [relation_equivalence] must be used before introducing the two values:
      afterwards the goal is a [pointwise_lifting], where neither [rewrite] nor
      [etransitivity] applies. *)
  etransitivity; [ exact HR |].
  intros f f'; split; intros Hf c c' equiv_c_c';
    specialize (Hf _ _ equiv_c_c');
    destruct (Hout _ _ equiv_c_c') as [b b' Hb Hb' Hbb'].
  - rewrite <- (per_head_iff Hb Hb' Hbb'); exact Hf.
  - rewrite (per_head_iff Hb Hb' Hbb'); exact Hf.
Qed.

(** The four-value pattern of a Π-type at one element PER, as required by
    every semantic judgment whose type is a Π.  Each link is built by
    [per_univ_elem_pi_canonical] at its own codomain pair and so carries its
    own [per_pi]; the three agree by irrelevance, since consecutive links share
    a Π-value.  The chain is stated at the inner link's PER: the only link
    whose sides are both unsubstituted, and the one an application reads its
    output PER from.

    The domain is a four-value pattern already at [in_rel], which by weak
    functionality is what a semantic type judgment provides
    ([functionalize_per_univ_chain]).  The three codomain premises are, in
    order, the three obligations produced by [rel_exp_of_typ_under_ctx_q]. *)
Lemma per_univ_elem_pi_chain : forall {i in_rel a1 a2 a3 a4 B1 ρ1 B2 ρ2 B3 ρ3 B4 ρ4},
    rel_chain (per_univ_elem i in_rel) ([a1; a2; a3; a4]) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B1 ⟧ ρ1 ↦ c ↘ b /\ ⟦ B2 ⟧ ρ2 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B2 ⟧ ρ2 ↦ c ↘ b /\ ⟦ B3 ⟧ ρ3 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    (forall c c',
        Dom c ≈ c' ∈ in_rel ->
        exists b b', ⟦ B3 ⟧ ρ3 ↦ c ↘ b /\ ⟦ B4 ⟧ ρ4 ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
    rel_chain (per_univ_elem i (per_pi in_rel B2 ρ2 B3 ρ3))
      ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2; Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]).
Proof.
  intros * Hchain HB12 HB23 HB34.
  assert (H12 : DF a1 ≈ a2 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H23 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  assert (H34 : DF a3 ≈ a4 ∈ per_univ_elem i ↘ in_rel) by pairwise.
  (** One [per_univ_elem_pi_canonical] per link, adapting the premise's
      [per_univ] to the [exists R] the lemma wants. *)
  assert (Hlink : forall B ρ B' ρ' a a',
             DF a ≈ a' ∈ per_univ_elem i ↘ in_rel ->
             (forall c c',
                 Dom c ≈ c' ∈ in_rel ->
                 exists b b', ⟦ B ⟧ ρ ↦ c ↘ b /\ ⟦ B' ⟧ ρ' ↦ c' ↘ b' /\ Dom b ≈ b' ∈ per_univ i) ->
             DF Πᵈ a ρ B ≈ Πᵈ a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ')).
  { intros * Ha HB.
    apply per_univ_elem_pi_canonical; [ eassumption |].
    intros c c' Hc.
    destruct (HB _ _ Hc) as [b [b' [Hb [Hb' [R HR]]]]].
    exists b, b', R; repeat split; eassumption. }
  pose proof (Hlink _ _ _ _ _ _ H12 HB12) as HL1.
  pose proof (Hlink _ _ _ _ _ _ H23 HB23) as HL2.
  pose proof (Hlink _ _ _ _ _ _ H34 HB34) as HL3.
  (** The three links are a chain in [per_univ i], so weak functionality puts
      them at one PER, and uniqueness, with [HL2] as anchor, makes it the inner
      link's.  [handle_per_univ_elem_irrel] would keep an unpredictable one of
      the three [per_pi]s. *)
  assert (Hpi : rel_chain (per_univ i)
                  ([Πᵈ a1 ρ1 B1; Πᵈ a2 ρ2 B2;
                   Πᵈ a3 ρ3 B3; Πᵈ a4 ρ4 B4]))
    by (apply rel_chain_4; eexists; eassumption).
  functionalize_per_univ_chain Hpi R.
  retype_rel_chain Hpi HL2 Hpi.
  exact Hpi.
Qed.

(** ** Closing an Extended Context PER Goal

    Every completeness proof in an extended context ends the same way, with
    these three tactics.

    - [destruct_per_univ_chain] turns a four-value chain in [per_univ i] into
      the three [per_univ_elem] hypotheses that [handle_per_univ_elem_irrel]
      works on.  It goes through [per_univ_chain_functional], so the three are
      at one element PER rather than three independent ones.
    - [solve_per_head] discharges a [per_head] goal.  [per_head] quantifies
      over an arbitrary [per_univ_elem] relating the two type values, so the
      proof is always the same: introduce it, identify its two values with
      known ones, let irrelevance identify its PER with that of the term
      chain, and read the pair off that chain.
    - [solve_per_env_extend_chain] relates a chain of extended environments in
      an extended context PER.  [per_env_extend_intro'] splits each link into
      a tail and a head; the tails come from the chain of the underlying
      substitution, and the heads are bridged.  The chain may have any length:
      substitution cases need four environments, while rules with a premise in
      an extended context need every extension of the four tails by either of
      the two heads. *)
End Fixed_GCtx.

Ltac destruct_per_univ_chain H :=
  apply per_univ_chain_functional in H;
  destruct H as [? H];
  destruct H as [? [? ?]].

Ltac solve_per_head :=
  hnf; intros ? ? ? ? ? ? ?;
  functional_eval_rewrite_clear;
  handle_per_univ_elem_irrel;
  pairwise.

Section Fixed_GCtx.
  Context {GC : GCtx}.


End Fixed_GCtx.

(** The links are peeled by matching the goal's shape rather than with
    [first]: [rel_chain R [x; y]] is convertible to [R x y], so an unguarded
    [apply rel_chain_of_pair] would also fire on a link goal, and an unguarded
    [apply rel_chain_cons] would peel past the last link. *)
Ltac solve_per_env_extend_chain :=
  repeat
    match goal with
    | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
  apply per_env_extend_intro'; first [ pairwise | solve_per_head ].

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma per_ctx_respects_length : forall {Γ Γ'},
    Exp Γ ≈ Γ' ∈ per_ctx ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

Lemma per_ctx_subtyp_to_env : forall Γ Δ,
    SubE Γ <: Δ ->
    exists R R',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R /\
        EF Δ ≈ Δ ∈ per_ctx_env ↘ R'.
Proof.
  destruct 1; destruct_all.
  1: repeat eexists; econstructor; apply Equivalence_Reflexive.
  all: eauto.
Qed.

(** An inclusion of context PERs holds for any other names of them. *)
Lemma per_ctx_env_incl_irrel : forall Γ Δ R R1 R' R2 ρ ρ',
    (forall ρ ρ', R1 ρ ρ' -> R2 ρ ρ') ->
    R ρ ρ' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R1 ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R2 ->
    R' ρ ρ'.
Proof.
  intros * Hinc Hρ HR HR1 HR' HR2.
  apply (per_ctx_env_right_irrel _ _ _ _ _ HR' HR2), Hinc, (per_ctx_env_right_irrel _ _ _ _ _ HR HR1), Hρ.
Qed.

Lemma per_ctx_env_subtyping : forall Γ Δ,
    SubE Γ <: Δ ->
    forall R R' ρ ρ',
      EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
      EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    try solve [ eapply per_ctx_env_incl_irrel; eassumption ];
    handle_per_ctx_env_irrel;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    apply_relation_equivalence;
    trivial.

  destruct_all.
  assert (Dom ρ↯ ≈ ρ'↯ ∈ tail_rel0) by intuition.
  unshelve eexists; [eassumption |].
  destruct_rel_typ.
  eapply per_elem_subtyping with (i := max x (max i0 i)); try eassumption.
  - eauto using per_subtyp_cumu_right.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
Qed.

Lemma per_ctx_subtyp_refl1 : forall Γ Δ R,
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    SubE Γ <: Δ.
Proof.
  induction 1; mauto.

  - assert (exists R, EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R) by
      (eexists; eapply per_ctx_env_cons'; eassumption).
    destruct_all.
    econstructor; try solve [saturate_refl; mauto 2].
    intros.
    destruct_rel_typ.
    simplify_evals.
    eauto using per_subtyp_refl1.
  - (** A definition: both sides' environments are the related ones. *)
    assert (HR : EF Γ ▸ A ≔ M ≈ Γ' ▸ A' ≔ M' ∈ per_ctx_env ↘ env_rel) by (econstructor; eassumption).
    eapply per_ctx_subtyp_def with (env_rel := env_rel) (env_rel' := env_rel);
      [ assumption
      | etransitivity; [ exact HR | symmetry; exact HR ]
      | etransitivity; [ symmetry; exact HR | exact HR ]
      | auto ].
  - (** A slot, likewise. *)
    assert (HR : EF Γ ▹ₘ U ≈ Γ' ▹ₘ U' ∈ per_ctx_env ↘ env_rel) by (econstructor; eassumption).
    eapply per_ctx_subtyp_mod with (env_rel := env_rel) (env_rel' := env_rel);
      [ assumption
      | etransitivity; [ exact HR | symmetry; exact HR ]
      | etransitivity; [ symmetry; exact HR | exact HR ]
      | auto ].
Qed.

Lemma per_ctx_subtyp_refl2 : forall Γ Δ R,
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    SubE Δ <: Γ.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_trans : forall Γ1 Γ2,
    SubE Γ1 <: Γ2 ->
    forall Γ3,
      SubE Γ2 <: Γ3 ->
      SubE Γ1 <: Γ3.
Proof.
  induction 1; intros;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    mauto 1;
    clear_PER.

  1: handle_per_ctx_env_irrel.
  1: econstructor; try eassumption.
  - firstorder.
  - instantiate (1 := max i i0).
    intros.
    assert (Dom ρ ≈ ρ' ∈ tail_rel0) by (eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    etransitivity.
    + intuition mauto using per_subtyp_cumu_left.
    + intuition mauto using per_subtyp_cumu_right.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
  - (** A definition: the inclusions of environments compose. *)
    match goal with HS : SubE (e :: Γ') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      destruct Γ3 as [| e3 Γ3']; [ inversion HS |];
      assert (SubE Γ' <: Γ3') by (inversion HS; assumption);
      eapply per_ctx_subtyp_def with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
  - (** A slot: the inclusions compose. *)
    match goal with HS : SubE (?Γ'' ▹ₘ ?U'') <: ?Γ3 |- _ =>
      destruct (per_ctx_subtyp_to_env _ _ HS) as [R2 [R3 [HR2 HR3]]];
      inversion HS; subst;
      eapply per_ctx_subtyp_mod with (env_rel' := R3); [ eauto | eassumption | eassumption |];
      intros ρ ρ' Hρ;
      eapply per_ctx_env_subtyping; [ exact HS | eassumption | eassumption | ];
      handle_per_ctx_env_irrel; eauto
    end.
Qed.

Hint Resolve per_ctx_subtyp_trans : mctt.

#[local] Instance per_ctx_subtyp_trans_ins : Transitive per_ctx_subtyp.
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.

(** * Context PERs Respect Pointwise Equality of Environments

    Evaluating a substitution determines its result only up to [env_eq]
    ([functional_eval_sub]), so every use of a context PER in the completeness
    proof needs this lemma.  It does not follow from evaluation respecting
    [env_eq], which is false because a closure captures its environment.  It
    holds because a context PER inspects an environment only pointwise, and
    its head relations at pointwise-equal environments coincide up to [<~>] by
    irrelevance. *)
(** The closures of two units related over related tails, read at two
    related tails in either combination. *)
Lemma mod_closure_move : forall (T : relation env) U U' ρ1 ρ2,
    PER T -> T ρ1 ρ2 ->
    (forall ρ ρ', T ρ ρ' -> per_dmod (dm_local ρ U nil) (dm_local ρ' U' nil)) ->
    per_dmod (dm_local ρ1 U nil) (dm_local ρ2 U nil) /\
    per_dmod (dm_local ρ1 U nil) (dm_local ρ2 U' nil) /\
    per_dmod (dm_local ρ1 U' nil) (dm_local ρ2 U nil) /\
    per_dmod (dm_local ρ1 U' nil) (dm_local ρ2 U' nil).
Proof.
  intros * HT H12 HP.
  assert (H11 : T ρ1 ρ1) by (etransitivity; [ exact H12 | symmetry; exact H12 ]).
  assert (H22 : T ρ2 ρ2) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
  pose proof (HP _ _ H12) as A; pose proof (HP _ _ H11) as B; pose proof (HP _ _ H22) as C.
  assert (D1 : per_dmod (dm_local ρ1 U nil) (dm_local ρ2 U nil)) by (eapply per_dmod_trans; [ exact A | apply per_dmod_sym; exact C ]).
  split; [ exact D1 | split; [ exact A | split ] ].
  - eapply per_dmod_trans; [ apply per_dmod_sym; exact B | exact D1 ].
  - eapply per_dmod_trans; [ apply per_dmod_sym; exact B | exact A ].
Qed.

Lemma per_ctx_env_resp_env_eq : forall {Γ Δ R},
    EF Γ ≈ Δ ∈ per_ctx_env ↘ R ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_eq ρ1 ρ2 ->
      env_eq ρ1' ρ2' ->
      Dom ρ1 ≈ ρ1' ∈ R ->
      Dom ρ2 ≈ ρ2' ∈ R.
Proof.
  intros * H.
  induction H; intros * Heq Heq' HR; apply_relation_equivalence; [ trivial | | | ].
  3: { (** A slot: the heads are the same, and the closures over the new
         tails are related to those over the old ones. *)
    destruct HR as (Dtail1 & T1 & T2 & T3 & T4).
    assert (Hd : env_eq ρ1↯ ρ2↯) by (now rewrite Heq).
    assert (Hd' : env_eq ρ1'↯ ρ2'↯) by (now rewrite Heq').
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption).
    assert (D11 : Dom ρ1↯ ≈ ρ1↯ ∈ tail_rel) by solve_per.
    assert (D11' : Dom ρ1'↯ ≈ ρ1'↯ ∈ tail_rel) by solve_per.
    assert (D12 : Dom ρ1↯ ≈ ρ2↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | exact D11 ]).
    assert (D12' : Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | exact D11' ]).
    destruct (mod_closure_move _ _ _ _ _ _ D12 H0) as (M1 & M2 & M3 & M4).
    destruct (mod_closure_move _ _ _ _ _ _ D12' H0) as (M1' & M2' & M3' & M4').
    rewrite <- (env_eq_mod _ _ Heq 0), <- (env_eq_mod _ _ Heq' 0).
    repeat split; [ exact Dtail2 | .. ]; eapply per_dmod_trans; eassumption. }
  all: destruct HR as [Dtail1 Hhead1];
    assert (Hd : env_eq ρ1↯ ρ2↯) by (now rewrite Heq);
    assert (Hd' : env_eq ρ1'↯ ρ2'↯) by (now rewrite Heq');
    assert (Dmix : Dom ρ1↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption ]);
    assert (Dtail2 : Dom ρ2↯ ≈ ρ2'↯ ∈ tail_rel) by (eapply IHper_ctx_env; eassumption);
    unshelve eexists; try exact Dtail2;
    rewrite <- (env_eq_var _ _ Heq 0), <- (env_eq_var _ _ Heq' 0).
  - pose proof (H0 _ _ Dtail1).
    pose proof (H0 _ _ Dmix).
    pose proof (H0 _ _ Dtail2).
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    first [ eassumption | use_relation_equivalence; eassumption ].
  - (** A definition: the bodies at the new tails are related to the old
        heads through the other side's body. *)
    destruct_conjs.
    assert (Dom ρ2↯ ≈ ρ2↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ2'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    assert (Dom ρ1'↯ ≈ ρ2'↯ ∈ tail_rel) by solve_per.
    solve_def_heads.
Qed.

#[local] Instance per_ctx_env_Proper {Γ Δ R} (H : EF Γ ≈ Δ ∈ per_ctx_env ↘ R) :
  Proper (env_eq ==> env_eq ==> iff) R.
Proof.
  intros ρ1 ρ2 Heq ρ1' ρ2' Heq'.
  split; intros; eapply per_ctx_env_resp_env_eq;
    try eassumption; symmetry; eassumption.
Qed.

(** Cumulativity on [per_univ], along the order of indices. *)
Corollary per_univ_cumu_uidx : forall {u v a a'},
    uidx_le u v ->
    Dom a ≈ a' ∈ per_univ u ->
    Dom a ≈ a' ∈ per_univ v.
Proof. intros * ? [R ?]; eexists; eapply per_univ_elem_cumu_uidx; eassumption. Qed.

(** The universe at an index is in every universe above it, at either tier,
    with its own elements as the relation. *)
Lemma per_univ_elem_univ_val : forall u i,
    uidx_lt u i ->
    DF univ_val u ≈ univ_val u ∈ per_univ_elem i ↘ per_univ u.
Proof.
  intros [n | n] * Hlt; cbn;
    [ apply per_univ_elem_core_suniv' | apply per_univ_elem_core_univ' ]; solve [ assumption | reflexivity ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_subtyp_trans : mctt.
#[export] Existing Instance per_ctx_subtyp_trans_ins.
#[export] Existing Instance per_ctx_env_Proper.

#[export]
Hint Resolve per_univ_elem_univ_val : mctt.
