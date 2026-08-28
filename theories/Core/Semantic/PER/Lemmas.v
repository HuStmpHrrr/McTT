From Stdlib Require Import Equivalence Lia List Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Chain PER.CoreTactics PER.Definitions.
Import Domain_Notations.
Import ListNotations.

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
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_bot_sym : mctt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mctt.

#[export]
Instance per_bot_PER : PER per_bot.
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot : forall {n},
    {{ Dom !n ≈ !n ∈ per_bot }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mctt.

Lemma per_top_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_sym : mctt.

Lemma per_top_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ l ∈ per_top }} ->
    {{ Dom m ≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mctt.

#[export]
Instance per_top_PER : PER per_top.
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mctt.

Lemma per_top_typ_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mctt.

Lemma per_top_typ_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mctt.

#[export]
Instance per_top_typ_PER : PER per_top_typ.
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.

Lemma per_nat_sym : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mctt.

Lemma per_nat_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mctt.

#[export]
Instance per_nat_PER : PER per_nat.
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
Qed.

Lemma per_ne_sym : forall m n,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mctt.

Lemma per_ne_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mctt.

#[export]
Instance per_ne_PER : PER per_ne.
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof with mautosolve.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    induction Horig using per_univ_elem_ind; basic_per_univ_elem_econstructor; eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor...
Qed.

(** The same morphism in forward form.  [apply -> per_univ_elem_morphism_iff]
    requires the level to be known already, and building a context PER is exactly
    the situation where it is not: the level of the head relation is pinned down
    only by the witness supplied for it.  Consuming the witness first leaves the
    [<~>] as the sole goal — and leaves the relation being moved *to* implicit,
    so the caller never has to spell out the impredicative head relation. *)
Lemma per_univ_elem_resp_iff : forall {i R R' a a'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    (R <~> R') ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R' }}.
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
  {{ Dom f ≈ f' ∈ per_bot }} ->
  {{ Dom a ≈ a' ∈ per_top }} ->
  {{ Dom f a ≈ f' a' ∈ per_bot }}.
Proof.
  intros. intros s.
  destruct (H s) as [? []].
  destruct (H0 s) as [? []].
  mauto.
Qed.

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

(** [apply_relation_equivalence] only ever *rewrites*, and [setoid_rewrite] needs
    the relation to be rewritable in place.  When both sides of the [<~>] are
    applications — as the head relations [head_rel _ _ D] of a context PER are,
    for two different witnesses [D] — the conclusion is left untouched.  This
    closes such a conclusion from the biconditional directly. *)
Ltac use_relation_equivalence :=
  match goal with
  | H : ?R1 <~> ?R2 |- ?R1 _ _ => apply H
  | H : ?R1 <~> ?R2 |- ?R2 _ _ => apply H
  end.

Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a ≈ b' ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof with (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear; econstructor; intuition).
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  induction Horig using per_univ_elem_ind; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros.
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder...
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder...
Qed.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ^?a ≈ ^?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^?b' ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Lemma per_univ_elem_sym : forall i R a b,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ a ∈ per_univ_elem i ↘ R }} /\
      (forall m m',
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Dom m' ≈ m ∈ R }}).
Proof with mautosolve.
  simpl.
  induction 1 using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1...
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]...
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
  - split; [econstructor | intros; apply_relation_equivalence]...
Qed.

Corollary per_univ_sym : forall i R a b,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ a ∈ per_univ_elem i ↘ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_sym' : forall i a b,
    {{ Dom a ≈ b ∈ per_univ i }} ->
    {{ Dom b ≈ a ∈ per_univ i }}.
Proof.
  intros * [? ?%per_univ_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a' ≈ b ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b' ≈ a ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      (** Order matters less here as H1 and H2 cannot be exchanged *)
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

Lemma per_univ_elem_trans : forall i R a1 a2,
    per_univ_elem i R a1 a2 ->
    (forall j a3,
        per_univ_elem j R a2 a3 ->
        per_univ_elem i R a1 a3) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof with (basic_per_univ_elem_econstructor; mautosolve 4).
  induction 1 using per_univ_elem_ind;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (** univ case *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** nat case *)
    idtac...
  - (** pi case *)
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
      handle_per_univ_elem_irrel...
  - (** fun case *)
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (** neut case *)
    idtac...
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
    {{ Dom a1 ≈ a2 ∈ per_univ i }} ->
    {{ Dom a2 ≈ a3 ∈ per_univ j }} ->
    {{ Dom a1 ≈ a3 ∈ per_univ i }}.
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

#[export]
Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[export]
Instance per_univ_PER' {i} : PER (per_univ i).
Proof.
  split.
  - auto using per_univ_sym'.
  - eauto using per_univ_trans'.
Qed.

#[export]
Instance per_elem_PER {i R a b} `(H : per_univ_elem i R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** [per_elem_PER] off a *folded* chain, so that [solve_chain_PER] does not force
    a pair to be read off one first. *)
#[export]
Instance per_elem_chain_PER {i R l} `(H : rel_chain (per_univ_elem i R) l) : PER R.
Proof.
  destruct (rel_chain_shape _ _ H) as [a [b [l' ->]]].
  eapply per_elem_PER; pairwise.
Qed.

(** ** Chains of Types

    A chain in [per_univ i] — which is what a semantic *type* judgment hands over,
    each link carrying its own element PER — refined to a chain at one PER, given
    any one of its pairs at that PER.  This is the only use irrelevance is ever
    put to in the Completeness layer, and it is the step that makes a type
    judgment usable: what the consumer wants is not "each pair is related at some
    PER" but "all of them at *the* PER", namely the one the judgment's own
    element chain lives in.

    Both moves are one irrelevance each, through the anchor's left value [x]: to
    the pair [(x, u)], which shares [x]; and thence to [(u, v)], which shares
    [u]. *)
Lemma per_univ_chain_at_in : forall {i R l x y},
    rel_chain (per_univ i) l ->
    In x l ->
    In y l ->
    {{ DF x ≈ y ∈ per_univ_elem i ↘ R }} ->
    rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain Hx Hy HR.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  apply rel_chain_intro; intros u v Hu Hv.
  assert (Hxu : {{ Dom x ≈ u ∈ per_univ i }}) by pairwise.
  destruct Hxu as [Rxu HRxu].
  assert (HRxu' : {{ DF x ≈ u ∈ per_univ_elem i ↘ R }})
    by (eapply per_univ_elem_resp_iff; [ exact HRxu |];
        eapply per_univ_elem_right_irrel; [ exact HRxu | exact HR ]).
  assert (Huv : {{ Dom u ≈ v ∈ per_univ i }}) by pairwise.
  destruct Huv as [Ruv HRuv].
  eapply per_univ_elem_resp_iff; [ exact HRuv |].
  eapply per_univ_elem_cross_irrel; [ exact HRuv | exact HRxu' ].
Qed.

(** Weak functionality of [per_univ i]: a chain in it is *already* a chain at one
    element PER, with no anchor supplied from outside.  This is the paper's
    [S ⊆_R ↘ R'] in full; [per_univ_chain_at_in] is the case where the caller
    insists on a particular [R'].  Any link's PER will do, all of them being
    logically equivalent, so the first is taken. *)
Corollary per_univ_chain_functional : forall {i l},
    rel_chain (per_univ i) l ->
    exists R, rel_chain (per_univ_elem i R) l.
Proof.
  intros * Hchain.
  destruct (rel_chain_shape _ _ Hchain) as [a [b [l' ->]]].
  assert (Hab : {{ Dom a ≈ b ∈ per_univ i }}) by pairwise.
  destruct Hab as [R HR].
  exists R.
  eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in.
Qed.

(** Names the element PER of a chain in [per_univ i] and refines the chain to it,
    in place.  This is the whole use a type judgment is ever put to, and by weak
    functionality it takes no anchor and loses nothing: every pair of the chain
    remains available, at [R], through [pairwise]. *)
Ltac functionalize_per_univ_chain H R :=
  apply per_univ_chain_functional in H; destruct H as [R H].

(** [pairwise] at a [per_univ i] goal, whose existential the refined chain no
    longer carries. *)
Ltac pairwise_univ := first [ pairwise | eexists; pairwise ].

(** The other half of weak functionality — that the output PER is *unique*, which
    is what makes [S ⊆_R ↘ R'] well defined.  A chain determines its [R'] from a
    single value it shares with anything else in the universe: reflexivity at
    that value is available because the chain is at a PER, and then irrelevance
    needs no second value. *)
Lemma per_univ_chain_rel_irrel : forall {i j R R' l x y},
    rel_chain (per_univ_elem i R) l ->
    {{ DF x ≈ y ∈ per_univ_elem j ↘ R' }} ->
    In x l ->
    R <~> R'.
Proof.
  intros * Hchain Hanchor Hx.
  assert (Hxx : {{ DF x ≈ x ∈ per_univ_elem i ↘ R }})
    by (eapply rel_chain_refl; first [ eassumption | solve_chain_PER ]).
  eapply per_univ_elem_right_irrel; [ exact Hxx | exact Hanchor ].
Qed.

(** Uniqueness put to work: [retype_rel_chain Htyp Hanchor H] moves [H] between
    the element PER the type chain [Htyp] reported and the one [Hanchor] names.
    The two need share only one value, and only [H] says which direction is
    wanted, so both are tried.  [H] may be a [rel_chain] — [rel_chain_Proper] is
    what rewrites it — or a bare pair, either at the relation itself or under the
    [per_head] of a type whose values the anchor is about. *)
Ltac retype_rel_chain Htyp Hanchor H :=
  let Hiff := fresh "Hiff" in
  pose proof (per_univ_chain_rel_irrel Htyp Hanchor ltac:(solve_in)) as Hiff;
  first [ rewrite Hiff in H | rewrite <- Hiff in H ];
  clear Hiff.

(** This lemma gets rid of the unnecessary PER premise. *)
Lemma per_univ_elem_pi' :
  forall i a a' ρ B ρ' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
    elem_rel,
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel}} ->
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_univ_elem i) B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }}.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

#[export]
Hint Resolve per_univ_elem_pi' : mctt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j a a' in_rel ρ ρ' B B' elem_rel},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
    {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem j ↘ elem_rel }} ->
    exists (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain),
      (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
          rel_mod_eval (per_univ_elem j) B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) /\
        (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')).
Proof.
  intros * Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_typ j B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

Lemma per_univ_elem_cumu : forall i a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R }}.
Proof with solve [eauto].
  simpl.
  induction 1 using per_univ_elem_ind; subst;
    per_univ_elem_econstructor; eauto.
  intros.
  destruct_rel_mod_eval.
  econstructor...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu : mctt.

Lemma per_univ_elem_cumu_ge : forall i i' a0 a1 R,
    i <= i' ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu_ge : mctt.

Lemma per_univ_elem_cumu_max_left : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (i <= max i j) by lia...
Qed.

Lemma per_univ_elem_cumu_max_right : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem j ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (j <= max i j) by lia...
Qed.

Lemma per_subtyp_to_univ_elem : forall a b i,
    {{ Sub a <: b at i }} ->
    exists R R',
      {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} /\
        {{ DF b ≈ b ∈ per_univ_elem i ↘ R' }}.
Proof.
  destruct 1; do 2 eexists; mauto;
    split; per_univ_elem_econstructor; mauto;
    try apply Equivalence_Reflexive.
  lia.
Qed.


Lemma per_elem_subtyping : forall A B i,
    {{ Sub A <: B at i }} ->
    forall R R' a b,
      {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} ->
      {{ DF B ≈ B ∈ per_univ_elem i ↘ R' }} ->
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
    {{ Sub a <: b at i }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ b' ∈ per_univ_elem i ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub a <: b at i }}.
Proof.
  simpl; induction 1 using per_univ_elem_ind;
    subst;
    mauto;
    destruct_all.
  assert ({{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }})
    by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto).
  saturate_refl.
  econstructor; eauto.
  intros;
    destruct_rel_mod_eval;
    functional_eval_rewrite_clear;
    trivial.
Qed.

#[export]
Hint Resolve per_subtyp_refl1 : mctt.

Lemma per_subtyp_refl2 : forall a b i R,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub b <: a at i }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_refl2 : mctt.

Lemma per_subtyp_trans : forall a1 a2 i,
    {{ Sub a1 <: a2 at i }} ->
    forall a3,
      {{ Sub a2 <: a3 at i }} ->
      {{ Sub a1 <: a3 at i }}.
Proof.
  induction 1; intros ? Hsub; simpl in *.
  1-3: progressive_inversion; mauto.
  - econstructor; lia.
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

#[export]
Hint Resolve per_subtyp_trans : mctt.

#[export]
Instance per_subtyp_trans_ins i : Transitive (per_subtyp i).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp : forall a b i a' b' R R',
    {{ Sub a <: b at i }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ b' ∈ per_univ_elem i ↘ R' }} ->
    {{ Sub a' <: b' at i }}.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_subtyp_cumu : forall a1 a2 i,
    {{ Sub a1 <: a2 at i }} ->
    forall j,
      i <= j ->
      {{ Sub a1 <: a2 at j }}.
Proof.
  induction 1; intros; econstructor; mauto.
  lia.
Qed.

#[export]
Hint Resolve per_subtyp_cumu : mctt.

Lemma per_subtyp_cumu_left : forall a1 a2 i j,
    {{ Sub a1 <: a2 at i }} ->
    {{ Sub a1 <: a2 at max i j }}.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Lemma per_subtyp_cumu_right : forall a1 a2 i j,
    {{ Sub a1 <: a2 at i }} ->
    {{ Sub a1 <: a2 at max j i }}.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
  split; intros [].
  - assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition...
  - assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition...
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }} /\
      (forall ρ ρ',
          {{ Dom ρ ≈ ρ' ∈ R }} ->
          {{ Dom ρ' ≈ ρ ∈ R }}).
Proof with solve [intuition].
  simpl.
  induction 1; split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise env).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_conjs.
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    eexists; symmetry; handle_per_univ_elem_irrel; intuition.
Qed.

Corollary per_ctx_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym : forall Γ Δ R ρ ρ',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom ρ' ≈ ρ ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^_ ≈ ^?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (** Order matters less here as H1 and H2 cannot be exchanged *)
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

Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R }} ->
        {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R }}) /\
      (forall ρ1 ρ2 ρ3,
          {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
          {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
          {{ Dom ρ1 ≈ ρ3 ∈ R }}).
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
      (** This one cannot be replaced with `etransitivity` as we need different `i`s. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - destruct_conjs.
    assert (tail_rel d{{{ ρ1 ↯ }}} d{{{ ρ3 ↯ }}}) by eauto.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    eexists.
    apply_relation_equivalence.
    etransitivity; intuition.
Qed.

Corollary per_ctx_trans : forall Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans : forall Γ1 Γ2 R ρ1 ρ2 ρ3,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
    {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
    {{ Dom ρ1 ≈ ρ3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[export]
Instance per_ctx_PER {R} : PER (per_ctx_env R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[export]
Instance per_env_PER {R Γ Δ} (H : per_ctx_env R Γ Δ) : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** This lemma removes the PER argument *)
Lemma per_ctx_env_cons' : forall {Γ Γ' i A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation domain)
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
        rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> fun ρ ρ' =>
         exists (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }}),
           {{ Dom ^(ρ 0) ≈ ^(ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop }}) ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mctt.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_relΓA }} -> 
    exists i (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation domain),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈ ρ' ↯ ∈ env_relΓ }}),
               {{ Dom ^(ρ 0) ≈ ^(ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop }}).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ i A ρ A' ρ' R ->
                          {{ Dom m ≈ m' ∈ R }}).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
  - intros ρ ρ'.
    split; intros; destruct_conjs;
      assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve eexists; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
Qed.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; destruct H as [? [? []]])
  + (inversion H; subst).

(** ** A Canonical Extended Context PER

    [per_ctx_env_cons] leaves the head relation of an extended context
    existentially quantified, and indexed by the evidence relating the tails.
    Both are inconvenient downstream: the completeness substitution cases have to
    *build* the context PER of [Δ, S] and then relate four environments in it, which means producing the
    head evidence three times, once per link of the chain.

    So name the head relation once and for all, impredicatively — [per_head S S'
    ρ ρ'] is "whatever every [per_univ_elem] relating the values of [S] and [S']
    in [ρ] and [ρ'] relates".  This is the choice [rel_ctx_extend] already makes;
    what is new is that it does not mention the tail evidence, so the whole
    extended PER collapses to a *conjunction* ([per_env_extend]) rather than a
    dependent pair. *)

Definition per_head (S S' : typ) (ρ ρ' : env) : relation domain :=
  fun m m' =>
    forall i R a a',
      {{ ⟦ S ⟧ ρ ↘ a }} ->
      {{ ⟦ S' ⟧ ρ' ↘ a' }} ->
      {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
      {{ Dom m ≈ m' ∈ R }}.

Definition per_env_extend (S S' : typ) (R : relation env) : relation env :=
  fun ρ ρ' =>
    {{ Dom ρ ↯ ≈ ρ' ↯ ∈ R }} /\
      {{ Dom ^(ρ 0) ≈ ^(ρ' 0) ∈ per_head S S' d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}} }}.

(** [per_head] *is* the PER the types denote, because evaluation is functional
    and [per_univ_elem] is irrelevant in its relation argument.  This direction is
    the one with content, and it is also the one every head obligation of
    completeness needs: produce a [per_head] from an element PER already at hand. *)
Lemma per_head_of : forall {S S' ρ ρ' i R a a' m m'},
    {{ ⟦ S ⟧ ρ ↘ a }} ->
    {{ ⟦ S' ⟧ ρ' ↘ a' }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m ≈ m' ∈ per_head S S' ρ ρ' }}.
Proof.
  intros * Ha Ha' HR Hm.
  hnf; intros * Ha0 Ha0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** The converse instantiates the universal quantification at the witness
    itself. *)
Corollary per_head_iff : forall {S S' ρ ρ' i R a a'},
    {{ ⟦ S ⟧ ρ ↘ a }} ->
    {{ ⟦ S' ⟧ ρ' ↘ a' }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    R <~> per_head S S' ρ ρ'.
Proof.
  intros * Ha Ha' HR m m'; split.
  - intros Hm. eapply per_head_of; eassumption.
  - intros Hm. eapply Hm; eassumption.
Qed.

(** Hence any related pair of type values is a [per_univ_elem] *at the canonical
    head PER of the expressions they came from*.  This is the form in which an
    obligation of the shape "the motive at an arbitrary argument pair" is handed
    to a semantic recursion: what a type judgment reports is a level and an
    anonymous element PER, and what the recursion's family must be is the head
    PER, so the level is kept and the PER replaced. *)
Corollary per_univ_elem_at_head : forall {S S' ρ ρ' i a a'},
    {{ ⟦ S ⟧ ρ ↘ a }} ->
    {{ ⟦ S' ⟧ ρ' ↘ a' }} ->
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ (per_head S S' ρ ρ') }}.
Proof.
  intros * Ha Ha' [R HR].
  eapply per_univ_elem_resp_iff; [ exact HR |].
  eapply per_head_iff; eassumption.
Qed.

(** So the head PER of a type does not depend on *which* environment of a related
    family it is read in: any two evaluations of [S] and [S'] whose four values
    form a chain give the same relation.  This is what lets a judgment proved at
    one pair of environments be used at another — the situation of every rule
    whose type is an instantiated codomain, where the environment the type is
    evaluated in is not the one the term chain was produced at. *)
Lemma per_head_resp : forall {S S' ρ1 ρ2 ρ3 ρ4 i a1 a2 a3 a4},
    {{ ⟦ S ⟧ ρ1 ↘ a1 }} ->
    {{ ⟦ S' ⟧ ρ2 ↘ a2 }} ->
    {{ ⟦ S ⟧ ρ3 ↘ a3 }} ->
    {{ ⟦ S' ⟧ ρ4 ↘ a4 }} ->
    rel_chain (per_univ i) [a1; a2; a3; a4] ->
    per_head S S' ρ1 ρ2 <~> per_head S S' ρ3 ρ4.
Proof.
  intros * Ha1 Ha2 Ha3 Ha4 Hchain.
  assert (H12 : {{ Dom a1 ≈ a2 ∈ per_univ i }}) by pairwise.
  destruct H12 as [R HR].
  (** Refining the chain to [R] is what identifies the two head PERs: each is
      [R] by [per_head_iff], at its own pair of type values. *)
  assert (HchainR : rel_chain (per_univ_elem i R) [a1; a2; a3; a4])
    by (eapply per_univ_chain_at_in; [ exact Hchain | | | exact HR ]; solve_in).
  assert (H34 : {{ DF a3 ≈ a4 ∈ per_univ_elem i ↘ R }}) by pairwise.
  etransitivity; [ symmetry; eapply per_head_iff; [ exact Ha1 | exact Ha2 | exact HR ] |].
  eapply per_head_iff; [ exact Ha3 | exact Ha4 | exact H34 ].
Qed.

(** The form of the above that an elimination rule needs, where the two pairs of
    environments differ only in their heads.  The chain [per_head_resp] asks for
    is not at hand there; what is, is the codomain judgment read at an *arbitrary*
    related pair of arguments, and each link of the chain is one instance of it —
    the middle one at the crossing pair [(u, y)], which is why that relatedness is
    a premise and not derived: [RN] is a PER at every use, but taking it as such
    would oblige every caller to produce the instance. *)
Lemma per_head_of_args : forall {i B ρ ρ' RN},
    (forall x y,
        {{ Dom x ≈ y ∈ RN }} ->
        exists b b',
          {{ ⟦ B ⟧ ρ ↦ x ↘ b }} /\ {{ ⟦ B ⟧ ρ' ↦ y ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
    forall x y u v,
      {{ Dom x ≈ y ∈ RN }} ->
      {{ Dom u ≈ v ∈ RN }} ->
      {{ Dom u ≈ y ∈ RN }} ->
      per_head B B d{{{ ρ ↦ x }}} d{{{ ρ' ↦ y }}} <~> per_head B B d{{{ ρ ↦ u }}} d{{{ ρ' ↦ v }}}.
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

(** The two moves above in the form their callers use them in: the codomain at one
    argument pair, reported as a [per_univ_elem] *at the head PER of another*.
    This is the only way an element PER handed over by a judgment can be
    identified with the canonical one — irrelevance needs a shared type value, and
    the shared value is precisely the codomain's value at the pair the judgment was
    read at, while the PER wanted is the one at the pair the *goal* names. *)
Corollary per_head_anchor : forall {i B ρ ρ' RN},
    (forall x y,
        {{ Dom x ≈ y ∈ RN }} ->
        exists b b',
          {{ ⟦ B ⟧ ρ ↦ x ↘ b }} /\ {{ ⟦ B ⟧ ρ' ↦ y ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
    forall x y u v,
      {{ Dom x ≈ y ∈ RN }} ->
      {{ Dom u ≈ v ∈ RN }} ->
      {{ Dom u ≈ y ∈ RN }} ->
      exists b b',
        {{ ⟦ B ⟧ ρ ↦ x ↘ b }} /\ {{ ⟦ B ⟧ ρ' ↦ y ↘ b' }} /\
          {{ DF b ≈ b' ∈ per_univ_elem i
               ↘ (per_head B B d{{{ ρ ↦ u }}} d{{{ ρ' ↦ v }}}) }}.
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

(** Hence the premise [per_ctx_env_cons] asks for, at the canonical head
    relation.  Its own premise is the shape [rel_exp_of_typ_inversion_simple]
    delivers, which is how the Completeness layer feeds it. *)
Lemma per_ctx_env_extend : forall {Δ Δ' S S' env_relΔ i},
    {{ EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} ->
    (forall ρ ρ',
        {{ Dom ρ ≈ ρ' ∈ env_relΔ }} ->
        exists a a',
          {{ ⟦ S ⟧ ρ ↘ a }} /\ {{ ⟦ S' ⟧ ρ' ↘ a' }} /\ {{ Dom a ≈ a' ∈ per_univ i }}) ->
    {{ EF Δ, S ≈ Δ', S' ∈ per_ctx_env ↘ per_env_extend S S' env_relΔ }}.
Proof.
  intros * HΔ HS.
  eapply (per_ctx_env_cons' (i := i) (fun ρ ρ' (_ : {{ Dom ρ ≈ ρ' ∈ env_relΔ }}) => per_head S S' ρ ρ'));
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

(** The introduction rule of [per_env_extend], which is where the collapse to a
    conjunction pays off: it is [split], and it applies to *any* pair of
    environments rather than only to a literal extension.  That generality
    matters, because completeness must place environments of the form [⟦q ψ⟧w ρ]
    and
    [⟦σ ,, M⟧s ρ] in an extended context PER, and only the second of those is a
    literal [ρ ↦ m].  For the ones that are, both projections are conversions, so
    the premises are discharged by [assumption] all the same. *)
Lemma per_env_extend_intro : forall {S S' R ρ ρ'},
    {{ Dom ρ ↯ ≈ ρ' ↯ ∈ R }} ->
    {{ Dom ^(ρ 0) ≈ ^(ρ' 0) ∈ per_head S S' d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}} }} ->
    {{ Dom ρ ≈ ρ' ∈ per_env_extend S S' R }}.
Proof.
  intros * ? ?; split; assumption.
Qed.

(** The same rule pre-projected, for the common case of a literal extension.
    Stating it separately is not redundancy: the premises of
    [per_env_extend_intro] applied to [ρ ↦ m] mention [(ρ ↦ m) ↯] and
    [(ρ ↦ m) 0], and although those are convertible to [ρ] and [m], the tactics
    that discharge head obligations match syntactically. *)
Corollary per_env_extend_intro' : forall {S S' R ρ ρ' m m'},
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom m ≈ m' ∈ per_head S S' ρ ρ' }} ->
    {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ per_env_extend S S' R }}.
Proof.
  intros * ? ?; apply per_env_extend_intro; assumption.
Qed.

(** Transporting a [per_head] to another pair of environments, which is the
    "bridging" step of every completeness proof.  The two head relations are equal
    because their types are related in [per_univ]: [Ha]/[Ha'] name the source's
    types and [HR] its PER, [Hb]/[Hb'] the target's, and [Hab] says the two left
    types agree — enough, since [per_univ_elem] is irrelevant on either side. *)
Lemma per_head_bridge : forall {S S' ρ ρ' T T' u u' i R a a' b b' m m'},
    {{ Dom m ≈ m' ∈ per_head S S' ρ ρ' }} ->
    {{ ⟦ S ⟧ ρ ↘ a }} ->
    {{ ⟦ S' ⟧ ρ' ↘ a' }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ ⟦ T ⟧ u ↘ b }} ->
    {{ ⟦ T' ⟧ u' ↘ b' }} ->
    {{ Dom a ≈ b ∈ per_univ i }} ->
    {{ Dom m ≈ m' ∈ per_head T T' u u' }}.
Proof.
  intros * Hm Ha Ha' HR Hb Hb' [? Hab].
  assert (Hmm : {{ Dom m ≈ m' ∈ R }}) by (eapply Hm; eassumption).
  hnf; intros * Hb0 Hb0' HR0.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  eassumption.
Qed.

(** ** A Canonical Function PER

    The same device one level down.  [per_univ_elem_core_pi] leaves the codomain
    family [out_rel] existentially quantified and indexed by the evidence
    relating the two arguments, so a Π-value's element PER is determined only up
    to that choice.  The four-value pattern of a Π-*type* cannot live with
    that: its three links compare Π-values whose codomain expressions and
    environments all differ ([B[q σ]] at [ρ], [B] at [⟦σ⟧ρ], …), yet they must
    all be links of one and the same element PER.

    So name the family canonically, exactly as [per_head] does for a context
    extension — and with the very same relation, since "the PER the codomain
    denotes at [ρ ↦ c] and [ρ' ↦ c']" is what a head PER already means.  Being
    independent of the evidence and of the level is what lets one [per_pi] serve
    every link. *)

Definition per_pi (in_rel : relation domain) (B : typ) (ρ : env) (B' : typ) (ρ' : env) : relation domain :=
  fun f f' =>
    forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
      rel_mod_app f c f' c' (per_head B B' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}).

(** Building a Π-value at that PER.  The codomain premise is stated with the
    element PER existentially quantified — the shape a four-value chain hands
    over after [destruct_per_univ_chain] — because [per_head_iff] is what turns
    any such PER into the canonical one. *)
Lemma per_univ_elem_pi_canonical : forall {i a a' in_rel ρ B ρ' B'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
    (forall c c',
        {{ Dom c ≈ c' ∈ in_rel }} ->
        exists b b' R,
          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} /\
          {{ ⟦ B' ⟧ ρ' ↦ c' ↘ b' }} /\
          {{ DF b ≈ b' ∈ per_univ_elem i ↘ R }}) ->
    {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ') }}.
Proof.
  intros * Ha HB.
  eapply (per_univ_elem_pi' _ _ _ _ _ _ _ in_rel
            (fun c c' (_ : {{ Dom c ≈ c' ∈ in_rel }}) =>
               per_head B B' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}));
    [ eassumption | | reflexivity ].
  intros c c' equiv_c_c'.
  destruct (HB _ _ equiv_c_c') as [b [b' [R [Hb [Hb' HR]]]]].
  econstructor; try eassumption.
  eapply per_univ_elem_resp_iff; [ eassumption |].
  eapply per_head_iff; eassumption.
Qed.

(** And reading one off, which is how an application is justified: whatever PER a
    Π-value carries, it is the canonical one.  Note the two levels are
    unrelated — [per_univ_elem] irrelevance is cross-level — so a Π-type from one
    judgment and a domain from another need no lifting. *)
Corollary per_pi_iff : forall {i j a a' in_rel ρ B ρ' B' R},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
    {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem j ↘ R }} ->
    R <~> per_pi in_rel B ρ B' ρ'.
Proof.
  intros * Ha HΠ.
  invert_per_univ_elem HΠ.
  rename x into out_rel; rename H into Hout; rename H0 into HR.
  (** [HR] identifies [R] with the family-indexed relation; what is left is that
      the family is pointwise the canonical head PER.  Transitivity of
      [relation_equivalence] must be used *before* introducing the two values: at
      that point the goal is a [pointwise_lifting], which is no longer a relation
      position and neither [rewrite] nor [etransitivity] applies to it. *)
  etransitivity; [ exact HR |].
  intros f f'; split; intros Hf c c' equiv_c_c';
    specialize (Hf _ _ equiv_c_c');
    destruct (Hout _ _ equiv_c_c') as [b b' Hb Hb' Hbb'].
  - rewrite <- (per_head_iff Hb Hb' Hbb'); exact Hf.
  - rewrite (per_head_iff Hb Hb' Hbb'); exact Hf.
Qed.

(** The four-value pattern of a Π-type, at one element PER — the shape asked for
    by every semantic judgment whose type is a Π.  Each of the three links is
    built by [per_univ_elem_pi_canonical] at its own codomain pair, so each
    arrives carrying its own canonical [per_pi]; that the three agree is
    [per_univ_elem] irrelevance applied to the links themselves, consecutive
    links sharing a Π-value.  The one they are stated at is the *inner* link's,
    the only one of the three whose two sides are both unsubstituted, and the one
    an application reads its output PER off of.

    The domain is given as a four-value pattern already at [in_rel], which by weak
    functionality is all a semantic type judgment hands over
    ([functionalize_per_univ_chain]); no separate anchor is needed, and the three
    links come off it by [pairwise].  The three codomain premises are, in order,
    the three obligations [rel_exp_of_typ_under_ctx_q] produces. *)
Lemma per_univ_elem_pi_chain : forall {i in_rel a1 a2 a3 a4 B1 ρ1 B2 ρ2 B3 ρ3 B4 ρ4},
    rel_chain (per_univ_elem i in_rel) [a1; a2; a3; a4] ->
    (forall c c',
        {{ Dom c ≈ c' ∈ in_rel }} ->
        exists b b', {{ ⟦ B1 ⟧ ρ1 ↦ c ↘ b }} /\ {{ ⟦ B2 ⟧ ρ2 ↦ c' ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
    (forall c c',
        {{ Dom c ≈ c' ∈ in_rel }} ->
        exists b b', {{ ⟦ B2 ⟧ ρ2 ↦ c ↘ b }} /\ {{ ⟦ B3 ⟧ ρ3 ↦ c' ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
    (forall c c',
        {{ Dom c ≈ c' ∈ in_rel }} ->
        exists b b', {{ ⟦ B3 ⟧ ρ3 ↦ c ↘ b }} /\ {{ ⟦ B4 ⟧ ρ4 ↦ c' ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
    rel_chain (per_univ_elem i (per_pi in_rel B2 ρ2 B3 ρ3))
      [d{{{ Π a1 ρ1 B1 }}}; d{{{ Π a2 ρ2 B2 }}}; d{{{ Π a3 ρ3 B3 }}}; d{{{ Π a4 ρ4 B4 }}}].
Proof.
  intros * Hchain HB12 HB23 HB34.
  assert (H12 : {{ DF a1 ≈ a2 ∈ per_univ_elem i ↘ in_rel }}) by pairwise.
  assert (H23 : {{ DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel }}) by pairwise.
  assert (H34 : {{ DF a3 ≈ a4 ∈ per_univ_elem i ↘ in_rel }}) by pairwise.
  (** One [per_univ_elem_pi_canonical] per link, up to the [exists R] the
      canonical form wants where the premise offers [per_univ]. *)
  assert (Hlink : forall B ρ B' ρ' a a',
             {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
             (forall c c',
                 {{ Dom c ≈ c' ∈ in_rel }} ->
                 exists b b', {{ ⟦ B ⟧ ρ ↦ c ↘ b }} /\ {{ ⟦ B' ⟧ ρ' ↦ c' ↘ b' }} /\ {{ Dom b ≈ b' ∈ per_univ i }}) ->
             {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ (per_pi in_rel B ρ B' ρ') }}).
  { intros * Ha HB.
    apply per_univ_elem_pi_canonical; [ eassumption |].
    intros c c' Hc.
    destruct (HB _ _ Hc) as [b [b' [Hb [Hb' [R HR]]]]].
    exists b, b', R; repeat split; eassumption. }
  pose proof (Hlink _ _ _ _ _ _ H12 HB12) as HL1.
  pose proof (Hlink _ _ _ _ _ _ H23 HB23) as HL2.
  pose proof (Hlink _ _ _ _ _ _ H34 HB34) as HL3.
  (** The three links are a chain in [per_univ i], so weak functionality puts them
      at one PER and uniqueness says which: the *inner* link's, [HL2] being the
      anchor that names it.  [handle_per_univ_elem_irrel] would instead keep
      whichever of the three [per_pi]s it happened to pick, which is not
      predictable. *)
  assert (Hpi : rel_chain (per_univ i)
                  [d{{{ Π a1 ρ1 B1 }}}; d{{{ Π a2 ρ2 B2 }}};
                   d{{{ Π a3 ρ3 B3 }}}; d{{{ Π a4 ρ4 B4 }}}])
    by (apply rel_chain_4; eexists; eassumption).
  functionalize_per_univ_chain Hpi R.
  retype_rel_chain Hpi HL2 Hpi.
  exact Hpi.
Qed.

(** ** Closing an Extended Context PER Goal

    Every completeness proof in an extended context ends the same way, and these
    three tactics are that ending.

    [destruct_per_univ_chain] turns a four-value chain in [per_univ i] into the
    three [per_univ_elem] hypotheses that [handle_per_univ_elem_irrel] saturates
    over.  Nothing ever does anything else with such a chain: it is only a way of
    carrying those three around.  It goes through
    [per_univ_chain_functional], so the three come out at *one* element PER
    rather than at three independent existential ones — which is most of what
    irrelevance would otherwise have to reconcile.

    [solve_per_head] discharges a [per_head] goal.  [per_head] quantifies over an
    *arbitrary* [per_univ_elem] relating the two type values, so the proof is
    always the same four steps: introduce it, identify its two values with ones
    already named, let irrelevance identify its PER with the one the term chain
    lives in, and read the wanted pair off that chain.

    [solve_per_env_extend_chain] is the whole last step: a chain of environments,
    all of them extensions, to be related in an extended context PER.  Splitting
    each link into a tail and a head is [per_env_extend_intro']; the tails then
    come straight off the chain the underlying substitution arrived with, and the
    heads are bridged.  The chain is of any length, because the substitution
    cases want four environments while the rules with a premise in an extended context
    want every extension of the four tails by either of the two heads. *)
Ltac destruct_per_univ_chain H :=
  apply per_univ_chain_functional in H;
  destruct H as [? H];
  destruct H as [? [? ?]].

Ltac solve_per_head :=
  hnf; intros ? ? ? ? ? ? ?;
  functional_eval_rewrite_clear;
  handle_per_univ_elem_irrel;
  pairwise.

(** The peel is driven by the goal's syntactic shape, not by [first]: since
    [rel_chain R [x; y]] is *convertible* to [R x y], an unguarded
    [apply rel_chain_of_pair] would also fire on a link goal, and an unguarded
    [apply rel_chain_cons] would peel one step past the last link. *)
Ltac solve_per_env_extend_chain :=
  repeat
    match goal with
    | |- rel_chain _ [_; _] => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
  apply per_env_extend_intro'; first [ pairwise | solve_per_head ].

Lemma per_ctx_respects_length : forall {Γ Γ'},
    {{ Exp Γ ≈ Γ' ∈ per_ctx }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

Lemma per_ctx_subtyp_to_env : forall Γ Δ,
    {{ SubE Γ <: Δ }} ->
    exists R R',
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R }} /\
        {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ R' }}.
Proof.
  destruct 1; destruct_all.
  - repeat eexists; econstructor; apply Equivalence_Reflexive.
  - eauto.
Qed.

Lemma per_ctx_env_subtyping : forall Γ Δ,
    {{ SubE Γ <: Δ }} ->
    forall R R' ρ ρ',
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R }} ->
      {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ R' }} ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    handle_per_ctx_env_irrel;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    apply_relation_equivalence;
    trivial.

  destruct_all.
  assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition.
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
    {{ EF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ SubE Γ <: Δ }}.
Proof.
  induction 1; mauto.

  assert (exists R, {{ EF Γ , A ≈ Γ' , A' ∈ per_ctx_env ↘ R }}) by
    (eexists; eapply per_ctx_env_cons'; eassumption).
  destruct_all.
  econstructor; try solve [saturate_refl; mauto 2].
  intros.
  destruct_rel_typ.
  simplify_evals.
  eauto using per_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_refl2 : forall Γ Δ R,
    {{ EF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ SubE Δ <: Γ }}.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_trans : forall Γ1 Γ2,
    {{ SubE Γ1 <: Γ2 }} ->
    forall Γ3,
      {{ SubE Γ2 <: Γ3 }} ->
      {{ SubE Γ1 <: Γ3 }}.
Proof.
  induction 1; intros;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    mauto 1;
    clear_PER.

  handle_per_ctx_env_irrel.
  econstructor; try eassumption.
  - firstorder.
  - instantiate (1 := max i i0).
    intros.
    assert {{ Dom ρ ≈ ρ' ∈ tail_rel0 }} by (eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    etransitivity.
    + intuition mauto using per_subtyp_cumu_left.
    + intuition mauto using per_subtyp_cumu_right.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_trans : mctt.

#[export]
Instance per_ctx_subtyp_trans_ins : Transitive per_ctx_subtyp.
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.

(** * Context PERs Respect Pointwise Equality of Environments

    Evaluating a substitution pins its result environment down only up to
    [env_eq] ([functional_eval_sub]), so every use of a context PER in the
    completeness proof needs this lemma.  It is *not* an instance of
    "evaluation respects [env_eq]", which is false — see the closing comment of
    [Evaluation/Definitions.v].  What makes it true is that a context PER only
    ever inspects an environment pointwise, and that the head relations it
    produces at pointwise-equal environments coincide up to [<~>] by
    irrelevance. *)
Lemma per_ctx_env_resp_env_eq : forall {Γ Δ R},
    {{ EF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    forall ρ1 ρ2 ρ1' ρ2',
      env_eq ρ1 ρ2 ->
      env_eq ρ1' ρ2' ->
      {{ Dom ρ1 ≈ ρ1' ∈ R }} ->
      {{ Dom ρ2 ≈ ρ2' ∈ R }}.
Proof.
  intros * H.
  induction H; intros * Heq Heq' HR; apply_relation_equivalence; [ trivial |].
  destruct HR as [Dtail1 Hhead1].
  assert (Hd : env_eq d{{{ ρ1 ↯ }}} d{{{ ρ2 ↯ }}}) by (now rewrite Heq).
  assert (Hd' : env_eq d{{{ ρ1' ↯ }}} d{{{ ρ2' ↯ }}}) by (now rewrite Heq').
  assert (Dmix : {{ Dom ρ1 ↯ ≈ ρ2' ↯ ∈ tail_rel }}) by (eapply IHper_ctx_env; [ reflexivity | eassumption | eassumption ]).
  assert (Dtail2 : {{ Dom ρ2 ↯ ≈ ρ2' ↯ ∈ tail_rel }}) by (eapply IHper_ctx_env; eassumption).
  unshelve eexists; [ exact Dtail2 |].
  rewrite <- (Heq 0), <- (Heq' 0).
  pose proof (H0 _ _ Dtail1).
  pose proof (H0 _ _ Dmix).
  pose proof (H0 _ _ Dtail2).
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  first [ eassumption | use_relation_equivalence; eassumption ].
Qed.

#[export]
Instance per_ctx_env_Proper {Γ Δ R} (H : {{ EF Γ ≈ Δ ∈ per_ctx_env ↘ R }}) :
  Proper (env_eq ==> env_eq ==> iff) R.
Proof.
  intros ρ1 ρ2 Heq ρ1' ρ2' Heq'.
  split; intros; eapply per_ctx_env_resp_env_eq;
    try eassumption; symmetry; eassumption.
Qed.
