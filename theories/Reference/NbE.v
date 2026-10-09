(** * The Reference Normalizer

    Normalization by the reference evaluator and readback
    ([Reference.Evaluation], [Reference.Readback]), at the termination orders
    of [Extraction.NbE].  [Extraction.NbE] computes the same normal forms by
    the evaluation that skips unread recursive results. *)
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Reference Require Import Evaluation Readback.
From Mctt.Extraction Require Import NbE.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

#[local]
Hint Constructors initial_env_order nbe_order nbe_ty_order : mctt.
#[local]
Hint Resolve initial_env_order_sound nbe_order_sound nbe_ty_order_sound : mctt.

Section InitialEnvImpl.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : initial_env_order _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl Θ Ξ G (H : initial_env_order Θ Ξ G) : { p | initial_env Θ Ξ G p } by struct H :=
  | Θ, Ξ, nil, H => exist _ nil _
  | Θ, Ξ, cons (ce_ass A) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      exist _ (p ↦ ⇑! a (List.length G)) _
  | Θ, Ξ, cons (ce_def A M) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (m, Hm) := eval_exp_impl Θ Ξ M p _ in
      exist _ (p ↦ m) _
  | Θ, Ξ, cons (ce_mod U) G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      exist _ (p ↦ᵐ dm_local p U nil) _.

End InitialEnvImpl.

Lemma initial_env_impl_complete : forall Θ Ξ G p,
    initial_env Θ Ξ G p ->
    exists H H', initial_env_impl Θ Ξ G H = exist _ p H'.
Proof.
  intros.
  assert (Horder : initial_env_order Θ Ξ G) by mauto.
  exists Horder.
  destruct (initial_env_impl Θ Ξ G Horder).
  functional_initial_env_rewrite_clear.
  eexists; reflexivity.
Qed.

(** The same approach works for the NbE implementations; as there are two
    of them, for [nbe] and [nbe_ty], one tactic handles both. *)

Ltac functional_nbe_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_nbe_rewrite_clear;
          eexists; reflexivity
      end
  end.

Section NbEDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_order _ _ _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_impl Θ Ξ G M A (H : nbe_order Θ Ξ G M A) : { w | nbe Θ Ξ G M A w } by struct H :=
  | Θ, Ξ, G, M, A, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (m, Hm) := eval_exp_impl Θ Ξ M p _ in
      let (w, Hw) := read_nf_impl Θ Ξ (List.length G) ⇓ a m _ in
      exist _ w _.

End NbEDef.

Lemma nbe_impl_complete : forall Θ Ξ G M A w,
    nbe Θ Ξ G M A w ->
    exists H H', nbe_impl Θ Ξ G M A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.

Section NbETyDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_ty_order _ _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_impl Θ Ξ G A (H : nbe_ty_order Θ Ξ G A) : { w | nbe_ty Θ Ξ G A w } by struct H :=
  | Θ, Ξ, G, A, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (w, Hw) := read_typ_impl Θ Ξ (List.length G) a _ in
      exist _ w _.

End NbETyDef.

Lemma nbe_ty_impl_complete : forall Θ Ξ G A w,
    nbe_ty Θ Ξ G A w ->
    exists H H', nbe_ty_impl Θ Ξ G A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.

(** [nbe_ty_impl] at an initial environment computed beforehand: the
    checker computes the initial environment of its context once, and extends
    it under binders, rather than once per normalization. *)
Section NbETyEnvDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_ty_order _ _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_env_impl Θ Ξ G (P : { p | initial_env Θ Ξ G p }) A (H : nbe_ty_order Θ Ξ G A) :
    { w | nbe_ty Θ Ξ G A w } :=
  | Θ, Ξ, G, exist _ p Hp, A, H =>
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      let (w, Hw) := read_typ_impl Θ Ξ (List.length G) a _ in
      exist _ w _.

End NbETyEnvDef.
