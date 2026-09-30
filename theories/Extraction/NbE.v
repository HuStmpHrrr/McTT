From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Extraction Require Import Evaluation Readback.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

Inductive initial_env_order (Θ : gdeps) (Ξ : gstack) : ctx -> Prop :=
| ie_nil : initial_env_order Θ Ξ nil
| ie_cons :
  `( initial_env_order Θ Ξ Γ ->
     (forall p, initial_env Θ Ξ Γ p ->
           eval_exp_order Θ Ξ A p) ->
     initial_env_order Θ Ξ (A :: Γ)).

#[local]
Hint Constructors initial_env_order : mctt.

Lemma initial_env_order_sound : forall Θ Ξ Γ p,
    initial_env Θ Ξ Γ p ->
    initial_env_order Θ Ξ Γ.
Proof.
  induction 1; (econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto).
Qed.

#[local]
Hint Resolve initial_env_order_sound : mctt.

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
  | Θ, Ξ, cons A G, H =>
      let (p, Hp) := initial_env_impl Θ Ξ G _ in
      let (a, Ha) := eval_exp_impl Θ Ξ A p _ in
      exist _ (p ↦ ⇑! a (List.length G)) _.

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

(** A similar approach works for nbe implementations.
    However, as we have 2 implementations (each for [nbe] and [nbe_ty]),
    We define a tactic to deal with both cases. *)

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

(** The order of NbE in [Θ ⍮ Ξ ⍮ Γ]. *)
Inductive nbe_order Θ Ξ G M A : Prop :=
| nbe_order_run :
  `( initial_env_order Θ Ξ G ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p) ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ M p) ->
     (forall p a m,
         initial_env Θ Ξ G p ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
         ⟦ M ⟧ Θ ⍮ Ξ ⍮ p ↘ m ->
         read_nf_order Θ Ξ (List.length G) ⇓ a m) ->
     nbe_order Θ Ξ G M A ).

#[local]
Hint Constructors nbe_order : mctt.

Lemma nbe_order_sound : forall Θ Ξ G M A w,
    nbe Θ Ξ G M A w ->
    nbe_order Θ Ξ G M A.
Proof.
  induction 1;
    (econstructor; intros; functional_initial_env_rewrite_clear;
     functional_eval_rewrite_clear; functional_read_rewrite_clear; mauto).
Qed.

#[local]
Hint Resolve nbe_order_sound : mctt.

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

Inductive nbe_ty_order Θ Ξ G A : Prop :=
| nbe_ty_order_run :
  `( initial_env_order Θ Ξ G ->
     (forall p, initial_env Θ Ξ G p -> eval_exp_order Θ Ξ A p) ->
     (forall p a,
         initial_env Θ Ξ G p ->
         ⟦ A ⟧ Θ ⍮ Ξ ⍮ p ↘ a ->
         read_typ_order Θ Ξ (List.length G) a) ->
     nbe_ty_order Θ Ξ G A ).

#[local]
Hint Constructors nbe_ty_order : mctt.

Lemma nbe_ty_order_sound : forall Θ Ξ G A w,
    nbe_ty Θ Ξ G A w ->
    nbe_ty_order Θ Ξ G A.
Proof.
  induction 1;
    (econstructor; intros; functional_initial_env_rewrite_clear;
     functional_eval_rewrite_clear; functional_read_rewrite_clear; mauto).
Qed.

#[local]
Hint Resolve nbe_ty_order_sound : mctt.

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
