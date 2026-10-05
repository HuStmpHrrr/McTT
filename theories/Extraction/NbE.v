From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import List String.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Extraction Require Import Evaluation Readback.
Import Domain_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

Inductive initial_env_order (Θ : gctx) : ctx -> Prop :=
| ie_nil : initial_env_order Θ nil
| ie_cons :
  `( initial_env_order Θ Γ ->
     (forall p, initial_env Θ Γ p ->
           eval_exp_order Θ A p) ->
     initial_env_order Θ (Γ ▹ A))
| ie_cons_def :
  `( initial_env_order Θ Γ ->
     (forall p, initial_env Θ Γ p ->
           eval_exp_order Θ M p) ->
     initial_env_order Θ (Γ ▸ A ≔ M))
| ie_cons_mod :
  `( initial_env_order Θ Γ ->
     initial_env_order Θ (Γ ▹ₘ U)).

#[local]
Hint Constructors initial_env_order : mctt.

Lemma initial_env_order_sound : forall Θ Γ p,
    initial_env Θ Γ p ->
    initial_env_order Θ Γ.
Proof.
  induction 1; solve [ econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto
                     | econstructor; eauto ].
Qed.

#[local]
Hint Resolve initial_env_order_sound : mctt.

Section InitialEnvImpl.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : initial_env_order _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl Θ G (H : initial_env_order Θ G) : { p | initial_env Θ G p } by struct H :=
  | Θ, nil, H => exist _ nil _
  | Θ, cons (ce_ass A) G, H =>
      let (p, Hp) := initial_env_impl Θ G _ in
      let (a, Ha) := eval_exp_impl Θ A p _ in
      exist _ (p ↦ ⇑! a (List.length G)) _
  | Θ, cons (ce_def A M) G, H =>
      let (p, Hp) := initial_env_impl Θ G _ in
      let (m, Hm) := eval_exp_impl Θ M p _ in
      exist _ (p ↦ m) _
  | Θ, cons (ce_mod U) G, H =>
      let (p, Hp) := initial_env_impl Θ G _ in
      exist _ (p ↦ᵐ dm_of p U) _.

End InitialEnvImpl.

Lemma initial_env_impl_complete : forall Θ G p,
    initial_env Θ G p ->
    exists H H', initial_env_impl Θ G H = exist _ p H'.
Proof.
  intros.
  assert (Horder : initial_env_order Θ G) by mauto.
  exists Horder.
  destruct (initial_env_impl Θ G Horder).
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

(** The order of NbE in [Θ ⍮ Γ]. *)
Inductive nbe_order Θ G M A : Prop :=
| nbe_order_run :
  `( initial_env_order Θ G ->
     (forall p, initial_env Θ G p -> eval_exp_order Θ A p) ->
     (forall p, initial_env Θ G p -> eval_exp_order Θ M p) ->
     (forall p a m,
         initial_env Θ G p ->
         ⟦ A ⟧ Θ ⍮ p ↘ a ->
         ⟦ M ⟧ Θ ⍮ p ↘ m ->
         read_nf_order Θ (List.length G) ⇓ a m) ->
     nbe_order Θ G M A ).

#[local]
Hint Constructors nbe_order : mctt.

Lemma nbe_order_sound : forall Θ G M A w,
    nbe Θ G M A w ->
    nbe_order Θ G M A.
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
  | H : nbe_order _ _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_impl Θ G M A (H : nbe_order Θ G M A) : { w | nbe Θ G M A w } by struct H :=
  | Θ, G, M, A, H =>
      let (p, Hp) := initial_env_impl Θ G _ in
      let (a, Ha) := eval_exp_impl Θ A p _ in
      let (m, Hm) := eval_exp_impl Θ M p _ in
      let (w, Hw) := read_nf_impl Θ (List.length G) ⇓ a m _ in
      exist _ w _.

End NbEDef.

Lemma nbe_impl_complete : forall Θ G M A w,
    nbe Θ G M A w ->
    exists H H', nbe_impl Θ G M A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.

Inductive nbe_ty_order Θ G A : Prop :=
| nbe_ty_order_run :
  `( initial_env_order Θ G ->
     (forall p, initial_env Θ G p -> eval_exp_order Θ A p) ->
     (forall p a,
         initial_env Θ G p ->
         ⟦ A ⟧ Θ ⍮ p ↘ a ->
         read_typ_order Θ (List.length G) a) ->
     nbe_ty_order Θ G A ).

#[local]
Hint Constructors nbe_ty_order : mctt.

Lemma nbe_ty_order_sound : forall Θ G A w,
    nbe_ty Θ G A w ->
    nbe_ty_order Θ G A.
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
  | H : nbe_ty_order _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_impl Θ G A (H : nbe_ty_order Θ G A) : { w | nbe_ty Θ G A w } by struct H :=
  | Θ, G, A, H =>
      let (p, Hp) := initial_env_impl Θ G _ in
      let (a, Ha) := eval_exp_impl Θ A p _ in
      let (w, Hw) := read_typ_impl Θ (List.length G) a _ in
      exist _ w _.

End NbETyDef.

Lemma nbe_ty_impl_complete : forall Θ G A w,
    nbe_ty Θ G A w ->
    exists H H', nbe_ty_impl Θ G A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.
