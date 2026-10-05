From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Algorithmic Require Export Subtyping.
From Mctt.Extraction Require Import NbE PseudoMonadic.
From Equations Require Import Equations.
Import Domain_Notations Fixed_Notations.

#[local]
Ltac subtyping_tac :=
  intros;
  lazymatch goal with
  | |- ⊢anf _ ⊆ _ =>
      subst;
      mauto 4;
      try congruence;
      econstructor; simpl; trivial
  | |- ~ ⊢anf _ ⊆ _ =>
      let H := fresh "H" in
      intro H; dependent destruction H; simpl in *;
      try lia;
      try congruence
  end.

#[tactic="subtyping_tac",derive(equations=no,eliminator=no)]
Equations subtyping_nf_impl A B : { ⊢anf A ⊆ B } + {~ ⊢anf A ⊆ B } :=
| Typeⁿ@i, Typeⁿ@j =>
    let*b _ := Compare_dec.le_lt_dec i j while _ in
    pureb _
| Πⁿ A B, Πⁿ A' B' =>
    let*b _ := nf_eq_dec A A' while _ in
    let*b _ := subtyping_nf_impl B B' while _ in
    pureb _
(** Pseudo-monadic syntax in this catch-all branch leaves obligations
    unsolved, so it matches on [nf_eq_dec A B] directly. *)
| A, B with nf_eq_dec A B => {
  | left _ => left _
  | right _ => right _
  }.

(** [subtyping_nf_impl] is sound by construction, and its completeness is
    straightforward. *)

Theorem subtyping_nf_impl_complete : forall A B,
    ⊢anf A ⊆ B ->
    exists H, subtyping_nf_impl A B = left H.
Proof.
  intros; dec_complete.
Qed.

Inductive subtyping_order {GC : GCtx} G A B :=
| subtyping_order_run :
  nbe_ty_order gc_ctx G A ->
  nbe_ty_order gc_ctx G B ->
  subtyping_order G A B.
Arguments subtyping_order {GC} G A B.
Arguments subtyping_order_run {GC G A B}.
#[local]
Hint Constructors subtyping_order : mctt.

Lemma subtyping_order_sound : forall {GC : GCtx} G A B,
    G ⊢a A ⊆ B ->
    subtyping_order G A B.
Proof.
  intros * H.
  dependent destruction H.
  mauto using nbe_ty_order_sound.
Qed.

#[local]
Ltac subtyping_impl_tac1 :=
  match goal with
  | H : subtyping_order _ _ _ |- _ => progressive_invert H
  | H : nbe_ty_order _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac subtyping_impl_tac :=
  repeat subtyping_impl_tac1; try econstructor; mauto.

#[tactic="subtyping_impl_tac",derive(equations=no,eliminator=no)]
Equations subtyping_impl {GC : GCtx} G A B (H : subtyping_order G A B) :
  { G ⊢a A ⊆ B } + { ~ G ⊢a A ⊆ B } :=
| G, A, B, H =>
    let (a, Ha) := nbe_ty_impl gc_ctx G A _ in
    let (b, Hb) := nbe_ty_impl gc_ctx G B _ in
    let*b _ := subtyping_nf_impl a b while _ in
    pureb _.
Next Obligation.
  progressive_inversion.
  functional_nbe_rewrite_clear.
  contradiction.
Qed.

(** The same holds for [subtyping_impl]. *)

Theorem subtyping_impl_complete' : forall {GC : GCtx} G A B,
    G ⊢a A ⊆ B ->
    forall (H : subtyping_order G A B),
      exists H', subtyping_impl G A B H = left H'.
Proof.
  intros; dec_complete.
Qed.

#[local]
Hint Resolve subtyping_order_sound subtyping_impl_complete' : mctt.

Theorem subtyping_impl_complete : forall {GC : GCtx} G A B,
    G ⊢a A ⊆ B ->
    exists H H', subtyping_impl G A B H = left H'.
Proof.
  repeat unshelve mauto.
Qed.
