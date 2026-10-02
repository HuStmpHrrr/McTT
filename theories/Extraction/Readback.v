From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import GlobalCtx.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌@i a )
| rnf_zero :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ zeroᵈ )
| rnf_succ :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (succᵈ m) )
| rnf_nat_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (⇑ a m) )
| rnf_fn :
  `( read_typ_order Θ Ξ s a ->
     eval_app_order Θ Ξ m ⇑! a s ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall m' b,
         $| m & ⇑! a s | Θ ⍮ Ξ ↘ m' ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_nf_order Θ Ξ (S s) ⇓ b m') ->
     read_nf_order Θ Ξ s ⇓ (Πᵈ a p B) m )
| rnf_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (⇑ a b) (⇑ c m) )

with read_ne_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_ne -> Prop :=
| rne_var :
  `( read_ne_order Θ Ξ s #ᵈ x )
| rne_app :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s n ->
     read_ne_order Θ Ξ s (m $ᵈ n) )
| rne_natrec :
  `( eval_exp_order Θ Ξ B (p ↦ ⇑! ℕᵈ s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     eval_exp_order Θ Ξ B (p ↦ zeroᵈ) ->
     (forall bz,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ zeroᵈ ↘ bz ->
         read_nf_order Θ Ξ s ⇓ bz mz) ->
     eval_exp_order Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         eval_exp_order Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s))) ->
     (forall b bs ms,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↘ b ->
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ succᵈ (⇑! ℕᵈ s) ↘ bs ->
         ⟦ MS ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s) ↘ ms ->
         read_nf_order Θ Ξ (S (S s)) ⇓ bs ms) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s recᵈ m under p return B | zero -> mz | succ -> MS end )
| rne_glob :
  `( read_ne_order Θ Ξ s (d_glob p) )

with read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order Θ Ξ s 𝕌@i )
| rtyp_nat :
  `( read_typ_order Θ Ξ s ℕᵈ )
| rtyp_pi :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s Πᵈ a p B)
| rtyp_neut :
  `( read_ne_order Θ Ξ s b ->
    read_typ_order Θ Ξ s ⇑ a b ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order : mctt.

Lemma read_nf_order_sound : forall Θ Ξ s d m,
    Rnf d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_nf_order Θ Ξ s d
with read_ne_order_sound : forall Θ Ξ s d m,
    Rne d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_ne_order Θ Ξ s d
with read_typ_order_sound : forall Θ Ξ s d m,
    Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_typ_order Θ Ξ s d.
Proof.
  - clear read_nf_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_ne_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_typ_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound : mctt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order Θ Ξ s d) : { m | Rnf d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌@i a      , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, ⇓ ℕᵈ zeroᵈ, H => exist _ zeroⁿ _
| s, ⇓ ℕᵈ (succᵈ m) , H =>
    let (M, HM) := read_nf_impl s ⇓ ℕᵈ m _ in
    exist _ succⁿ M _
| s, ⇓ ℕᵈ (⇑ _ m)  , H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ (Πᵈ a p B) m, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (m', Hm') := eval_app_impl Θ Ξ m ⇑! a s _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (M, HM) := read_nf_impl (S s) ⇓ b m' _ in
    exist _ (λⁿ A M) _
| s, ⇓ (⇑ a b) (⇑ c m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _

  with read_ne_impl s d (H : read_ne_order Θ Ξ s d) : { m | Rne d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, #ᵈ x, H => exist _ #ⁿ (s - x - 1) _
| s, d_glob p, H => exist _ (ne_glob p) _
| s, m $ᵈ n, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ (M $ⁿ N) _
| s, recᵈ m under p return B | zero -> mz | succ -> MS end, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! ℕᵈ s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (bz, Hbz) := eval_exp_impl Θ Ξ B (p ↦ zeroᵈ) _ in
    let (MZ, HMZ) := read_nf_impl s ⇓ bz mz _ in
    let (bs, Hbs) := eval_exp_impl Θ Ξ B (p ↦ succᵈ (⇑! ℕᵈ s)) _ in
    let (ms, Hms) := eval_exp_impl Θ Ξ MS (p ↦ ⇑! ℕᵈ s ↦ ⇑! b (S s)) _ in
    let (MS', HMS') := read_nf_impl (S (S s)) ⇓ bs ms _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ recⁿ M return B' | zero -> MZ | succ -> MS' end _

      with read_typ_impl s d (H : read_typ_order Θ Ξ s d) : { m | Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌@i, H => exist _ Typeⁿ@i _
| s, ℕᵈ, H => exist _ ℕⁿ _
| s, Πᵈ a p B, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ ⇑ⁿ B _.


(** The [read_*_impl] functions are sound by construction.  Completeness
    follows from the soundness of the readback orders and the functionality
    of readback. *)

#[local]
Ltac functional_read_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_read_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma read_nf_impl_complete : forall s d m,
    Rnf d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_ne_impl_complete : forall s d m,
    Rne d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_typ_impl_complete : forall s d m,
    Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m ->
    exists H H', read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.
End ReadbackImpl.

Extraction Inline read_nf_impl_functional
  read_ne_impl_functional
  read_typ_impl_functional.
