From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive read_nf_order : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order s a ->
    read_nf_order s d{{{ ⇓ 𝕌@i a }}} )
| rnf_zero :
  `( read_nf_order s d{{{ ⇓ ℕ zero }}} )
| rnf_succ :
  `( read_nf_order s d{{{ ⇓ ℕ m }}} ->
     read_nf_order s d{{{ ⇓ ℕ (succ m) }}} )
| rnf_nat_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ ℕ (⇑ a m) }}} )
| rnf_fn :
  `( read_typ_order s a ->
     eval_app_order m d{{{ ⇑! a s }}} ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     (forall m' b,
         {{ $| m & ⇑! a s |↘ m' }} ->
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_nf_order (S s) d{{{ ⇓ b m' }}}) ->
     read_nf_order s d{{{ ⇓ (Π a p B) m }}} )
| rnf_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ (⇑ a b) (⇑ c m) }}} )

with read_ne_order : nat -> domain_ne -> Prop :=
| rne_var :
  `( read_ne_order s d{{{ !x }}} )
| rne_app :
  `( read_ne_order s m ->
     read_nf_order s n ->
     read_ne_order s d{{{ m n }}} )
| rne_natrec :
  `( eval_exp_order B d{{{ p ↦ ⇑! ℕ s }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         read_typ_order (S s) b) ->
     eval_exp_order B d{{{ p ↦ zero }}} ->
     (forall bz,
         {{ ⟦ B ⟧ p ↦ zero ↘ bz }} ->
         read_nf_order s d{{{ ⇓ bz mz }}}) ->
     eval_exp_order B d{{{ p ↦ succ (⇑! ℕ s) }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         eval_exp_order MS d{{{ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) }}}) ->
     (forall b bs ms,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         {{ ⟦ B ⟧ p ↦ succ (⇑! ℕ s) ↘ bs }} ->
         {{ ⟦ MS ⟧ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) ↘ ms }} ->
         read_nf_order (S (S s)) d{{{ ⇓ bs ms }}}) ->
     read_ne_order s m ->
     read_ne_order s d{{{ rec m under p return B | zero -> mz | succ -> MS end }}} )

with read_typ_order : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order s d{{{ 𝕌@i }}} )
| rtyp_nat :
  `( read_typ_order s d{{{ ℕ }}} )
| rtyp_pi :
  `( read_typ_order s a ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_typ_order (S s) b) ->
     read_typ_order s d{{{ Π a p B }}})
| rtyp_neut :
  `( read_ne_order s b ->
    read_typ_order s d{{{ ⇑ a b }}} ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order : mctt.

Lemma read_nf_order_sound : forall s d m,
    {{ Rnf d in s ↘ m }} ->
    read_nf_order s d
with read_ne_order_sound : forall s d m,
    {{ Rne d in s ↘ m }} ->
    read_ne_order s d
with read_typ_order_sound : forall s d m,
    {{ Rtyp d in s ↘ m }} ->
    read_typ_order s d.
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
  | H : read_nf_order _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order s d) : { m | {{ Rnf d in s ↘ m }} } by struct H :=
| s, d{{{ ⇓ 𝕌@i a }}}      , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, d{{{ ⇓ ℕ zero }}}, H => exist _ n{{{ zero }}} _
| s, d{{{ ⇓ ℕ (succ m) }}} , H =>
    let (M, HM) := read_nf_impl s d{{{ ⇓ ℕ m }}} _ in
    exist _ n{{{ succ M }}} _
| s, d{{{ ⇓ ℕ (⇑ ^_ m) }}}  , H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ ⇑ M }}} _
| s, d{{{ ⇓ (Π a p B) m }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (m', Hm') := eval_app_impl m d{{{ ⇑! a s }}} _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (M, HM) := read_nf_impl (S s) d{{{ ⇓ b m' }}} _ in
    exist _ n{{{ λ A M }}} _
| s, d{{{ ⇓ (⇑ a b) (⇑ c m) }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ ⇑ M }}} _

  with read_ne_impl s d (H : read_ne_order s d) : { m | {{ Rne d in s ↘ m }} } by struct H :=
| s, d{{{ !x }}}, H => exist _ n{{{ #(s - x - 1) }}} _
| s, d{{{ m n }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ n{{{ M N }}} _
| s, d{{{ rec m under p return B | zero -> mz | succ -> MS end }}}, H =>
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! ℕ s }}} _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (bz, Hbz) := eval_exp_impl B d{{{ p ↦ zero }}} _ in
    let (MZ, HMZ) := read_nf_impl s d{{{ ⇓ bz mz }}} _ in
    let (bs, Hbs) := eval_exp_impl B d{{{ p ↦ succ (⇑! ℕ s) }}} _ in
    let (ms, Hms) := eval_exp_impl MS d{{{ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) }}} _ in
    let (MS', HMS') := read_nf_impl (S (S s)) d{{{ ⇓ bs ms }}} _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ rec M return B' | zero -> MZ | succ -> MS' end }}} _

      with read_typ_impl s d (H : read_typ_order s d) : { m | {{ Rtyp d in s ↘ m }} } by struct H :=
| s, d{{{ 𝕌@i }}}, H => exist _ n{{{ Type@i }}} _
| s, d{{{ ℕ }}}, H => exist _ n{{{ ℕ }}} _
| s, d{{{ Π a p B }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ n{{{ Π A B' }}} _
| s, d{{{ ⇑ a b }}}, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ n{{{ ⇑ B }}} _.

Extraction Inline read_nf_impl_functional
  read_ne_impl_functional
  read_typ_impl_functional.

(** The definitions of [read_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of readback. *)

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
    {{ Rnf d in s ↘ m }} ->
    exists H H', read_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_ne_impl_complete : forall s d m,
    {{ Rne d in s ↘ m }} ->
    exists H H', read_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_typ_impl_complete : forall s d m,
    {{ Rtyp d in s ↘ m }} ->
    exists H H', read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.
