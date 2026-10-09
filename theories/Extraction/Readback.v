From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

(** The canonical level a level normal form encodes.  A level always reads
    back as [nf_lvl_of] of a canonical level ([read_nf_level_lvl_of_nf]), so
    the default is never reached. *)
Definition lvl_of_nf (W : nf) : lvl :=
  match W with nf_lvl c xs => (c, xs) | _ => (oz, la_nil) end.

Lemma read_nf_level_lvl_of_nf : forall Θ Ξ s l W,
    Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    W = nf_lvl_of (lvl_of_nf W).
Proof. inversion 1; subst; reflexivity. Qed.

Lemma read_typ_suniv_of_nf : forall Θ Ξ s l W,
    Rnf ⇓ Levelᵈ l in Θ ⍮ Ξ ⍮ s ↘ W ->
    Rtyp 𝕌@l in Θ ⍮ Ξ ⍮ s ↘ nf_univ_of (lvl_of_nf W).
Proof.
  intros * H; apply read_typ_suniv.
  rewrite <- (read_nf_level_lvl_of_nf _ _ _ _ _ H); exact H.
Qed.

Inductive read_nf_order (Θ : gdeps) (Ξ : gstack) : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌ω@i a )
| rnf_stype :
  `( read_typ_order Θ Ξ s a ->
    read_nf_order Θ Ξ s ⇓ 𝕌@n a )
| rnf_lvl :
  `( read_la_order Θ Ξ s xs ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (lvᵈ c xs) )
| rnf_lvl_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ (Levelᵈ@n) (⇑ a m) )
| rnf_zero :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ zeroᵈ )
| rnf_succ :
  `( read_nf_order Θ Ξ s ⇓ ℕᵈ m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (succᵈ m) )
| rnf_nat_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ℕᵈ (⇑ a m) )
| rnf_true :
  `( read_nf_order Θ Ξ s ⇓ ⊤ᵈ m )
| rnf_False_neut :
  `( read_ne_order Θ Ξ s m ->
     read_nf_order Θ Ξ s ⇓ ⊥ᵈ (⇑ a m) )
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
| rne_exfalso :
  `( eval_exp_order Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! ⊥ᵈ s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_ne_order Θ Ξ s m ->
     read_ne_order Θ Ξ s efqᵈ m under p return B )
| rne_glob :
  `( read_ne_order Θ Ξ s (d_glob p) )

with read_typ_order (Θ : gdeps) (Ξ : gstack) : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order Θ Ξ s 𝕌ω@i )
(** A small universe reads its level back. *)
| rtyp_suniv :
  `( read_nf_order Θ Ξ s ⇓ Levelᵈ l ->
     read_typ_order Θ Ξ s 𝕌@l )
| rtyp_level :
  `( read_typ_order Θ Ξ s (Levelᵈ@n) )
| rtyp_nat :
  `( read_typ_order Θ Ξ s ℕᵈ )
| rtyp_True :
  `( read_typ_order Θ Ξ s ⊤ᵈ )
| rtyp_False :
  `( read_typ_order Θ Ξ s ⊥ᵈ )
| rtyp_pi :
  `( read_typ_order Θ Ξ s a ->
     eval_exp_order Θ Ξ B (p ↦ ⇑! a s) ->
     (forall b,
         ⟦ B ⟧ Θ ⍮ Ξ ⍮ p ↦ ⇑! a s ↘ b ->
         read_typ_order Θ Ξ (S s) b) ->
     read_typ_order Θ Ξ s Πᵈ a p B)
| rtyp_neut :
  `( read_ne_order Θ Ξ s b ->
    read_typ_order Θ Ξ s ⇑ a b )

with read_la_order (Θ : gdeps) (Ξ : gstack) : nat -> list (nat * domain_ne) -> Prop :=
| rla_nil :
  `( read_la_order Θ Ξ s nil )
| rla_cons :
  `( read_ne_order Θ Ξ s m ->
     read_la_order Θ Ξ s xs ->
     read_la_order Θ Ξ s ((k, m) :: xs) ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order read_la_order : mctt.

Lemma read_nf_order_sound : forall Θ Ξ s d m,
    Rnf d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_nf_order Θ Ξ s d
with read_ne_order_sound : forall Θ Ξ s d m,
    Rne d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_ne_order Θ Ξ s d
with read_typ_order_sound : forall Θ Ξ s d m,
    Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m ->
    read_typ_order Θ Ξ s d
with read_la_order_sound : forall Θ Ξ s xs ys,
    Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    read_la_order Θ Ξ s xs.
Proof.
  - clear read_nf_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_ne_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_typ_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_la_order_sound; induction 1; (econstructor; intros; functional_eval_rewrite_clear; mauto).
Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound read_la_order_sound : mctt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ _ _ |- _ => progressive_invert H
  | H : read_la_order _ _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

Section ReadbackImpl.
Variables (Θ : gdeps) (Ξ : gstack).

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order Θ Ξ s d) : { m | Rnf d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, ⇓ 𝕌ω@i a      , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, ⇓ 𝕌@n a     , H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, ⇓ (Levelᵈ@n) (lvᵈ c xs), H =>
    let (ys, Hys) := read_la_impl s xs _ in
    exist _ (nf_lvl_of (lvl_canon (c, ys))) _
| s, ⇓ (Levelᵈ@n) (⇑ _ m), H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ (lvⁿ oz (la_cons 0 M la_nil)) _
| s, ⇓ ℕᵈ zeroᵈ, H => exist _ zeroⁿ _
| s, ⇓ ℕᵈ (succᵈ m) , H =>
    let (M, HM) := read_nf_impl s ⇓ ℕᵈ m _ in
    exist _ succⁿ M _
| s, ⇓ ℕᵈ (⇑ _ m)  , H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ ⇑ⁿ M _
| s, ⇓ ⊤ᵈ m, H => exist _ ⋆ⁿ _
| s, ⇓ ⊥ᵈ (⇑ _ m), H =>
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
| s, efqᵈ m under p return B, H =>
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! ⊥ᵈ s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ (efqⁿ M return B') _

      with read_typ_impl s d (H : read_typ_order Θ Ξ s d) : { m | Rtyp d in Θ ⍮ Ξ ⍮ s ↘ m } by struct H :=
| s, 𝕌ω@i, H => exist _ Typeωⁿ@i _
| s, 𝕌@l, H =>
    let (W, HW) := read_nf_impl s ⇓ Levelᵈ l _ in
    exist _ (nf_univ_of (lvl_of_nf W)) _
| s, Levelᵈ@n, H => exist _ (Levelⁿ@n) _
| s, ℕᵈ, H => exist _ ℕⁿ _
| s, ⊤ᵈ, H => exist _ ⊤ⁿ _
| s, ⊥ᵈ, H => exist _ ⊥ⁿ _
| s, Πᵈ a p B, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl Θ Ξ B (p ↦ ⇑! a s) _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ (Πⁿ A B') _
| s, ⇑ a b, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ ⇑ⁿ B _

  with read_la_impl s xs (H : read_la_order Θ Ξ s xs) : { ys | Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys } by struct H :=
| s, nil, H => exist _ la_nil _
| s, cons (k, m) xs, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (ys, Hys) := read_la_impl s xs _ in
    exist _ (la_cons k M ys) _.

(** Each hole is either a readback order of a subterm, read off the order of
    the whole by inversion, or the readback itself, by its rule. *)
#[local]
Ltac rb_ord :=
  repeat impl_obl_tac1;
  first [ eassumption
        (** A readback under a binder: the order of the body is a premise
            quantified over the results of the evaluations above it. *)
        | solve [ eauto 2 ] ].

#[local]
Ltac rb_run := repeat impl_obl_tac1; econstructor; eassumption.

Obligation 1. all: first [ rb_ord | rb_run ]. Qed.
Obligation 2. all: first [ rb_ord | rb_run ]. Defined.
Obligation 3. all: first [ rb_ord | rb_run ]. Qed.
Obligation 4. all: first [ rb_ord | rb_run ]. Defined.
Obligation 5. all: first [ rb_ord | rb_run ]. Qed.
Obligation 6. all: first [ rb_ord | rb_run ]. Defined.
Obligation 7. all: first [ rb_ord | rb_run ]. Defined.
Obligation 8. all: first [ rb_ord | rb_run ]. Defined.
Obligation 9. all: first [ rb_ord | rb_run ]. Defined.
Obligation 10. all: first [ rb_ord | rb_run ]. Qed.
Obligation 11. all: first [ rb_ord | rb_run ]. Defined.
Obligation 12. all: first [ rb_ord | rb_run ]. Qed.
Obligation 13. all: first [ rb_ord | rb_run ]. Defined.
Obligation 14. all: first [ rb_ord | rb_run ]. Qed.
Obligation 15. all: first [ rb_ord | rb_run ]. Defined.
Obligation 16. all: first [ rb_ord | rb_run ]. Qed.
Obligation 17. all: first [ rb_ord | rb_run ]. Defined.
Obligation 18. all: first [ rb_ord | rb_run ]. Qed.
Obligation 19. all: first [ rb_ord | rb_run ]. Qed.
Obligation 20. all: first [ rb_ord | rb_run ]. Defined.
Obligation 21. all: first [ rb_ord | rb_run ]. Qed.
Obligation 22. all: first [ rb_ord | rb_run ]. Defined.
Obligation 23. all: first [ rb_ord | rb_run ]. Qed.
Obligation 24. all: first [ rb_ord | rb_run ]. Qed.
Obligation 25. all: first [ rb_ord | rb_run ]. Defined.
Obligation 26. all: first [ rb_ord | rb_run ]. Defined.
Obligation 27. all: first [ rb_ord | rb_run ]. Qed.
Obligation 28. all: first [ rb_ord | rb_run ]. Defined.
Obligation 29. all: first [ rb_ord | rb_run ]. Defined.
Obligation 30. all: first [ rb_ord | rb_run ]. Defined.
Obligation 31. all: first [ rb_ord | rb_run ]. Defined.
Obligation 32. all: first [ rb_ord | rb_run ]. Defined.
Obligation 33. all: first [ rb_ord | rb_run ]. Defined.
Obligation 34. all: first [ rb_ord | rb_run ]. Defined.
Obligation 35. all: first [ rb_ord | rb_run ]. Defined.
Obligation 36. all: first [ rb_ord | rb_run ]. Qed.
Obligation 37. all: first [ rb_ord | rb_run ]. Defined.
Obligation 38. all: first [ rb_ord | rb_run ]. Defined.
Obligation 39. all: first [ rb_ord | rb_run ]. Defined.
Obligation 40. all: first [ rb_ord | rb_run ]. Qed.
Obligation 41. all: first [ rb_ord | rb_run ]. Qed.
Obligation 42. all: first [ rb_ord | rb_run ]. Qed.
Obligation 43. all: first [ rb_ord | rb_run ]. Defined.
Obligation 44. all: first [ rb_ord | rb_run ]. Defined.
Obligation 45. all: first [ rb_ord | rb_run ]. Defined.
Obligation 46. all: first [ rb_ord | rb_run ]. Qed.
Obligation 47. all: first [ rb_ord | rb_run ]. Qed.
Obligation 48. all: first [ rb_ord | rb_run ]. Defined.
(** A small universe: its readback is the universe at the canonical level its
    level reads back as. *)
Obligation 49. eapply read_typ_suniv_of_nf; eassumption. Qed.
Obligation 50. all: first [ rb_ord | rb_run ]. Qed.
Obligation 51. all: first [ rb_ord | rb_run ]. Qed.
Obligation 52. all: first [ rb_ord | rb_run ]. Qed.
Obligation 53. all: first [ rb_ord | rb_run ]. Defined.
Obligation 54. all: first [ rb_ord | rb_run ]. Qed.
Obligation 55. all: first [ rb_ord | rb_run ]. Qed.
Obligation 56. all: first [ rb_ord | rb_run ]. Defined.
Obligation 57. all: first [ rb_ord | rb_run ]. Defined.
Obligation 58. all: first [ rb_ord | rb_run ]. Qed.


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

Lemma read_la_impl_complete : forall s xs ys,
    Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys ->
    exists H H', read_la_impl s xs H = exist _ ys H'.
Proof.
  intros; functional_read_complete.
Qed.

End ReadbackImpl.

Extraction Inline read_nf_impl_functional
  read_ne_impl_functional
  read_typ_impl_functional
  read_la_impl_functional.
