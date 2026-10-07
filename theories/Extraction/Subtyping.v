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

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations subtyping_nf_impl A B : { ⊢anf A ⊆ B } + {~ ⊢anf A ⊆ B } :=
| Typeωⁿ@i, Typeωⁿ@j =>
    let*b _ := Compare_dec.le_lt_dec i j while _ in
    pureb _
(** Two small universes, by the decidable order on canonical levels. *)
| univⁿ c xs, univⁿ d ys =>
    let*b _ := lvl_le_dec (c, xs) (d, ys) while _ in
    pureb _
(** A small universe is below every large one. *)
| univⁿ c xs, Typeωⁿ@i => left _
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

(** A branch that rules out subtyping: the judgment is inverted, and what the
    branch knows (a disequality of normal forms, or an arithmetic bound)
    contradicts every rule that could have derived it. *)
#[local]
Ltac st_neg :=
  lazymatch goal with H : ⊢anf _ ⊆ _ |- False => inversion H; subst end;
  simpl in *;
  first [ lia | congruence | contradiction ].

(** A branch that derives subtyping: by the rule for the two normal forms,
    whose side condition the branch has decided. *)
#[local]
Ltac st_pos :=
  subst;
  lazymatch goal with
  | |- ⊢anf Typeωⁿ@_ ⊆ Typeωⁿ@_ => apply asnf_univ; assumption
  (** The decided level order arrives destructed into its two components
      (the constant and the sorted atoms), so the pair is rebuilt here. *)
  | |- ⊢anf univⁿ _ _ ⊆ univⁿ _ _ =>
      apply asnf_suniv;
      first [ assumption
            | unfold lvl_le, lvl_canon; cbn; f_equal; assumption ]
  | |- ⊢anf univⁿ _ _ ⊆ Typeωⁿ@_ => apply asnf_small_large
  | |- ⊢anf Πⁿ _ _ ⊆ Πⁿ _ _ => apply asnf_pi; [ first [ assumption | reflexivity ] | assumption ]
  (** Every other normal form is below itself only, by [asnf_refl], whose
      side condition holds by computation. *)
  | |- ⊢anf ?A ⊆ ?A => apply asnf_refl; [ exact I | reflexivity ]
  end.

Obligation 1. all: first [ st_neg | st_pos ]. Qed.
Obligation 2. all: first [ st_neg | st_pos ]. Qed.
Obligation 3. all: first [ st_neg | st_pos ]. Qed.
Obligation 4. all: first [ st_neg | st_pos ]. Qed.
Obligation 5. all: first [ st_neg | st_pos ]. Qed.
Obligation 6. all: first [ st_neg | st_pos ]. Qed.
Obligation 7. all: first [ st_neg | st_pos ]. Qed.
Obligation 8. all: first [ st_neg | st_pos ]. Qed.
Obligation 9. all: first [ st_neg | st_pos ]. Qed.
Obligation 10. all: first [ st_neg | st_pos ]. Qed.
Obligation 11. all: first [ st_neg | st_pos ]. Qed.
Obligation 12. all: first [ st_neg | st_pos ]. Qed.
Obligation 13. all: first [ st_neg | st_pos ]. Qed.
Obligation 14. all: first [ st_neg | st_pos ]. Qed.
Obligation 15. all: first [ st_neg | st_pos ]. Qed.
Obligation 16. all: first [ st_neg | st_pos ]. Qed.
Obligation 17. all: first [ st_neg | st_pos ]. Qed.
Obligation 18. all: first [ st_neg | st_pos ]. Qed.
Obligation 19. all: first [ st_neg | st_pos ]. Qed.
Obligation 20. all: first [ st_neg | st_pos ]. Qed.
Obligation 21. all: first [ st_neg | st_pos ]. Qed.
Obligation 22. all: first [ st_neg | st_pos ]. Qed.
Obligation 23. all: first [ st_neg | st_pos ]. Qed.
Obligation 24. all: first [ st_neg | st_pos ]. Qed.
Obligation 25. all: first [ st_neg | st_pos ]. Qed.
Obligation 26. all: first [ st_neg | st_pos ]. Qed.
Obligation 27. all: first [ st_neg | st_pos ]. Qed.
Obligation 28. all: first [ st_neg | st_pos ]. Qed.
Obligation 29. all: first [ st_neg | st_pos ]. Qed.
Obligation 30. all: first [ st_neg | st_pos ]. Qed.
Obligation 31. all: first [ st_neg | st_pos ]. Qed.
Obligation 32. all: first [ st_neg | st_pos ]. Qed.
Obligation 33. all: first [ st_neg | st_pos ]. Qed.
Obligation 34. all: first [ st_neg | st_pos ]. Qed.
Obligation 35. all: first [ st_neg | st_pos ]. Qed.
Obligation 36. all: first [ st_neg | st_pos ]. Qed.
Obligation 37. all: first [ st_neg | st_pos ]. Qed.
Obligation 38. all: first [ st_neg | st_pos ]. Qed.
Obligation 39. all: first [ st_neg | st_pos ]. Qed.
Obligation 40. all: first [ st_neg | st_pos ]. Qed.
Obligation 41. all: first [ st_neg | st_pos ]. Qed.
Obligation 42. all: first [ st_neg | st_pos ]. Qed.
Obligation 43. all: first [ st_neg | st_pos ]. Qed.
Obligation 44. all: first [ st_neg | st_pos ]. Qed.
Obligation 45. all: first [ st_neg | st_pos ]. Qed.
Obligation 46. all: first [ st_neg | st_pos ]. Qed.
Obligation 47. all: first [ st_neg | st_pos ]. Qed.
Obligation 48. all: first [ st_neg | st_pos ]. Qed.
Obligation 49. all: first [ st_neg | st_pos ]. Qed.
Obligation 50. all: first [ st_neg | st_pos ]. Qed.
Obligation 51. all: first [ st_neg | st_pos ]. Qed.
Obligation 52. all: first [ st_neg | st_pos ]. Qed.
Obligation 53. all: first [ st_neg | st_pos ]. Qed.
Obligation 54. all: first [ st_neg | st_pos ]. Qed.
Obligation 55. all: first [ st_neg | st_pos ]. Qed.
Obligation 56. all: first [ st_neg | st_pos ]. Qed.
Obligation 57. all: first [ st_neg | st_pos ]. Qed.
Obligation 58. all: first [ st_neg | st_pos ]. Qed.
Obligation 59. all: first [ st_neg | st_pos ]. Qed.
Obligation 60. all: first [ st_neg | st_pos ]. Qed.
Obligation 61. all: first [ st_neg | st_pos ]. Qed.
Obligation 62. all: first [ st_neg | st_pos ]. Qed.
Obligation 63. all: first [ st_neg | st_pos ]. Qed.
Obligation 64. all: first [ st_neg | st_pos ]. Qed.
Obligation 65. all: first [ st_neg | st_pos ]. Qed.
Obligation 66. all: first [ st_neg | st_pos ]. Qed.
Obligation 67. all: first [ st_neg | st_pos ]. Qed.
Obligation 68. all: first [ st_neg | st_pos ]. Qed.
Obligation 69. all: first [ st_neg | st_pos ]. Qed.
Obligation 70. all: first [ st_neg | st_pos ]. Qed.
Obligation 71. all: first [ st_neg | st_pos ]. Qed.
Obligation 72. all: first [ st_neg | st_pos ]. Qed.
Obligation 73. all: first [ st_neg | st_pos ]. Qed.
Obligation 74. all: first [ st_neg | st_pos ]. Qed.
Obligation 75. all: first [ st_neg | st_pos ]. Qed.
Obligation 76. all: first [ st_neg | st_pos ]. Qed.
Obligation 77. all: first [ st_neg | st_pos ]. Qed.
Obligation 78. all: first [ st_neg | st_pos ]. Qed.
Obligation 79. all: first [ st_neg | st_pos ]. Qed.
Obligation 80. all: first [ st_neg | st_pos ]. Qed.
Obligation 81. all: first [ st_neg | st_pos ]. Qed.
Obligation 82. all: first [ st_neg | st_pos ]. Qed.
Obligation 83. all: first [ st_neg | st_pos ]. Qed.
Obligation 84. all: first [ st_neg | st_pos ]. Qed.
Obligation 85. all: first [ st_neg | st_pos ]. Qed.
Obligation 86. all: first [ st_neg | st_pos ]. Qed.
Obligation 87. all: first [ st_neg | st_pos ]. Qed.
Obligation 88. all: first [ st_neg | st_pos ]. Qed.
Obligation 89. all: first [ st_neg | st_pos ]. Qed.
Obligation 90. all: first [ st_neg | st_pos ]. Qed.
Obligation 91. all: first [ st_neg | st_pos ]. Qed.
Obligation 92. all: first [ st_neg | st_pos ]. Qed.
Obligation 93. all: first [ st_neg | st_pos ]. Qed.
Obligation 94. all: first [ st_neg | st_pos ]. Qed.
Obligation 95. all: first [ st_neg | st_pos ]. Qed.
Obligation 96. all: first [ st_neg | st_pos ]. Qed.
Obligation 97. all: first [ st_neg | st_pos ]. Qed.
Obligation 98. all: first [ st_neg | st_pos ]. Qed.


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
  nbe_ty_order gc_deps gc_stack G A ->
  nbe_ty_order gc_deps gc_stack G B ->
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
  | H : nbe_ty_order _ _ _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac subtyping_impl_tac :=
  repeat subtyping_impl_tac1; try econstructor; mauto.

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations subtyping_impl {GC : GCtx} G A B (H : subtyping_order G A B) :
  { G ⊢a A ⊆ B } + { ~ G ⊢a A ⊆ B } :=
| G, A, B, H =>
    let (a, Ha) := nbe_ty_impl gc_deps gc_stack G A _ in
    let (b, Hb) := nbe_ty_impl gc_deps gc_stack G B _ in
    let*b _ := subtyping_nf_impl a b while _ in
    pureb _.
(** The two normalizations are the two halves of the order. *)
Obligation 1. (* nbe_ty_order gc_deps gc_stack G A *)
  destruct H; assumption.
Defined.
Obligation 2. (* nbe_ty_order gc_deps gc_stack G B *)
  destruct H; assumption.
Defined.
(** The normal forms are functional, so a failing check on them rules out the
    judgment, whose own derivation normalizes the same two types. *)
Obligation 3. (* ~ G ⊢a A ⊆ B *)
  progressive_inversion.
  functional_nbe_rewrite_clear.
  contradiction.
Qed.
Obligation 4. (* G ⊢a A ⊆ B *)
  econstructor; eassumption.
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
