From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Algorithmic Require Export Subtyping.
From Mctt.Extraction Require Import Lookup NbE PseudoMonadic.
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
(** Two types of levels, by the order on sorts. *)
| Levelⁿ@m, Levelⁿ@n =>
    let*b _ := Compare_dec.le_lt_dec m n while _ in
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
  | |- ⊢anf Typeωⁿ@_ ⊆ Typeωⁿ@_ => apply alg_subtyping_nf_univ; assumption
  (** The decided level order arrives destructed into its two components
      (the constant and the sorted atoms), so the pair is rebuilt here. *)
  | |- ⊢anf univⁿ _ _ ⊆ univⁿ _ _ =>
      apply alg_subtyping_nf_suniv;
      first [ assumption
            | unfold lvl_le, lvl_canon; cbn; f_equal; assumption ]
  | |- ⊢anf univⁿ _ _ ⊆ Typeωⁿ@_ => apply alg_subtyping_nf_small_large
  | |- ⊢anf Levelⁿ@_ ⊆ Levelⁿ@_ => apply alg_subtyping_nf_level; assumption
  | |- ⊢anf Πⁿ _ _ ⊆ Πⁿ _ _ => apply alg_subtyping_nf_pi; [ first [ assumption | reflexivity ] | assumption ]
  (** Every other normal form is below itself only, by [alg_subtyping_nf_refl_case], whose
      side condition holds by computation. *)
  | |- ⊢anf ?A ⊆ ?A => apply alg_subtyping_nf_refl_case; [ exact I | reflexivity ]
  end.

Solve All Obligations with (repeat intro; first [ discriminate | st_neg | st_pos ]).


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

(** The implementations, through a fast context [F]; the judgments are
    those of the global context it stands for. *)
Section SubtypingImpl.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations subtyping_impl G A B (H : subtyping_order G A B) :
  { G ⊢a A ⊆ B } + { ~ G ⊢a A ⊆ B } :=
| G, A, B, H =>
    let (a, Ha) := nbe_ty_impl F G A _ in
    let (b, Hb) := nbe_ty_impl F G B _ in
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

(** [subtyping_impl] at an initial environment of [G] computed beforehand,
    which both normalizations share. *)
#[tactic="idtac",derive(equations=no,eliminator=no)]
Equations subtyping_env_impl G (P : fast_env gc_deps gc_stack G) A B
  (H : subtyping_order G A B) : { G ⊢a A ⊆ B } + { ~ G ⊢a A ⊆ B } :=
| G, P, A, B, H =>
    let (a, Ha) := nbe_ty_env_impl F G P A _ in
    let (b, Hb) := nbe_ty_env_impl F G P B _ in
    let*b _ := subtyping_nf_impl a b while _ in
    pureb _.
Obligation 1. (* nbe_ty_order gc_deps gc_stack G A *)
  destruct H; assumption.
Defined.
Obligation 2. (* nbe_ty_order gc_deps gc_stack G B *)
  destruct H; assumption.
Defined.
Obligation 3. (* ~ G ⊢a A ⊆ B *)
  progressive_inversion.
  functional_nbe_rewrite_clear.
  contradiction.
Qed.
Obligation 4. (* G ⊢a A ⊆ B *)
  econstructor; eassumption.
Qed.

(** The same holds for [subtyping_impl]. *)

Theorem subtyping_impl_complete' : forall G A B,
    G ⊢a A ⊆ B ->
    forall (H : subtyping_order G A B),
      exists H', subtyping_impl G A B H = left H'.
Proof.
  intros; dec_complete.
Qed.

#[local]
Hint Resolve subtyping_order_sound subtyping_impl_complete' : mctt.

Theorem subtyping_impl_complete : forall G A B,
    G ⊢a A ⊆ B ->
    exists H H', subtyping_impl G A B H = left H'.
Proof.
  repeat unshelve mauto.
Qed.
End SubtypingImpl.
