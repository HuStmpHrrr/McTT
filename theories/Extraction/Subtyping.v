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
(** Two [Π]s: into a proposition, equal up to proofs; into an evaluated
    kind, of the same kinds, out of domains equal up to proofs, covariant
    in the codomain. *)
| nf_pi κd κc A B, nf_pi κd' κc' A' B' with abs_kind_eq_dec κc ak_propositional => {
  | left _ with nf_eq_upto_proofs_dec (nf_pi κd κc A B) (nf_pi κd' κc' A' B') => {
    | left _ => left _
    | right _ => right _ }
  | right _ =>
    let*b _ := abs_kind_eq_dec κd κd' while _ in
    let*b _ := abs_kind_eq_dec κc κc' while _ in
    let*b _ := nf_eq_upto_proofs_dec A A' while _ in
    let*b _ := subtyping_nf_impl B B' while _ in
    pureb _ }
(** Pseudo-monadic syntax in this catch-all branch leaves obligations
    unsolved, so it matches on [nf_eq_upto_proofs_dec A B] directly. *)
| A, B with nf_eq_upto_proofs_dec A B => {
  | left _ => left _
  | right _ => right _
  }.

(** A branch that rules out subtyping: the judgment is inverted, and what the
    branch knows (a disequality of normal forms, or an arithmetic bound)
    contradicts every rule that could have derived it. *)
#[local]
Ltac subtyping_failure :=
  lazymatch goal with H : ⊢anf _ ⊆ _ |- False => inversion H; subst end;
  simpl in *;
  first [ lia | congruence | contradiction
        (** A kind left open: the refused [Π]'s codomain kind *)
        | repeat match goal with κ : abs_kind |- _ => destruct κ end; simpl in *;
          first [ congruence | contradiction | match goal with H : evaluated_kind _ |- _ => inversion H end ] ].

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
  (** A [Π] into a proposition, equal up to proofs *)
  | |- ⊢anf nf_pi _ ak_propositional _ _ ⊆ _ => apply alg_subtyping_nf_refl_case; [ exact I | assumption ]
  | |- ⊢anf nf_pi _ _ _ _ ⊆ nf_pi _ _ _ _ =>
      apply alg_subtyping_nf_pi; [ apply evaluated_kind_of_not_propositional; assumption | assumption | assumption ]
  (** Every other normal form is below those equal to it up to proofs, by
      [alg_subtyping_nf_refl_case], whose side condition holds by
      computation; of different heads, none is. *)
  | |- ⊢anf ?A ⊆ ?B =>
      first [ apply alg_subtyping_nf_refl_case; [ exact I | assumption ]
            | exfalso; match goal with H : nf_eq_upto_proofs _ _ |- _ => unfold nf_eq_upto_proofs in H; cbn in H; discriminate end ]
  end.

Solve All Obligations with (repeat intro; first [ discriminate | subtyping_failure | st_pos ]).


(** [subtyping_nf_impl] is sound by construction, and its completeness is
    straightforward. *)

Theorem subtyping_nf_impl_complete : forall A B,
    ⊢anf A ⊆ B ->
    exists H, subtyping_nf_impl A B = left H.
Proof.
  intros; decision_complete.
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
  intros; decision_complete.
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
