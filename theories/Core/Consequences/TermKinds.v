(** * The Kind of a Term Is Unique

    Two types of one term are types of one kind ([term_kind_unique]).  The
    type checker infers one type of every typed term, below each of its
    types ([alg_type_infer_complete], [functional_alg_type_infer]); an
    algorithmic subtyping relates normal forms of one kind
    ([alg_subtyping_nf_kind]), and a type's normal form is of the kind of
    its sort ([nbe_ty_kind_of_sort]).  The set model's interpretation of
    a λ needs it ([fn_kinds_unique_ext]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Algorithmic.Typing Require Import Definitions Lemmas.
Import Domain_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A sort is of one kind. *)
Lemma sort_kind_unique : forall S κ κ', sort_kind S κ -> sort_kind S κ' -> κ = κ'.
Proof. intros * H H'; destruct H; inversion H'; reflexivity. Qed.

(** A type below the inferred one has the kind of the inferred type's
    normal form. *)
Lemma alg_subtyping_kind : forall Γ B T S κ W, Γ ⊢a B ⊆ T -> nbe_ty_f Γ B W ->
    Γ ⊢ T : S -> sort_kind S κ -> κ = nf_type_kind W.
Proof.
  intros * [W1 W2 HB HT Hs] HW HTS Hk.
  pose proof (functional_nbe_ty _ _ _ _ HB HW) as <-.
  rewrite (alg_subtyping_nf_kind _ _ Hs).
  rewrite (nbe_ty_kind_of_sort (sort_kind_type_sort _ _ Hk) HTS HT).
  exact (sort_kind_unique _ _ _ Hk (sort_kind_sort_exp_kind _ (sort_kind_type_sort _ _ Hk))).
Qed.

(** Two types of one term are of one kind. *)
Theorem term_kind_unique : forall Γ M T T' S S' κ κ', ⊢ᵍ gc_deps ⍮ gc_stack ->
    Γ ⊢ M : T -> Γ ⊢ M : T' -> Γ ⊢ T : S -> sort_kind S κ -> Γ ⊢ T' : S' -> sort_kind S' κ' -> κ = κ'.
Proof.
  intros * Hg HT HT' HTS Hk HTS' Hk'.
  destruct (alg_type_infer_complete (user_exp_all M) HT) as (B & HB & HBT).
  destruct (alg_type_infer_complete (user_exp_all M) HT') as (B' & HB' & HBT').
  pose proof (functional_alg_type_infer Hg HB HB') as <-.
  destruct HBT as [W W2 HW HT0 Hs].
  rewrite (alg_subtyping_kind _ _ _ _ _ W (alg_subtyp_run _ _ _ W W2 HW HT0 Hs) HW HTS Hk).
  rewrite (alg_subtyping_kind _ _ _ _ _ W HBT' HW HTS' Hk').
  reflexivity.
Qed.

End Fixed_GCtx.
