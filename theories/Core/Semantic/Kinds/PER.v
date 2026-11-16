(** * Inhabited Types and Expanded Bodies

    Every type relates some elements ([per_univ_elem_inhabited]), and
    related bodies are expanded: they have no open ([per_body_noopen]). *)

From Stdlib Require Import Lia List String.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Semantic Require Import PER Realizability.
From Mctt.Core.Semantic.Kinds Require Import Renaming Evaluation.
Import Domain_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hg : ⊢ᵍ gc_deps ⍮ gc_stack.

  (** Every type relates some elements: the reflection of a variable, or
      at [LevelSort], which has no variables, [Level@0]. *)
  Lemma per_univ_elem_inhabited : forall i R a a', DF a ≈ a' ∈ per_univ_elem i ↘ R -> exists c c', R c c'.
  Proof.
    intros * H.
    assert (Hd : a = LevelSortᵈ \/ not_level_sort a) by (destruct a; first [ left; reflexivity | right; discriminate ]).
    destruct Hd as [-> | Hn]; [| exists (⇑! a 0), (⇑! a' 0); exact (var_per_elem 0 H Hn) ].
    basic_invert_per_univ_elem H.
    exists Levelᵈ@0, Levelᵈ@0; apply H.
    split; [ exists (per_lvl_at 0), Levelᵈ@0; left; constructor; reflexivity |].
    split; [ exists (per_lvl_at 0), Levelᵈ@0; left; constructor; reflexivity |].
    exists (per_lvl_at 0); simp per_univ_elem; apply per_univ_elem_core_level; reflexivity.
  Qed.

  (** Related bodies are expanded: they have no open. *)
  Lemma per_body_noopen : forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> gm_noopen Φ /\ gm_noopen Φ'.
  Proof. induction 1; cbn; tauto. Qed.

End Fixed_GCtx.
