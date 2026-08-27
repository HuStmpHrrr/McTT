From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions Lemmas.
Import Domain_Notations.

(** Substitution and weakening are now *operations*, so [M[σ]] is not in
    constructor form even when [M] is: an evaluation hypothesis
    [⟦ Type@i[σ] ⟧ ρ ↘ a] cannot be inverted until [exp_sub] has been unfolded
    far enough to expose the head.  Restricting the [cbn] delta list to the two
    recursive functions does exactly that and nothing else — in particular
    [eval_sub] ([simpl never]) and [sb_q] ([simpl never]) stay folded, so the
    encoding of lifting is never exposed. *)
Ltac simplify_subs := cbn [exp_sub exp_wk] in *.

Ltac simplify_evals :=
  functional_eval_rewrite_clear;
  clear_dups;
  simplify_subs;
  (** [eval_sub] is absent on purpose: it is a pointwise [Definition], not an
      inductive family, so there are no cases to split.  Take it apart with
      [eval_sub_index] instead. *)
  repeat (match_by_head eval_exp ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_app ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_natrec ltac:(fun H => directed dependent destruction H));
  functional_eval_rewrite_clear;
  clear_dups.
