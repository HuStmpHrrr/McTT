From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions Lemmas.
Import Domain_Notations.

(** Substitution and weakening are functions on syntax, so [M[σ]] is not in
    constructor form even when [M] is: an evaluation hypothesis
    [⟦ Typeω@i[σ] ⟧ ρ ↘ a] cannot be inverted until [exp_sub] is unfolded far
    enough to expose the head.  [simplify_subs] unfolds only [exp_sub] and
    [exp_wk]; [eval_sub] and [sb_q] stay folded, so the encoding of lifting is
    never exposed. *)
Ltac simplify_subs := cbn [exp_sub exp_wk] in *.

Ltac simplify_evals :=
  functional_eval_rewrite_clear;
  clear_dups;
  simplify_subs;
  (** [eval_sub] is a pointwise [Definition], not an inductive family, so it
      has no cases to split.  Use [eval_sub_index] instead. *)
  repeat (match_by_head eval_exp ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_app ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_natrec ltac:(fun H => directed dependent destruction H));
  functional_eval_rewrite_clear;
  clear_dups.
