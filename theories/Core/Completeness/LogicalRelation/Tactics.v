From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions.
Import Domain_Notations Fixed_Notations.

(** Each semantic judgment is a record whose witnesses come first: the
    context PERs, read off a hypothesis by [eassumption], and the universe
    level, left to be found.  These open one, leaving its body.  The derived
    forms of the judgments ([rel_exp_under_ctx_simple] and the like) state the
    same witnesses as existentials, which the second alternative opens. *)
Ltac eexists_ctx_level :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_ctx_level_with i :=
  eexists;
  eexists; [eassumption |];
  exists i.

Ltac eexists_ctx_pair :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].

Ltac eexists_rel_exp :=
  first [ eapply mk_rel_exp_under_ctx; [eassumption |] | eexists_ctx_level ].

Ltac eexists_rel_exp_with i :=
  first [ eapply mk_rel_exp_under_ctx with (reu_lvl := i); [eassumption |] | eexists_ctx_level_with i ].

Ltac eexists_rel_sub :=
  first [ eapply mk_rel_sub_under_ctx; [eassumption | eassumption |] | eexists_ctx_pair ].

(** [rel_wk_under_ctx] has the same outer shape as [rel_sub_under_ctx] — two
    environment PERs, each with its context witness read off the goal. *)
Ltac eexists_rel_wk :=
  first [ eapply mk_rel_wk_under_ctx; [eassumption | eassumption |] | eexists_ctx_pair ].

Ltac eexists_subtyp :=
  first [ eapply mk_subtyp_under_ctx; [eassumption |] | eexists_ctx_level ].

Ltac eexists_subtyp_with i :=
  first [ eapply mk_subtyp_under_ctx with (stu_lvl := i); [eassumption |] | eexists_ctx_level_with i ].

Ltac invert_rel_typ_body :=
  simplify_evals;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  clear_dups;
  try rewrite <- per_univ_elem_equation_1 in *.
