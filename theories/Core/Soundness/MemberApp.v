(** * Members of Applied Module Expressions

    A member of a module expression lacking a parameter, applied to an
    argument, is the member of the module expression given the argument
    ([wf_exp_eq_mem_app]).  No rule says so: both sides are δ-equal to
    reducts related by [β], or the member is the filed member of a bare
    stored body ([mem_alias_filed]) and its application the self-named
    reduct of the member of the stored body at the argument. *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System SystemOpt CoreInversions.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Selection.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A description abstracted over a telescope ending in an assumption, as
    the term part's reduct: a [λ] over the outermost parameter. *)
Lemma reduct_up_last : forall Δ0 κ B X M,
    mdesc_reduct X = Some M ->
    mdesc_reduct (mdesc_up (Δ0 ++ ce_ass κ B :: nil) X) = Some (λ B (ctx_fn Δ0 M)).
Proof. intros * HM; rewrite mdesc_reduct_up, HM; cbn [option_map]; rewrite ctx_fn_app; reflexivity. Qed.

End Fixed_GCtx.
