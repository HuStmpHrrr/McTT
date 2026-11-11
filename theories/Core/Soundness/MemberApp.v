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

(** Parameters of types of levels, the inner ones. *)
Lemma level_sorted_parameters_app_l : forall Δ0 Δ1, level_sorted_parameters (Δ0 ++ Δ1) -> level_sorted_parameters Δ0.
Proof. intros * H Δa κ T Δb ->; eapply H; rewrite <- app_assoc; reflexivity. Qed.

(** A definition of a type of levels in an open module: the module's
    parameters are of types of levels ([desc_levels_abstractable]). *)
Lemma open_entry_level_params : forall Γ Δ Φw Φx y Φ0 E A M,
    desc_ok gc_deps gc_stack Γ (mdesc_open Δ Φw Φx) ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    entry_kind E = ak_level -> level_sorted_parameters Δ.
Proof.
  intros * Hok Hp HE Hk; inversion Hok; subst.
  match goal with HL : desc_levels_abstractable _ _ _ _ _ |- _ => destruct HL as [HLs | Hnl] end; [ assumption |].
  exfalso; inversion Hnl; subst.
  match goal with Hne : forall y Φ0 E A M, gm_prefix_upto _ y = Some _ -> entry_tm E = Some (A, M) -> entry_kind E <> ak_level |- _ =>
    exact (Hne _ _ _ _ _ Hp HE Hk) end.
Qed.

End Fixed_GCtx.
