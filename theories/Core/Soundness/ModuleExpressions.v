(** * Module Expressions at the Instances

    A module expression is glued at the instances of its context
    ([glu_rel_modexp_under_sub]) when, at each instance, its value at
    every glued environment is glued as it ([glu_modexp_at]).  A slot moves
    to its instance's module component: the literal of the slot's unit
    moved, glued by the construction ([glu_unit_modexp_at]), or a slot,
    glued by the context gluing ([glu_slot_modexp_at]).  A literal is the
    construction at each instance ([glu_rel_modexp_under_sub_lit]). *)

From Stdlib Require Import Lia List PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas MemberWf.
From Mctt.Core.Soundness Require Import LogicalRelation ContextCases VariableCases ModuleValues Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A module slot of a context glued with its variables' types is glued at
    the instances: its instance is its unit's literal moved, glued by the
    construction from the instance's gluing of the unit, or a slot of the
    instance's context. *)
Lemma glu_rel_modexp_under_sub_var : forall {Γ x U},
    glu_rel_ctx_types Γ ->
    Γ ∋ #x ≔ₘ U ->
    glu_rel_modexp_under_sub Γ (me_var x).
Proof.
  intros * HΓ Hx; constructor; [ exact HΓ |].
  intros Γ' τ Hτ.
  pose proof (glu_rel_sub_inst_typed _ _ _ Hτ) as Hτt.
  pose proof (glu_rel_sub_inst_ctx _ _ _ Hτ) as HΓ'.
  destruct (wf_sub_mod_compat _ _ _ _ _ Hτt _ _ Hx) as [E | (z & Ez & Hz)]; cbn [modexp_sub]; [ rewrite E | rewrite Ez ].
  - (** The literal of the unit moved *)
    assert (HwΓ : ⊢ Γ) by exact (wf_sub_cod _ _ _ _ _ Hτt).
    assert (HwΓ' : ⊢ Γ') by exact (wf_sub_dom _ _ _ _ _ Hτt).
    pose proof (sub_preserves_unit _ _ _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ HwΓ Hx) Hτt) as HUτ.
    pose proof (glu_rel_sub_inst_mods _ _ _ Hτ _ _ Hx _ _ (wf_wk_id _ _ _ HwΓ') HΓ') as Hg; rewrite gunit_wk_id in Hg.
    exact (glu_unit_modexp_at _ _ HUτ HΓ' Hg).
  - (** A slot of the instance's context *)
    exact (glu_slot_modexp_at _ _ _ Hz).
Qed.

End Fixed_GCtx.
