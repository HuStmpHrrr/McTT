(** * Extensions at the Instances

    An extension [Ψ] of a context [Γ] is glued at the instances of [Γ]
    ([glu_rel_ext_under_sub]) when each instance of [Γ], lifted through
    [Ψ], is an instance of [Ψ ++ Γ].  An extension is built entry by
    entry, as the extension rules build it: each entry lifts the instances
    by the lifting of its kind ([Instances.v]), which asks of the entry its
    parts glued at the instances of the context before it.  A term glued at
    the instances of [Ψ ++ Γ] is then glued at the instances of [Γ] lifted
    through [Ψ], as the motives and the branches of an eliminator are. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Soundness Require Import LogicalRelation Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The empty extension: an instance lifted through no entry is itself. *)
Lemma glu_rel_ext_under_sub_nil : forall {Γ},
    glu_rel_ctx_types Γ ->
    glu_rel_ext_under_sub Γ ⋅.
Proof. intros * HΓ; econstructor; [ exact HΓ | intros Γ' τ Hτ; exact Hτ ]. Qed.

(** An extension by an assumption of a type glued at the instances. *)
Lemma glu_rel_ext_under_sub_ass : forall {Γ Ψ A S κ},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_exp_under_sub (Ψ ++ Γ) A S ->
    sort_kind S κ ->
    glu_rel_ext_under_sub Γ (Ψ ▹{κ} A).
Proof.
  intros * [HΓ HΨ] HA HS; econstructor; [ exact HΓ | intros Γ' τ Hτ ].
  exact (glu_rel_sub_inst_q (HΨ _ _ Hτ) HA HS).
Qed.

(** An extension by a definition whose type and body are glued at the
    instances. *)
Lemma glu_rel_ext_under_sub_def : forall {Γ Ψ A M S},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_exp_under_sub (Ψ ++ Γ) A S ->
    type_sort S ->
    glu_rel_exp_under_sub (Ψ ++ Γ) M A ->
    glu_rel_ext_under_sub Γ (Ψ ▸ A ≔ M).
Proof.
  intros * [HΓ HΨ] HA HS HM; econstructor; [ exact HΓ | intros Γ' τ Hτ ].
  exact (glu_rel_sub_inst_q_def (HΨ _ _ Hτ) HA HS HM).
Qed.

(** An extension by a module slot whose unit is well formed and glued at
    the instances. *)
Lemma glu_rel_ext_under_sub_mod : forall {Γ Ψ U},
    glu_rel_ext_under_sub Γ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U ->
    glu_rel_unit_under_sub (Ψ ++ Γ) U ->
    glu_rel_ext_under_sub Γ (Ψ ▹ₘ U).
Proof.
  intros * [HΓ HΨ] HU HUg; econstructor; [ exact HΓ | intros Γ' τ Hτ ].
  pose proof (HΨ _ _ Hτ) as Hτ'.
  exact (glu_rel_sub_inst_q_mod Hτ' HU (sub_preserves_unit _ _ _ _ _ _ _ HU (glu_rel_sub_inst_typed _ _ _ Hτ')) HUg).
Qed.

(** An extension by a definition with a module part: its type and body
    glued at the instances, its alias well formed and glued at them. *)
Lemma glu_rel_ext_under_sub_dm : forall {Γ Ψ A M E} {i : nat},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_exp_under_sub (Ψ ++ Γ) A Typeω@i ->
    glu_rel_exp_under_sub (Ψ ++ Γ) M A ->
    gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    glu_rel_unit_under_sub (Ψ ++ Γ) (gu_mk nil (md_alias E)) ->
    glu_rel_ext_under_sub Γ (Ψ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)).
Proof.
  intros * [HΓ HΨ] HA HM HU HUg; econstructor; [ exact HΓ | intros Γ' τ Hτ ].
  pose proof (HΨ _ _ Hτ) as Hτ'.
  pose proof (sub_preserves_unit _ _ _ _ _ _ _ HU (glu_rel_sub_inst_typed _ _ _ Hτ')) as HUτ.
  exact (glu_rel_sub_inst_q_dm Hτ' HA HM HU HUτ HUg).
Qed.

(** A term glued at the instances of an extended context is glued at each
    instance of the context lifted through the extension. *)
Lemma glu_rel_exp_under_sub_ext_inst : forall {Γ Ψ Γ' τ M A},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_exp_under_sub (Ψ ++ Γ) M A ->
    glu_rel_sub_inst Γ' τ Γ ->
    tele_sub Ψ τ ++ Γ' ⊩ M[sb_qn (List.length Ψ) τ] : A[sb_qn (List.length Ψ) τ].
Proof. intros * [_ HΨ] HM Hτ; exact (glu_rel_exp_under_sub_inst _ _ _ HM _ _ (HΨ _ _ Hτ)). Qed.

End Fixed_GCtx.
