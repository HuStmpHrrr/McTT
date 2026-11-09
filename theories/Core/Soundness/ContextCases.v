(** * Glued Contexts

    Each entry kind extends a glued context.  The fundamental theorem's
    judgment of contexts also glues the variables' types, which
    [Instances.v] builds on these. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** As [wf_ctx_empty], relative to a well-formed global context. *)
Lemma glu_rel_ctx_empty : ⊢ᵍ gc_deps ⍮ gc_stack -> ⊩ ⋅.
Proof.
  intros; do 2 econstructor; [reflexivity | assumption].
Qed.

Hint Resolve glu_rel_ctx_empty : mctt.

(** An assumption of a type of a sort of its kind. *)
Lemma glu_rel_ctx_extend : forall {Γ A S κ},
    ⊩ Γ ->
    Γ ⊩ A : S ->
    sort_kind S κ ->
    ⊩ Γ ▹{κ} A.
Proof.
  intros * _ HA HS.
  destruct (glu_rel_exp_sort_typ HA HS) as (Sb & i & HSb & HAt & HAg).
  eexists; econstructor; [ exact HSb | exact HAt | exact HAg | reflexivity ].
Qed.

Hint Resolve glu_rel_ctx_extend : mctt.

(** A definition, of a type of a sort. *)
Lemma glu_rel_ctx_extend_def : forall {Γ A S M},
    ⊩ Γ ->
    Γ ⊩ A : S ->
    type_sort S ->
    Γ ⊩ M : A ->
    ⊩ Γ ▸ A ≔ M.
Proof.
  intros * _ HA HS HM.
  pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  assert (HSk : exists κ, sort_kind S κ) by (destruct HS; eexists; constructor).
  destruct HSk as [κ HSk].
  destruct (glu_rel_exp_sort_typ HA HSk) as (Sb & i & HSb & HAt & HAg).
  pose proof (glu_rel_exp_at_typ_index HSb HAg HM) as HMg.
  eexists; econstructor; [ exact HSb | exact HAt | exact HMt | exact HAg | exact HMg | reflexivity ].
Qed.

Hint Resolve glu_rel_ctx_extend_def : mctt.

(** A module slot of a well-formed unit. *)
Lemma glu_rel_ctx_extend_mod : forall {Γ U},
    ⊩ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    ⊩ Γ ▹ₘ U.
Proof.
  intros * [Sb HΓ] HU.
  exists (cons_mod_glu_sub_pred Γ U Sb).
  econstructor; [ exact HΓ | exact HU | reflexivity ].
Qed.

(** A definition with a module part glues when its term part does as a
    definition and its unit is well formed. *)
Lemma glu_rel_ctx_extend_dm : forall {Γ A M E} {i : nat},
    ⊩ Γ ->
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    ⊩ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E).
Proof.
  intros * _ HA HM HU.
  pose proof (glu_rel_exp_to_wf_exp HA) as HAt; pose proof (glu_rel_exp_to_wf_exp HM) as HMt.
  destruct (glu_rel_exp_sort_typ (κ := ak_relevant) HA ltac:(constructor)) as (Sb & j & HSb & HAt' & HAg).
  pose proof (glu_rel_exp_at_typ_index HSb HAg HM) as HMg.
  eexists; econstructor;
    [ exact HSb | exact HAt' | exact HMt | eapply wf_ctx_extend_dm; eassumption | exact HAg | exact HMg | reflexivity ].
Qed.

(** The tail of a glued context glues. *)
Lemma glu_rel_ctx_tail : forall {e Γ}, ⊩ e :: Γ -> ⊩ Γ.
Proof. intros * [Sb H]; inversion H; subst; eexists; eassumption. Qed.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_empty : mctt.
#[export]
Hint Resolve glu_rel_ctx_extend glu_rel_ctx_extend_def : mctt.
