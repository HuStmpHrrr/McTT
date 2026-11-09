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

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_empty : mctt.
#[export]
Hint Resolve glu_rel_ctx_extend glu_rel_ctx_extend_def : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊩ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. glu_intro; eapply glu_rel_ctx_empty; eapply gctx_embedding_wf, glu_gctx_embedding_embedding; eassumption. Qed.

Lemma glu_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof. glu_intro; eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp | |]; eassumption. Qed.

Lemma glu_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. glu_intro; eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | | |]; eassumption. Qed.
