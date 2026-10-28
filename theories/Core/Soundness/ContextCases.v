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

Lemma glu_rel_ctx_extend : forall {Γ A} {i : nat},
    ⊩ Γ ->
    Γ ⊩ A : Typeω@i ->
    ⊩ Γ ▹ A.
Proof.
  intros * [Sb] HA.
  assert (Γ ⊢ A : Typeω@i) by mauto 3.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
Qed.

Hint Resolve glu_rel_ctx_extend : mctt.

Lemma glu_rel_ctx_extend_def : forall {Γ A M} {i : nat},
    ⊩ Γ ->
    Γ ⊩ A : Typeω@i ->
    Γ ⊩ M : A ->
    ⊩ Γ ▸ A ≔ M.
Proof.
  intros * [Sb] HA HM.
  assert (Γ ⊢ A : Typeω@i) by mauto 3.
  assert (Γ ⊢ M : A) by mauto 3.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
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
Proof. glu_intro; eapply glu_rel_ctx_empty; eapply gctx_embedding_wf, glu_emb_emb; eassumption. Qed.

Lemma glu_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ A ).
Proof. glu_intro; eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp |]; eassumption. Qed.

Lemma glu_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. glu_intro; eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp | |]; eassumption. Qed.
