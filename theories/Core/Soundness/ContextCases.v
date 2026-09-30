From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** As [wf_ctx_empty], relative to a well-formed global context. *)
Lemma glu_rel_ctx_empty : wf_gctx gc_deps gc_stack -> ⊩ ⋅.
Proof.
  intros; do 2 econstructor; [reflexivity | assumption].
Qed.

Hint Resolve glu_rel_ctx_empty : mctt.

Lemma glu_rel_ctx_extend : forall {Γ A i},
    ⊩ Γ ->
    Γ ⊩ A : Type@i ->
    ⊩ Γ ▹ A.
Proof.
  intros * [Sb] HA.
  assert (Γ ⊢ A : Type@i) by mauto 3.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
Qed.

Hint Resolve glu_rel_ctx_extend : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_ctx_empty : mctt.
#[export]
Hint Resolve glu_rel_ctx_extend : mctt.
