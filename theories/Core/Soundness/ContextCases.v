(** * The Rules of Contexts

    The rules of [⊢ Γ] in the gluing model: the empty context and its
    extensions.  The lemmas they rest on are in [LogicalRelation/Contexts.v]
    and [LogicalRelation/Instance.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Variables LogicalRelation.Contexts
  Modules.ModuleValues LogicalRelation.Instance.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

Lemma glu_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊩ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. glu_intro; eapply glu_rel_ctx_types_empty; eapply gctx_embedding_wf, glu_gctx_embedding_embedding; eassumption. Qed.

Lemma glu_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof. glu_intro; eapply glu_rel_ctx_types_extend; eassumption. Qed.

Lemma glu_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. glu_intro; eapply glu_rel_ctx_types_extend_def; eassumption. Qed.

(** A slot glues when the context does and its unit is well formed and
    glues. *)
Lemma glu_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     glu_unit_eq Θ Ξ Γ U U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  - eapply (@glu_rel_ctx_types_extend_mod (gc_mk _ _)); [ eassumption | apply Hwu; eassumption | eassumption ].
  - eapply glu_ctx_deep_cons_unit; [ reflexivity | eassumption | eassumption ].
Qed.

(** A definition with a module part glues when its term part does and its
    unit is well formed and glues. *)
Lemma glu_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
     glu_unit_eq Θ Ξ Γ (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E)) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  - eapply (@glu_rel_ctx_types_extend_dm (gc_mk _ _)); [ eassumption | eassumption | apply Hwu; eassumption | eassumption ].
  - eapply glu_ctx_deep_cons_unit; [ reflexivity | eassumption | eassumption ].
Qed.
