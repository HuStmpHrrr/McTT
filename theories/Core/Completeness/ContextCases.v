(** * The Rules of Contexts

    The rules of [⊢ Γ] in the PER model: the empty context and its
    extensions.  The lemmas they rest on are in [LogicalRelation/Contexts.v]
    and, for the module entries, [Modules/MemberTypes.v]. *)

From Stdlib Require Import List Morphisms_Relations.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import LogicalRelation LogicalRelation.Universes.
From Mctt.Core.Completeness.LogicalRelation Require Import Contexts.
From Mctt.Core.Completeness.Modules Require Import Slots MemberTypes.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma sem_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κ ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof.
  intros * HA HS; sem_intro.
  apply valid_ctx_ass; [ assumption | eapply rel_ctx_wf_extend_sort; eassumption ].
Qed.

Lemma sem_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof.
  intros * HA HS HM; sem_intro.
  apply valid_ctx_def; [ assumption | eapply rel_ctx_wf_extend_def_sort; eassumption ].
Qed.

(** The empty context, which has no relation of its own: [⊨ ⋅] is a
    constructor. *)
Lemma sem_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊨ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. intros * H; sem_intro; constructor. Qed.

Lemma sem_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof.
  intros * HU; sem_intro.
  apply valid_ctx_mod;
    [ assumption | eapply rel_ctx_wf_extend_mod; [ eassumption | eassumption | eapply valid_unit_lit_scoped; eassumption ]
    | assumption ].
Qed.

Lemma sem_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ).
Proof.
  intros * HA HM HU; sem_intro.
  apply valid_ctx_dm; [ assumption | eapply rel_ctx_wf_extend_dm; [ eassumption | eassumption | eassumption | eassumption | eapply valid_unit_lit_scoped; eassumption ] | assumption ].
Qed.
