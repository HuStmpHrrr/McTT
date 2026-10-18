(** * The Gluing Judgments

    The soundness counterpart of [Core/Completeness/Judgments.v]: a gluing
    judgment is stated at a global context [Θ ⍮ Ξ] and holds at every
    global context [Θ2 ⍮ Ξ2] that [Θ ⍮ Ξ] embeds into soundly ([glu_emb]),
    as the gluing relation of [Core/Soundness/LogicalRelation/Definitions.v]
    read there.  The model is unary, so there are three judgments: a context
    glues, a term glues at its type, and a universe is one.  A module slot of
    a glued context carries its unit's well-formedness, which is what the
    gluing of a slot asks for ([glu_ctx_env_cons_mod]).

    The relations at one global context are the building blocks; a sound
    embedding is stated over them, so the definitions below are not
    circular. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import GlobalPresup GlobalPaths.
From Mctt.Core.Soundness Require Import LogicalRelation IndCases.
Import Domain_Notations Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Sound embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, its
    declarations glue there, and so does a member of one of its stored
    bodies that is an axiom or an abstract definition, at its stored type. *)
Record glu_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { gme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; gme_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @glu_core (gc_mk Θ2 Ξ2) D
  ; gme_glob : forall p T Φ x Φ0 b pv A oM Γ,
      loc Θ1 Ξ1 p T Φ ->
      gm_prefix_upto Φ x = Some (gm_ext Φ0 x (ge_def b pv A oM)) ->
      (if b then oM else None) = None ->
      @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ ->
      @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_mem (qname_mod p) x) A
  }.

(** ** The judgments at one target *)

(** A universe, as its two cases: large, or small at a level that glues. *)
Record kglu_univ_at (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop := mk_kglu_univ_at
  { kgu_ctx : @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ
  ; kgu_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @glu_rel_exp (gc_mk Θ2 Ξ2) Γ L (Level@n)) }.

Arguments kgu_ctx {Θ2 Ξ2 Γ U}.
Arguments kgu_univ {Θ2 Ξ2 Γ U}.

(** ** The judgments *)

Definition kglu_ctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ.

Definition kglu_exp Θ Ξ Γ M A : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ M A.

Definition kglu_univ Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, glu_emb Θ Ξ Θ2 Ξ2 -> kglu_univ_at Θ2 Ξ2 Γ U.

Notation "⊩ Θ ⍮ Ξ ⍮ Γ" := (kglu_ctx Θ Ξ Γ)
  (at level 70, Θ at next level, Ξ at level 69, Γ at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ M : A" := (kglu_exp Θ Ξ Γ M A)
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊩ᵤ U" := (kglu_univ Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
