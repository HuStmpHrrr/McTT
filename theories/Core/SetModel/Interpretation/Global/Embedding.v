(** * Modelling a Context Where It Grows

    A valuation models a global context at a bigger one
    ([set_gctx_embedding]) when everything the smaller context resolves is
    modelled there: the fields are [set_gctx_ok]'s, with the lookups read
    at the smaller context and the set judgments taken at the bigger one.

    One valuation serves the whole growth, as it does in the completeness
    and soundness layers ([glu_gctx_embedding]): the context grows, the
    valuation does not.  So a derivation is read where it is checked and
    its judgment lands where the derivation is used ([set_fundamental]),
    and no value is ever carried from one context to another.

    [set_gctx_ok] is the instance where the two contexts are the same
    ([set_gctx_embedding_refl], [set_gctx_ok_of_embedding]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation.Global Require Export Model.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic.System.Global Require Import Paths Presup.
Import ListNotations.

(** [set_gctx_embedding Θ1 Ξ1 GC2 T γ]: everything the context [Θ1 ⍮ Ξ1]
    resolves is modelled at [GC2] by [γ].  The target is a context
    instance, not a pair of its two parts, so that the fields are the set
    judgments of the section that uses them: [GC2] and
    [gc_mk gc_deps gc_stack] are equal only after a case on [GC2]. *)
Record set_gctx_embedding (Θ1 : gdeps) (Ξ1 : gstack) (GC2 : GCtx)
    (T : universe_tower) (γ : global_valuation) : Prop :=
  { (** The smaller context grows into the bigger one *)
    set_gctx_embedding_embedding : gctx_embedding Θ1 Ξ1 (@gc_deps GC2) (@gc_stack GC2)
    (** Every module it files or has open is modelled there *)
  ; set_gctx_embedding_filed : forall p Tl Φ, gc_loc Θ1 Ξ1 p = Some (Tl, Φ) ->
      @set_filed_mod GC2 T γ p Tl Φ
    (** A filed module or frame is its own global module *)
  ; set_gctx_embedding_bodies : forall q TΦ, gc_loc Θ1 Ξ1 q = Some TΦ -> global_module γ q = set_module_global q nil
    (** Every global module equals itself, so selection respects
        equality *)
  ; set_gctx_embedding_modules : forall q, set_module_eq γ (global_module γ q) (global_module γ q)
    (** An alias is the module its closed unit denotes there *)
  ; set_gctx_embedding_aliases : forall q Ua FU, gc_module Θ1 Ξ1 q = Some (mr_alias Ua) ->
      @set_modexp_denotes GC2 T γ nil (me_lit Ua) FU -> set_module_eq γ (global_module γ q) (FU empty_set_env)
    (** Every group it declares is modelled there *)
  ; set_gctx_embedding_groups : forall p D, ind_lookup Θ1 Ξ1 p = Some D ->
      @set_group_ok GC2 T γ p D (global_group γ p)
    (** So is every record type *)
  ; set_gctx_embedding_records : forall p R, record_lookup Θ1 Ξ1 p = Some R ->
      @set_record_ok GC2 T γ p R (global_record γ p) }.

Section Reflexivity.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A valuation that models a context models it where it is. *)
Lemma set_gctx_embedding_refl : ⊢ᵍ gc_deps ⍮ gc_stack -> set_gctx_ok T γ ->
    set_gctx_embedding gc_deps gc_stack GC T γ.
Proof.
  intros Hg [Hf Hb Hm Ha Hgr Hr]; constructor;
    [ exact (gctx_embedding_refl _ _ Hg) | exact Hf | exact Hb | exact Hm | exact Ha | exact Hgr | exact Hr ].
Qed.

(** So, read where it is, an embedding is what it is to model a context. *)
Lemma set_gctx_ok_of_embedding : set_gctx_embedding gc_deps gc_stack GC T γ -> set_gctx_ok T γ.
Proof.
  intros [_ Hf Hb Hm Ha Hgr Hr]; constructor;
    [ exact Hf | exact Hb | exact Hm | exact Ha | exact Hgr | exact Hr ].
Qed.

End Reflexivity.
