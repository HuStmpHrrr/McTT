(** * Embeddings of Valuations

    A valuation [γ2] extends a valuation [γ1] along an embedding
    [gctx_embedding Θ1 Ξ1 Θ2 Ξ2] when it agrees on every global resolved
    by [Θ1 ⍮ Ξ1] and on the proofness table at every path.  Along such
    an extension the set interpretation is preserved
    ([set_interp_embedding]), and so are the set judgments
    ([set_embedding]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Interp.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic.System.Global Require Import Paths Presup.
Import ListNotations.

(** [valuation_extends Θ1 Ξ1 γ1 γ2]: [γ2] has the values [γ1] has at every
    global resolved by [Θ1 ⍮ Ξ1], and the same proofness table at every
    path.  Reads of the valuation at globals the smaller context has
    not resolved are left free: the construction of a model fixes them
    once, so that every intermediate valuation agrees with every later
    one at every chain of a resolved path. *)
Record valuation_extends (Θ1 : gdeps) (Ξ1 : gstack) (γ1 γ2 : global_valuation) : Prop := mk_valuation_extends
  { (** The value of a term entry resolved in the smaller context is
        kept *)
    ve_term : forall p E, gc_resolve Θ1 Ξ1 p = Some E -> global_term γ2 p = global_term γ1 p
    (** A module's value resolved in the smaller context is kept *)
  ; ve_module : forall p r, gc_module Θ1 Ξ1 p = Some r -> global_module γ2 p = global_module γ1 p
    (** The type former of a member of a group the smaller context has
        is kept *)
  ; ve_former : forall p D k, ind_lookup Θ1 Ξ1 p = Some D -> global_former γ2 p k = global_former γ1 p k
    (** A constructor of a group the smaller context has is kept *)
  ; ve_constructor : forall p D k c, ind_lookup Θ1 Ξ1 p = Some D -> global_constructor γ2 p k c = global_constructor γ1 p k c
    (** The semantics of a group the smaller context has is kept *)
  ; ve_group : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> global_group γ2 p = global_group γ1 p
    (** The type former of a record type the smaller context has is
        kept *)
  ; ve_record_former : forall p R, record_lookup Θ1 Ξ1 p = Some R -> global_record_former γ2 p = global_record_former γ1 p
    (** The semantics of a record type the smaller context has is
        kept *)
  ; ve_record : forall p R, record_lookup Θ1 Ξ1 p = Some R -> global_record γ2 p = global_record γ1 p
    (** The proofness table agrees at every path *)
  ; ve_proofs : forall q x, global_proofs γ2 q x = global_proofs γ1 q x }.
