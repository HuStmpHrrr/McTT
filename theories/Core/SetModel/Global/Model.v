(** * Valuations That Model a Global Context

    A valuation models the global context ([set_gctx_ok]) when what it
    gives each global is what the global's stored description denotes:

    - a term member of a filed module or frame, closed over the module's
      telescope, has its stored kind, is of its closed type and is its
      closed δ-reduct ([set_filed_term_with]);
    - a filed body or frame is its own global module, and an alias is the
      module its unit denotes. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.Syntactic Require Import Syntax Members.
Import ListNotations.

Section Model.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** [set_filed_term_with R0 κ g]: the closed member read as [R0] has the
    kind [κ] and the value [g]: of its type, its δ-reduct's. *)
Record set_filed_term_with (R0 : mdesc) (κ : abs_kind) (g : aczel_set) : Prop :=
  { (** The kind is the stored one *)
    set_filed_term_kind : κ = mdesc_kind R0
    (** The value is of the closed type *)
  ; set_filed_term_typed : forall A FA, mdesc_type R0 = Some A -> set_denotes T γ nil A FA ->
      set_mem g (code_carrier (FA empty_set_env))
    (** The value is the closed δ-reduct's *)
  ; set_filed_term_reduct : forall M FM, mdesc_reduct R0 = Some M -> set_denotes T γ nil M FM ->
      set_eq g (FM empty_set_env) }.

(** [set_gctx_ok]: [γ] models the global context. *)
Record set_gctx_ok : Prop :=
  { (** Every term member stored at a filed module or frame is modelled *)
    set_gctx_ok_terms : forall p Tl Φ x R0, gc_loc gc_deps gc_stack p = Some (Tl, Φ) ->
      stored_term_member gc_stack Φ p x R0 ->
      set_filed_term_with R0 (fst (global_term γ (qname_in p x))) (snd (global_term γ (qname_in p x)))
    (** A filed module or frame is its own global module *)
  ; set_gctx_ok_bodies : forall q TΦ, gc_loc gc_deps gc_stack q = Some TΦ -> global_module γ q = set_module_global q nil
    (** An alias is the module its closed unit denotes *)
  ; set_gctx_ok_aliases : forall q Ua FU, gc_module gc_deps gc_stack q = Some (mr_alias Ua) ->
      set_modexp_denotes T γ nil (me_lit Ua) FU -> set_module_eq (global_module γ q) (FU empty_set_env) }.

End Model.
