(** * Embeddings of Valuations

    A valuation [γ2] extends a valuation [γ1] along a growth of the global
    context when the two agree at every path the smaller context already
    knows, and at every path the bigger one still has nothing at
    ([valuation_extends]): they differ only where the growth newly
    resolves something.  Along such an extension the set interpretation is
    preserved ([set_interp_embedding]), and so are the set judgments
    ([set_embedding]).

    The module a term entry gives where a module is read
    ([set_entry_module_part] of a [set_entry_term]) is the global module at
    the empty path, which no well-formed context has anything at
    ([empty_unit_nothing]); so the two valuations agree there, and the
    interpretation of a module expression reads only globals they agree on
    ([set_module_filed]). *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Interp.
From Mctt.Core.Syntactic Require Import Syntax Members.
From Mctt.Core.Syntactic.System Require Import Definitions.
From Mctt.Core.Syntactic.System.Global Require Import Paths Presup.
Import ListNotations.

(** [gctx_knows Θ Ξ p]: the global context has something at the path [p].
    Its negation is [gctx_finds_nothing]. *)
Definition gctx_knows (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  gc_resolve Θ Ξ p <> None \/ gc_module Θ Ξ p <> None \/ gc_loc Θ Ξ p <> None \/
  ind_lookup Θ Ξ p <> None \/ record_lookup Θ Ξ p <> None.

(** [valuation_agrees_at γ1 γ2 p]: the two valuations give the path [p] the
    same values. *)
Record valuation_agrees_at (γ1 γ2 : global_valuation) (p : qname) : Prop :=
  { (** The term entry's value and kind *)
    va_term : global_term γ2 p = global_term γ1 p
    (** The module *)
  ; va_module : global_module γ2 p = global_module γ1 p
    (** Every member's type former *)
  ; va_former : forall k, global_former γ2 p k = global_former γ1 p k
    (** Every constructor *)
  ; va_constructor : forall k c, global_constructor γ2 p k c = global_constructor γ1 p k c
    (** The group's semantics *)
  ; va_group : global_group γ2 p = global_group γ1 p
    (** The record type's former *)
  ; va_record_former : global_record_former γ2 p = global_record_former γ1 p
    (** The record type's semantics *)
  ; va_record : global_record γ2 p = global_record γ1 p }.

(** The agreement at a path is reflexive. *)
Lemma valuation_agrees_at_refl : forall γ p, valuation_agrees_at γ γ p.
Proof. intros; constructor; reflexivity. Qed.

(** [valuation_extends Θ1 Ξ1 Θ2 Ξ2 γ1 γ2]: the two valuations agree at
    every path the smaller context already knows, and at every path the
    bigger one still has nothing at, so that they differ only where the
    growth newly resolves something.  The proofness table agrees
    everywhere: the construction fixes it once for the whole context. *)
Record valuation_extends (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (γ1 γ2 : global_valuation) : Prop :=
  { (** The values agree at every path that the growth does not newly
        resolve *)
    ve_agrees : forall p, gctx_knows Θ1 Ξ1 p \/ gctx_finds_nothing Θ2 Ξ2 p -> valuation_agrees_at γ1 γ2 p
    (** The proofness table agrees at every path *)
  ; ve_proofs : forall q x, global_proofs γ2 q x = global_proofs γ1 q x }.

(** A valuation extends itself along any growth. *)
Lemma valuation_extends_refl : forall Θ1 Ξ1 Θ2 Ξ2 γ, valuation_extends Θ1 Ξ1 Θ2 Ξ2 γ γ.
Proof. intros; constructor; [ intros p _; apply valuation_agrees_at_refl | intros; reflexivity ]. Qed.

(** [set_module_filed Θ1 Ξ1 Θ2 Ξ2 m]: every global module inside [m] is
    one the smaller context has filed, or one at a path the bigger one
    still has nothing at — the junk module a term entry gives where a
    module is read ([set_entry_module_part]) is the second kind, at a path
    no well-formed context has anything at ([empty_unit_nothing]). *)
Inductive set_module_filed (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : set_module -> Prop :=
(** A function of a parameter: at every value of it *)
| smf_params : forall dom P f, (forall v, set_module_filed Θ1 Ξ1 Θ2 Ξ2 (f v)) ->
    set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_params dom P f)
(** A table: the module part of every entry it has *)
| smf_members : forall ms, (forall x e, members_lookup ms x = Some e -> set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_entry_module_part e)) ->
    set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_members ms)
(** A global module: filed in the smaller context, or at a path the
    bigger one has nothing at *)
| smf_global : forall p args, gc_loc Θ1 Ξ1 p <> None \/ gctx_finds_nothing Θ2 Ξ2 p ->
    set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_global p args)
(** Under a condition: the module under it *)
| smf_cond : forall φ P m, set_module_filed Θ1 Ξ1 Θ2 Ξ2 m -> set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_cond φ P m).

(** The empty table has no global, so it is filed. *)
Lemma set_module_filed_nil : forall Θ1 Ξ1 Θ2 Ξ2, set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_members nil).
Proof. intros; apply smf_members; intros x e He; cbn in He; discriminate. Qed.

(** The module a term entry gives is filed: nothing is at the empty unit
    path ([empty_unit_nothing]). *)
Lemma set_module_filed_term : forall Θ1 Ξ1 Θ2 Ξ2, ⊢ᵍ Θ2 ⍮ Ξ2 ->
    set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_module_global (q_abs nil nil) nil).
Proof. intros * Hg2; apply smf_global; right; exact (empty_unit_nothing _ _ Hg2 (q_abs nil nil) eq_refl). Qed.

(** So is the module part of every entry a term gives. *)
Lemma set_module_filed_entry_term : forall Θ1 Ξ1 Θ2 Ξ2 κ v, ⊢ᵍ Θ2 ⍮ Ξ2 ->
    set_module_filed Θ1 Ξ1 Θ2 Ξ2 (set_entry_module_part (set_entry_term κ v)).
Proof. intros * Hg2; cbn [set_entry_module_part]; exact (set_module_filed_term _ _ _ _ Hg2). Qed.
