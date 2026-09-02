(** * Saturating the Context with Presuppositions

    The rules mention only the premises they need, but almost every
    proof about them needs more: that the context is well-formed, that the type
    of a term is a type, that a looked-up binding is a type.  All of these are
    consequences of the premises, and the tactics here add them to the context
    once, so that the rules can afterwards be applied by [mauto] without the
    search having to rediscover them at every step.

    Each tactic is idempotent: a presupposition that is already present — even
    marked by [on_all_hyp:] — is not added a second time.  That is what makes
    them safe to compose and to call repeatedly. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions Lemmas.
Import Syntax_Notations Wk_Notations.

(** [ctx_decomp] on a single context well-formedness hypothesis.  The type of
    the top binding is only added if the context does not already have it. *)
#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | ⊢ ?Γ ▹ ?A =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof ctx_decomp H as [HΓ HAi];
      match goal with
      | _: Γ ⊢ A : Type@_ |- _ => clear HAi
      | _: __mark__ _ Γ ⊢ A : Type@_ |- _ => clear HAi
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          destruct HAi as [i HA]
      end
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

(** The presuppositions that need no induction over equality: [presup_exp_typ]
    for typing, and the two projections of a weakening or a substitution.  The [wf_wk] and [wf_sub] cases are exactly [saturate_wk] and
    [saturate_sub], so [gen_core_presups] calls those rather than repeating
    them. *)
Ltac gen_core_presup H :=
  match type of H with
  | ?Γ ⊢ ?M : ?A =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof presup_exp H as [HΓ HAi];
      match goal with
      | _: Γ ⊢ A : Type@_ |- _ => clear HAi
      | _: __mark__ _ Γ ⊢ A : Type@_ |- _ => clear HAi
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          destruct HAi as [i HA]
      end
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | ?Γ ∋ #?x : ?A =>
      match goal with
      | _: Γ ⊢ A : Type@_ |- _ => fail
      | _: __mark__ _ Γ ⊢ A : Type@_ |- _ => fail
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          pose proof (ctx_lookup_wf _ _ _ ltac:(eassumption) H) as [i HA]
      end
  end.

Ltac gen_core_presups :=
  (on_all_hyp: fun H => gen_core_presup H);
  invert_wf_ctx;
  (on_all_hyp: fun H => gen_lookup_presup H);
  saturate_wk;
  saturate_sub;
  clear_dups.
