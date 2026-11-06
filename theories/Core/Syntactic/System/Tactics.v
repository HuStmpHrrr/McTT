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
From Mctt.Core.Syntactic.System.Inductives Require Export Typing Views UniformParams.
Import Syntax_Notations Wk_Notations.

(** The type [A] of a typed term [HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : A], its type
    being [HAi : Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A], is added as its sort, the sort's
    [type_sort] and the typing, unless the context already has [A] at a
    universe, at [Propₘ], or at a sort it knows to be one.  [A] is of a
    sort when [M] is no former of a type of levels
    ([presup_exp_typ_not_level]); otherwise [A] may be the sort
    [LevelSort] itself, of no sort, and [HAi] is kept as it is. *)
Ltac add_type Θ Ξ Γ M A HM HAi :=
  match goal with
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@_ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : Typeω@_ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : Propₘ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : Propₘ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : ?S, _: type_sort ?S |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : ?S, _: type_sort ?S |- _ => clear HAi
  | _ => lazymatch A with LevelSort => clear HAi | _ => fail end
  | _ =>
      let Hn := fresh "Hn" in
      assert (Hn : ~ level_type_former M) by (inversion 1);
      let S := fresh "S" in
      let HS := fresh "HS" in
      let HA := fresh "HA" in
      destruct (presup_exp_typ_not_level HM Hn) as (S & HS & HA); clear Hn HAi
  (** or when [A] is visibly another type than [LevelSort] *)
  | _ =>
      let Hn := fresh "Hn" in
      assert (Hn : A <> LevelSort) by discriminate; clear Hn;
      let Hc := fresh "Hc" in
      let S := fresh "S" in
      let HS := fresh "HS" in
      let HA := fresh "HA" in
      pose proof (presup_exp_typ_cases HM) as Hc;
      inversion Hc as [? S HS HA | ? ?]; clear Hc HAi
  | _ => idtac
  end.

(** A type known to be of a sort, by the tactic [tac] that adds its sort,
    the sort's [type_sort] and the typing, unless the context already has
    [A] at a sort; [HAi : ⊢ᵗ A] is dropped either way. *)
Ltac add_sorted_type Θ Ξ Γ A HAi tac :=
  match goal with
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@_ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : Typeω@_ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : Propₘ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : Propₘ |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ Γ ⊢ A : ?S, _: type_sort ?S |- _ => clear HAi
  | _: Θ ⍮ Ξ ⍮ __mark__ _ Γ ⊢ A : ?S, _: type_sort ?S |- _ => clear HAi
  | _ => clear HAi; tac
  end.

(** [ctx_decomp] on a single context well-formedness hypothesis.  The type of
    the top binding is only added if the context does not already have it. *)
#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | ⊢ ?Θ ⍮ ?Ξ ⍮ ?Γ ▹{_} ?A =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof ctx_decomp H as [HΓ HAi];
      (** the entry is at a sort of its kind, never at [LevelSort] *)
      add_sorted_type Θ Ξ Γ A HAi ltac:(
        let S := fresh "S" in let HS := fresh "HS" in let HA := fresh "HA" in let Hk := fresh "Hk" in
        destruct (proj2 (ctx_decomp_sort_kind H)) as (S & Hk & HA); pose proof (sort_kind_type_sort _ _ Hk) as HS; clear Hk)
  | ⊢ ?Θ ⍮ ?Ξ ⍮ ?Γ ▸ ?A ≔ ?M =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      let HM := fresh "HM" in
      pose proof ctx_decomp_def H as [HΓ [HAi HM]];
      add_sorted_type Θ Ξ Γ A HAi ltac:(
        let S := fresh "S" in let HS := fresh "HS" in let HA := fresh "HA" in
        destruct (ctx_decomp_def_sorted H) as (S & HS & HA))
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

(** The presuppositions that need no induction over equality: [presup_exp_typ]
    for typing, and the two projections of a weakening or a substitution.  The
    [wf_wk] and [wf_sub] cases are exactly [saturate_wk] and [saturate_sub],
    which [gen_core_presups] calls. *)
Ltac gen_core_presup H :=
  match type of H with
  | ?Θ ⍮ ?Ξ ⍮ ?Γ ⊢ ?M : ?A =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof presup_exp H as [HΓ HAi];
      match goal with
      | _: __mark__ _ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@_ |- _ => clear HAi
      | _: __mark__ _ Θ ⍮ Ξ ⍮ Γ ⊢ A : Propₘ |- _ => clear HAi
      | _: __mark__ _ Θ ⍮ Ξ ⍮ Γ ⊢ A : ?S, _: type_sort ?S |- _ => clear HAi
      | _ => add_type Θ Ξ Γ M A H HAi
      end
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | ?Γ ∋ #?x : ?A =>
      match goal with
      | _: _ ⍮ _ ⍮ Γ ⊢ A : Typeω@_ |- _ => fail
      | _: _ ⍮ _ ⍮ __mark__ _ Γ ⊢ A : Typeω@_ |- _ => fail
      | _: _ ⍮ _ ⍮ Γ ⊢ A : Propₘ |- _ => fail
      | _: _ ⍮ _ ⍮ __mark__ _ Γ ⊢ A : Propₘ |- _ => fail
      | _: _ ⍮ _ ⍮ Γ ⊢ A : ?S, _: type_sort ?S |- _ => fail
      | _: _ ⍮ _ ⍮ __mark__ _ Γ ⊢ A : ?S, _: type_sort ?S |- _ => fail
      | _ =>
          let S := fresh "S" in
          let HS := fresh "HS" in
          let HA := fresh "HA" in
          pose proof (ctx_lookup_wf_sorted _ _ _ _ _ ltac:(eassumption) H) as (S & HS & HA)
      end
  | ?Γ ∋ #?x ≔ ?M : ?A =>
      match goal with
      | _: _ ⍮ _ ⍮ Γ ⊢ M : A |- _ => fail
      | _: _ ⍮ _ ⍮ __mark__ _ Γ ⊢ M : A |- _ => fail
      | _ =>
          let HM := fresh "HM" in
          pose proof (ctx_lookup_def_wf _ _ _ _ _ _ ltac:(eassumption) H) as HM
      end
  end.

Ltac gen_core_presups :=
  (on_all_hyp: fun H => gen_core_presup H);
  invert_wf_ctx;
  (on_all_hyp: fun H => gen_lookup_presup H);
  saturate_wk;
  saturate_sub;
  clear_dups.
