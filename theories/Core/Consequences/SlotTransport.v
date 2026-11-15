(** * Moving a Judgment to Equal Module Slots

    A judgment in a context with a module slot [▹ₘ U] holds with the slot
    holding an equal unit [U'] instead: [Γ ⊢ᵘ U ≈ U' → Γ ▹ₘ U ⊢ M : T →
    Γ ▹ₘ U' ⊢ M : T] ([slot_conv_exp]), and likewise for a definition with
    a module part [▸ₘ A ≔ M ‖ U].

    The judgment is read through a substitution [inline_sub Δ] that sends
    every module slot of the telescope [Δ] above a common tail to the
    literal of its own unit, moved along: a well-typed substitution into
    [Δ ++ Γ] from any [Δ2 ++ Γ] whose entries are those of [Δ] up to
    equality with their images ([tele_rel]).  With the identity it forms a
    related pair of substitutions ([sub_pair], [sub_pair_inline]): the two
    send every entry to equal things, only the right one well typed.
    Every judgment holds between the two images of a related pair
    ([pair_transport_all]), by induction on the judgment: a slot is equal
    to its unit's literal by its δ ([wf_me_delta_slot]), what equal module
    expressions look up is compared along paths ([modexp_conv_all]), and
    binders, instances and reducts extend the pair.  At the pair
    [(Id, inline_sub Δ)] this gives the finish line
    ([slot_transport_exp]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Inversions ModexpConversion.
From Mctt.Core.Syntactic Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Structural SlotConversion.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping Presup Paths LookupSound NoLevelReflect.
From Mctt.Core.Syntactic.System.Records Require Typing.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Substitution *)

(** [slot_image d σ]: what the substitution sends the newest variable to,
    for the entry [d] read under [σ]: a module slot to the literal of its
    unit, a definition with a module part to itself with that literal as
    its module part, any other entry to itself. *)
Definition slot_image (d : centry) (σ : sub) : sentry :=
  match d with
  | ce_mod V => se_mod (me_lit V[sb_wk σ wk_shift]ᵘ)
  | ce_dm A M V => se_dm (a_var 0) (me_lit V[sb_wk σ wk_shift]ᵘ)
  | _ => se_var 0
  end.

(** [inline_sub Δ]: the substitution from [Δ2 ++ Γ] to [Δ ++ Γ] sending
    each module slot of [Δ] to the literal of its unit, moved along, and
    every other variable to itself. *)
Fixpoint inline_sub (Δ : ctx) : sub :=
  match Δ with
  | nil => Id
  | d :: Δ' => sb_extend (sb_wk (inline_sub Δ') wk_shift) (slot_image d (inline_sub Δ'))
  end.

(** [tele_rel Θ Ξ Γ Δ Δ2]: the telescope [Δ2] over [Γ] is [Δ] entry by
    entry, each part of [Δ2] equal to the image of the part of [Δ] along
    [inline_sub], read in [Δ2]; each part of [Δ] is equal to its image
    there too.  An entry is compared under the entries before it. *)
Inductive tele_rel (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : ctx -> ctx -> Prop :=
(** The empty telescopes *)
| tele_rel_nil : tele_rel Θ Ξ Γ nil nil
(** Assumptions of one kind, of equal types *)
| tele_rel_ass : forall Δ Δ2 κ A A2 Srt,
    tele_rel Θ Ξ Γ Δ Δ2 ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ A2 ≈ A[inline_sub Δ] : Srt ->
    type_sort Srt ->
    tele_rel Θ Ξ Γ (ce_ass κ A :: Δ) (ce_ass κ A2 :: Δ2)
(** Definitions of equal types and bodies *)
| tele_rel_def : forall Δ Δ2 A A2 M M2 Srt,
    tele_rel Θ Ξ Γ Δ Δ2 ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ A2 ≈ A[inline_sub Δ] : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ M2 ≈ M[inline_sub Δ] : A[inline_sub Δ] ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ M ≈ M[inline_sub Δ] : A[inline_sub Δ] ->
    tele_rel Θ Ξ Γ (ce_def A M :: Δ) (ce_def A2 M2 :: Δ2)
(** Module slots of equal units *)
| tele_rel_mod : forall Δ Δ2 V V2,
    tele_rel Θ Ξ Γ Δ Δ2 ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ᵘ V2 ≈ V[inline_sub Δ]ᵘ ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ᵘ V ≈ V[inline_sub Δ]ᵘ ->
    tele_rel Θ Ξ Γ (ce_mod V :: Δ) (ce_mod V2 :: Δ2)
(** Definitions with a module part of equal types, bodies and units, the
    units aliases under no parameters *)
| tele_rel_dm : forall Δ Δ2 A A2 M M2 E E2 i,
    tele_rel Θ Ξ Γ Δ Δ2 ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ A2 ≈ A[inline_sub Δ] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ M2 ≈ M[inline_sub Δ] : A[inline_sub Δ] ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ M ≈ M[inline_sub Δ] : A[inline_sub Δ] ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ᵘ gu_mk nil (md_alias E2) ≈ (gu_mk nil (md_alias E))[inline_sub Δ]ᵘ ->
    Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ (gu_mk nil (md_alias E))[inline_sub Δ]ᵘ ->
    tele_rel Θ Ξ Γ (ce_dm A M (gu_mk nil (md_alias E)) :: Δ) (ce_dm A2 M2 (gu_mk nil (md_alias E2)) :: Δ2).

#[export]
Hint Constructors tele_rel : mctt.

(** ** Conversions *)

(** A term of a type equal to its image, at the image. *)
Lemma tr_conv : forall Θ Ξ Γ M A A' Srt, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt -> type_sort Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof. intros * HM HA HS; eapply wf_conv_sort; [ exact HM | exact (presup_exp_eq_right HA) | exact HS | exact HA ]. Qed.

(** The same back. *)
Lemma tr_conv_back : forall Θ Ξ Γ M A A' Srt, Θ ⍮ Ξ ⍮ Γ ⊢ M : A' -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt -> type_sort Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof. intros * HM HA HS; eapply wf_conv_sort; [ exact HM | exact (presup_exp_eq_left HA) | exact HS | apply wf_exp_eq_sym; exact HA ]. Qed.

(** A term of a type, read off an equation whose type is the image of a
    type equal to its image. *)
Lemma tr_left : forall Θ Ξ Γ M M' A A' Srt, Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A' -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Srt -> type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof. intros * HM HA HS; eapply tr_conv_back; [ exact (presup_exp_eq_left HM) | exact HA | exact HS ]. Qed.

(** ** Related Pairs of Substitutions

    [sub_pair Θ Ξ Γ' Γ τ1 τ2]: two substitutions from [Γ] into [Γ'] that
    send every entry of [Γ] to equal things, the right one well typed and
    the left one not necessarily.  The transport is stated over such
    pairs ([pair_transport_all]): every judgment of [Γ] holds between its
    two images, the left image at the right image's type.  Its instance
    [(Id, inline_sub Δ)] from [Δ2 ++ Γ] ([sub_pair_inline]) gives the
    finish line; the others are what binders, instances and reducts need,
    so that a reduct such as a [β]- or [ι]-reduct is related through the
    hypothesis of its body at an extended pair, with no detour.

    It is [wf_sub_eq] with three differences, each for a reason:
    - no typing of the left substitution: a module slot of [Γ] may be kept
      as a slot by [τ1] while [τ2] sends it to the literal of its unit
      ([sub_pair_mod_inline]); the kept slot holds a unit only equal to
      [Γ]'s, and a well-typed substitution sends a slot to exactly its
      unit, moved, or to a slot holding exactly that ([wf_sub_apply_mod]),
      so [τ1] is no substitution into [Γ];
    - the assumptions' images are equal at the right-hand image of their
      types, [A[τ2]], not [A[τ1]]: only [τ2] is well typed, so only
      [A[τ2]] is known to be a type of [Γ'];
    - a field for definitions ([sub_pair_apply_def]): for [wf_sub_eq] it
      follows from both sides being well typed, here the left side is not,
      and the case of [δ] for a defined variable needs the left image of
      the variable equal to the right image of the body, which comes from
      the context, not from a subterm, so has no induction hypothesis;
    - a field for the units of module slots ([sub_pair_apply_unit]): the
      slot's δ ([wf_me_delta_slot]) relates the slot to the literal of
      its unit, which comes from the context, and the left image of that
      literal is related only through this field; for [wf_sub_eq] it is
      the substitution equality's action on the slot's unit. *)
Record sub_pair (Θ : gdeps) (Ξ : gstack) (Γ' Γ : ctx) (τ1 τ2 : sub) : Prop := mk_sub_pair
  { (** The right-hand substitution is well typed; the left one need not be *)
    sub_pair_right : Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ
    (** An assumption is sent to equal terms, at the right-hand image of
        its type *)
  ; sub_pair_apply : forall x A, Γ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ' ⊢ #x[τ1] ≈ #x[τ2] : A[τ2]
    (** A definition is sent, on the left, to something equal to the
        right-hand image of its body: [δ] for a defined variable holds of
        the pair *)
  ; sub_pair_apply_def : forall x A M, Γ ∋ #x ≔ M : A -> Θ ⍮ Ξ ⍮ Γ' ⊢ #x[τ1] ≈ M[τ2] : A[τ2]
    (** A module slot is sent to equal module expressions *)
  ; sub_pair_apply_mod : forall x U, Γ ∋ #x ≔ₘ U ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ sentry_modexp (τ1 x) ≈ sentry_modexp (τ2 x)
    (** A module slot's unit is equal to itself across the pair *)
  ; sub_pair_apply_unit : forall x U, Γ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ U[τ1]ᵘ ≈ U[τ2]ᵘ }.

(** An equation of substitutions is a pair: both sides are well typed and
    agree. *)
Lemma sub_pair_of_eq : forall Θ Ξ Γ' Γ τ1 τ2, Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ1 ≈ τ2 : Γ -> sub_pair Θ Ξ Γ' Γ τ1 τ2.
Proof.
  intros * Hτ.
  pose proof (wf_sub_eq_left _ _ _ _ _ _ Hτ) as Hl1; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hτ) as Hl2.
  pose proof (wf_sub_cod _ _ _ _ _ Hl1) as HΓ.
  (** Every binding's type is of a sort, so its two images are equal there
      and a reading at the left image converts to the right *)
  assert (Hconv : forall x A, Γ ∋ #x : A -> forall M N, Θ ⍮ Ξ ⍮ Γ' ⊢ M ≈ N : A[τ1] -> Θ ⍮ Ξ ⍮ Γ' ⊢ M ≈ N : A[τ2]).
  { intros x A Hx M N HMN.
    destruct (ctx_lookup_wf_sorted _ _ _ _ _ HΓ Hx) as (Srt & HS & HA).
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HA _ _ _ Hτ) as HAA; rewrite (type_sort_sub _ _ HS) in HAA.
    eapply wf_exp_eq_conv_sort; [ exact HMN | exact (presup_exp_eq_right HAA) | exact HS | exact HAA ]. }
  constructor.
  - exact Hl2.
  - intros x A Hx; exact (Hconv _ _ Hx _ _ (wf_sub_eq_apply _ _ _ _ _ _ Hτ _ _ Hx)).
  - intros x A M Hx.
    pose proof (ctx_lookup_def_lookup _ _ _ _ Hx) as Hxp.
    eapply wf_exp_eq_trans;
      [ exact (Hconv _ _ Hxp _ _ (wf_sub_eq_apply _ _ _ _ _ _ Hτ _ _ Hxp))
      | exact (wf_sub_apply_def _ _ _ _ _ Hl2 _ _ _ Hx) ].
  - intros x U Hx; exact (wf_sub_eq_apply_mod _ _ _ _ _ _ Hτ _ _ Hx).
  - intros x U Hx; exact (sub_eq_preserves_unit _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hx) _ _ _ Hτ).
Qed.

(** A well-typed substitution is a pair with itself. *)
Corollary sub_pair_refl : forall Θ Ξ Γ' Γ τ, Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ : Γ -> sub_pair Θ Ξ Γ' Γ τ τ.
Proof. intros * Hτ; apply sub_pair_of_eq, wf_sub_eq_refl; exact Hτ. Qed.

(** Over one assumption more the pair is lifted, the moved-to context
    extended by the right-hand image of the type: the binder is sent to
    itself on both sides, and the rest by weakening. *)
Lemma sub_pair_q : forall Θ Ξ Γ' Γ τ1 τ2 κ A Srt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    sub_pair Θ Ξ (Γ' ▹{κ} A[τ2]) (Γ ▹{κ} A) (q τ1) (q τ2).
Proof.
  intros * [Hr Ha Hd Hm Hu] HA HS.
  pose proof (sort_kind_type_sort _ _ HS) as HSt.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA HSt Hr) as HAτ.
  assert (HΓ2 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▹{κ} A[τ2]) by (eapply wf_ctx_extend; [ exact HAτ | exact HS ]).
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  constructor.
  - eapply wf_sub_q; [ exact Hr | exact HA | exact HS | exact HAτ ].
  - intros x B Hx; inversion Hx; subst; reduce_index; rewrite exp_wk_shift_sub_q.
    + apply wf_exp_eq_refl; eapply wf_vlookup; [ exact HΓ2 | constructor ].
    + rewrite <- !sentry_exp_wk; fold (exp_sub (a_var n) τ1); fold (exp_sub (a_var n) τ2).
      exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (Ha _ _ ltac:(eassumption)) Hφ).
  - intros x B M Hx; inversion Hx; subst; reduce_index; rewrite !exp_wk_shift_sub_q.
    rewrite <- sentry_exp_wk; fold (exp_sub (a_var n) τ1).
    exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (Hd _ _ _ ltac:(eassumption)) Hφ).
  - intros x U Hx; inversion Hx; subst; cbn [sb_q].
    rewrite !sb_q_succ, !sentry_modexp_wk.
    exact (wk_preserves_modexp _ _ _ _ _ _ _ (Hm _ _ ltac:(eassumption)) Hφ).
  - intros x U Hx; inversion Hx; subst; rewrite !gunit_wk_shift_sub_q.
    exact (wk_preserves_unit _ _ _ _ _ _ _ (Hu _ _ ltac:(eassumption)) Hφ).
Qed.

(** One assumption more, sent on the two sides to terms equal at the
    right-hand image of its type: what an instance, a [β]-reduct or a
    [ζ]-reduct needs. *)
Lemma sub_pair_extend : forall Θ Ξ Γ' Γ τ1 τ2 κ A Srt N1 N2,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ N1 ≈ N2 : A[τ2] ->
    sub_pair Θ Ξ Γ' (Γ ▹{κ} A) (τ1,,N1) (τ2,,N2).
Proof.
  intros * [Hr Ha Hd Hm Hu] HA HS HN.
  constructor.
  - eapply wf_sub_extend; [ exact Hr | exact HA | exact HS | exact (presup_exp_eq_right HN) ].
  - intros x B Hx; inversion Hx; subst; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + exact HN.
    + exact (Ha _ _ ltac:(eassumption)).
  - intros x B M Hx; inversion Hx; subst; rewrite !exp_sub_shift_extend; exact (Hd _ _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; exact (Hm _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; rewrite !gunit_sub_shift_extend; exact (Hu _ _ ltac:(eassumption)).
Qed.

(** One module slot more, kept on the left and inlined on the right: the
    left side sends it to a slot [y] of the moved-to context, holding a
    unit [V] only equal to the moved unit, the right side to the literal
    of the moved unit.  This is the clause the transport is for, and the
    only one where the two sides send an entry to expressions of
    different shapes: the slot is its unit's literal by its δ
    ([wf_me_delta_slot]), and that literal the moved unit's by [V]'s
    equation. *)
Lemma sub_pair_mod_inline : forall Θ Ξ Γ' Γ τ1 τ2 U V y,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ V ≈ U[τ2]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ U[τ1]ᵘ ≈ U[τ2]ᵘ ->
    Γ' ∋ #y ≔ₘ V ->
    sub_pair Θ Ξ Γ' (Γ ▹ₘ U) (sb_extend τ1 (se_var y)) (τ2 ,,ₘ me_lit U[τ2]ᵘ).
Proof.
  intros * [Hr Ha Hd Hm Hu] HU HVU HUU Hy.
  pose proof (wf_sub_dom _ _ _ _ _ Hr) as HΓ'.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HVU) HVU) as HUτ.
  constructor.
  - apply wf_sub_extend_mod; [ exact Hr | exact HU | exact HUτ ].
  - intros x B Hx; inversion Hx; subst; cbn [sb_extend].
    rewrite !exp_sub_shift_extend; exact (Ha _ _ ltac:(eassumption)).
  - intros x B M Hx; inversion Hx; subst; cbn [sb_extend].
    rewrite !exp_sub_shift_extend; exact (Hd _ _ _ ltac:(eassumption)).
  - intros x W Hx; inversion Hx; subst; cbn [sb_extend].
    + (** the new slot: the kept slot on the left, the literal on the right *)
      eapply wf_me_trans; [ eapply wf_me_delta_slot; [ exact HΓ' | exact Hy ] | apply wf_me_lit; exact HVU ].
    + exact (Hm _ _ ltac:(eassumption)).
  - intros x W Hx; inversion Hx; subst; rewrite !gunit_sub_shift_extend.
    + exact HUU.
    + exact (Hu _ _ ltac:(eassumption)).
Qed.

(** A pair moved along a weakening of the moved-to context. *)
Lemma sub_pair_wk : forall Θ Ξ Γ' Γ'' Γ τ1 τ2 φ,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ʷ φ : Γ' ->
    sub_pair Θ Ξ Γ'' Γ (sb_wk τ1 φ) (sb_wk τ2 φ).
Proof.
  intros * [Hr Ha Hd Hm Hu] Hφ.
  constructor.
  - exact (wf_sub_wk _ _ _ _ _ _ _ Hr Hφ).
  - intros x A Hx; rewrite <- !exp_wk_sub; exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (Ha _ _ Hx) Hφ).
  - intros x A M Hx; rewrite <- !exp_wk_sub; exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ (Hd _ _ _ Hx) Hφ).
  - intros x U Hx; unfold sb_wk; rewrite !sentry_modexp_wk.
    exact (wk_preserves_modexp _ _ _ _ _ _ _ (Hm _ _ Hx) Hφ).
  - intros x U Hx; rewrite <- !gunit_wk_sub; exact (wk_preserves_unit _ _ _ _ _ _ _ (Hu _ _ Hx) Hφ).
Qed.

(** Pointwise equal substitutions are related as the originals. *)
Lemma sub_pair_sb_eq : forall Θ Ξ Γ' Γ τ1 τ2 τ1' τ2',
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> sb_eq τ1 τ1' -> sb_eq τ2 τ2' -> sub_pair Θ Ξ Γ' Γ τ1' τ2'.
Proof.
  intros * [Hr Ha Hd Hm Hu] E1 E2.
  constructor.
  - rewrite <- E2; exact Hr.
  - intros x A Hx; rewrite <- E1, <- E2; exact (Ha _ _ Hx).
  - intros x A M Hx; rewrite <- E1, <- E2; exact (Hd _ _ _ Hx).
  - intros x U Hx; rewrite <- (E1 x), <- (E2 x); exact (Hm _ _ Hx).
  - intros x U Hx; rewrite <- E1, <- E2; exact (Hu _ _ Hx).
Qed.

(** Over one assumption more whose moved-to type is only equal to the
    right-hand image: the binder is sent to itself on both sides. *)
Lemma sub_pair_q_conv : forall Θ Ξ Γ' Γ τ1 τ2 κ A A2 Srt Srt',
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    ⊢ Θ ⍮ Ξ ⍮ Γ' ▹{κ} A2 -> type_sort Srt' -> Θ ⍮ Ξ ⍮ Γ' ⊢ A2 ≈ A[τ2] : Srt' ->
    sub_pair Θ Ξ (Γ' ▹{κ} A2) (Γ ▹{κ} A) (q τ1) (q τ2).
Proof.
  intros * Hp HA HS HΓ2 HSt HAA.
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  destruct (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) as [Hr Ha Hd Hm Hu].
  (** the binder: itself, at the moved image of the type, by the equation *)
  pose proof (wk_preserves_sort_eq _ _ _ _ _ _ _ _ HAA HSt Hφ) as HAAw.
  rewrite exp_wk_sub in HAAw.
  assert (Hv : Θ ⍮ Ξ ⍮ Γ' ▹{κ} A2 ⊢ #0 : A[sb_wk τ2 ↑]).
  { eapply wf_conv_sort; [ eapply wf_vlookup; [ exact HΓ2 | constructor ] | exact (presup_exp_eq_right HAAw) | exact HSt | exact HAAw ]. }
  constructor.
  - unfold sb_q; apply wf_sub_extend_gen; [ exact Hr | eapply wf_ctx_extend; [ exact HA | exact HS ] | | | ];
      intros * Hlk; inversion Hlk; subst; cbn [sentry_exp sentry_modexp].
    rewrite exp_sub_shift_extend; exact Hv.
  - intros x B Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + apply wf_exp_eq_refl; exact Hv.
    + exact (Ha _ _ ltac:(eassumption)).
  - intros x B M Hx; inversion Hx; subst; unfold sb_q; rewrite !exp_sub_shift_extend; exact (Hd _ _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; exact (Hm _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; rewrite !gunit_sub_shift_extend; exact (Hu _ _ ltac:(eassumption)).
Qed.

(** The newest variable of a definition whose type and body are equal to
    the images [A[τ]], [M[τ]] moved past it: of the moved type, and equal
    to the moved body by its δ. *)
Lemma var0_def_image : forall Θ Ξ Γ' e τ A A2 M M2 Srt,
    ⊢ Θ ⍮ Ξ ⍮ e :: Γ' -> e :: Γ' ∋ #0 ≔ M2[↑]ʷ : A2[↑]ʷ -> type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ A2 ≈ A[τ] : Srt -> Θ ⍮ Ξ ⍮ Γ' ⊢ M2 ≈ M[τ] : A[τ] ->
    Θ ⍮ Ξ ⍮ e :: Γ' ⊢ #0 : A[sb_wk τ ↑] /\
    Θ ⍮ Ξ ⍮ e :: Γ' ⊢ #0 ≈ M[sb_wk τ ↑] : A[sb_wk τ ↑].
Proof.
  intros * HΓ2 Hl HSt HAA HMM.
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  pose proof (wk_preserves_sort_eq _ _ _ _ _ _ _ _ HAA HSt Hφ) as HAAw; rewrite exp_wk_sub in HAAw.
  pose proof (wk_preserves_exp_eq _ _ _ _ _ _ _ _ HMM Hφ) as HMMw; rewrite !exp_wk_sub in HMMw.
  assert (Hv : Θ ⍮ Ξ ⍮ e :: Γ' ⊢ #0 : A[sb_wk τ ↑]).
  { eapply wf_conv_sort; [ eapply wf_vlookup; [ exact HΓ2 | exact (ctx_lookup_def_lookup _ _ _ _ Hl) ]
                         | exact (presup_exp_eq_right HAAw) | exact HSt | exact HAAw ]. }
  split; [ exact Hv |].
  eapply wf_exp_eq_trans; [| exact HMMw ].
  eapply wf_exp_eq_conv_sort; [ eapply wf_exp_eq_var_delta; [ exact HΓ2 | exact Hl ]
                              | exact (presup_exp_eq_right HAAw) | exact HSt | exact HAAw ].
Qed.

(** Over one definition more whose moved-to type and body are only equal
    to the right-hand images: the binder is sent to itself on both sides,
    and on the left it is equal to the moved body by its δ. *)
Lemma sub_pair_q_def_conv : forall Θ Ξ Γ' Γ τ1 τ2 A A2 M M2 Srt Srt',
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> type_sort Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    type_sort Srt' -> Θ ⍮ Ξ ⍮ Γ' ⊢ A2 ≈ A[τ2] : Srt' -> Θ ⍮ Ξ ⍮ Γ' ⊢ M2 ≈ M[τ2] : A[τ2] ->
    sub_pair Θ Ξ (Γ' ▸ A2 ≔ M2) (Γ ▸ A ≔ M) (q τ1) (q τ2).
Proof.
  intros * Hp HA HS HM HS' HAA HMM.
  assert (HΓ2 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▸ A2 ≔ M2)
    by (eapply wf_ctx_extend_def; [ exact (presup_exp_eq_left HAA) | exact HS'
                                  | exact (tr_left _ _ _ _ _ _ _ _ HMM HAA HS') ]).
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  destruct (var0_def_image _ _ _ _ _ _ _ _ _ _ HΓ2 ltac:(constructor) HS' HAA HMM) as [Hv Hδ].
  destruct (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) as [Hr Ha Hd Hm Hu].
  constructor.
  - unfold sb_q; apply wf_sub_extend_gen; [ exact Hr | eapply wf_ctx_extend_def; [ exact HA | exact HS | exact HM ] | | | ];
      intros * Hlk; inversion Hlk; subst; cbn [sentry_exp sentry_modexp]; rewrite ?exp_sub_shift_extend.
    + exact Hv.
    + exact Hδ.
  - intros x B Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + apply wf_exp_eq_refl; exact Hv.
    + exact (Ha _ _ ltac:(eassumption)).
  - intros x B N Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + exact Hδ.
    + exact (Hd _ _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; exact (Hm _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; rewrite !gunit_sub_shift_extend; exact (Hu _ _ ltac:(eassumption)).
Qed.

(** One definition with a module part more, its term part kept on both
    sides and its module part kept on the left and inlined on the right:
    the definition clause and the slot clause at once.  The moved-to
    entry's type, body and unit are only equal to the right-hand images. *)
Lemma sub_pair_dm_inline : forall Θ Ξ Γ' Γ τ1 τ2 A A2 M M2 V V2 i i',
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ V -> ⊢ Θ ⍮ Ξ ⍮ Γ' ▸ₘ A2 ≔ M2 ‖ V2 ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ A2 ≈ A[τ2] : Typeω@i' -> Θ ⍮ Ξ ⍮ Γ' ⊢ M2 ≈ M[τ2] : A[τ2] ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ V2 ≈ V[τ2]ᵘ -> Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ V[τ1]ᵘ ≈ V[τ2]ᵘ -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    sub_pair Θ Ξ (Γ' ▸ₘ A2 ≔ M2 ‖ V2) (Γ ▸ₘ A ≔ M ‖ V)
      (q τ1) (sb_extend (sb_wk τ2 ↑) (se_dm (a_var 0) (me_lit V[sb_wk τ2 ↑]ᵘ))).
Proof.
  intros * Hp HΓ1 HΓ2 HAA HMM HVV HVV1 HA.
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  destruct (var0_def_image _ _ _ _ _ _ _ _ _ _ HΓ2 ltac:(constructor) ltac:(constructor) HAA HMM) as [Hv Hδ].
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HVV Hφ) as HVVw; rewrite gunit_wk_sub in HVVw.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HVVw) HVVw) as HVw.
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HVV1 Hφ) as HVV1w; rewrite !gunit_wk_sub in HVV1w.
  destruct (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) as [Hr Ha Hd Hm Hu].
  constructor.
  - apply wf_sub_extend_gen; [ exact Hr | exact HΓ1 | | | ];
      intros * Hlk; inversion Hlk; subst; cbn [sentry_exp sentry_modexp]; rewrite ?exp_sub_shift_extend.
    + exact Hv.
    + exact Hδ.
    + left; rewrite gunit_sub_shift_extend; split; [ reflexivity | exact HVw ].
  - intros x B Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + apply wf_exp_eq_refl; exact Hv.
    + exact (Ha _ _ ltac:(eassumption)).
  - intros x B N Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + exact Hδ.
    + exact (Hd _ _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; cbn [sb_extend sentry_modexp].
    + (** the module part: the kept slot on the left, the literal on the right *)
      eapply wf_me_trans; [ eapply wf_me_delta_slot; [ exact HΓ2 | constructor ] | apply wf_me_lit; exact HVVw ].
    + exact (Hm _ _ ltac:(eassumption)).
  - intros x U Hx; inversion Hx; subst; unfold sb_q; rewrite !gunit_sub_shift_extend.
    + exact HVV1w.
    + exact (Hu _ _ ltac:(eassumption)).
Qed.

(** Over one definition more, the moved-to context extended by the
    right-hand images: the binder is sent to itself on both sides. *)
Corollary sub_pair_q_def : forall Θ Ξ Γ' Γ τ1 τ2 A M Srt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> type_sort Srt -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    sub_pair Θ Ξ (Γ' ▸ A[τ2] ≔ M[τ2]) (Γ ▸ A ≔ M) (q τ1) (q τ2).
Proof.
  intros * Hp HA HS HM.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA HS Hr) as HAτ.
  eapply sub_pair_q_def_conv; [ exact Hp | exact HA | exact HS | exact HM | exact HS
                              | apply wf_exp_eq_refl; exact HAτ
                              | apply wf_exp_eq_refl; exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hr) ].
Qed.

(** Over one module slot more, the moved-to context extended by the
    right-hand image of the unit: the slot is sent to itself on both
    sides, a slot holding exactly the moved unit. *)
Lemma sub_pair_q_mod : forall Θ Ξ Γ' Γ τ1 τ2 U,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U -> Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ U[τ1]ᵘ ≈ U[τ2]ᵘ ->
    sub_pair Θ Ξ (Γ' ▹ₘ U[τ2]ᵘ) (Γ ▹ₘ U) (q τ1) (q τ2).
Proof.
  intros * Hp HU HUU.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  pose proof (sub_preserves_unit _ _ _ _ _ _ _ HU Hr) as HUτ.
  assert (HΓ2 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▹ₘ U[τ2]ᵘ) by (apply wf_ctx_extend_mod; exact HUτ).
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HUU Hφ) as HUUw.
  destruct (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) as [Hw Ha Hd Hm Hu].
  constructor.
  - exact (wf_sub_q_gen _ _ _ _ _ (ce_mod U) Hr HΓ2 (wf_ctx_extend_mod _ _ _ _ HU)).
  - intros x B Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    exact (Ha _ _ ltac:(eassumption)).
  - intros x B N Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    exact (Hd _ _ _ ltac:(eassumption)).
  - intros x V Hx; inversion Hx; subst; unfold sb_q; cbn [sb_extend sentry_modexp].
    + eapply wf_me_var; [ exact HΓ2 | constructor ].
    + exact (Hm _ _ ltac:(eassumption)).
  - intros x V Hx; inversion Hx; subst; unfold sb_q; rewrite !gunit_sub_shift_extend.
    + rewrite !gunit_wk_sub in HUUw; exact HUUw.
    + exact (Hu _ _ ltac:(eassumption)).
Qed.

(** Over one definition with a module part more, the moved-to context
    extended by the right-hand images: the entry is sent to itself on both
    sides, its term part equal to the moved body by its δ, its module part
    a slot holding exactly the moved unit. *)
Lemma sub_pair_q_dm : forall Θ Ξ Γ' Γ τ1 τ2 A M V i,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ V -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ V[τ1]ᵘ ≈ V[τ2]ᵘ ->
    ⊢ Θ ⍮ Ξ ⍮ Γ' ▸ₘ A[τ2] ≔ M[τ2] ‖ V[τ2]ᵘ ->
    sub_pair Θ Ξ (Γ' ▸ₘ A[τ2] ≔ M[τ2] ‖ V[τ2]ᵘ) (Γ ▸ₘ A ≔ M ‖ V) (q τ1) (q τ2).
Proof.
  intros * Hp HΓ1 HA HVV HΓ2.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  pose proof (wf_wk_shift _ _ _ _ HΓ2) as Hφ.
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HVV Hφ) as HVVw; rewrite !gunit_wk_sub in HVVw.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA ltac:(constructor) Hr) as HAτ.
  destruct (proj2 (proj2 (ctx_decomp_dm HΓ1))) as [HM _].
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hr) as HMτ.
  destruct (var0_def_image _ _ _ _ τ2 A A[τ2] M M[τ2] _ HΓ2 ltac:(constructor) ltac:(constructor)
              (wf_exp_eq_refl HAτ) (wf_exp_eq_refl HMτ)) as [Hv Hδ].
  destruct (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) as [Hw Ha Hd Hm Hu].
  constructor.
  - exact (wf_sub_q_gen _ _ _ _ _ (ce_dm A M V) Hr HΓ2 HΓ1).
  - intros x B Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + apply wf_exp_eq_refl; exact Hv.
    + exact (Ha _ _ ltac:(eassumption)).
  - intros x B N Hx; inversion Hx; subst; unfold sb_q; cbn [exp_sub sb_extend sentry_exp]; rewrite !exp_sub_shift_extend.
    + exact Hδ.
    + exact (Hd _ _ _ ltac:(eassumption)).
  - intros x W Hx; inversion Hx; subst; unfold sb_q; cbn [sb_extend sentry_modexp].
    + eapply wf_me_var; [ exact HΓ2 | constructor ].
    + exact (Hm _ _ ltac:(eassumption)).
  - intros x W Hx; inversion Hx; subst; unfold sb_q; rewrite !gunit_sub_shift_extend.
    + exact HVVw.
    + exact (Hu _ _ ltac:(eassumption)).
Qed.

(** ** The Finish Line's Pair

    The identity and the inlining substitution are related, from [Δ2 ++ Γ]
    to [Δ ++ Γ], when [Δ2] is [Δ] up to equality with images
    ([tele_rel]): over each entry the pair is lifted, a module slot kept
    on the left and inlined on the right.  The left side is [q] applied
    once per entry to the identity, pointwise the identity. *)
Lemma sub_pair_inline_q : forall Θ Ξ Γ Δ Δ2, tele_rel Θ Ξ Γ Δ Δ2 ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ2 ++ Γ ->
    sub_pair Θ Ξ (Δ2 ++ Γ) (Δ ++ Γ) (sb_qn (length Δ) Id) (inline_sub Δ).
Proof.
  intros *; induction 1 as [| Δ Δ2 κ A A2 Srt HR IH HA HS | Δ Δ2 A A2 M M2 Srt HR IH HA HS HM HM' | Δ Δ2 V V2 HR IH HV HV'
                           | Δ Δ2 A A2 M M2 E E2 i HR IH HA HM HM' HE HE'];
    intros H1 H2; cbn [inline_sub List.app length sb_qn] in *.
  - exact (sub_pair_refl _ _ _ _ _ (wf_sub_id _ _ _ H2)).
  - pose proof (IH (ctx_decomp_tail H1) (ctx_decomp_tail H2)) as Hp.
    destruct (ctx_decomp_sort_kind H1) as [_ (S0 & HS0 & HA0)].
    eapply sub_pair_q_conv; [ exact Hp | exact HA0 | exact HS0 | exact H2 | exact HS | exact HA ].
  - pose proof (IH (ctx_decomp_tail H1) (ctx_decomp_tail H2)) as Hp.
    destruct (ctx_decomp_def_sorted H1) as (S0 & HS0 & HA0).
    eapply sub_pair_q_def_conv; [ exact Hp | exact HA0 | exact HS0 | exact (ctx_decomp_def_body H1) | exact HS | exact HA | exact HM ].
  - pose proof (IH (ctx_decomp_tail H1) (ctx_decomp_tail H2)) as Hp.
    pose proof (wf_wk_shift _ _ _ _ H2) as Hφ.
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HV Hφ) as HVw; rewrite gunit_wk_sub in HVw.
    (** the unit across the pair: the left side is the identity, pointwise,
        so this is the relation's own reflexivity clause, weakened *)
    assert (HVV : Θ ⍮ Ξ ⍮ (Δ2 ++ Γ) ▹ₘ V2 ⊢ᵘ V[sb_wk (sb_qn (length Δ) Id) ↑]ᵘ ≈ V[sb_wk (inline_sub Δ) ↑]ᵘ).
    { rewrite <- !gunit_wk_sub, (sb_qn_id_ext _ Id ltac:(reflexivity)), gunit_sub_id.
      exact (wk_preserves_unit _ _ _ _ _ _ _ HV' Hφ). }
    eapply sub_pair_mod_inline;
      [ exact (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) | exact (ctx_decomp_mod_unit H1) | exact HVw | exact HVV | constructor ].
  - pose proof (IH (ctx_decomp_tail H1) (ctx_decomp_tail H2)) as Hp.
    destruct (ctx_decomp_dm H1) as (_ & [i0 HA0] & _).
    assert (HEE : Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ᵘ (gu_mk nil (md_alias E))[sb_qn (length Δ) Id]ᵘ ≈ (gu_mk nil (md_alias E))[inline_sub Δ]ᵘ)
      by (rewrite (sb_qn_id_ext _ Id ltac:(reflexivity)), gunit_sub_id; exact HE').
    eapply sub_pair_dm_inline; [ exact Hp | exact H1 | exact H2 | exact HA | exact HM | exact HE | exact HEE | exact HA0 ].
Qed.

(** The finish line's pair: the identity and the inlining substitution. *)
Corollary sub_pair_inline : forall Θ Ξ Γ Δ Δ2, tele_rel Θ Ξ Γ Δ Δ2 ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ2 ++ Γ ->
    sub_pair Θ Ξ (Δ2 ++ Γ) (Δ ++ Γ) Id (inline_sub Δ).
Proof.
  intros * HR H1 H2.
  eapply sub_pair_sb_eq; [ exact (sub_pair_inline_q _ _ _ _ _ HR H1 H2) | apply sb_qn_id_ext; reflexivity | reflexivity ].
Qed.

(** ** What Equal Module Expressions Look Up

    Read off [modexp_conv_all] at the identity: along every path, the two
    sides denote together, and show the same ([path_leaf]). *)

(** Equal module expressions are compared along paths in their own
    context. *)
Lemma modexp_paths_conv : forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> paths_conv Θ Ξ Γ H H'.
Proof.
  intros * HH; pose proof (proj2 ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 modexp_conv_all))))))) _ _ _ _ _ HH) as Hc.
  pose proof (presup_modexp_eq_ctx HH) as HΓ.
  pose proof (proj2 Hc _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))) as Hp; rewrite !modexp_sub_id in Hp; exact Hp.
Qed.

(** Equal module expressions denote descriptions with members of types of
    levels together: their module parts are compared at the empty path
    ([leaf_nl]). *)
Lemma no_level_modexp_conv : forall Θ Ξ Γ H H' R R', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    mdenote Θ Ξ Γ H R -> mdenote Θ Ξ Γ H' R' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R.
Proof.
  intros * HH Hm Hm' Hn'.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  destruct (me_denotes _ _ _ _ _ HH) as (X0 & Xm0 & HX0 & HXm0).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX0 _ Hm) in HXm0.
  destruct (proj2 (modexp_paths_conv _ _ _ _ _ HH nil (path_pairs_nil _ _ _ _)) _ Hm') as (R0 & HR0 & Hl).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ Hm) in Hl.
  unfold path_leaf in Hl; cbn in Hl; rewrite HXm0 in Hl.
  destruct (mdesc_mod R') as [Rm' |] eqn:E'; cbn in Hl; [| contradiction ].
  apply (no_level_mod_iff _ _ _ _ _ HXm0), (proj2 (leaf_nl _ _ _ _ _ Hl)), (no_level_mod_iff _ _ _ _ _ E'); exact Hn'.
Qed.

(** A member of the right side is one of the left side, showing the same. *)
Lemma modexp_eq_mem_left : forall Θ Ξ Γ H H' x R', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    mdenote Θ Ξ Γ (me_mem H' x) R' -> exists R, mdenote Θ Ξ Γ (me_mem H x) R /\ leaf_conv Θ Ξ Γ R R'.
Proof.
  intros * HH Hm; destruct (modexp_paths_conv _ _ _ _ _ HH (ps_mem x :: nil) (path_pairs_mem _ _ _ _ _ _ (path_pairs_nil _ _ _ _)))
    as [_ H2]; exact (H2 _ Hm).
Qed.

(** ** Auxiliary Facts *)

(** A body under the image of a slot, instantiated: the slot is gone, so the
    instance is the body at the substitution extended by the slot's image. *)
Lemma inline_mod_compose : forall σ U N C,
  C[sb_extend (sb_wk σ wk_shift) (se_mod (me_lit U[sb_wk σ wk_shift]ᵘ))][Id ,,ₘ N] = C[σ ,,ₘ me_lit U[σ]ᵘ].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq; intros [| x]; reduce_index.
  - cbn; rewrite <- gunit_wk_sub, gunit_sub_shift_extend, gunit_sub_id; reflexivity.
  - cbn; rewrite sentry_sub_shift_extend, sentry_sub_id; reflexivity.
Qed.

(** The same for a definition with a module part: its term part is still
    the variable, instantiated. *)
Lemma inline_dm_compose : forall σ V N H C,
  C[sb_extend (sb_wk σ wk_shift) (se_dm (a_var 0) (me_lit V[sb_wk σ wk_shift]ᵘ))][Id ,,ᵈ N ‖ H] = C[σ ,,ᵈ N ‖ me_lit V[σ]ᵘ].
Proof.
  intros; rewrite exp_sub_sub; apply exp_sub_sb_eq; intros [| x]; reduce_index.
  - cbn; rewrite <- gunit_wk_sub, gunit_sub_shift_extend, gunit_sub_id; reflexivity.
  - cbn; rewrite sentry_sub_shift_extend, sentry_sub_id; reflexivity.
Qed.

(** A comparison along paths is one up to units at the leaves. *)
Lemma paths_core_of_conv : forall Θ Ξ Δ P P', paths_conv Θ Ξ Δ P P' -> paths_core Θ Ξ Δ P P'.
Proof.
  intros * Hp s Hs; destruct (Hp s Hs) as [H1 H2]; split.
  - intros X HX; destruct (H1 _ HX) as (X' & HX' & Hl); exists X'; split; [ exact HX' |].
    unfold path_leaf, path_core in *; destruct (path_all_apps s); [| exact (leaf_core_of_conv _ _ _ _ _ Hl) ].
    destruct (mdesc_mod X), (mdesc_mod X'); cbn in *; try contradiction; [ exact (leaf_core_of_conv _ _ _ _ _ Hl) | exact I ].
  - intros X' HX'; destruct (H2 _ HX') as (X & HX & Hl); exists X; split; [ exact HX |].
    unfold path_leaf, path_core in *; destruct (path_all_apps s); [| exact (leaf_core_of_conv _ _ _ _ _ Hl) ].
    destruct (mdesc_mod X), (mdesc_mod X'); cbn in *; try contradiction; [ exact (leaf_core_of_conv _ _ _ _ _ Hl) | exact I ].
Qed.

(** The module part of a description is its own module part. *)
Lemma mdesc_mod_idem : forall R Rm, mdesc_mod R = Some Rm -> mdesc_mod Rm = Some Rm.
Proof. induction R; cbn; intros Rm H; try discriminate; try (injection H as <-; reflexivity); eauto. Qed.

(** What a module expression denotes reads an open frame exactly when what
    a module expression compared with it denotes does, by the module parts. *)
Lemma desc_reads_frame_mod_conv : forall Θ Ξ Δ X X',
    opt_rel (leaf_conv Θ Ξ Δ) (mdesc_mod X) (mdesc_mod X') -> desc_reads_frame Ξ X' -> desc_reads_frame Ξ X.
Proof.
  intros * Hr (Θ' & p & T & Φ & Ns & HX' & Hf).
  destruct (mdesc_mod X) as [Xm |] eqn:EX; rewrite HX' in Hr; cbn in Hr; [| contradiction ].
  assert (Hc : desc_reads_frame Ξ (mdesc_closed Θ' p T Φ Ns)) by (do 5 eexists; split; [ reflexivity | exact Hf ]).
  apply (leaf_frame _ _ _ _ _ Hr) in Hc as (Θ1 & p1 & T1 & Φ1 & Ns1 & HXm & Hf1).
  rewrite (mdesc_mod_idem _ _ EX) in HXm; injection HXm as ->.
  do 5 eexists; split; [ exact EX | exact Hf1 ].
Qed.

(** A module expression compared with one that is no open frame is none. *)
Lemma frame_free_target_conv : forall Θ Ξ Γ H H', ⊢ Θ ⍮ Ξ ⍮ Γ -> modexp_conv Θ Ξ Γ H H' ->
    frame_free_target Θ Ξ Γ H -> frame_free_target Θ Ξ Γ H'.
Proof.
  intros * HΓ Hc (R & HR & Hn).
  pose proof (Hc _ _ _ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))) as Hp; rewrite !modexp_sub_id in Hp.
  destruct (proj1 (Hp nil (path_pairs_nil _ _ _ _)) _ HR) as (R' & HR' & Hl).
  exists R'; split; [ exact HR' |]; intros Hf; apply Hn.
  exact (desc_reads_frame_mod_conv _ _ _ _ _ Hl Hf).
Qed.

(** ** The Transport over Pairs

    Every judgment holds between the two images of a related pair
    ([sub_pair]): a term is equal to itself across the pair, at the right
    image of its type; a unit, a module expression, a telescope is equal
    to itself across the pair, each side of an equation of them.  As for
    [sub_eq_preserves_mut], the equation judgment of terms needs nothing
    here: no typing rule reads a term equation it would need moved
    ([wf_tuple]'s is read at the right image only), and the equation half
    follows from the typing half by presupposition
    ([pair_transport_exp_eq]).  So a reduct, a [β]- or [ι]-reduct, needs
    no hypothesis of its own: its typing is presupposition's.  Subtyping
    and universes need nothing either: their rules read only right-hand
    images, which [sub_preserves_wf] moves.

    Each case applies the congruence of its rule with the right image on
    the left, where every premise is the right image of a premise
    ([sub_pair_right], [sub_preserves_wf]) or an induction hypothesis,
    and the left image on the right, then turns it round. *)

(** Over one assumption more, from the left image of its type, which is
    equal to the right image: the pair a binder premise is read along
    when a rule is applied at the left images. *)
Corollary sub_pair_q_left : forall Θ Ξ Γ' Γ τ1 τ2 κ A Srt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ A[τ1] ≈ A[τ2] : Srt ->
    sub_pair Θ Ξ (Γ' ▹{κ} A[τ1]) (Γ ▹{κ} A) (q τ1) (q τ2).
Proof.
  intros * Hp HA HS HAA.
  eapply sub_pair_q_conv; [ exact Hp | exact HA | exact HS | | exact (sort_kind_type_sort _ _ HS) | exact HAA ].
  eapply wf_ctx_extend; [ exact (presup_exp_eq_left HAA) | exact HS ].
Qed.

(** A proof across the pair: the left image, typed at a proposition equal
    to the right image of the proposition, is equal to the right image by
    irrelevance. *)
Lemma pair_irrel : forall Θ Ξ Γ' Γ τ2 X X1 P P1,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ X : P -> Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ X1 : P1 -> Θ ⍮ Ξ ⍮ Γ' ⊢ P1 ≈ P[τ2] : Propₘ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ X1 ≈ X[τ2] : P[τ2].
Proof.
  intros * Hr HX HP HX1 HPP.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HP Hr) as HPτ; cbn [exp_sub] in HPτ.
  apply wf_exp_eq_irrelevant;
    [ exact HPτ | exact (tr_conv _ _ _ _ _ _ _ HX1 HPP ltac:(constructor))
    | exact (sub_preserves_exp _ _ _ _ _ _ _ HX Hr) ].
Qed.

(** The proof formers across the pair: the left image typed by the rule
    at the left images of the components, each from its hypothesis, then
    equal to the right image by irrelevance ([pair_irrel]). *)
Section PairProofs.
  Context (Θ : gdeps) (Ξ : gstack) (Γ' Γ : ctx) (τ1 τ2 : sub) (Hp : sub_pair Θ Ξ Γ' Γ τ1 τ2).

  Let Hr := sub_pair_right _ _ _ _ _ _ Hp.

  Lemma pair_proof_tag : forall P M,
      Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : P ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ P[τ1] ≈ P[τ2] : Propₘ -> Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : P[τ2] ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ (a_proof P M)[τ1] ≈ (a_proof P M)[τ2] : P[τ2].
  Proof.
    intros * HP HM IHP IHM.
    eapply pair_irrel; [ exact Hr | econstructor; eassumption | exact HP | | exact IHP ].
    cbn [exp_sub]; econstructor;
      [ exact (presup_exp_eq_left IHP) | exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left IHM) IHP ltac:(constructor)) ].
  Qed.

  (** A conjunction across the pair: its two components, the second over
      the first; the second component's proposition at the first proof, by
      the hypothesis of the proposition at the pair extended by it. *)
  Lemma pair_and_left : forall P Q,
      Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ P[τ1] ≈ P[τ2] : Propₘ ->
      (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▹{ak_propositional} P) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ Q[t1] ≈ Q[t2] : Propₘ) ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ Σₚ P[τ1] Q[q τ1] ≈ (Σₚ P Q)[τ2] : Propₘ /\
      Θ ⍮ Ξ ⍮ Γ' ▹{ak_propositional} P[τ1] ⊢ Q[q τ1] : Propₘ.
  Proof.
    intros * HP HQ IHP IHQ.
    pose proof (IHQ _ _ _ (sub_pair_q_left _ _ _ _ _ _ _ _ _ Hp HP ltac:(constructor) IHP)) as HQQ.
    split; [| exact (presup_exp_eq_left HQQ) ].
    cbn [exp_sub]; eapply wf_exp_eq_and_cong; [ exact (presup_exp_eq_left IHP) | exact IHP | exact HQQ ].
  Qed.

  Lemma pair_conj : forall P Q M N,
      Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : P -> Θ ⍮ Ξ ⍮ Γ ⊢ N : Q[Id,,M] ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ P[τ1] ≈ P[τ2] : Propₘ ->
      (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▹{ak_propositional} P) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ Q[t1] ≈ Q[t2] : Propₘ) ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : P[τ2] -> Θ ⍮ Ξ ⍮ Γ' ⊢ N[τ1] ≈ N[τ2] : Q[Id,,M][τ2] ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ (a_conj P Q M N)[τ1] ≈ (a_conj P Q M N)[τ2] : (Σₚ P Q)[τ2].
  Proof.
    intros * HP HQ HM HN IHP IHQ IHM IHN.
    destruct (pair_and_left _ _ HP HQ IHP IHQ) as [HΣ HQ1].
    (** the second component's proposition at the two first proofs *)
    pose proof (IHQ _ _ _ (sub_pair_extend _ _ _ _ _ _ _ _ _ _ _ Hp HP ltac:(constructor) IHM)) as HQM.
    rewrite exp_sub_extend_sub in IHN.
    eapply pair_irrel; [ exact Hr | econstructor; eassumption | econstructor; eassumption | | exact HΣ ].
    cbn [exp_sub]; econstructor;
      [ exact (presup_exp_eq_left IHP) | exact HQ1
      | exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left IHM) IHP ltac:(constructor)) | ].
    rewrite exp_sub_q_extend.
    exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left IHN) HQM ltac:(constructor)).
  Qed.

  Lemma pair_left : forall P Q M,
      Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : Σₚ P Q ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ P[τ1] ≈ P[τ2] : Propₘ ->
      (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▹{ak_propositional} P) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ Q[t1] ≈ Q[t2] : Propₘ) ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : (Σₚ P Q)[τ2] ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ (a_left M)[τ1] ≈ (a_left M)[τ2] : P[τ2].
  Proof.
    intros * HP HQ HM IHP IHQ IHM.
    destruct (pair_and_left _ _ HP HQ IHP IHQ) as [HΣ HQ1].
    eapply pair_irrel; [ exact Hr | econstructor; eassumption | exact HP | | exact IHP ].
    cbn [exp_sub]; econstructor;
      [ exact (presup_exp_eq_left IHP) | exact HQ1
      | exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left IHM) HΣ ltac:(constructor)) ].
  Qed.

  Lemma pair_right : forall P Q M,
      Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : Σₚ P Q ->
      Θ ⍮ Ξ ⍮ Γ ⊢ Q[Id,,a_left M] : Propₘ ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ P[τ1] ≈ P[τ2] : Propₘ ->
      (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▹{ak_propositional} P) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ Q[t1] ≈ Q[t2] : Propₘ) ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : (Σₚ P Q)[τ2] ->
      Θ ⍮ Ξ ⍮ Γ' ⊢ (a_right M)[τ1] ≈ (a_right M)[τ2] : Q[Id,,a_left M][τ2].
  Proof.
    intros * HP HQ HM HQl IHP IHQ IHM.
    destruct (pair_and_left _ _ HP HQ IHP IHQ) as [HΣ HQ1].
    (** the first projections, equal by irrelevance; the proposition at
        them by the hypothesis at the pair extended by them *)
    pose proof (pair_left _ _ _ HP HQ HM IHP IHQ IHM) as HL.
    pose proof (IHQ _ _ _ (sub_pair_extend _ _ _ _ _ _ _ _ _ _ _ Hp HP ltac:(constructor) HL)) as HQL.
    cbn [exp_sub] in HQL.
    eapply pair_irrel with (P1 := Q[q τ1][Id,,a_left M[τ1]]);
      [ exact Hr | eapply wf_right; [ exact HP | exact HQ | exact HM | exact HQl ] | exact HQl | | ].
    - cbn [exp_sub]; econstructor;
        [ exact (presup_exp_eq_left IHP) | exact HQ1
        | exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left IHM) HΣ ltac:(constructor))
        | rewrite exp_sub_q_extend; exact (presup_exp_eq_left HQL) ].
    - rewrite exp_sub_q_extend, exp_sub_extend_sub; cbn [exp_sub]; exact HQL.
  Qed.
End PairProofs.

(** A selection of a well-formed module expression whose description has
    a module part has a module telescope. *)
Lemma mem_mod_tele_of_mod : forall Θ Ξ Γ K y X,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ K ≈ K -> mdenote Θ Ξ Γ (me_mem K y) X -> mdesc_mod X <> None ->
    exists T, mdesc_mod_tele X = Some T.
Proof.
  intros * HK Hm Hn.
  destruct (mdesc_mod X) as [Xm |] eqn:EX; [| contradiction ].
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HK)) as Hg.
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  destruct (desc_ok_tele _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HK Hm) EX)
              (mdesc_mod_is_mod _ _ EX)) as [T HT].
  exists T; unfold mdesc_mod_tele; rewrite EX; exact HT.
Qed.

(** A selection of a module across the pair: the selection's congruence,
    the left image's selection read off the right image's through the
    equal module expressions ([modexp_eq_mem_left]). *)
Lemma pair_me_mem : forall Θ Ξ Γ' Γ τ1 τ2 H y R T,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θ Ξ Γ (me_mem H y) R -> mdesc_mod_tele R = Some T ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ H[τ1]ᵐ ≈ H[τ2]ᵐ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ (me_mem H y)[τ1]ᵐ ≈ (me_mem H y)[τ2]ᵐ.
Proof.
  intros * Hr HH Hm HT IH.
  pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH Hm Hr) as Hm2.
  pose proof (wf_modexp_eq_refl_right IH) as HH2.
  pose proof (wf_modexp_eq_refl_left IH) as HH1.
  (** the right image has a module part, so the left one does *)
  assert (Hmod2 : mdesc_mod (mdesc_sub R τ2) <> None).
  { unfold mdesc_mod_tele in HT; destruct (mdesc_mod R) as [Rm |] eqn:ER; [| discriminate ].
    rewrite (mdesc_mod_sub _ _ τ2 ER); discriminate. }
  destruct (modexp_eq_mem_left _ _ _ _ _ _ _ IH Hm2) as (R1 & Hm1 & Hl).
  assert (Hmod1 : mdesc_mod R1 <> None).
  { pose proof (leaf_unit _ _ _ _ _ Hl) as Hu.
    destruct (mdesc_mod R1), (mdesc_mod (mdesc_sub R τ2)); cbn in Hu; try contradiction; congruence. }
  destruct (mem_mod_tele_of_mod _ _ _ _ _ _ HH1 Hm1 Hmod1) as [T1 HT1].
  destruct (mem_mod_tele_of_mod _ _ _ _ _ _ HH2 Hm2 Hmod2) as [T2 HT2].
  cbn [modexp_sub]; eapply wf_me_mem; [ exact IH | exact Hm1 | exact HT1 | exact Hm2 | exact HT2 ].
Qed.

(** A member across the pair: the congruence of members at the right
    images, the left image's member looked up through the equal module
    expressions ([modexp_eq_mem_left]), of a type convertible to the right
    image's ([leaf_type]). *)
Lemma pair_mem : forall Θ Ξ Γ' Γ τ1 τ2 H x R A,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θ Ξ Γ (me_mem H x) R -> mdesc_type R = Some A ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ H[τ1]ᵐ ≈ H[τ2]ᵐ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (a_mem H x)[τ1] ≈ (a_mem H x)[τ2] : A[τ2].
Proof.
  intros * Hr HH Hm Ht IH.
  pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH Hm Hr) as Hm2.
  pose proof (mdesc_type_sub _ _ τ2 Ht) as Ht2.
  destruct (modexp_eq_mem_left _ _ _ _ _ _ _ IH Hm2) as (R1 & Hm1 & Hl).
  pose proof (leaf_type _ _ _ _ _ Hl) as HT.
  rewrite Ht2 in HT; destruct (mdesc_type R1) as [A1 |] eqn:Ht1; cbn in HT; [| contradiction ].
  destruct HT as (j & HAA).
  pose proof (type_sort_abs_kind (mdesc_kind R1) _ (type_sort_universe j)) as HSt.
  (** the left image's member, at the right image's type *)
  pose proof (wf_mem_desc _ _ _ _ _ _ _ (wf_modexp_eq_refl_left IH) Hm1 Ht1) as HM1.
  pose proof (tr_conv _ _ _ _ _ _ _ HM1 HAA HSt) as HM1'.
  apply wf_exp_eq_sym; cbn [exp_sub].
  eapply wf_exp_eq_mem_cong; [ apply wf_me_sym; exact IH | exact Hm2 | exact Ht2 | exact Hm1 | exact Ht1 | exact HM1' ].
Qed.

(** A record element across the pair: the congruence with the right image
    on the left.  The left image is typed at its own type, equal to the
    record type at the right image's parameters, its fields at their types
    there and at the right image's fields before them, moved to its own
    fields before them ([record_field_typ_cong]). *)
Lemma pair_tuple : forall Θ Ξ Γ' Γ τ1 τ2 i T p Ns R fs,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ T[τ1] ≈ T[τ2] : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
    record_lookup Θ Ξ p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))][τ2]) ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (a_tuple T fs)[τ1] ≈ (a_tuple T fs)[τ2] : T[τ2].
Proof.
  intros * Hσ HT IHT HTa Hr Hl Hn HNs Hnames HFs IHFs.
  pose proof (wf_sub_dom _ _ _ _ _ Hσ) as HΓ2.
  destruct (Records.Typing.wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFt _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ (presup_exp_ctx Hr) Hl) as HRd.
  set (Ns2 := List.map (fun N => N[τ2]) Ns).
  set (fs1 := List.map (fun f => (fst f, (snd f)[τ1])) fs).
  set (fs2 := List.map (fun f => (fst f, (snd f)[τ2])) fs).
  assert (Hr2 : Θ ⍮ Ξ ⍮ Γ' ⊢ a_record p : record_ty R)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hr Hσ) as X; rewrite record_ty_sub in X by exact HRd; exact X).
  assert (Hl2 : List.length Ns2 = List.length (record_params R)) by (unfold Ns2; rewrite List.length_map; exact Hn).
  assert (HNs2 : forall j N A, List.nth_error Ns2 j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns2) j = Some A ->
                   Θ ⍮ Ξ ⍮ Γ' ⊢ N : A).
  { intros j N A HN HA; unfold Ns2 in *; rewrite <- record_params_insts_sub in HA by exact HRd.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HNs _ _ _ HN0 HA0) Hσ). }
  assert (HN22 : forall j X Y A, List.nth_error Ns2 j = Some X -> List.nth_error Ns2 j = Some Y ->
                   List.nth_error (tele_insts (record_params R) Id Ns2) j = Some A -> Θ ⍮ Ξ ⍮ Γ' ⊢ X ≈ Y : A).
  { intros j X Y A HX HY HA; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; exact (HNs2 _ _ _ HX HA). }
  assert (HTa2 : Θ ⍮ Ξ ⍮ Γ' ⊢ T[τ2] ≈ apps_exp (a_record p) Ns2 : Typeω@i)
    by (pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HTa Hσ) as X; rewrite apps_exp_sub in X; exact X).
  (** the right image's fields equal to the left image's, at the right
      image's parameters and fields before them *)
  assert (HF21 : forall k f M M' U, List.nth_error fs2 k = Some (f, M) -> List.nth_error fs1 k = Some (f, M') ->
                   List.nth_error (record_fields R) k = Some (f, U) ->
                   Θ ⍮ Ξ ⍮ Γ' ⊢ M ≈ M' : U[sb_of_list Id (Ns2 ++ List.firstn k (List.map snd fs2))]).
  { intros k f M M' U HM HM' HU; unfold fs1, fs2, Ns2 in *.
    apply nth_error_map_inv in HM as ([f0 M0] & HM0 & Heq); cbn in Heq; injection Heq as -> ->.
    apply nth_error_map_inv in HM' as ([f1 M1] & HM1 & Heq); cbn in Heq; injection Heq as <- ->.
    rewrite HM0 in HM1; injection HM1 as <-.
    pose proof (IHFs _ _ _ _ HM0 HU) as X.
    rewrite (record_field_sub _ _ _ _ _ _ _ HRd HU Hn) in X
      by (rewrite List.length_firstn, List.length_map; pose proof (nth_error_lt_length _ _ _ HM0); lia).
    rewrite tuple_values_sub in X; apply wf_exp_eq_sym; exact X. }
  assert (Hnames1 : List.map fst fs1 = List.map fst fs2) by (unfold fs1, fs2; rewrite !tuple_names_sub; reflexivity).
  assert (Hnames2 : List.map fst fs2 = List.map fst (record_fields R)) by (unfold fs2; rewrite tuple_names_sub; exact Hnames).
  (** the left image, at its own type *)
  assert (HK : Θ ⍮ Ξ ⍮ Γ' ⊢ a_tuple T[τ1] fs1 : T[τ1]).
  { eapply wf_tuple with (Ns := Ns2);
      [ exact (presup_exp_eq_left IHT) | eapply wf_exp_eq_trans; [ exact IHT | exact HTa2 ]
      | exact Hr2 | exact Hl | exact Hl2 | exact HNs2 | rewrite Hnames1; exact Hnames2 | ].
    intros k f M U HM HU.
    assert (HM2 : exists M2, List.nth_error fs2 k = Some (f, M2)).
    { unfold fs1, fs2 in *; apply nth_error_map_inv in HM as ([f0 M0] & HM0 & Heq); cbn in Heq; injection Heq as -> ->.
      exists M0[τ2]; rewrite List.nth_error_map, HM0; reflexivity. }
    destruct HM2 as (M2 & HM2).
    pose proof (HF21 _ _ _ _ _ HM2 HM HU) as X.
    assert (Hk : k <= List.length (record_fields R)) by (pose proof (nth_error_lt_length _ _ _ HU); lia).
    pose proof (nth_error_lt_length _ _ _ HM) as HMk.
    assert (HL1 : List.length (Ns2 ++ List.firstn k (List.map snd fs2)) = k + List.length (record_params R))
      by (unfold fs1, fs2 in *; rewrite List.length_app, List.length_firstn, !List.length_map in *; lia).
    assert (HL2 : List.length (Ns2 ++ List.firstn k (List.map snd fs1)) = k + List.length (record_params R))
      by (unfold fs1, fs2 in *; rewrite List.length_app, List.length_firstn, !List.length_map in *; lia).
    destruct (Records.Typing.record_field_typ_cong _ _ _ _ _ _ _ _ _ HRd Hass HF HΓ2 HU HL1 HL2
                ltac:(eapply Records.Typing.record_fields_insts_eq;
                        [ exact Hr2 | exact Hl | exact Hl2 | exact Hl2 | exact HN22
                        | exact Hnames2 | exact Hnames1 | exact HF21 | exact Hk ]))
      as (S0 & HS0 & HUU).
    eapply tr_conv; [ exact (presup_exp_eq_right X) | exact HUU | exact HS0 ]. }
  assert (HT1 : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T) by (eapply wf_tuple; eassumption).
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT1 Hσ) as Hσt.
  cbn [exp_sub] in Hσt |- *; fold fs1 fs2 in Hσt |- *.
  apply wf_exp_eq_sym.
  eapply wf_exp_eq_tuple_cong with (Ns := Ns2) (i := i);
    [ exact Hσt | apply wf_exp_eq_sym; exact IHT | exact HTa2 | exact Hl | exact Hl2 | exact HNs2
    | exact Hnames2 | exact Hnames1 | exact HF21 | eapply tr_conv; [ exact HK | exact IHT | constructor ] ].
Qed.

(** A projection across the pair: the congruence with the right image on
    the left.  The left image is typed at its own parameters, its element
    moved there along the equal record types at the two images'
    parameters, and then at the right image's type by the hypothesis on
    the field's type. *)
Lemma pair_proj : forall Θ Ξ Γ' Γ τ1 τ2 M p Ns R k f U Srt,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : (apps_exp (a_record p) Ns)[τ2] ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
    record_lookup Θ Ξ p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
       Θ ⍮ Ξ ⍮ Γ' ⊢ N[τ1] ≈ N[τ2] : A[τ2]) ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Srt ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)][τ1] ≈ U[sb_of_list Id (Ns ++ record_pre R k M)][τ2] : Srt[τ2] ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (a_proj f M)[τ1] ≈ (a_proj f M)[τ2] : U[sb_of_list Id (Ns ++ record_pre R k M)][τ2].
Proof.
  intros * Hσ IHM Hr Hl Hn HNs IHNs Hk HU IHU HS.
  rewrite (type_sort_sub _ _ HS) in IHU.
  pose proof (wf_sub_dom _ _ _ _ _ Hσ) as HΓ2.
  destruct (Records.Typing.wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 Hty HF HSr HFt _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ (presup_exp_ctx Hr) Hl) as HRd.
  set (Ns1 := List.map (fun N => N[τ1]) Ns).
  set (Ns2 := List.map (fun N => N[τ2]) Ns).
  assert (Hr2 : Θ ⍮ Ξ ⍮ Γ' ⊢ a_record p : record_ty R)
    by (pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hr Hσ) as X; rewrite record_ty_sub in X by exact HRd; exact X).
  assert (Hl1 : List.length Ns1 = List.length (record_params R)) by (unfold Ns1; rewrite List.length_map; exact Hn).
  assert (Hl2 : List.length Ns2 = List.length (record_params R)) by (unfold Ns2; rewrite List.length_map; exact Hn).
  assert (HNs2 : forall j N A, List.nth_error Ns2 j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns2) j = Some A ->
                   Θ ⍮ Ξ ⍮ Γ' ⊢ N : A).
  { intros j N A HN HA; unfold Ns2 in *; rewrite <- record_params_insts_sub in HA by exact HRd.
    apply nth_error_map_inv in HN as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HNs _ _ _ HN0 HA0) Hσ). }
  assert (HN21 : forall j X Y A, List.nth_error Ns2 j = Some X -> List.nth_error Ns1 j = Some Y ->
                   List.nth_error (tele_insts (record_params R) Id Ns2) j = Some A -> Θ ⍮ Ξ ⍮ Γ' ⊢ X ≈ Y : A).
  { intros j X Y A HX HY HA; unfold Ns1, Ns2 in *; rewrite <- record_params_insts_sub in HA by exact HRd.
    apply nth_error_map_inv in HX as (N0 & HN0 & ->); apply nth_error_map_inv in HA as (A0 & HA0 & ->).
    rewrite List.nth_error_map, HN0 in HY; injection HY as <-.
    apply wf_exp_eq_sym; exact (IHNs _ _ _ HN0 HA0). }
  pose proof (Records.Typing.record_params_eq_right _ _ _ _ _ _ HRd Hass HF HΓ2 Hl2 Hl1 HN21) as HNs1.
  pose proof (Records.Typing.wf_exp_eq_record_apps _ _ _ _ _ _ _ Hr2 Hl Hl2 Hl1 HN21) as HAp.
  destruct (Records.Typing.record_sort_large _ _ _ _ _ _ Hr2 Hl Hl2 HNs2) as [n Hn'].
  assert (HAp' : Θ ⍮ Ξ ⍮ Γ' ⊢ apps_exp (a_record p) Ns2 ≈ apps_exp (a_record p) Ns1 : Typeω@n)
    by (eapply wf_exp_eq_subtyp; [ exact HAp | apply wf_typ; exact HΓ2 | constructor | exact Hn' ]).
  rewrite apps_exp_sub in IHM; fold Ns2 in IHM.
  assert (HM1 : Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] : apps_exp (a_record p) Ns1)
    by (eapply tr_conv; [ exact (presup_exp_eq_left IHM) | exact HAp' | constructor ]).
  assert (EU : forall τ, U[sb_of_list Id (Ns ++ record_pre R k M)][τ]
                         = U[sb_of_list Id (List.map (fun N => N[τ]) Ns ++ record_pre R k M[τ])]).
  { intros τ; rewrite (record_field_sub _ _ _ _ _ _ _ HRd Hk Hn), record_pre_sub; [ reflexivity |].
    apply length_record_pre; pose proof (nth_error_lt_length _ _ _ Hk); lia. }
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HU Hσ) as HUσ; rewrite (type_sort_sub _ _ HS) in HUσ.
  rewrite !EU in IHU; rewrite EU in HUσ |- *; fold Ns1 Ns2 in IHU, HUσ |- *.
  (** the left image, at its own parameters, then at the right image's type *)
  assert (HK : Θ ⍮ Ξ ⍮ Γ' ⊢ a_proj f M[τ1] : U[sb_of_list Id (Ns1 ++ record_pre R k M[τ1])])
    by (eapply wf_proj; [ exact HM1 | exact Hr2 | exact Hl | exact Hl1 | exact HNs1 | exact Hk
                        | exact (presup_exp_eq_left IHU) | exact HS ]).
  cbn [exp_sub]; apply wf_exp_eq_sym.
  eapply wf_exp_eq_proj_cong with (Ns := Ns2) (Srt := Srt);
    [ apply wf_exp_eq_sym; exact IHM | exact Hr2 | exact Hl | exact Hl2 | exact HNs2 | exact Hk | exact HUσ | exact HS
    | eapply tr_conv; [ exact HK | exact IHU | exact HS ] ].
Qed.

(** An application of a module across the pair: any module expression
    and argument equal to the right images apply to give the right image
    of the application, along the equal heads' paths ([path_eq]).  The
    same as [tr_me_app], with any left side for the head and the
    argument. *)
Lemma pair_me_app : forall Θ Ξ Γ1 Γ2 H N H1 N1 R T B T1 σ,
    Θ ⍮ Ξ ⍮ Γ2 ⊢ˢ σ : Γ1 ->
    Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ me_app H N ≈ me_app H N -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H ≈ H ->
    mdenote Θ Ξ Γ1 H R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
    Θ ⍮ Ξ ⍮ Γ2 ⊢ᵐ H1 ≈ H[σ]ᵐ -> Θ ⍮ Ξ ⍮ Γ2 ⊢ N1 ≈ N[σ] : B[σ] ->
    Θ ⍮ Ξ ⍮ Γ2 ⊢ᵐ me_app H1 N1 ≈ (me_app H N)[σ]ᵐ.
Proof.
  intros * Hσ HA HH Hm Ht Hv HH1 HN.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH1)) as Hg.
  pose proof (modexp_paths_conv _ _ _ _ _ HH1) as Hp.
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HH Hm Hσ) as Hmσ.
  pose proof (wf_sub_mdesc_mod_tele _ _ _ _ _ _ _ _ _ HH Hm Ht Hσ) as Htσ.
  pose proof (tele_view_sub T σ) as Ev; rewrite Hv in Ev; cbn in Ev.
  destruct (proj2 (Hp nil (path_pairs_nil _ _ _ _)) _ Hmσ) as (R2 & Hm2 & Hl); cbn in Hl.
  assert (Hl' : opt_rel (leaf_conv Θ Ξ Γ2) (mdesc_mod (mdesc_sub R σ)) (mdesc_mod R2))
    by (unfold path_leaf in Hl; cbn in Hl; eapply opt_rel_sym; [| exact Hl ]; intros; apply leaf_conv_sym; assumption).
  destruct (head_conv_arg_mod _ _ _ _ _ _ _ _ _ _ Hl' Htσ Ev HN) as (T2 & B2 & T12 & Ht2 & Hv2 & HN2 & _ & _).
  assert (Hs : path_pairs Θ Ξ Γ2 H1 (ps_app N1 N[σ] :: nil))
    by (eapply path_pairs_app; [ exact Hm2 | exact Ht2 | exact Hv2 | exact HN2 | constructor ]).
  destruct (me_denotes _ _ _ _ _ HA) as (X0 & Xm0 & HX0 & HXm0).
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HA HX0 Hσ) as HXσ; cbn [modexp_sub] in HXσ.
  pose proof (mdesc_mod_sub _ _ σ HXm0) as HXσm.
  destruct (proj2 (Hp _ Hs) _ HXσ) as (X & HX & HlX).
  unfold path_leaf in HlX; cbn in HlX; rewrite HXσm in HlX.
  destruct (mdesc_mod X) as [Xm |] eqn:HXm; cbn in HlX; [| contradiction ].
  cbn [modexp_sub].
  exact (path_eq _ _ _ _ _ Hs _ HH1 (paths_core_of_conv _ _ _ _ _ Hp) _ _ _ HX HXσ HXm).
Qed.

(** A local module across the pair: the congruence at the right images,
    its right side, the left image, typed by the rule at the left images,
    the body read at the pair lifted over the left image of the slot
    ([sub_pair_mod_inline]), whose right side inlines the slot. *)
Lemma pair_let_mod : forall Θ Ξ Γ' Γ τ1 τ2 U C Srt B,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Srt -> type_sort Srt -> module_body_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ U[τ1]ᵘ ≈ U[τ2]ᵘ ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▹ₘ U) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ B[t1] ≈ B[t2] : C[t2]) ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (ℓₘ U in B)[τ1] ≈ (ℓₘ U in B)[τ2] : C[Id ,,ₘ me_lit U][τ2].
Proof.
  intros * Hp HU HC HS HMS HUU IHB.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  pose proof (sub_pair_q_mod _ _ _ _ _ _ _ Hp HU HUU) as Pq.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HS (sub_pair_right _ _ _ _ _ _ Pq)) as HCq.
  (** the left lifting: a slot holding the left image, inlined on the right *)
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HU1.
  assert (HΓ1 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▹ₘ U[τ1]ᵘ) by (apply wf_ctx_extend_mod; exact HU1).
  pose proof (wf_wk_shift _ _ _ _ HΓ1) as Hφ.
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HUU Hφ) as HVw; rewrite (gunit_wk_sub U τ2) in HVw.
  pose proof HVw as HUw; rewrite gunit_wk_sub in HUw.
  pose proof (sub_pair_mod_inline _ _ _ _ _ _ _ _ _ (sub_pair_wk _ _ _ _ _ _ _ _ Hp Hφ) HU HVw HUw
                ltac:(constructor)) as P1.
  pose proof (IHB _ _ _ P1) as HB1.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HS (sub_pair_right _ _ _ _ _ _ P1)) as HC1.
  (** the right side's typing, at the left images *)
  assert (HR : Θ ⍮ Ξ ⍮ Γ' ⊢ (ℓₘ U in B)[τ1] : C[q τ2][Id ,,ₘ me_lit U[τ2]ᵘ]).
  { rewrite exp_sub_q_extend_mod, <- (inline_mod_compose τ2 U (me_lit U[τ1]ᵘ) C).
    cbn [exp_sub]; eapply wf_let_mod; [ exact HU1 | exact HC1 | exact HS | exact HMS | ].
    unfold sb_q; exact (presup_exp_eq_left HB1). }
  rewrite exp_sub_extend_mod_sub, <- exp_sub_q_extend_mod.
  apply wf_exp_eq_sym; cbn [exp_sub modexp_sub].
  eapply wf_exp_eq_let_mod_cong;
    [ apply wf_unit_eq_sym; exact HUU | exact HCq | exact HMS | apply wf_exp_eq_sym; exact (IHB _ _ _ Pq) | exact HR ].
Qed.

(** A local definition with a module part across the pair: as a local
    module, the entry lifted on the right by [sub_pair_q_dm] and on the
    left by [sub_pair_dm_inline]. *)
Lemma pair_let_dm : forall Θ Ξ Γ' Γ τ1 τ2 A M E i C Srt B,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ⊢ C : Srt -> type_sort Srt -> module_body_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ A[τ1] ≈ A[τ2] : Typeω@i -> Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : A[τ2] ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk nil (md_alias E))[τ1]ᵘ ≈ (gu_mk nil (md_alias E))[τ2]ᵘ ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ B[t1] ≈ B[t2] : C[t2]) ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (ℓᵈ A ≔ M ‖ (gu_mk nil (md_alias E)) in B)[τ1] ≈ (ℓᵈ A ≔ M ‖ (gu_mk nil (md_alias E)) in B)[τ2]
      : C[Id ,,ᵈ M ‖ me_lit (gu_mk nil (md_alias E))][τ2].
Proof.
  intros * Hp HA HM HU HC HS HMS HAA HMM HUU IHB.
  set (V := gu_mk nil (md_alias E)) in *.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  assert (HΓ0 : ⊢ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ V) by (eapply wf_ctx_extend_dm; eassumption).
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUU (wf_unit_eq_sym _ _ _ _ _ HUU)) as HU1.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HUU) HUU) as HU2.
  pose proof (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left HMM) HAA ltac:(constructor)) as HM1.
  (** the two extended contexts, their units aliases once pushed in *)
  assert (HΓ2 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▸ₘ A[τ2] ≔ M[τ2] ‖ V[τ2]ᵘ).
  { unfold V in *; rewrite gunit_sub_mk in HU2 |- *; cbn [tele_sub moddef_sub length sb_qn] in HU2 |- *.
    eapply wf_ctx_extend_dm; [ exact (presup_exp_eq_right HAA) | exact (presup_exp_eq_right HMM) | exact HU2 ]. }
  assert (HΓ1 : ⊢ Θ ⍮ Ξ ⍮ Γ' ▸ₘ A[τ1] ≔ M[τ1] ‖ V[τ1]ᵘ).
  { unfold V in *; rewrite gunit_sub_mk in HU1 |- *; cbn [tele_sub moddef_sub length sb_qn] in HU1 |- *.
    eapply wf_ctx_extend_dm; [ exact (presup_exp_eq_left HAA) | exact HM1 | exact HU1 ]. }
  pose proof (sub_pair_q_dm _ _ _ _ _ _ _ _ _ _ Hp HΓ0 HA HUU HΓ2) as Pq.
  pose proof (sub_pair_dm_inline _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp HΓ0 HΓ1 HAA HMM HUU HUU HA) as P1.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HS (sub_pair_right _ _ _ _ _ _ Pq)) as HCq.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HS (sub_pair_right _ _ _ _ _ _ P1)) as HC1.
  pose proof (IHB _ _ _ P1) as HB1.
  (** the right side's typing, at the left images: the term part of the
      instance is the left image of the body, equal to the right one *)
  assert (HR1 : Θ ⍮ Ξ ⍮ Γ' ⊢ (ℓᵈ A ≔ M ‖ V in B)[τ1] : C[τ2 ,,ᵈ M[τ1] ‖ me_lit V[τ2]ᵘ]).
  { rewrite <- (inline_dm_compose τ2 V M[τ1] (me_lit V[τ1]ᵘ) C).
    pose proof HU1 as HU1'; pose proof HC1 as HC1'; pose proof HB1 as HB1'.
    unfold V in *; cbn [exp_sub]; rewrite gunit_sub_mk in HU1', HC1', HB1' |- *;
      cbn [tele_sub moddef_sub length sb_qn] in HU1', HC1', HB1' |- *.
    eapply wf_let_dm; [ exact (presup_exp_eq_left HAA) | exact HM1 | exact HU1' | exact HC1' | exact HS | exact HMS | ].
    unfold sb_q; exact (presup_exp_eq_left HB1'). }
  assert (HCC : Θ ⍮ Ξ ⍮ Γ' ⊢ C[τ2 ,,ᵈ M[τ1] ‖ me_lit V[τ2]ᵘ] ≈ C[τ2 ,,ᵈ M[τ2] ‖ me_lit V[τ2]ᵘ] : Srt).
  { pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hr) as HMτ.
    assert (Hs : Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 ,,ᵈ M[τ1] ‖ me_lit V[τ2]ᵘ ≈ τ2 ,,ᵈ M[τ2] ‖ me_lit V[τ2]ᵘ : Γ ▸ₘ A ≔ M ‖ V)
      by (unfold V; eapply wf_sub_eq_extend_dm;
            [ apply wf_sub_eq_refl; exact Hr | exact HA | exact HM | exact HU | exact (presup_exp_eq_left HMM) | exact HMτ
            | exact HMM | apply wf_exp_eq_refl; exact HMτ | exact HMM | exact HU2 ]).
    pose proof (sub_eq_preserves_exp _ _ _ _ _ HC _ _ _ Hs) as H; rewrite (type_sort_sub _ _ HS) in H; exact H. }
  assert (HR : Θ ⍮ Ξ ⍮ Γ' ⊢ (ℓᵈ A ≔ M ‖ V in B)[τ1] : C[q τ2][Id ,,ᵈ M[τ2] ‖ me_lit V[τ2]ᵘ])
    by (rewrite exp_sub_q_extend_dm; exact (tr_conv _ _ _ _ _ _ _ HR1 HCC HS)).
  rewrite exp_sub_sub_extend_dm.
  apply wf_exp_eq_sym; cbn [exp_sub modexp_sub].
  unfold V in *; rewrite gunit_sub_mk in HU2, HUU, HCq, HR |- *; cbn [tele_sub moddef_sub length sb_qn] in HU2, HUU, HCq, HR |- *.
  pose proof (IHB _ _ _ Pq) as HBq.
  rewrite gunit_sub_mk in HBq; cbn [tele_sub moddef_sub length sb_qn] in HBq.
  eapply wf_exp_eq_let_dm_cong;
    [ exact (presup_exp_eq_right HAA) | apply wf_exp_eq_sym; exact HAA | exact (presup_exp_eq_right HMM)
    | apply wf_exp_eq_sym; exact HMM | apply wf_unit_eq_sym; exact HUU | exact HCq | exact HMS
    | apply wf_exp_eq_sym; exact HBq | exact HR ].
Qed.

(** ** Telescopes across a Pair

    [ext_pair Θ Ξ Γ' Γ τ1 τ2 X]: a telescope [X] over [Γ] moves along the
    pair [(τ1, τ2)] from [Γ']: the pair lifts over it from its right
    images, and from its left images with some right side, and the two
    images are equal telescopes.  The left lifting is what a rule needs to
    type its right side's entries, which are read in the right side's own
    telescope; its right side inlines the telescope's module slots, whose
    left images hold units only equal to the right ones
    ([sub_pair_mod_inline]). *)
Record ext_pair (Θ : gdeps) (Ξ : gstack) (Γ' Γ : ctx) (τ1 τ2 : sub) (X : ctx) : Prop := mk_ext_pair
  { (** The pair lifted over the telescope, from its right images *)
    ext_pair_right : sub_pair Θ Ξ (tele_sub X τ2 ++ Γ') (X ++ Γ) (sb_qn (length X) τ1) (sb_qn (length X) τ2)
    (** The pair lifted over the telescope, from its left images, with some
        right side *)
  ; ext_pair_left : exists τ', sub_pair Θ Ξ (tele_sub X τ1 ++ Γ') (X ++ Γ) (sb_qn (length X) τ1) τ'
    (** The two images are equal telescopes *)
  ; ext_pair_eq : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub X τ2 ≈ tele_sub X τ1 }.

(** The empty telescope: the pair itself. *)
Lemma ext_pair_nil : forall Θ Ξ Γ' Γ τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 -> ext_pair Θ Ξ Γ' Γ τ1 τ2 nil.
Proof.
  intros * Hp; constructor; cbn [tele_sub List.app length sb_qn].
  - exact Hp.
  - exists τ2; exact Hp.
  - constructor; exact (wf_sub_dom _ _ _ _ _ (sub_pair_right _ _ _ _ _ _ Hp)).
Qed.

(** An assumption more: lifted over it from its right image by
    [sub_pair_q], from its left image by [sub_pair_q_conv]; the two
    images of its type below each other by its hypothesis. *)
Lemma ext_pair_ass : forall Θ Ξ Γ' Γ τ1 τ2 Ψ κ A Srt,
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Ψ ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Srt -> sort_kind Srt κ ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ A[t1] ≈ A[t2] : Srt[t2]) ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 (ce_ass κ A :: Ψ).
Proof.
  intros * [Hpr (τ' & Hpl) HΨ] HA HS IHA.
  pose proof (sort_kind_type_sort _ _ HS) as HSt.
  pose proof (IHA _ _ _ Hpr) as HAr; rewrite (type_sort_sub _ _ HSt) in HAr.
  pose proof (IHA _ _ _ Hpl) as HAl; rewrite (type_sort_sub _ _ HSt) in HAl.
  constructor; cbn [tele_sub List.app length sb_qn centry_sub].
  - exact (sub_pair_q _ _ _ _ _ _ _ _ _ Hpr HA HS).
  - exists (q τ'); eapply sub_pair_q_conv;
      [ exact Hpl | exact HA | exact HS | eapply wf_ctx_extend; [ exact (presup_exp_eq_left HAl) | exact HS ] | exact HSt | exact HAl ].
  - eapply wf_ext_eq_ass;
      [ exact HΨ | exact (presup_exp_eq_right HAr) | exact HS | exact (presup_exp_eq_left HAl) | exact HS
      | eapply wf_subtyp_refl; [ exact (presup_exp_eq_left HAr) | exact HSt | apply wf_exp_eq_sym; exact HAr ]
      | eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HAr) | exact HSt | exact HAr ] ].
Qed.

(** A definition more: as an assumption, its body by its hypothesis. *)
Lemma ext_pair_def : forall Θ Ξ Γ' Γ τ1 τ2 Ψ A M Srt,
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Ψ ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Srt -> type_sort Srt -> Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ A[t1] ≈ A[t2] : Srt[t2]) ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ M[t1] ≈ M[t2] : A[t2]) ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 (ce_def A M :: Ψ).
Proof.
  intros * [Hpr (τ' & Hpl) HΨ] HA HSt HM IHA IHM.
  pose proof (IHA _ _ _ Hpr) as HAr; rewrite (type_sort_sub _ _ HSt) in HAr.
  pose proof (IHA _ _ _ Hpl) as HAl; rewrite (type_sort_sub _ _ HSt) in HAl.
  pose proof (IHM _ _ _ Hpr) as HMr.
  pose proof (IHM _ _ _ Hpl) as HMl.
  constructor; cbn [tele_sub List.app length sb_qn centry_sub].
  - exact (sub_pair_q_def _ _ _ _ _ _ _ _ _ Hpr HA HSt HM).
  - exists (q τ'); eapply sub_pair_q_def_conv; [ exact Hpl | exact HA | exact HSt | exact HM | exact HSt | exact HAl | exact HMl ].
  - eapply wf_ext_eq_def;
      [ exact HΨ | exact (presup_exp_eq_right HAr) | exact HSt | exact (presup_exp_eq_left HAl) | exact HSt
      | eapply wf_subtyp_refl; [ exact (presup_exp_eq_left HAr) | exact HSt | apply wf_exp_eq_sym; exact HAr ]
      | eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HAr) | exact HSt | exact HAr ]
      | exact (presup_exp_eq_right HMr) | apply wf_exp_eq_sym; exact HMr
      | exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left HMl) HAl HSt) ].
Qed.

(** A module slot more: lifted over it from its right image by
    [sub_pair_q_mod], from its left image, a slot holding a unit only
    equal to the right image, by [sub_pair_mod_inline]. *)
Lemma ext_pair_mod : forall Θ Ξ Γ' Γ τ1 τ2 Ψ U,
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Ψ ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U[t1]ᵘ ≈ U[t2]ᵘ) ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 (ce_mod U :: Ψ).
Proof.
  intros * [Hpr (τ' & Hpl) HΨ] HU IHU.
  pose proof (IHU _ _ _ Hpr) as HUr.
  pose proof (IHU _ _ _ Hpl) as HUl.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUl (wf_unit_eq_sym _ _ _ _ _ HUl)) as HU1.
  assert (HΓ1 : ⊢ Θ ⍮ Ξ ⍮ (tele_sub Ψ τ1 ++ Γ') ▹ₘ U[sb_qn (length Ψ) τ1]ᵘ) by (apply wf_ctx_extend_mod; exact HU1).
  pose proof (wf_wk_shift _ _ _ _ HΓ1) as Hφ.
  pose proof (wk_preserves_unit _ _ _ _ _ _ _ HUl Hφ) as HVw.
  rewrite (gunit_wk_sub U τ') in HVw.
  pose proof HVw as HUlw; rewrite gunit_wk_sub in HUlw.
  constructor; cbn [tele_sub List.app length sb_qn centry_sub].
  - exact (sub_pair_q_mod _ _ _ _ _ _ _ Hpr HU HUr).
  - exists (sb_wk τ' ↑ ,,ₘ me_lit U[sb_wk τ' ↑]ᵘ).
    eapply sub_pair_mod_inline;
      [ exact (sub_pair_wk _ _ _ _ _ _ _ _ Hpl Hφ) | exact HU | exact HVw | exact HUlw | constructor ].
  - eapply wf_ext_eq_mod; [ exact HΨ | apply wf_unit_eq_sym; exact HUr | exact HU1 ].
Qed.

(** A definition with a module part more: as a definition and a module
    slot at once ([sub_pair_q_dm], [sub_pair_dm_inline]). *)
Lemma ext_pair_dm : forall Θ Ξ Γ' Γ τ1 τ2 Ψ A M E i,
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Ψ ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ A[t1] ≈ A[t2] : Typeω@i[t2]) ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ M[t1] ≈ M[t2] : A[t2]) ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ (gu_mk nil (md_alias E))[t1]ᵘ ≈ (gu_mk nil (md_alias E))[t2]ᵘ) ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 (ce_dm A M (gu_mk nil (md_alias E)) :: Ψ).
Proof.
  intros * [Hpr (τ' & Hpl) HΨ] HA HM HU IHA IHM IHU.
  pose proof (IHA _ _ _ Hpr) as HAr; cbn [exp_sub] in HAr.
  pose proof (IHA _ _ _ Hpl) as HAl; cbn [exp_sub] in HAl.
  pose proof (IHM _ _ _ Hpr) as HMr.
  pose proof (IHM _ _ _ Hpl) as HMl.
  pose proof (IHU _ _ _ Hpr) as HUr.
  pose proof (IHU _ _ _ Hpl) as HUl.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ HUl (wf_unit_eq_sym _ _ _ _ _ HUl)) as HU1.
  pose proof (wf_unit_eq_trans _ _ _ _ _ _ (wf_unit_eq_sym _ _ _ _ _ HUr) HUr) as HU2.
  pose proof (HMl) as HMl'; apply presup_exp_eq_left in HMl'.
  pose proof (tr_conv_back _ _ _ _ _ _ _ HMl' HAl ltac:(constructor)) as HM1.
  assert (HΓ0 : ⊢ Θ ⍮ Ξ ⍮ (Ψ ++ Γ) ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) by (eapply wf_ctx_extend_dm; eassumption).
  (** the two moved-to contexts: their units, once pushed in, are aliases
      again *)
  assert (HΓ2 : ⊢ Θ ⍮ Ξ ⍮ (tele_sub Ψ τ2 ++ Γ') ▸ₘ A[sb_qn (length Ψ) τ2] ≔ M[sb_qn (length Ψ) τ2]
                  ‖ (gu_mk nil (md_alias E))[sb_qn (length Ψ) τ2]ᵘ).
  { rewrite gunit_sub_mk; cbn [tele_sub moddef_sub length sb_qn].
    rewrite !gunit_sub_mk in HU2; cbn [tele_sub moddef_sub length sb_qn] in HU2.
    eapply wf_ctx_extend_dm; [ exact (presup_exp_eq_right HAr) | exact (presup_exp_eq_right HMr) | exact HU2 ]. }
  assert (HΓ1 : ⊢ Θ ⍮ Ξ ⍮ (tele_sub Ψ τ1 ++ Γ') ▸ₘ A[sb_qn (length Ψ) τ1] ≔ M[sb_qn (length Ψ) τ1]
                  ‖ (gu_mk nil (md_alias E))[sb_qn (length Ψ) τ1]ᵘ).
  { rewrite gunit_sub_mk; cbn [tele_sub moddef_sub length sb_qn].
    rewrite !gunit_sub_mk in HU1; cbn [tele_sub moddef_sub length sb_qn] in HU1.
    eapply wf_ctx_extend_dm; [ exact (presup_exp_eq_left HAl) | exact HM1 | exact HU1 ]. }
  constructor; cbn [tele_sub List.app length sb_qn centry_sub].
  - eapply sub_pair_q_dm; [ exact Hpr | exact HΓ0 | exact HA | exact HUr | exact HΓ2 ].
  - eexists; eapply sub_pair_dm_inline; [ exact Hpl | exact HΓ0 | exact HΓ1 | exact HAl | exact HMl | exact HUl | exact HUl | exact HA ].
  - rewrite gunit_sub_mk; cbn [tele_sub moddef_sub length sb_qn].
    rewrite !gunit_sub_mk in HUr, HU1; cbn [tele_sub moddef_sub length sb_qn] in HUr, HU1.
    eapply wf_ext_eq_dm;
      [ exact HΨ | exact (presup_exp_eq_right HAr) | apply wf_exp_eq_sym; exact HAr
      | exact (presup_exp_eq_right HMr) | apply wf_exp_eq_sym; exact HMr
      | exact (presup_exp_eq_left HAl) | exact HM1
      | apply wf_unit_eq_sym; exact HUr | exact HU1 ].
Qed.

(** [ext_pairs Θ Ξ Γ' Γ τ1 τ2 X]: every tail of the telescope [X] moves
    along the pair ([ext_pair]).  A body's open is read where the expansion
    so far ends, under a tail of the body's telescope. *)
Definition ext_pairs (Θ : gdeps) (Ξ : gstack) (Γ' Γ : ctx) (τ1 τ2 : sub) (X : ctx) : Prop :=
  forall Z Y, X = Z ++ Y -> ext_pair Θ Ξ Γ' Γ τ1 τ2 Y.

(** The whole telescope is a tail. *)
Lemma ext_pairs_full : forall Θ Ξ Γ' Γ τ1 τ2 X, ext_pairs Θ Ξ Γ' Γ τ1 τ2 X -> ext_pair Θ Ξ Γ' Γ τ1 τ2 X.
Proof. intros * H; exact (H nil X eq_refl). Qed.

(** The empty telescope's only tail. *)
Lemma ext_pairs_nil : forall Θ Ξ Γ' Γ τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 nil.
Proof. intros * Hp [|] Y E; [ cbn in E; subst; exact (ext_pair_nil _ _ _ _ _ _ Hp) | discriminate ]. Qed.

(** An entry more: the whole, or a tail of the rest. *)
Lemma ext_pairs_cons : forall Θ Ξ Γ' Γ τ1 τ2 e X,
    ext_pairs Θ Ξ Γ' Γ τ1 τ2 X -> ext_pair Θ Ξ Γ' Γ τ1 τ2 (e :: X) -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 (e :: X).
Proof.
  intros * HX He [| z Z] Y E; cbn in E; [ subst; exact He |]; injection E as -> E; exact (HX _ _ E).
Qed.

(** A target with no module still being defined has a left image with
    none: the right image has none ([sub_frame_free0]), and the left image
    is convertible to it ([modexp_conv_all], [frame_free_target_conv]). *)
Lemma pair_frame_free : forall Θ Ξ Γ' Γ τ1 τ2 E,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> frame_free_target Θ Ξ Γ E ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ E[τ1]ᵐ ≈ E[τ2]ᵐ ->
    frame_free_target Θ Ξ Γ' E[τ1]ᵐ.
Proof.
  intros * Hr HE Hf IH.
  pose proof (sub_frame_free0 _ _ _ _ _ _ Hr HE Hf) as Hf2.
  destruct modexp_conv_all as (_ & _ & _ & _ & _ & _ & _ & Hc).
  exact (frame_free_target_conv _ _ _ _ _ (wf_sub_dom _ _ _ _ _ Hr) (proj2 (Hc _ _ _ _ _ (wf_me_sym _ _ _ _ _ IH))) Hf2).
Qed.

(** An alias with no parameter across the pair: each image is its
    target's image, by [β]; the left one's target has no module still
    being defined ([pair_frame_free]). *)
Lemma pair_beta_alias0 : forall Θ Ξ Γ' Γ τ1 τ2 E,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> frame_free_target Θ Ξ Γ E ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ E[τ1]ᵐ ≈ E[τ2]ᵐ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ (me_lit (gu_mk nil (md_alias E)))[τ1]ᵐ ≈ (me_lit (gu_mk nil (md_alias E)))[τ2]ᵐ.
Proof.
  intros * Hr HE Hf IH.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ (wf_me_beta_alias0 _ _ _ _ HE Hf) Hr) as H2.
  eapply wf_me_trans; [| eapply wf_me_trans; [ exact IH | apply wf_me_sym; exact H2 ] ].
  cbn [modexp_sub gunit_sub moddef_sub]; apply wf_me_beta_alias0;
    [ exact (wf_modexp_eq_refl_left IH) | exact (pair_frame_free _ _ _ _ _ _ _ Hr HE Hf IH) ].
Qed.

(** Equal literals with an outermost parameter have it at convertible
    types: an argument equal to another at the right one's parameter type
    is at the left one's ([head_conv_arg_mod] along the literals' equal
    denotations). *)
Lemma lit_arg_conv : forall Θ Ξ Γ Δ1 κ1 X1 D1 Δ2 κ2 X2 D2 N1 N2,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ1 ++ ce_ass κ1 X1 :: nil) D1 ≈ gu_mk (Δ2 ++ ce_ass κ2 X2 :: nil) D2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N1 ≈ N2 : X2 ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N1 ≈ N2 : X1.
Proof.
  intros * HU HN.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HU))) as Hv.
  pose proof (wf_me_lit _ _ _ _ _ HU) as HH.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HH) as (_ & (R1 & _ & HR1 & _) & _).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH Hv) as (_ & HK1 & HK2).
  assert (Ht : forall Δ κ X D R, mdenote Θ Ξ Γ (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) R -> desc_ok Θ Ξ Γ R ->
            exists T1, mdesc_mod_tele R = Some (T1 ++ ce_ass κ X :: nil)).
  { intros * Hm Hok; inversion Hm; subst; try (unfold gc_unit in *; cbn in *; discriminate).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
      destruct (udenote_last _ _ _ _ _ _ _ _ Hu) as (R0 & Hu0 & ->);
      exact (desc_ok_mtele_last _ _ _ _ _ _ (udenote_is_mod _ _ _ _ _ _ Hu0) Hok) end. }
  pose proof (modexp_paths_conv _ _ _ _ _ HH) as Hp.
  destruct (proj1 (Hp nil (path_pairs_nil _ _ _ _)) _ HR1) as (R2 & HR2 & Hl).
  unfold path_leaf in Hl; cbn in Hl.
  destruct (Ht _ _ _ _ _ HR1 (HK1 _ HR1)) as (T1 & HT1).
  destruct (Ht _ _ _ _ _ HR2 (HK2 _ HR2)) as (T2 & HT2).
  assert (Hl' : opt_rel (leaf_conv Θ Ξ Γ) (mdesc_mod R2) (mdesc_mod R1))
    by (eapply opt_rel_sym; [| exact Hl ]; intros; apply leaf_conv_sym; assumption).
  destruct (head_conv_arg_mod _ _ _ _ _ _ _ _ _ _ Hl' HT2 (tele_view_last _ _ _) HN) as (T' & B' & T1' & Ht' & Hv' & HN' & _ & _).
  rewrite HT1 in Ht'; injection Ht' as <-; rewrite tele_view_last in Hv'; injection Hv' as <- _.
  exact HN'.
Qed.

(** [β] across the pair, for a literal at any open definition: the left
    image's argument is at the left image's parameter type
    ([lit_arg_conv]), so the left images of both sides are the left image
    of the application and the instantiated literal ([sub_beta_gen]), and
    the applications are equal ([lit_app_cong]). *)
Lemma pair_beta : forall Θ Ξ Γ' Γ τ1 τ2 Δ κ X D N,
    md_open D ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) D ≈ gu_mk (Δ ++ ce_ass κ X :: nil) D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk (Δ ++ ce_ass κ X :: nil) D)[τ1]ᵘ ≈ (gu_mk (Δ ++ ce_ass κ X :: nil) D)[τ2]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ N[τ1] ≈ N[τ2] : X[τ2] ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N)[τ1]ᵐ
                ≈ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N)[τ2]ᵐ /\
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (length Δ) (Id,,N)))))[τ1]ᵐ
                ≈ (me_lit (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (length Δ) (Id,,N)))))[τ2]ᵐ.
Proof.
  intros * HD Hr HU HN IHU IHN.
  replace (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (length Δ) (Id,,N)))) with ((gu_mk Δ D)[Id,,N]ᵘ)
    by (rewrite gunit_sub_mk; reflexivity).
  pose proof IHU as HU'; rewrite !gunit_sub_last in HU'.
  pose proof (lit_arg_conv _ _ _ _ _ _ _ _ _ _ _ _ _ HU' IHN) as HN1.
  pose proof (presup_exp_eq_left HN1) as HN1t.
  assert (Happ : Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N)[τ1]ᵐ
                              ≈ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N)[τ2]ᵐ)
    by (cbn [modexp_sub]; rewrite !gunit_sub_last;
        eapply lit_app_cong; [ exact HU' | exact HN1t | exact HN1 | exact (presup_exp_eq_right IHN) ]).
  split; [ exact Happ |].
  pose proof (sub_beta_gen _ _ _ τ1 _ _ _ _ _ HD (wf_unit_eq_refl_left IHU) HN1t) as B1.
  pose proof (sub_preserves_modexp _ _ _ _ _ _ _ (wf_me_beta _ _ _ _ _ _ _ _ HD HU HN) Hr) as B2.
  eapply wf_me_trans; [ apply wf_me_sym; exact B1 | eapply wf_me_trans; [ exact Happ | exact B2 ] ].
Qed.

(** A body unit's expansion across the pair: the left image's expansion
    is the expansion of the left image ([gm_expand_sub]), equal to it; the
    right image's is the image of the expansion. *)
Lemma pair_unit_expand : forall Θ Ξ Γ' Γ τ1 τ2 Δ Φ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ τ2 : Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_open Δ Φ)[τ1]ᵘ ≈ (gu_open Δ Φ)[τ2]ᵘ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_open Δ (gm_expand Φ))[τ1]ᵘ ≈ (gu_open Δ (gm_expand Φ))[τ2]ᵘ.
Proof.
  intros * Hr HU IH.
  eapply wf_unit_eq_trans;
    [| eapply wf_unit_eq_trans; [ exact IH | exact (sub_preserves_unit _ _ _ _ _ _ _ (wf_unit_eq_expand _ _ _ _ _ HU) Hr) ] ].
  apply wf_unit_eq_sym.
  pose proof (wf_unit_eq_refl_left IH) as H1.
  replace ((gu_open Δ (gm_expand Φ))[τ1]ᵘ)
    with (gu_open (tele_sub Δ τ1) (gm_expand (gmod_sub Φ (sb_qn (List.length Δ) τ1))))
    by (rewrite gunit_sub_mk, gm_expand_sub; reflexivity).
  replace ((gu_open Δ Φ)[τ1]ᵘ) with (gu_open (tele_sub Δ τ1) (gmod_sub Φ (sb_qn (List.length Δ) τ1)))
    in H1 |- * by (rewrite gunit_sub_mk; reflexivity).
  apply wf_unit_eq_expand; exact H1.
Qed.

(** The pair lifted over a telescope of assumptions, from its right
    images: [sub_pair_q] entry by entry. *)
Lemma sub_pair_qn : forall Θ Ξ Γ' Γ τ1 τ2 Ψ,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> all_assumptions Ψ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ ->
    sub_pair Θ Ξ (tele_sub Ψ τ2 ++ Γ') (Ψ ++ Γ) (sb_qn (length Ψ) τ1) (sb_qn (length Ψ) τ2).
Proof.
  intros * Hp; induction Ψ as [| e Ψ IH]; intros Hass HΨ; [ exact Hp |].
  inversion_clear Hass as [| ? ? Hx Hass']; destruct Hx as (κ & A & Hx); subst e.
  cbn [List.app] in HΨ; destruct (ctx_decomp_sort_kind HΨ) as [HΨ' (S & HS & HA)].
  cbn [tele_sub centry_sub List.app length sb_qn].
  exact (sub_pair_q _ _ _ _ _ _ _ _ _ (IH Hass' HΨ') HA HS).
Qed.

(** Equal images of a telescope have equal images of each tail. *)
Lemma tele_sub_tail_eq : forall Θ Ξ Γ' Δ Δa e Δb τ1 τ2,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub Δ τ2 ≈ tele_sub Δ τ1 -> Δ = Δa ++ e :: Δb ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub Δb τ2 ≈ tele_sub Δb τ1.
Proof.
  intros * H ->; rewrite !tele_sub_app in H; cbn [tele_sub] in H.
  apply ext_eq_app_inv in H; [ exact (ext_eq_cons_inv _ _ _ _ _ _ _ H) | rewrite !length_tele_sub; reflexivity ].
Qed.

(** The parameters of a unit across the pair: each image's parameter
    types are of the sorts the parameters are; the left image's are the
    left sides of their hypotheses at the pair lifted over the right
    image of the tail ([sub_pair_qn]), moved to the left image of the
    tail along the images' equation ([ctxsub_ext]). *)
Lemma pair_params : forall Θ Ξ Γ' Γ τ1 τ2 Δ l (PS : nat -> exp),
    sub_pair Θ Ξ Γ' Γ τ1 τ2 -> all_assumptions Δ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub Δ τ2 ≈ tele_sub Δ τ1 ->
    (forall k, parameter_sort l (PS k)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : PS (List.length Δb)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δb ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (PS (List.length Δb))[t2]) ->
    (forall Δa κ T Δb, tele_sub Δ τ1 = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ' ⊢ T : PS (List.length Δb)) /\
    (forall Δa κ T Δb, tele_sub Δ τ2 = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ' ⊢ T : PS (List.length Δb)).
Proof.
  intros * Hp Hass HΔ HPS HT IHT.
  assert (Hx : forall Δa T Δb κ, Δ = Δa ++ ce_ass κ T :: Δb ->
                 Θ ⍮ Ξ ⍮ tele_sub Δb τ2 ++ Γ' ⊢ T[sb_qn (length Δb) τ1] ≈ T[sb_qn (length Δb) τ2] : PS (List.length Δb)).
  { intros * E.
    pose proof (HT _ _ _ _ E) as HT0.
    assert (Hb : all_assumptions Δb) by (subst; apply List.Forall_app in Hass as [_ Hass]; inversion Hass; assumption).
    pose proof (sub_pair_qn _ _ _ _ _ _ _ Hp Hb (presup_exp_ctx HT0)) as Hq.
    pose proof (IHT _ _ _ _ E _ _ _ Hq) as X; rewrite (parameter_sort_sub _ _ _ (HPS _)) in X; exact X. }
  split; intros Δa' κ T' Δb' E'; destruct (tele_sub_split_ass _ _ _ _ _ _ E') as (Δa & T & Δb & E & -> & ->);
    rewrite length_tele_sub; pose proof (Hx _ _ _ _ E) as X.
  - assert (Hb : all_assumptions Δb) by (subst; apply List.Forall_app in Hass as [_ Hass]; inversion Hass; assumption).
    pose proof (ctxsub_ext _ _ _ _ _ (tele_sub_tail_eq _ _ _ _ _ _ _ _ _ HΔ E) (all_assumptions_sub _ _ Hb)) as HId.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ (presup_exp_eq_left X) HId) as Y.
    rewrite !exp_sub_id in Y; exact Y.
  - exact (presup_exp_eq_right X).
Qed.


(** [alias_side Θ Ξ Γ Δ E l PS]: the premises of one side of
    [wf_unit_eq_alias] for the alias of [E] under the parameters [Δ], over
    [Γ], the parameters of the sorts [PS] at the level [l]. *)
Record alias_side (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (E : modexp) (l : nat) (PS : nat -> exp) : Prop := mk_alias_side
  { (** The parameters are assumptions *)
    alias_side_ass : all_assumptions Δ
    (** The parameters form a well-formed extension *)
  ; alias_side_tele : Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ
    (** The target is well formed under them *)
  ; alias_side_target : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
    (** Each parameter's type is of its sort *)
  ; alias_side_params : forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : PS (List.length Δb)
    (** The parameters are types of levels, or the target has no member of
        a type of levels *)
  ; alias_side_levels : exists (lv : bool) Rt, (lv = true -> level_sorted_parameters Δ) /\
      (lv = false -> mdenote Θ Ξ (Δ ++ Γ) E Rt) /\ (lv = false -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ Rt)
    (** The target is no module still being defined *)
  ; alias_side_frame : frame_free_target Θ Ξ (Δ ++ Γ) E }.

(** Two sides of an alias, their parameters and targets equal: the
    rule. *)
Lemma alias_unit_eq : forall Θ Ξ Γ Δ E Δ' E' l PS,
    alias_side Θ Ξ Γ Δ E l PS -> alias_side Θ Ξ Γ Δ' E' l PS -> (forall k, parameter_sort l (PS k)) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E').
Proof.
  intros * [Ha _ _ HT (lv & Rt & H1 & H2 & H3) Hf] [Ha' _ HE' HT' (lv' & Rt' & H1' & H2' & H3') Hf'] HPS HΔ HE.
  eapply wf_unit_eq_alias with (lv := lv) (lv' := lv') (Rt := Rt) (Rt' := Rt'); eassumption.
Qed.

(** An alias of a literal under parameters, one side: the literal over
    both telescopes. *)
Lemma alias_unit_flatten : forall Θ Ξ Γ Δ Δ' D l PS,
    alias_side Θ Ξ Γ Δ (me_lit (gu_mk Δ' D)) l PS -> (forall k, parameter_sort l (PS k)) ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D.
Proof.
  intros * [Ha HΔ _ HT (lv & Rt & H1 & H2 & H3) Hf] HPS HU.
  eapply wf_unit_eq_flatten with (lv := lv) (Rt := Rt); eassumption.
Qed.

(** [alias_pair Θ Ξ Γ' Δ1 E1 Δ2 E2 l PS]: the two images of an alias
    across a pair, each a side of [wf_unit_eq_alias], with equal
    parameters and targets, the left parameters moved to the right ones
    along the identity. *)
Record alias_pair (Θ : gdeps) (Ξ : gstack) (Γ' Δ1 : ctx) (E1 : modexp) (Δ2 : ctx) (E2 : modexp) (l : nat) (PS : nat -> exp) : Prop :=
  mk_alias_pair
  { (** The left image is a side *)
    alias_pair_left : alias_side Θ Ξ Γ' Δ1 E1 l PS
    (** The right image is a side *)
  ; alias_pair_right : alias_side Θ Ξ Γ' Δ2 E2 l PS
    (** Their parameters are equal *)
  ; alias_pair_tele : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ Δ1 ≈ Δ2
    (** Their targets are equal under the left parameters *)
  ; alias_pair_target : Θ ⍮ Ξ ⍮ Δ1 ++ Γ' ⊢ᵐ E1 ≈ E2
    (** The left parameters' context is the right ones' along the
        identity *)
  ; alias_pair_id : Θ ⍮ Ξ ⍮ Δ1 ++ Γ' ⊢ˢ Id : Δ2 ++ Γ' }.

(** The images of an alias across the pair.  The left image's target is
    moved from the right image of the parameters to the left one
    ([ctxsub_ext]); its lack of a member of a type of levels, when asked,
    is the right image's target's, along their equation
    ([no_level_modexp_conv]). *)
Lemma pair_alias : forall Θ Ξ Γ' Γ τ1 τ2 Δ E l (PS : nat -> exp) (lv : bool) Rt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Δ -> all_assumptions Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ E[t1]ᵐ ≈ E[t2]ᵐ) ->
    (forall k, parameter_sort l (PS k)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : PS (List.length Δb)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δb ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (PS (List.length Δb))[t2]) ->
    (lv = true -> level_sorted_parameters Δ) ->
    (lv = false -> mdenote Θ Ξ (Δ ++ Γ) E Rt) ->
    (lv = false -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ Rt) ->
    frame_free_target Θ Ξ (Δ ++ Γ) E ->
    alias_pair Θ Ξ Γ' (tele_sub Δ τ1) E[sb_qn (length Δ) τ1]ᵐ (tele_sub Δ τ2) E[sb_qn (length Δ) τ2]ᵐ l PS.
Proof.
  intros * Hp [Hpr _ HΔ] Hass HE IHE HPS HT IHT Hlv Hm Hn Hf.
  pose proof (sub_pair_right _ _ _ _ _ _ Hpr) as Hσq.
  pose proof (IHE _ _ _ Hpr) as X.
  pose proof (all_assumptions_sub _ τ1 Hass) as Hass1.
  pose proof (all_assumptions_sub _ τ2 Hass) as Hass2.
  pose proof (ctxsub_ext _ _ _ _ _ HΔ Hass2) as HId.
  assert (HE12 : Θ ⍮ Ξ ⍮ tele_sub Δ τ1 ++ Γ' ⊢ᵐ E[sb_qn (length Δ) τ1]ᵐ ≈ E[sb_qn (length Δ) τ2]ᵐ)
    by (pose proof (sub_preserves_modexp _ _ _ _ _ _ _ X HId) as Y; rewrite !modexp_sub_id in Y; exact Y).
  destruct (pair_params _ _ _ _ _ _ _ _ _ Hp Hass HΔ HPS HT IHT) as [HT1 HT2].
  (** the left image's target with no member of a type of levels, when asked *)
  assert (Hnl1 : lv = false -> exists Rt1, mdenote Θ Ξ (tele_sub Δ τ1 ++ Γ') E[sb_qn (length Δ) τ1]ᵐ Rt1 /\
                                           Θ ⍮ Ξ ⍮ tele_sub Δ τ1 ++ Γ' ⊢ⁿˡ Rt1).
  { intros Hl.
    pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HE (Hm Hl) Hσq) as Hm2.
    pose proof (sub_preserves_no_level _ _ _ _ _ _ (Hn Hl) Hσq) as Hn2.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ (wf_modexp_eq_refl_left X))
      as (_ & (R1 & _ & HR1 & _) & _).
    pose proof (no_level_modexp_conv _ _ _ _ _ _ _ X HR1 Hm2 Hn2) as Hn1.
    exists (mdesc_sub R1 Id); split.
    - pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ (wf_modexp_eq_refl_left X) HR1 HId) as Y; rewrite modexp_sub_id in Y; exact Y.
    - exact (sub_preserves_no_level _ _ _ _ _ _ Hn1 HId). }
  pose proof (ext_eq_sym_ass _ _ _ _ _ Hass2 HΔ) as HΔ12.
  assert (HΔ1 : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub Δ τ1 ≈ tele_sub Δ τ1)
    by (eapply ext_eq_trans_ass; [ exact Hass1 | exact Hass2 | exact HΔ12 | exact HΔ ]).
  assert (HΔ2 : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub Δ τ2 ≈ tele_sub Δ τ2)
    by (eapply ext_eq_trans_ass; [ exact Hass2 | exact Hass1 | exact HΔ | exact HΔ12 ]).
  constructor; [ constructor | constructor | exact HΔ12 | exact HE12 | exact HId ].
  - exact Hass1.
  - exact HΔ1.
  - exact (wf_modexp_eq_refl_left HE12).
  - exact HT1.
  - destruct lv.
    + exists true, Rt; split; [ intros _; apply level_sorted_parameters_sub; exact (Hlv eq_refl) | split; discriminate ].
    + destruct (Hnl1 eq_refl) as (Rt1 & HRt1 & HnRt1).
      exists false, Rt1; split; [ discriminate | split; intros _; assumption ].
  - pose proof (pair_frame_free _ _ _ _ _ _ _ Hσq HE Hf X) as Hf1.
    pose proof (sub_frame_free0 _ _ _ _ _ _ HId (wf_modexp_eq_refl_left X) Hf1) as Y; rewrite modexp_sub_id in Y; exact Y.
  - exact Hass2.
  - exact HΔ2.
  - exact (wf_modexp_eq_refl_right X).
  - exact HT2.
  - destruct lv.
    + exists true, Rt; split; [ intros _; apply level_sorted_parameters_sub; exact (Hlv eq_refl) | split; discriminate ].
    + exists false, (mdesc_sub Rt (sb_qn (length Δ) τ2)); split; [ discriminate | split; intros _ ].
      * exact (wf_sub_mdenote _ _ _ _ _ _ _ _ HE (Hm eq_refl) Hσq).
      * exact (sub_preserves_no_level _ _ _ _ _ _ (Hn eq_refl) Hσq).
  - exact (sub_frame_free0 _ _ _ _ _ _ Hσq HE Hf).
Qed.

(** An alias unit across the pair: the rule at the two images
    ([pair_alias]). *)
Corollary pair_unit_alias : forall Θ Ξ Γ' Γ τ1 τ2 Δ E l (PS : nat -> exp) (lv : bool) Rt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Δ -> all_assumptions Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ E[t1]ᵐ ≈ E[t2]ᵐ) ->
    (forall k, parameter_sort l (PS k)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : PS (List.length Δb)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δb ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (PS (List.length Δb))[t2]) ->
    (lv = true -> level_sorted_parameters Δ) ->
    (lv = false -> mdenote Θ Ξ (Δ ++ Γ) E Rt) ->
    (lv = false -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ Rt) ->
    frame_free_target Θ Ξ (Δ ++ Γ) E ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk Δ (md_alias E))[τ1]ᵘ ≈ (gu_mk Δ (md_alias E))[τ2]ᵘ.
Proof.
  intros * Hp HX Hass HE IHE HPS HT IHT Hlv Hm Hn Hf.
  destruct (pair_alias _ _ _ _ _ _ _ _ _ _ _ _ Hp HX Hass HE IHE HPS HT IHT Hlv Hm Hn Hf) as [HL HR HΔ HE12 _].
  rewrite !gunit_sub_mk; cbn [moddef_sub].
  exact (alias_unit_eq _ _ _ _ _ _ _ _ _ HL HR HPS HΔ HE12).
Qed.

(** An alias of a literal across the pair, both sides: the alias by
    [pair_alias]; the literal over both telescopes is the alias at each
    image by [wf_unit_eq_flatten], the left one's literal moved to the
    left parameters along the identity. *)
Lemma pair_unit_flatten : forall Θ Ξ Γ' Γ τ1 τ2 Δ Δ' D l (PS : nat -> exp) (lv : bool) Rt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ -> all_assumptions Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
    (forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ (gu_mk Δ' D)[t1]ᵘ ≈ (gu_mk Δ' D)[t2]ᵘ) ->
    (forall k, parameter_sort l (PS k)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : PS (List.length Δb)) ->
    (forall Δa κ T Δb, Δ = Δa ++ ce_ass κ T :: Δb ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δb ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (PS (List.length Δb))[t2]) ->
    (lv = true -> level_sorted_parameters Δ) ->
    (lv = false -> mdenote Θ Ξ (Δ ++ Γ) (me_lit (gu_mk Δ' D)) Rt) ->
    (lv = false -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ Rt) ->
    frame_free_target Θ Ξ (Δ ++ Γ) (me_lit (gu_mk Δ' D)) ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[τ1]ᵘ ≈ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[τ2]ᵘ /\
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk (Δ' ++ Δ) D)[τ1]ᵘ ≈ (gu_mk (Δ' ++ Δ) D)[τ2]ᵘ.
Proof.
  intros * Hp HX HΔΔ Hass HV IHV HPS HT IHT Hlv Hm Hn Hf.
  assert (IHE : forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
                  Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ (me_lit (gu_mk Δ' D))[t1]ᵐ ≈ (me_lit (gu_mk Δ' D))[t2]ᵐ)
    by (intros * Hq; cbn [modexp_sub]; apply wf_me_lit; exact (IHV _ _ _ Hq)).
  pose proof (wf_me_lit _ _ _ _ _ HV) as HE.
  destruct (pair_alias _ _ _ _ _ _ _ _ _ _ _ _ Hp HX Hass HE IHE HPS HT IHT Hlv Hm Hn Hf) as [HL HR HΔ HE12 HId].
  assert (Hal : Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[τ1]ᵘ ≈ (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[τ2]ᵘ)
    by (rewrite !gunit_sub_mk; cbn [moddef_sub]; exact (alias_unit_eq _ _ _ _ _ _ _ _ _ HL HR HPS HΔ HE12)).
  split; [ exact Hal |].
  (** each image of the literal over both telescopes is the image of the alias *)
  assert (Ef : forall τ, (gu_mk (Δ' ++ Δ) D)[τ]ᵘ
                         = gu_mk (tele_sub Δ' (sb_qn (length Δ) τ) ++ tele_sub Δ τ) (moddef_sub D (sb_qn (length Δ') (sb_qn (length Δ) τ))))
    by (intros; rewrite gunit_sub_mk, tele_sub_app, List.length_app, sb_qn_plus; reflexivity).
  assert (Ea : forall τ, (gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))))[τ]ᵘ
                         = gu_mk (tele_sub Δ τ) (md_alias (me_lit (gu_mk (tele_sub Δ' (sb_qn (length Δ) τ))
                                                                           (moddef_sub D (sb_qn (length Δ') (sb_qn (length Δ) τ)))))))
    by (intros; rewrite gunit_sub_mk; cbn [moddef_sub modexp_sub]; rewrite gunit_sub_mk; reflexivity).
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  assert (H0 : Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D)
    by (eapply wf_unit_eq_flatten with (lv := lv) (Rt := Rt); eassumption).
  pose proof (sub_preserves_unit _ _ _ _ _ _ _ H0 Hr) as H2.
  rewrite Ea, Ef in H2.
  (** the left image's literal, under the left parameters *)
  pose proof (IHV _ _ _ (ext_pair_right _ _ _ _ _ _ _ HX)) as HV12.
  pose proof (sub_preserves_unit _ _ _ _ _ _ _ (wf_unit_eq_refl_left HV12) HId) as HV1; rewrite !gunit_sub_id in HV1.
  rewrite gunit_sub_mk in HV1.
  cbn [modexp_sub] in HL; rewrite gunit_sub_mk in HL.
  pose proof (alias_unit_flatten _ _ _ _ _ _ _ _ HL HPS HV1) as H1.
  rewrite !Ea in Hal.
  rewrite !Ef; eapply wf_unit_eq_trans; [ apply wf_unit_eq_sym; exact H1 |].
  eapply wf_unit_eq_trans; [ exact Hal | exact H2 ].
Qed.

(** ** The Expansion of a Body Across a Pair *)

(** [gen_retyped g g']: [g'] is the generated item [g] with the type of its
    term part, if it has one, replaced, as [gentry_retyped] is for
    entries. *)
Inductive gen_retyped : generated_item -> generated_item -> Prop :=
(** A definition, at any type *)
| gen_retyped_def : forall d pv r A A' M, gen_retyped (generated_item_def d pv r A M) (generated_item_def d pv r A' M)
(** An alias, as it is *)
| gen_retyped_alias : forall d pv E, gen_retyped (generated_item_alias d pv E) (generated_item_alias d pv E)
(** A definition with a module part, at any type *)
| gen_retyped_def_mod : forall d pv A A' M E,
    gen_retyped (generated_item_def_mod d pv A M E) (generated_item_def_mod d pv A' M E).

(** Items related one by one append related entries. *)
Lemma gens_append_retyped : forall gs gs' Φ Φ' k, List.Forall2 gen_retyped gs gs' -> gmod_retyped Φ Φ' ->
    gmod_retyped (gens_append Φ k gs) (gens_append Φ' k gs').
Proof.
  induction gs as [| g gs IH]; intros * H HΦ; inversion H as [| ? g' ? gs'' Hg Hgs]; subst; cbn [gens_append]; [ exact HΦ |].
  destruct Hg; cbn [generated_item_entry]; apply IH; try exact Hgs; constructor; try exact HΦ; apply gentry_retyped_wk; constructor.
Qed.

(** [sel_class X X1]: [X1] is a description of the same class as [X] for
    an open's items ([items_gen]): a term of the same kind, a module, or a
    term part with a module part. *)
Record sel_class (X X1 : mdesc) : Prop := mk_sel_class
  { (** A term is one of the same kind *)
    sel_class_term : forall r A om, X = mdesc_term r A om -> exists A1 om1, X1 = mdesc_term r A1 om1
    (** A module is one *)
  ; sel_class_mod : mdesc_is_mod X -> mdesc_is_mod X1
    (** A term part with a module part is one *)
  ; sel_class_dm : forall A Rm, mdesc_type X = Some A -> mdesc_mod X = Some Rm ->
      exists A1 Rm1, mdesc_type X1 = Some A1 /\ mdesc_mod X1 = Some Rm1 }.

(** [term_or_mod R]: a description with no module part is a term: no
    definition with a module part has a module part with none. *)
Definition term_or_mod (R : mdesc) : Prop := mdesc_mod R = None -> exists r A om, R = mdesc_term r A om.

(** A description with a module part keeps one given an argument. *)
Lemma mdesc_at_mod_some : forall R N R', mdesc_mod R <> None -> mdesc_at R N = Some R' -> mdesc_mod R' <> None.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ' p T Φ Ns | Θd A M Rm IH]; intros * Hm Ha; cbn in Hm, Ha |- *.
  - contradiction.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] |]; [ injection Ha as <-; cbn; discriminate | discriminate ].
  - destruct (tele_split (rev Θ')) as [[[? ?] ?] |]; injection Ha as <-; cbn; discriminate.
  - destruct (mdesc_at Rm N) as [Rm' |] eqn:E; [| discriminate ].
    destruct (tele_split (rev Θd)) as [[[? ?] ?] |]; injection Ha as <-; cbn; exact (IH _ _ Hm E).
Qed.

(** [term_or_mod] given an argument. *)
Lemma term_or_mod_at : forall R N R', term_or_mod R -> mdesc_at R N = Some R' -> term_or_mod R'.
Proof.
  intros [r A om | Δ Φ Φx | Θ' p T Φ Ns | Θd A M Rm] * Ht Ha HR'.
  - cbn in Ha; destruct (pi_view A) as [[? C] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; eauto.
  - exfalso; refine (mdesc_at_mod_some _ _ _ _ Ha HR'); cbn; discriminate.
  - exfalso; refine (mdesc_at_mod_some _ _ _ _ Ha HR'); cbn; discriminate.
  - exfalso; refine (mdesc_at_mod_some _ _ _ _ Ha HR'); cbn; intros Hn.
    destruct (Ht Hn) as (? & ? & ? & [=]).
Qed.

(** [term_or_mod] given arguments. *)
Lemma term_or_mod_ats : forall Ns R R', term_or_mod R -> mdesc_ats R Ns = Some R' -> term_or_mod R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Ht Ha; cbn in Ha; [ injection Ha as <-; exact Ht |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ]; exact (IH _ _ (term_or_mod_at _ _ _ Ht E) Ha).
Qed.

(** A module part, given arguments, is one. *)
Lemma mdesc_ats_mod_some : forall Ns R R', mdesc_mod R <> None -> mdesc_ats R Ns = Some R' -> mdesc_mod R' <> None.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha; [ injection Ha as <-; exact Hm |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ]; exact (IH _ _ (mdesc_at_mod_some _ _ _ Hm E) Ha).
Qed.

(** [term_or_mod] as an entry's description is read. *)
Lemma term_or_mod_read : forall rd R R', term_or_mod R -> mdesc_read rd R = Some R' -> term_or_mod R'.
Proof.
  intros [Δ Φ' | Θ' Ns M] * Ht Hr; cbn in Hr.
  - destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    intros Hn; rewrite mdesc_mod_up in Hn.
    destruct (mdesc_mod (mdesc_sub R σ)) eqn:E; cbn in Hn; [ discriminate |].
    assert (HR : mdesc_mod R = None) by (destruct (mdesc_mod R) eqn:E0; [ rewrite (mdesc_mod_sub _ _ σ E0) in E; discriminate | reflexivity ]).
    destruct (Ht HR) as (r & A & om & ->); cbn; eauto.
  - destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Ea; cbn in Hr; [ injection Hr as <- | discriminate ].
    assert (Ht1 : term_or_mod R1).
    { destruct R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns0 | [| ? ?] A M0 Rm]; cbn in Ea;
        try exact (term_or_mod_ats _ _ _ Ht Ea).
      destruct (mdesc_term_part_ats (mdesc_term ak_relevant A (Some M0)) Ns) as [[? ? [?|] | | |] |]; cbn in Ea;
        try discriminate Ea.
      destruct (mdesc_ats Rm Ns) as [Rm' |] eqn:E'; [ injection Ea as <- | discriminate Ea ].
      intros Hn; exfalso; refine (mdesc_ats_mod_some _ _ _ _ E' Hn).
      intros Hn0; destruct (Ht Hn0) as (? & ? & ? & [=]). }
    intros Hn; rewrite mdesc_mod_up in Hn.
    destruct (mdesc_mod (mdesc_named Θ' Ns M R1)) eqn:E; cbn in Hn; [ discriminate |].
    assert (HR1 : mdesc_mod R1 = None)
      by (destruct Θ', Ns; first [ exact E | destruct R1 as [| | | ? ? ? ?]; cbn in E |- *; first [ reflexivity | discriminate | exact E ] ]).
    destruct (Ht1 HR1) as (r & A & om & ->).
    destruct (mdesc_named_term Θ' Ns M r A om) as [om' ->]; cbn; eauto.
Qed.

(** What anything denotes, and the descriptions of entries, are terms when
    they have no module part. *)
Lemma term_or_mod_all : forall Θ Ξ,
    (forall Γ H R, mdenote Θ Ξ Γ H R -> term_or_mod R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> mdesc_is_mod R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> term_or_mod R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> True).
Proof.
  intros Θ Ξ; apply mdenote_all_ind; intros; try exact I; unfold term_or_mod, ind_former_desc, record_former_desc in *.
  all: try (intros Hn; cbn in Hn; discriminate).
  all: try (match goal with Hm : mdesc_is_mod ?R |- mdesc_mod ?R = None -> _ =>
              intros Hn; rewrite (mdesc_is_mod_mod _ Hm) in Hn; discriminate end).
  all: try (match goal with Hm : mdesc_is_mod ?R |- mdesc_mod (mdesc_dm _ _ _ ?R) = None -> _ =>
              intros Hn; cbn in Hn; rewrite (mdesc_is_mod_mod _ Hm) in Hn; discriminate end).
  all: try solve [ eapply term_or_mod_at; eassumption | eapply term_or_mod_read; eassumption | intros; eauto ].
  - match goal with He : mdesc_body _ ?sm _ _ _ = Some _ |- _ =>
      destruct sm; cbn in He; [ injection He as <-; exact I | destruct o; cbn in He; [ injection He as <-; exact I | discriminate ] ] end.
  - apply mdesc_is_mod_up; eapply mdesc_mod_is_mod; eassumption.
Qed.

(** Descriptions showing the same are of the same class, the left one
    being a term when it has no module part. *)
Lemma sel_class_of_leaf : forall Θ Ξ Γ X X1, term_or_mod X1 -> leaf_conv Θ Ξ Γ X1 X -> sel_class X X1.
Proof.
  intros * HX1 [Hk Ht _ Hu _ _ _]; constructor.
  - intros r A om ->; cbn in Hk, Ht, Hu.
    destruct (mdesc_mod X1) eqn:Em; cbn in Hu; [ contradiction |].
    destruct (HX1 Em) as (r1 & A1 & om1 & ->); cbn in Hk; subst; eauto.
  - intros Hm; destruct X as [| | | ]; cbn in Hm; try contradiction;
      destruct X1 as [r1 A1 om1 | | | Θd A1 M1 Rm1]; cbn in Ht, Hu |- *; try contradiction; auto.
  - intros A Rm HA HRm; rewrite HA in Ht; rewrite HRm in Hu.
    destruct (mdesc_type X1) as [A1 |]; cbn in Ht; [| contradiction ].
    destruct (mdesc_mod X1) as [Rm1 |]; cbn in Hu; [ eauto | contradiction ].
Qed.

(** The class of a description is its substitution's. *)
Lemma sel_class_sub : forall X σ, sel_class X (mdesc_sub X σ).
Proof.
  intros; constructor.
  - intros r A om ->; cbn; eauto.
  - intros Hm; exact (mdesc_is_mod_sub _ _ Hm).
  - intros A Rm HA HRm; rewrite (mdesc_type_sub _ _ σ HA), (mdesc_mod_sub _ _ σ HRm); eauto.
Qed.

(** Classes chained. *)
Lemma sel_class_trans : forall X X1 X2, sel_class X X1 -> sel_class X1 X2 -> sel_class X X2.
Proof.
  intros * [H1 H2 H3] [H1' H2' H3']; constructor.
  - intros * E; destruct (H1 _ _ _ E) as (A1 & om1 & E1); exact (H1' _ _ _ E1).
  - auto.
  - intros * HA HRm; destruct (H3 _ _ HA HRm) as (A1 & Rm1 & HA1 & HRm1); exact (H3' _ _ HA1 HRm1).
Qed.

(** The items of an open of [H] generated again from [H[σ1]] read in
    another context, its selections of the same classes: the same items up
    to the types of their term parts. *)
Lemma items_gen_pair : forall Θ Ξ G G1 H its gs σ1,
    items_gen Θ Ξ G H its gs ->
    (forall n X, mdenote Θ Ξ G (me_mem H n) X -> exists X1, mdenote Θ Ξ G1 (me_mem H[σ1]ᵐ n) X1 /\ sel_class X X1) ->
    exists gs1, items_gen Θ Ξ G1 H[σ1]ᵐ its gs1 /\ List.Forall2 gen_retyped gs1 (List.map (fun g => generated_item_sub g σ1) gs).
Proof.
  induction 1 as [G H | G H d pv its gs Hg IH | G H n d pv r A om its gs Hm Hg IH | G H n d pv R its gs Hm HR Hg IH
                 | G H n d pv R A Rm its gs Hm HA HRm Hg IH]; intros Hsel.
  - exists nil; split; constructor.
  - destruct (IH Hsel) as (gs1 & Hg1 & Hr); exists (generated_item_alias d pv H[σ1]ᵐ :: gs1); split;
      [ constructor; exact Hg1 | constructor; [ constructor | exact Hr ] ].
  - destruct (IH Hsel) as (gs1 & Hg1 & Hr); destruct (Hsel _ _ Hm) as (X1 & HX1 & Hc).
    destruct (sel_class_term _ _ Hc _ _ _ eq_refl) as (A1 & om1 & ->).
    exists (generated_item_def d pv r A1 (a_mem H[σ1]ᵐ n) :: gs1); split;
      [ econstructor; eassumption | constructor; [ cbn; constructor | exact Hr ] ].
  - destruct (IH Hsel) as (gs1 & Hg1 & Hr); destruct (Hsel _ _ Hm) as (X1 & HX1 & Hc).
    exists (generated_item_alias d pv (me_mem H[σ1]ᵐ n) :: gs1); split;
      [ eapply items_gen_mod; [ exact HX1 | exact (sel_class_mod _ _ Hc HR) | exact Hg1 ] | constructor; [ cbn; constructor | exact Hr ] ].
  - destruct (IH Hsel) as (gs1 & Hg1 & Hr); destruct (Hsel _ _ Hm) as (X1 & HX1 & Hc).
    destruct (sel_class_dm _ _ Hc _ _ HA HRm) as (A1 & Rm1 & HA1 & HRm1).
    exists (generated_item_def_mod d pv A1 (a_mem H[σ1]ᵐ n) (me_mem H[σ1]ᵐ n) :: gs1); split;
      [ econstructor; eassumption | constructor; [ cbn; constructor | exact Hr ] ].
Qed.

(** [open_pair Θ Ξ G G1 H σ1]: the target [H] of an open, read in [G],
    has an image [H[σ1]] in [G1] that denotes a module and selects what
    [H] does, of the same classes. *)
Record open_pair (Θ : gdeps) (Ξ : gstack) (G G1 : ctx) (H : modexp) (σ1 : sub) : Prop := mk_open_pair
  { (** The image denotes a module *)
    open_pair_target : exists R1 Rm1, mdenote Θ Ξ G1 H[σ1]ᵐ R1 /\ mdesc_mod R1 = Some Rm1
    (** Its selections are of the classes of the target's *)
  ; open_pair_sel : forall n X, mdenote Θ Ξ G (me_mem H n) X ->
      exists X1, mdenote Θ Ξ G1 (me_mem H[σ1]ᵐ n) X1 /\ sel_class X X1 }.

(** An image equal to the target's image under a well-typed substitution:
    that image selects what the target does, moved ([mdenote_sub_all]),
    and the equal image what that one does, showing the same
    ([modexp_paths_conv]). *)
Lemma open_pair_of : forall Θ Ξ G G1 H σ1 τ,
    Θ ⍮ Ξ ⍮ G ⊢ᵐ H ≈ H -> Θ ⍮ Ξ ⍮ G1 ⊢ˢ τ : G -> Θ ⍮ Ξ ⍮ G1 ⊢ᵐ H[σ1]ᵐ ≈ H[τ]ᵐ -> open_pair Θ Ξ G G1 H σ1.
Proof.
  intros * HH Hτ Heq.
  pose proof (ctx_wf_gctx _ _ _ (wf_sub_dom _ _ _ _ _ Hτ)) as Hg.
  constructor.
  - exact (me_denotes _ _ _ _ _ Heq).
  - intros n X HX.
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HX Hτ) as HXτ.
    destruct (modexp_eq_mem_left _ _ _ _ _ _ _ Heq HXτ) as (X1 & HX1 & Hl).
    exists X1; split; [ exact HX1 |].
    exact (sel_class_trans _ _ _ (sel_class_sub X τ)
             (sel_class_of_leaf _ _ _ _ _ (proj1 (term_or_mod_all Θ Ξ) _ _ _ HX1) Hl)).
Qed.

(** A body expanded across the pair: the left image of the body expands
    to the left image of the expansion, each open's target's image
    denoting a module and selecting what the target does, of the same
    classes, so generating the stored entries ([items_gen_pair]). *)
Lemma body_xp_pair : forall Θ Ξ G0 G1 Φ Φx σ,
    body_xp Θ Ξ G0 Φ Φx ->
    (forall Ψ H, In (Ψ, H) (body_opens Φ Φx) -> open_pair Θ Ξ (Ψ ++ G0) (tele_sub Ψ σ ++ G1) H (sb_qn (length Ψ) σ)) ->
    body_xp Θ Ξ G1 (gmod_sub Φ σ) (gmod_sub Φx σ).
Proof.
  induction 1 as [G0 | G0 Φ Φx x E Hx IH | G0 Φ Φx H its Φg R Rm gs Hx IH HR HRm Hg Hok Hr]; intros HO.
  - constructor.
  - cbn [gmod_sub]; rewrite (body_xp_binders _ _ _ _ _ Hx); constructor; apply IH.
    intros Ψ H HI; apply HO; cbn [body_opens gm_dropn]; exact HI.
  - rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg Hr) in HO.
    pose proof (HO _ _ (or_introl eq_refl)) as [(R1 & Rm1 & HR1 & HRm1) Hsel].
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hnx.
    rewrite (length_body_ctx _ Hnx), (body_xp_binders _ _ _ _ _ Hx) in HR1, Hsel.
    rewrite <- (body_ctx_sub _ _ Hnx) in HR1, Hsel.
    destruct (items_gen_pair _ _ _ _ _ _ _ _ Hg Hsel) as (gs1 & Hg1 & Hgs1).
    cbn [gmod_sub]; rewrite gm_graft_sub, (body_xp_binders _ _ _ _ _ Hx).
    eapply body_xp_open; [ apply IH; intros Ψ H0 HI; exact (HO _ _ (or_intror HI)) | exact HR1 | exact HRm1 | exact Hg1 | exact Hok |].
    eapply gmod_retyped_trans; [ apply gens_append_retyped; [ exact Hgs1 | constructor ] |].
    pose proof (gmod_retyped_sub _ _ (sb_qn (gm_binders Φ) σ) Hr) as X.
    unfold gens_body in X; rewrite gens_append_sub in X by (cbn; lia); cbn [gmod_sub gm_binders] in X.
    replace (0 - 0) with 0 in X by lia; cbn [sb_qn] in X; exact X.
Qed.

(** ** Body Units Across a Pair *)

(** Judgments moved along the identity between two contexts. *)
Lemma exp_id_move : forall Θ Ξ Γ1 Γ2 M A, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 -> Θ ⍮ Ξ ⍮ Γ2 ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ1 ⊢ M : A.
Proof. intros * HId H; pose proof (sub_preserves_exp _ _ _ _ _ _ _ H HId) as X; rewrite !exp_sub_id in X; exact X. Qed.

Lemma exp_eq_id_move : forall Θ Ξ Γ1 Γ2 M N A, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 -> Θ ⍮ Ξ ⍮ Γ2 ⊢ M ≈ N : A -> Θ ⍮ Ξ ⍮ Γ1 ⊢ M ≈ N : A.
Proof. intros * HId H; pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ H HId) as X; rewrite !exp_sub_id in X; exact X. Qed.

Lemma unit_id_move : forall Θ Ξ Γ1 Γ2 U V, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 -> Θ ⍮ Ξ ⍮ Γ2 ⊢ᵘ U ≈ V -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵘ U ≈ V.
Proof. intros * HId H; pose proof (sub_preserves_unit _ _ _ _ _ _ _ H HId) as X; rewrite !gunit_sub_id in X; exact X. Qed.

Lemma modexp_id_move : forall Θ Ξ Γ1 Γ2 H K, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 -> Θ ⍮ Ξ ⍮ Γ2 ⊢ᵐ H ≈ K -> Θ ⍮ Ξ ⍮ Γ1 ⊢ᵐ H ≈ K.
Proof. intros * HId H0; pose proof (sub_preserves_modexp _ _ _ _ _ _ _ H0 HId) as X; rewrite !modexp_sub_id in X; exact X. Qed.

(** The identity under a telescope. *)
Lemma id_under : forall Θ Ξ Ψ Γ1 Γ2, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ2 ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ1 ⊢ˢ sb_qn (length Ψ) Id : Ψ ++ Γ2.
Proof.
  intros * HId HΨ; pose proof (wf_sub_ext _ _ _ _ _ _ HId (ctx_sub_wf_gen _ _ _ _ _ _ HId HΨ) HΨ) as X.
  rewrite tele_sub_id in X; exact X.
Qed.

(** Module expressions moved along the identity under a telescope. *)
Lemma modexp_id_move_under : forall Θ Ξ Ψ Γ1 Γ2 H K, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ2 ⊢ᵐ H ≈ K -> Θ ⍮ Ξ ⍮ Ψ ++ Γ1 ⊢ᵐ H ≈ K.
Proof.
  intros * HId H0; pose proof (sub_preserves_modexp _ _ _ _ _ _ _ H0 (id_under _ _ _ _ _ HId (presup_modexp_eq_ctx H0))) as X.
  rewrite !(modexp_sub_sb_eq _ (sb_qn (length Ψ) Id) Id (sb_qn_id_ext _ _ (fun _ => eq_refl))), !modexp_sub_id in X; exact X.
Qed.

(** A target with no module still being defined, moved alike. *)
Lemma frame_free_id_move_under : forall Θ Ξ Ψ Γ1 Γ2 E, Θ ⍮ Ξ ⍮ Γ1 ⊢ˢ Id : Γ2 ->
    Θ ⍮ Ξ ⍮ Ψ ++ Γ2 ⊢ᵐ E ≈ E -> frame_free_target Θ Ξ (Ψ ++ Γ2) E -> frame_free_target Θ Ξ (Ψ ++ Γ1) E.
Proof.
  intros * HId HE Hf.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HE) as (_ & HEs & _).
  pose proof (sub_frame_free _ _ _ _ _ _ _ HId (presup_modexp_eq_ctx HE) HEs Hf) as X.
  rewrite tele_sub_id, (modexp_sub_sb_eq _ (sb_qn (length Ψ) Id) Id (sb_qn_id_ext _ _ (fun _ => eq_refl))), modexp_sub_id in X;
    exact X.
Qed.

(** The context an open of a body is read in is a tail of the expansion's. *)
Lemma body_opens_tail : forall Θ Ξ G Φ Φx, body_xp Θ Ξ G Φ Φx ->
    forall Ψ H, In (Ψ, H) (body_opens Φ Φx) -> exists Z, body_ctx Φx = Z ++ Ψ.
Proof.
  induction 1 as [G | G Φ Φx x E Hx IH | G Φ Φx H its Φg R Rm gs Hx IH HR HRm Hg Hok Hr]; intros Ψ H0 HI.
  - contradiction.
  - rewrite body_opens_ext in HI; destruct (IH _ _ HI) as [Z HZ].
    destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx]; rewrite HZ; eexists; rewrite List.app_comm_cons; reflexivity.
  - rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg Hr) in HI.
    rewrite (body_ctx_graft _ _ (open_store_noopen _ _ Hr)).
    destruct HI as [[= <- <-] | HI]; [ eexists; reflexivity |].
    destruct (IH _ _ HI) as [Z ->]; eexists; rewrite List.app_assoc; reflexivity.
Qed.

(** A premise about the definitions of both sides of a body unit, read
    for one side: the other side's entry of the same name exists, filled
    in, by the shape. *)
Lemma tm_left : forall (P : String.string -> gmod -> gentry -> exp -> exp -> sub -> Prop) Φx Φx',
    gm_nopens Φx = 0 -> body_shape Φx Φx' ->
    (forall y Φ0 E A M Φ0' E' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P y Φ0 E A M σf) ->
    forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_fill Φ0 = Some σf -> P y Φ0 E A M σf.
Proof.
  intros * Hn Hs H y Φ0 E A M σf Hp HE Hf.
  destruct (shape_prefix _ _ _ _ _ Hs Hp) as (Φ0' & E' & Hp' & _ & HS).
  destruct (entry_shape_tm _ _ _ _ HS HE) as (A' & M' & HE').
  destruct (body_shape_fill _ _ Hn Hs) as [_ Hf'].
  destruct (fill_prefix _ _ _ _ Hf' Hp') as (σf' & Hσf').
  exact (H _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hσf').
Qed.

(** The same, read for the other side. *)
Lemma tm_right : forall (P : String.string -> gmod -> gentry -> exp -> exp -> sub -> Prop) Φx Φx',
    gm_nopens Φx = 0 -> body_shape Φx Φx' ->
    (forall y Φ0 E A M Φ0' E' A' M' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P y Φ0' E' A' M' σf') ->
    forall y Φ0' E' A' M' σf', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0' = Some σf' -> P y Φ0' E' A' M' σf'.
Proof.
  intros * Hn Hs H y Φ0' E' A' M' σf' Hp' HE' Hf'.
  destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hs) Hp') as (Φ0 & E & Hp & _ & HS).
  destruct (entry_shape_tm _ _ _ _ HS HE') as (A & M & HE).
  destruct (body_shape_fill _ _ Hn Hs) as [Hf0 _].
  destruct (fill_prefix _ _ _ _ Hf0 Hp) as (σf & Hσf).
  exact (H _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσf Hf').
Qed.

(** A premise about the modules of both sides, read for one side. *)
Lemma unit_left : forall (P : String.string -> gmod -> gentry -> gunit -> sub -> Prop) Φx Φx',
    gm_nopens Φx = 0 -> body_shape Φx Φx' ->
    (forall y Φ0 E U Φ0' E' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P y Φ0 E U σf) ->
    forall y Φ0 E U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_fill Φ0 = Some σf -> P y Φ0 E U σf.
Proof.
  intros * Hn Hs H y Φ0 E U σf Hp HE Hf.
  destruct (shape_prefix _ _ _ _ _ Hs Hp) as (Φ0' & E' & Hp' & _ & HS).
  destruct (entry_shape_unit _ _ _ HS HE) as (U' & HE').
  destruct (body_shape_fill _ _ Hn Hs) as [_ Hf'].
  destruct (fill_prefix _ _ _ _ Hf' Hp') as (σf' & Hσf').
  exact (H _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hf Hσf').
Qed.

(** The same, read for the other side. *)
Lemma unit_right : forall (P : String.string -> gmod -> gentry -> gunit -> sub -> Prop) Φx Φx',
    gm_nopens Φx = 0 -> body_shape Φx Φx' ->
    (forall y Φ0 E U Φ0' E' U' σf σf',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P y Φ0' E' U' σf') ->
    forall y Φ0' E' U' σf', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0' = Some σf' -> P y Φ0' E' U' σf'.
Proof.
  intros * Hn Hs H y Φ0' E' U' σf' Hp' HE' Hf'.
  destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hs) Hp') as (Φ0 & E & Hp & _ & HS).
  destruct (entry_shape_unit _ _ _ HS HE') as (U & HE).
  destruct (body_shape_fill _ _ Hn Hs) as [Hf0 _].
  destruct (fill_prefix _ _ _ _ Hf0 Hp) as (σf & Hσf).
  exact (H _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσf Hf').
Qed.

(** A premise about the opens of both sides, filled in, read for one
    side. *)
Lemma opens_left : forall Θ Ξ G G' Φ Φx Φ' Φx' (P : nat -> gmod -> modexp -> sub -> Prop),
    body_xp Θ Ξ G Φ Φx -> body_xp Θ Ξ G' Φ' Φx' -> body_shape Φ Φ' -> body_shape Φx Φx' ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P k Φ0 H σf) ->
    forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf -> P k Φ0 H σf.
Proof.
  intros * Hb Hb' Hs Hsx H k Φ0 H0 σf Hk Hf.
  destruct (body_opens_at_pair _ _ _ _ _ Hb _ _ _ _ _ _ Hb' Hs Hsx Hk) as (Φ0' & H' & Hk' & Hs0 & Hn0).
  destruct (body_shape_fill _ _ Hn0 Hs0) as [_ Hf0'].
  destruct (gm_fill Φ0') as [σf' |] eqn:E'; [| contradiction ].
  exact (H _ _ _ _ _ _ _ Hk Hk' Hf E').
Qed.

(** The same, read for the other side. *)
Lemma opens_right : forall Θ Ξ G G' Φ Φx Φ' Φx' (P : nat -> gmod -> modexp -> sub -> Prop),
    body_xp Θ Ξ G Φ Φx -> body_xp Θ Ξ G' Φ' Φx' -> body_shape Φ Φ' -> body_shape Φx Φx' ->
    (forall k Φ0 H Φ0' H' σf σf',
        List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σf -> gm_fill Φ0' = Some σf' -> P k Φ0' H' σf') ->
    forall k Φ0' H' σf', List.nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') -> gm_fill Φ0' = Some σf' -> P k Φ0' H' σf'.
Proof.
  intros * Hb Hb' Hs Hsx H k Φ0' H' σf' Hk' Hf'.
  destruct (body_opens_at_pair _ _ _ _ _ Hb' _ _ _ _ _ _ Hb (body_shape_sym _ _ Hs) (body_shape_sym _ _ Hsx) Hk')
    as (Φ0 & H0 & Hk & Hs0 & Hn0).
  destruct (body_shape_fill _ _ Hn0 Hs0) as [_ Hf0].
  destruct (gm_fill Φ0) as [σf |] eqn:E; [| contradiction ].
  exact (H _ _ _ _ _ _ _ Hk Hk' E Hf').
Qed.

(** A body unit across the pair, from the premises of one side of
    [wf_unit_eq_body] and their hypotheses: the rule at the two images
    ([unit_body_moved]).  Each premise of the left image is the left side
    of its hypothesis at the pair lifted over the left image of its
    telescope, or at the right lifting moved to the left parameters along
    the identity; the left image expands as the body does
    ([body_xp_pair]); its target has no member of a type of levels when
    the right image's has none, along the equation of the two images with
    no parameter, by the rule again ([no_level_modexp_conv]). *)
Lemma pair_unit_body : forall Θ Ξ Γ' Γ τ1 τ2 Δu Φ Φx (es : String.string -> exp) l ps (lv : bool) Rt,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    body_xp Θ Ξ (Δu ++ Γ) Φ Φx ->
    ext_pair Θ Ξ Γ' Γ τ1 τ2 Δu -> all_assumptions Δu ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δu ≈ body_ctx Φx ++ Δu ->
    ext_pairs Θ Ξ Γ' Γ τ1 τ2 (body_ctx Φx ++ Δu) ->
    (forall y, type_sort (es y)) ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (es y) (entry_kind E)) ->
    (forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σf -> Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ A[σf] : es y) ->
    (forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σf -> forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δu ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ A[σf][t1] ≈ A[σf][t2] : (es y)[t2]) ->
    (forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σf -> Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ M[σf] : A[σf]) ->
    (forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σf -> forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δu ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ M[σf][t1] ≈ M[σf][t2] : A[σf][t2]) ->
    (forall y Φ0 E U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_fill Φ0 = Some σf -> Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵘ U[σf]ᵘ ≈ U[σf]ᵘ) ->
    (forall y Φ0 E U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_fill Φ0 = Some σf -> forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δu ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U[σf]ᵘ[t1]ᵘ ≈ U[σf]ᵘ[t2]ᵘ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δu ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Δu ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[t1]ᵐ ≈ H[t2]ᵐ) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> frame_free_target Θ Ξ (Ψ ++ Δu ++ Γ) H) ->
    (forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf ->
       Θ ⍮ Ξ ⍮ Δu ++ Γ ⊢ᵐ H[σf]ᵐ ≈ H[σf]ᵐ) ->
    (forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δu ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[σf]ᵐ[t1]ᵐ ≈ H[σf]ᵐ[t2]ᵐ) ->
    body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    (forall k, parameter_sort l (ps k)) ->
    (forall Δa κ T Δb, Δu = Δa ++ ce_ass κ T :: Δb -> Θ ⍮ Ξ ⍮ Δb ++ Γ ⊢ T : ps (List.length Δb)) ->
    (forall Δa κ T Δb, Δu = Δa ++ ce_ass κ T :: Δb ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δb ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (ps (List.length Δb))[t2]) ->
    levels_flag Θ Ξ Γ Δu (me_lit (gu_open nil Φ)) lv Rt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δu Φ ≈ gu_open Δu Φ ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_open Δu Φ)[τ1]ᵘ ≈ (gu_open Δu Φ)[τ2]ᵘ.
Proof.
  intros * Hp Hb XΔ Ha Hx XX Hes Htg HA IHA HM IHM HU IHU Ho IHo Hfo HOo IHOo Hs Hsx Hn Hps HRp IHRp HF HU0.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr.
  assert (Hc : gctx_closed Θ Ξ) by (eapply wf_gctx_closed; exact (wf_sub_dom _ _ _ _ _ Hr)).
  pose proof (ctx_wf_gctx _ _ _ (wf_sub_dom _ _ _ _ _ Hr)) as Hg.
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU0) as (HΓs & HUs & _).
  rewrite gunit_scoped_mk in HUs; destruct HUs as [HΔs [_ HΦs]].
  pose proof (body_xp_nopens _ _ _ _ _ Hb) as Hnx.
  destruct XΔ as [Hpr (τ' & Hpl) HΔ].
  pose proof (sub_pair_right _ _ _ _ _ _ Hpr) as Hq2.
  pose proof (sub_pair_right _ _ _ _ _ _ Hpl) as Hτ'.
  pose proof (all_assumptions_sub _ τ1 Ha) as Ha1; pose proof (all_assumptions_sub _ τ2 Ha) as Ha2.
  pose proof (ctxsub_ext _ _ _ _ _ HΔ Ha2) as HId.
  pose proof (ext_eq_sym_ass _ _ _ _ _ Ha2 HΔ) as HΔ12.
  set (q1 := sb_qn (length Δu) τ1) in *; set (q2 := sb_qn (length Δu) τ2) in *.
  (** the definitions and modules, filled in, at the left image *)
  assert (FA : forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
            gm_fill Φ0 = Some σf ->
            Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ A[σf][q1] : es y /\
            Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ A[σf][q1] ≈ A[σf][q2] : es y /\
            Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ M[σf][q1] : A[σf][q1] /\
            Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ M[σf][q1] ≈ M[σf][q2] : A[σf][q1]).
  { intros * Hp0 HE Hf0.
    pose proof (IHA _ _ _ _ _ _ Hp0 HE Hf0 _ _ _ Hpl) as XAl; rewrite (type_sort_sub _ _ (Hes y)) in XAl.
    pose proof (IHA _ _ _ _ _ _ Hp0 HE Hf0 _ _ _ Hpr) as XAr; rewrite (type_sort_sub _ _ (Hes y)) in XAr.
    pose proof (IHM _ _ _ _ _ _ Hp0 HE Hf0 _ _ _ Hpl) as XMl.
    pose proof (IHM _ _ _ _ _ _ Hp0 HE Hf0 _ _ _ Hpr) as XMr.
    pose proof (exp_eq_id_move _ _ _ _ _ _ _ HId XAr) as HAA.
    pose proof (exp_eq_id_move _ _ _ _ _ _ _ HId XMr) as HMM.
    repeat split.
    - exact (presup_exp_eq_left XAl).
    - exact HAA.
    - exact (tr_conv_back _ _ _ _ _ _ _ (presup_exp_eq_left XMl) XAl (Hes y)).
    - eapply wf_exp_eq_conv_sort; [ exact HMM | exact (presup_exp_eq_left HAA) | exact (Hes y) | apply wf_exp_eq_sym; exact HAA ]. }
  assert (FU : forall y Φ0 E U σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
            gm_fill Φ0 = Some σf -> Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ᵘ U[σf]ᵘ[q1]ᵘ ≈ U[σf]ᵘ[q2]ᵘ)
    by (intros * Hp0 HE Hf0; exact (unit_id_move _ _ _ _ _ _ HId (IHU _ _ _ _ _ Hp0 HE Hf0 _ _ _ Hpr))).
  assert (FO : forall k Φ0 H σf, List.nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> gm_fill Φ0 = Some σf ->
            Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ᵐ H[σf]ᵐ[q1]ᵐ ≈ H[σf]ᵐ[q2]ᵐ)
    by (intros * Hk Hf0; exact (modexp_id_move _ _ _ _ _ _ HId (IHOo _ _ _ _ Hk Hf0 _ _ _ Hpr))).
  (** each open at the left image, under the left image of its context *)
  assert (FOl : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
            exists τo, Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) τ1 ++ Γ' ⊢ˢ τo : Ψ ++ Δu ++ Γ /\
              Θ ⍮ Ξ ⍮ tele_sub (Ψ ++ Δu) τ1 ++ Γ' ⊢ᵐ H[sb_qn (length (Ψ ++ Δu)) τ1]ᵐ ≈ H[τo]ᵐ).
  { intros * Hk.
    destruct (body_opens_tail _ _ _ _ _ Hb _ _ (List.nth_error_In _ _ Hk)) as [Z HZ].
    destruct (XX Z (Ψ ++ Δu) ltac:(rewrite HZ, List.app_assoc; reflexivity)) as [_ (τo & Hpo) _].
    rewrite <- List.app_assoc in Hpo.
    exists τo; split; [ exact (sub_pair_right _ _ _ _ _ _ Hpo) | exact (IHo _ _ _ Hk _ _ _ Hpo) ]. }
  (** the left image expands as the body does *)
  assert (Hb1 : body_xp Θ Ξ (tele_sub Δu τ1 ++ Γ') (gmod_sub Φ q1) (gmod_sub Φx q1)).
  { apply body_xp_pair with (G0 := Δu ++ Γ); [ exact Hb |].
    intros Ψ H HI; destruct (List.In_nth_error _ _ HI) as [k Hk].
    destruct (FOl _ _ _ Hk) as (τo & Hτo & Heq).
    rewrite tele_sub_app, <- List.app_assoc in Hτo, Heq; rewrite List.length_app, sb_qn_plus in Heq.
    exact (open_pair_of _ _ _ _ _ _ _ (Ho _ _ _ Hk) Hτo Heq). }
  assert (Hb2 : body_xp Θ Ξ (tele_sub Δu τ2 ++ Γ') (gmod_sub Φ q2) (gmod_sub Φx q2)).
  { eapply body_xp_sub; [ exact Hc | exact Hb | apply ctx_scoped_app_iff; split; assumption
                        | rewrite List.length_app; exact HΦs | exact (wf_sub_mod_compat _ _ _ _ _ Hq2) ]. }
  (** the expansions' contexts at both images *)
  assert (HX1 : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub (body_ctx Φx ++ Δu) τ1 ≈ tele_sub (body_ctx Φx ++ Δu) τ1).
  { destruct (XX nil _ eq_refl) as [_ (τx & Hpx) _]; apply ext_of_ctx'; exact (wf_sub_dom _ _ _ _ _ (sub_pair_right _ _ _ _ _ _ Hpx)). }
  assert (HX2 : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub (body_ctx Φx ++ Δu) τ2 ≈ tele_sub (body_ctx Φx ++ Δu) τ2)
    by exact (sub_preserves_ext _ _ _ _ _ _ _ Hx Hr).
  (** the parameters at both images *)
  destruct (pair_params _ _ _ _ _ _ _ _ _ Hp Ha HΔ Hps HRp IHRp) as [HP1 HP2].
  (** the right image's facts, and moved to the left parameters *)
  assert (FAr : forall y Φ0 E A M σf, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
             gm_fill Φ0 = Some σf ->
             Θ ⍮ Ξ ⍮ tele_sub Δu τ2 ++ Γ' ⊢ A[σf][q2] : es y /\ Θ ⍮ Ξ ⍮ tele_sub Δu τ2 ++ Γ' ⊢ M[σf][q2] : A[σf][q2]).
  { intros * Hp0 HE Hf0; split.
    - pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ _ _ _ _ Hp0 HE Hf0) Hq2) as X; rewrite (type_sort_sub _ _ (Hes y)) in X; exact X.
    - exact (sub_preserves_exp _ _ _ _ _ _ _ (HM _ _ _ _ _ _ Hp0 HE Hf0) Hq2). }
  assert (Hlv0 : level_sorted_parameters nil) by (intros [|] ? ? ? E; discriminate).
  assert (HsG : slots_agree (tele_sub Δu τ2 ++ Γ') (tele_sub Δu τ1 ++ Γ'))
    by exact (slots_agree_ass _ _ _ Ha2 Ha1 ltac:(rewrite !length_tele_sub; reflexivity)).
  destruct (mdenote_slots_agree Θ Ξ) as (HtrM & _ & _ & HtrB & _).
  (** the open in the context of each open, at the right image *)
  assert (FOr : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
             Θ ⍮ Ξ ⍮ tele_sub Ψ q2 ++ tele_sub Δu τ2 ++ Γ' ⊢ᵐ H[sb_qn (length Ψ) q2]ᵐ ≈ H[sb_qn (length Ψ) q2]ᵐ /\
             frame_free_target Θ Ξ (tele_sub Ψ q2 ++ tele_sub Δu τ2 ++ Γ') H[sb_qn (length Ψ) q2]ᵐ).
  { intros * Hk; pose proof (Ho _ _ _ Hk) as HH; pose proof (presup_modexp_eq_ctx HH) as HΨ.
    pose proof (wf_sub_ext _ _ _ _ _ _ Hq2 (ctx_sub_wf_gen _ _ _ _ _ _ Hq2 HΨ) HΨ) as Hl.
    split; [ exact (sub_preserves_modexp _ _ _ _ _ _ _ HH Hl) |].
    destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (_ & HHs & _).
    exact (sub_frame_free _ _ _ _ _ _ _ Hq2 HΨ HHs (Hfo _ _ _ Hk)). }
  (** each open at the left image *)
  assert (FOl' : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
             Θ ⍮ Ξ ⍮ tele_sub Ψ q1 ++ tele_sub Δu τ1 ++ Γ' ⊢ᵐ H[sb_qn (length Ψ) q1]ᵐ ≈ H[sb_qn (length Ψ) q1]ᵐ /\
             frame_free_target Θ Ξ (tele_sub Ψ q1 ++ tele_sub Δu τ1 ++ Γ') H[sb_qn (length Ψ) q1]ᵐ).
  { intros * Hk; destruct (FOl _ _ _ Hk) as (τo & Hτo & Heq).
    rewrite tele_sub_app, <- List.app_assoc in Hτo, Heq; rewrite List.length_app, sb_qn_plus in Heq.
    split; [ exact (wf_modexp_eq_refl_left Heq) |].
    exact (pair_frame_free _ _ _ _ _ _ _ Hτo (Ho _ _ _ Hk) (Hfo _ _ _ Hk) Heq). }
  (** the two images with no parameter, under the left parameters *)
  assert (NIL : Θ ⍮ Ξ ⍮ tele_sub Δu τ1 ++ Γ' ⊢ᵘ gu_open nil (gmod_sub Φ q1) ≈ gu_open nil (gmod_sub Φ q2)).
  { pose proof (unit_body_moved Θ Ξ (Δu ++ Γ) nil nil Φ Φ Φx Φx es l ps (tele_sub Δu τ1 ++ Γ') q1 q2) as X.
    rewrite !List.app_nil_r in X; cbn [tele_sub length sb_qn List.app] in X.
    rewrite !gunit_sub_mk in X; cbn [tele_sub length sb_qn moddef_sub] in X.
    eapply X; clear X.
    - exact Hb1.
    - exact (HtrB _ _ _ Hb2 _ HsG).
    - constructor; exact (wf_sub_dom _ _ _ _ _ Hτ').
    - apply ext_of_ctx'; pose proof (ext_eq_ctx_left _ _ _ _ _ HX1) as X; rewrite tele_sub_app, <- List.app_assoc in X; exact X.
    - apply ext_of_ctx'; pose proof (ext_eq_ctx_left _ _ _ _ _ HX2) as X; rewrite tele_sub_app, <- List.app_assoc in X.
      pose proof (ctx_sub_wf_gen _ _ _ _ _ _ HId X) as Y; rewrite tele_sub_id in Y; exact Y.
    - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
        rewrite HE in HE'; injection HE' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      exact (FA _ _ _ _ _ _ Hp0 HE Hf0).
    - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
        rewrite HE in HE'; injection HE' as <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      exact (FU _ _ _ _ _ Hp0 HE Hf0).
    - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
        rewrite HE in HE'; injection HE' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      destruct (FAr _ _ _ _ _ _ Hp0 HE Hf0) as [H1 H2].
      split; [ exact (exp_id_move _ _ _ _ _ _ HId H1) | exact (exp_id_move _ _ _ _ _ _ HId H2) ].
    - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
        rewrite HE in HE'; injection HE' as <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      exact (unit_id_move _ _ _ _ _ _ HId (sub_preserves_unit _ _ _ _ _ _ _ (HU _ _ _ _ _ Hp0 HE Hf0) Hq2)).
    - intros * Hk; rewrite List.app_nil_r; exact (proj1 (FOl' _ _ _ Hk)).
    - intros * Hk; rewrite List.app_nil_r; exact (modexp_id_move_under _ _ _ _ _ _ _ HId (proj1 (FOr _ _ _ Hk))).
    - intros * Hk; rewrite List.app_nil_r; exact (proj2 (FOl' _ _ _ Hk)).
    - intros * Hk; rewrite List.app_nil_r; destruct (FOr _ _ _ Hk) as [H1 H2].
      exact (frame_free_id_move_under _ _ _ _ _ _ HId H1 H2).
    - intros * Hk Hk' Hf0 Hf0'; rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      exact (FO _ _ _ _ Hk Hf0).
    - intros * Hk Hk' Hf0 Hf0'; rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
      exact (modexp_id_move _ _ _ _ _ _ HId (sub_preserves_modexp _ _ _ _ _ _ _ (HOo _ _ _ _ Hk Hf0) Hq2)).
    - exact Hb.
    - exact Hb.
    - constructor.
    - constructor.
    - reflexivity.
    - exact Hs.
    - exact Hsx.
    - exact Hn.
    - exact Hes.
    - exact Htg.
    - exact Htg.
    - exact Hps.
    - intros [|] ? ? ? E; discriminate.
    - intros [|] ? ? ? E; discriminate.
    - exact (fun _ : true = true => Hlv0).
    - discriminate.
    - discriminate.
    - exact (fun _ : true = true => Hlv0).
    - discriminate.
    - discriminate.
    Unshelve. all: exact Rt. }
  (** the flags of the two images: the right one moved, the left one from
      it along the equation of the two images with no parameter *)
  pose proof (body_nil_typed _ _ Hg _ _ _ _ HU0) as HL0.
  assert (HFr : levels_flag Θ Ξ Γ' (tele_sub Δu τ2) (me_lit (gu_open nil (gmod_sub Φ q2))) lv (mdesc_sub Rt q2)).
  { destruct HF as [HF1 HF2 HF3]; constructor.
    - intros E; exact (level_sorted_parameters_sub _ _ (HF1 E)).
    - intros E; pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HL0 (HF2 E) Hq2) as Hm2.
      cbn [modexp_sub] in Hm2; rewrite gunit_sub_mk in Hm2; cbn [tele_sub length sb_qn moddef_sub] in Hm2; exact Hm2.
    - intros E; exact (sub_preserves_no_level _ _ _ _ _ _ (HF3 E) Hq2). }
  assert (HFl : exists Rt1, levels_flag Θ Ξ Γ' (tele_sub Δu τ1) (me_lit (gu_open nil (gmod_sub Φ q1))) lv Rt1).
  { destruct (me_denotes _ _ _ _ _ (wf_me_lit _ _ _ _ _ (wf_unit_eq_refl_left NIL))) as (R1 & _ & HR1 & _).
    destruct HFr as [HF1 HF2 HF3].
    exists R1; constructor.
    - intros E; destruct HF as [HF1' _ _]; exact (level_sorted_parameters_sub _ _ (HF1' E)).
    - intros _; exact HR1.
    - intros E.
      pose proof (HtrM _ _ _ (HF2 E) _ HsG) as Hm2'.
      pose proof (no_level_ctx_conv _ _ _ _ _ _ Ha2 HΔ (HF3 E)) as Hn2.
      exact (no_level_modexp_conv _ _ _ _ _ _ _ (wf_me_lit _ _ _ _ _ NIL) HR1 Hm2' Hn2). }
  destruct HFl as (Rt1 & HFl).
  pose proof (unit_body_moved Θ Ξ Γ Δu Δu Φ Φ Φx Φx es l ps Γ' τ1 τ2) as X.
  eapply X; clear X.
  - exact Hb1.
  - exact Hb2.
  - exact HΔ12.
  - exact HX1.
  - exact HX2.
  - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
      rewrite HE in HE'; injection HE' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (FA _ _ _ _ _ _ Hp0 HE Hf0).
  - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
      rewrite HE in HE'; injection HE' as <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (FU _ _ _ _ _ Hp0 HE Hf0).
  - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
      rewrite HE in HE'; injection HE' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (FAr _ _ _ _ _ _ Hp0 HE Hf0).
  - intros * Hp0 HE Hp0' HE' Hf0 Hf0'; rewrite Hp0 in Hp0'; injection Hp0' as <- <-;
      rewrite HE in HE'; injection HE' as <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (sub_preserves_unit _ _ _ _ _ _ _ (HU _ _ _ _ _ Hp0 HE Hf0) Hq2).
  - intros * Hk; destruct (FOl _ _ _ Hk) as (τo & _ & Heq); exact (wf_modexp_eq_refl_left Heq).
  - intros * Hk; rewrite tele_sub_app, <- List.app_assoc, List.length_app, sb_qn_plus; exact (proj1 (FOr _ _ _ Hk)).
  - intros * Hk; rewrite tele_sub_app, <- List.app_assoc, List.length_app, sb_qn_plus; exact (proj2 (FOl' _ _ _ Hk)).
  - intros * Hk; rewrite tele_sub_app, <- List.app_assoc, List.length_app, sb_qn_plus; exact (proj2 (FOr _ _ _ Hk)).
  - intros * Hk Hk' Hf0 Hf0'; rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (FO _ _ _ _ Hk Hf0).
  - intros * Hk Hk' Hf0 Hf0'; rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf0 in Hf0'; injection Hf0' as <-.
    exact (sub_preserves_modexp _ _ _ _ _ _ _ (HOo _ _ _ _ Hk Hf0) Hq2).
  - exact Hb.
  - exact Hb.
  - exact Ha.
  - exact Ha.
  - reflexivity.
  - exact Hs.
  - exact Hsx.
  - exact Hn.
  - exact Hes.
  - exact Htg.
  - exact Htg.
  - exact Hps.
  - exact HP1.
  - exact HP2.
  - exact (levels_flag_sorted _ _ _ _ _ _ _ HFl).
  - exact (levels_flag_denotes _ _ _ _ _ _ _ HFl).
  - exact (levels_flag_no_level _ _ _ _ _ _ _ HFl).
  - exact (levels_flag_sorted _ _ _ _ _ _ _ HFr).
  - exact (levels_flag_denotes _ _ _ _ _ _ _ HFr).
  - exact (levels_flag_no_level _ _ _ _ _ _ _ HFr).
Qed.

(** The body unit case: each side by [pair_unit_body], its premises read
    off the rule's for that side ([tm_left], [tm_right], [unit_left],
    [unit_right], [opens_left], [opens_right]). *)
Lemma pair_unit_body_case : forall Θ Ξ Γ' Γ τ1 τ2 Δ Δ' Φ Φ' Φx Φx' (entry_sort : String.string -> exp)
    param_level param_sorts (lv lv' : bool) Rt Rt',
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 Δ -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 Δ' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 (body_ctx Φx ++ Δ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' -> ext_pairs Θ Ξ Γ' Γ τ1 τ2 (body_ctx Φx' ++ Δ') ->
    (forall y, type_sort (entry_sort y)) ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (entry_sort y) (entry_kind E)) ->
    (forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       sort_kind (entry_sort y) (entry_kind E')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : entry_sort y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ A[σ][t1] ≈ A[σ][t2] : (entry_sort y)[t2]) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ]) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ M[σ][t1] ≈ M[σ][t2] : A[σ][t2]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U[σ]ᵘ[t1]ᵘ ≈ U[σ]ᵘ[t2]ᵘ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U'[σ']ᵘ[t1]ᵘ ≈ U'[σ']ᵘ[t2]ᵘ) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ A'[σ'] : entry_sort y) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ A'[σ'][t1] ≈ A'[σ'][t2] : (entry_sort y)[t2]) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ M'[σ'] : A'[σ']) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ M'[σ'][t1] ≈ M'[σ'][t2] : A'[σ'][t2]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵘ U'[σ']ᵘ ≈ U'[σ']ᵘ) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U'[σ']ᵘ[t1]ᵘ ≈ U'[σ']ᵘ[t2]ᵘ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U'[σ']ᵘ[t1]ᵘ ≈ U'[σ']ᵘ[t2]ᵘ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ ++ Δ ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[t1]ᵐ ≈ H[t2]ᵐ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[t1]ᵐ ≈ H[t2]ᵐ) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊢ᵐ H' ≈ H') ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Ψ' ++ Δ' ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[t1]ᵐ ≈ H'[t2]ᵐ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[t1]ᵐ ≈ H'[t2]ᵐ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> frame_free_target Θ Ξ (Ψ ++ Δ ++ Γ) H) ->
    (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> frame_free_target Θ Ξ (Ψ' ++ Δ' ++ Γ) H') ->
    (forall k Φ0 H Φ0' H' σ σ',
       nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
    (forall k Φ0 H Φ0' H' σ σ',
       nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[σ]ᵐ[t1]ᵐ ≈ H[σ]ᵐ[t2]ᵐ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[σ']ᵐ[t1]ᵐ ≈ H'[σ']ᵐ[t2]ᵐ) ->
    (forall k Φ0 H Φ0' H' σ σ',
       nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ H'[σ']ᵐ ≈ H'[σ']ᵐ) ->
    (forall k Φ0 H Φ0' H' σ σ',
       nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[σ']ᵐ[t1]ᵐ ≈ H'[σ']ᵐ[t2]ᵐ /\ Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[σ']ᵐ[t1]ᵐ ≈ H'[σ']ᵐ[t2]ᵐ) ->
    all_assumptions Δ -> all_assumptions Δ' ->
    body_shape Φ Φ' -> body_shape Φx Φx' -> List.NoDup (gm_names Φ) ->
    (forall k, parameter_sort param_level (param_sorts k)) ->
    (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_sorts (List.length Δ2)) ->
    (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ2 ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (param_sorts (List.length Δ2))[t2]) ->
    (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_sorts (List.length Δ2)) ->
    (forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ2 ++ Γ) t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ T[t1] ≈ T[t2] : (param_sorts (List.length Δ2))[t2]) ->
    (lv = true -> level_sorted_parameters Δ) ->
    (lv = false -> mdenote Θ Ξ (Δ ++ Γ) (me_lit (gu_open nil Φ)) Rt) ->
    (lv = false -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ Rt) ->
    (lv' = true -> level_sorted_parameters Δ') ->
    (lv' = false -> mdenote Θ Ξ (Δ' ++ Γ) (me_lit (gu_open nil Φ')) Rt') ->
    (lv' = false -> Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ⁿˡ Rt') ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_open Δ Φ)[τ1]ᵘ ≈ (gu_open Δ Φ)[τ2]ᵘ /\ Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ (gu_open Δ' Φ')[τ1]ᵘ ≈ (gu_open Δ' Φ')[τ2]ᵘ.
Proof.
  intros * Hp Hb Hb' HΔ XΔ XΔ' Hx XX Hx' XX' Hes Htg Htg' HA IHA HM IHM HU IHU HAr IHAr HMr IHMr HUr IHUr
           Ho IHo Ho' IHo' Hfo Hfo' HOO IHOO HOR IHOR Ha Ha' Hs Hsx Hn Hps HRp IHRp HRp' IHRp' Hl1 Hl2 Hl3 Hl1' Hl2' Hl3' HU0.
  pose proof (body_xp_nopens _ _ _ _ _ Hb) as Hnx.
  pose proof (body_xp_nopens _ _ _ _ _ Hb') as Hnx'.
  destruct (body_shape_refl _ _ Hs) as (Hs1 & Hs2 & Hnm).
  destruct (body_shape_refl _ _ Hsx) as (Hsx1 & Hsx2 & _).
  split.
  - eapply (pair_unit_body _ _ _ _ _ _ Δ Φ Φx entry_sort param_level param_sorts lv Rt).
    all: first [ exact Hp | exact Hb | exact (ext_pairs_full _ _ _ _ _ _ _ XΔ) | exact Ha | exact Hx | exact XX | exact Hes | exact Htg
               | exact Ho | exact (fun k Ψ H Hk Γ'' t1 t2 Hq => proj1 (IHo k Ψ H Hk Γ'' t1 t2 Hq)) | exact Hfo
               | exact Hs1 | exact Hsx1 | exact Hn | exact Hps | exact HRp | exact IHRp
               | exact (wf_unit_eq_refl_left HU0) | constructor; assumption | idtac ].
    + exact (tm_left (fun y Φ0 E A M σf => Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σf] : entry_sort y) _ _ Hnx Hsx HA).
    + exact (tm_left (fun y Φ0 E A M σf => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
                        Θ ⍮ Ξ ⍮ Γ'' ⊢ A[σf][t1] ≈ A[σf][t2] : (entry_sort y)[t2]) _ _ Hnx Hsx IHA).
    + exact (tm_left (fun y Φ0 E A M σf => Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σf] : A[σf]) _ _ Hnx Hsx HM).
    + exact (tm_left (fun y Φ0 E A M σf => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
                        Θ ⍮ Ξ ⍮ Γ'' ⊢ M[σf][t1] ≈ M[σf][t2] : A[σf][t2]) _ _ Hnx Hsx IHM).
    + exact (unit_left (fun y Φ0 E U σf => Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ U[σf]ᵘ ≈ U[σf]ᵘ) _ _ Hnx Hsx
               (fun y Φ0 E U Φ0' E' U' σ σ' a b c d e f => wf_unit_eq_refl_left (HU y Φ0 E U Φ0' E' U' σ σ' a b c d e f))).
    + exact (unit_left (fun y Φ0 E U σf => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
                          Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U[σf]ᵘ[t1]ᵘ ≈ U[σf]ᵘ[t2]ᵘ) _ _ Hnx Hsx
               (fun y Φ0 E U Φ0' E' U' σ σ' a b c d e f Γ'' t1 t2 Hq => proj1 (IHU y Φ0 E U Φ0' E' U' σ σ' a b c d e f Γ'' t1 t2 Hq))).
    + exact (opens_left _ _ _ _ _ _ _ _ (fun k Φ0 H σf => Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ H[σf]ᵐ ≈ H[σf]ᵐ) Hb Hb' Hs Hsx
               (fun k Φ0 H Φ0' H' σ σ' a b c d => wf_modexp_eq_refl_left (HOO k Φ0 H Φ0' H' σ σ' a b c d))).
    + exact (opens_left _ _ _ _ _ _ _ _ (fun k Φ0 H σf => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ ++ Γ) t1 t2 ->
                                          Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H[σf]ᵐ[t1]ᵐ ≈ H[σf]ᵐ[t2]ᵐ) Hb Hb' Hs Hsx
               (fun k Φ0 H Φ0' H' σ σ' a b c d Γ'' t1 t2 Hq => proj1 (IHOO k Φ0 H Φ0' H' σ σ' a b c d Γ'' t1 t2 Hq))).
  - eapply (pair_unit_body _ _ _ _ _ _ Δ' Φ' Φx' entry_sort param_level param_sorts lv' Rt').
    all: first [ exact Hp | exact Hb' | exact (ext_pairs_full _ _ _ _ _ _ _ XΔ') | exact Ha' | exact Hx' | exact XX' | exact Hes
               | exact Htg' | exact Ho' | exact (fun k Ψ H Hk Γ'' t1 t2 Hq => proj1 (IHo' k Ψ H Hk Γ'' t1 t2 Hq)) | exact Hfo'
               | exact Hs2 | exact Hsx2 | rewrite <- Hnm; exact Hn | exact Hps | exact HRp' | exact IHRp'
               | exact (wf_unit_eq_refl_right HU0) | constructor; assumption | idtac ].
    + exact (tm_right (fun y Φ0' E' A' M' σf' => Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ A'[σf'] : entry_sort y) _ _ Hnx Hsx HAr).
    + exact (tm_right (fun y Φ0' E' A' M' σf' => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
                         Θ ⍮ Ξ ⍮ Γ'' ⊢ A'[σf'][t1] ≈ A'[σf'][t2] : (entry_sort y)[t2]) _ _ Hnx Hsx IHAr).
    + exact (tm_right (fun y Φ0' E' A' M' σf' => Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ M'[σf'] : A'[σf']) _ _ Hnx Hsx HMr).
    + exact (tm_right (fun y Φ0' E' A' M' σf' => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
                         Θ ⍮ Ξ ⍮ Γ'' ⊢ M'[σf'][t1] ≈ M'[σf'][t2] : A'[σf'][t2]) _ _ Hnx Hsx IHMr).
    + exact (unit_right (fun y Φ0' E' U' σf' => Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵘ U'[σf']ᵘ ≈ U'[σf']ᵘ) _ _ Hnx Hsx HUr).
    + exact (unit_right (fun y Φ0' E' U' σf' => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
                           Θ ⍮ Ξ ⍮ Γ'' ⊢ᵘ U'[σf']ᵘ[t1]ᵘ ≈ U'[σf']ᵘ[t2]ᵘ) _ _ Hnx Hsx
               (fun y Φ0 E U Φ0' E' U' σ σ' a b c d e f Γ'' t1 t2 Hq => proj1 (IHUr y Φ0 E U Φ0' E' U' σ σ' a b c d e f Γ'' t1 t2 Hq))).
    + exact (opens_right _ _ _ _ _ _ _ _ (fun k Φ0' H' σf' => Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ H'[σf']ᵐ ≈ H'[σf']ᵐ) Hb Hb' Hs Hsx HOR).
    + exact (opens_right _ _ _ _ _ _ _ _ (fun k Φ0' H' σf' => forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (Δ' ++ Γ) t1 t2 ->
                                           Θ ⍮ Ξ ⍮ Γ'' ⊢ᵐ H'[σf']ᵐ[t1]ᵐ ≈ H'[σf']ᵐ[t2]ᵐ) Hb Hb' Hs Hsx
               (fun k Φ0 H Φ0' H' σ σ' a b c d Γ'' t1 t2 Hq => proj1 (IHOR k Φ0 H Φ0' H' σ σ' a b c d Γ'' t1 t2 Hq))).
Qed.

(** A telescope of assumptions ending in [Z2], equal to one ending in
    [Z1] and to [Φ], stays equal to [Φ] with [Z1] for [Z2]. *)
Lemma ext_eq_last_swap : forall Θ Ξ Γ Ψ1 Ψ2 κ Z1 Z2 Φ,
    all_assumptions Ψ1 -> all_assumptions Ψ2 -> all_assumptions Φ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ▹{κ} Z2 ≈ Ψ1 ▹{κ} Z1 -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ▹{κ} Z2 ≈ Φ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ▹{κ} Z1 ≈ Φ.
Proof.
  intros * Ha1 Ha2 HaΦ H21 H2Φ.
  inversion H21 as [| ? ? ? ? ? ? ? ? ? ? HΨ HZ2 HS2 HZ1 HS1 H12 H12' | | | ]; subst.
  pose proof (ext_eq_sym_ass _ _ _ _ _ Ha2 HΨ) as HΨ12.
  assert (HΨ22 : Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ≈ Ψ2) by (eapply ext_eq_trans_ass; [ exact Ha2 | exact Ha1 | exact HΨ | exact HΨ12 ]).
  pose proof (ctxsub_ext _ _ _ _ _ HΨ12 Ha1) as HId.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HZ1 HId) as HZ1'.
  rewrite !exp_sub_id in HZ1'.
  assert (Hsw : Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ2 ▹{κ} Z1 ≈ Ψ2 ▹{κ} Z2)
    by (eapply wf_ext_eq_ass; [ exact HΨ22 | exact HZ1' | exact HS1 | exact HZ2 | exact HS2 | exact H12' | exact H12 ]).
  eapply ext_eq_trans_ass;
    [ constructor; [ eexists; eexists; reflexivity | exact Ha2 ] | constructor; [ eexists; eexists; reflexivity | exact Ha2 ]
    | exact Hsw | exact H2Φ ].
Qed.

(** The eliminator across the pair: the congruence with the right image
    on the left.  The right image's parts are typed by substitution (the
    [sub_as_sub] instances of the [move_*] lemmas); the equations between
    the two images' parts are the hypotheses, those under the motives'
    and the branches' telescopes at the pair lifted over the telescopes'
    right images ([ext_pair_right]); the left image's scrutinee types at
    the right image's parameters are equal to its own ones by the
    scrutinee telescopes' equal images ([ext_pair_eq],
    [ext_eq_last_swap]). *)
Lemma pair_elim : forall Θ Ξ Γ' Γ τ1 τ2 r p D Us m Mm Bks bm Ps M i,
    sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
    ind_lookup Θ Ξ p = Some D ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
    (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' Γ t1 t2 -> Θ ⍮ Ξ ⍮ Γ'' ⊢ P[t1] ≈ P[t2] : T[t2]) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps))[τ2] ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹{ak_relevant} eb_scrutinee_type b
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' Γ t1 t2 ->
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹{ak_relevant} eb_scrutinee_type b) /\
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r Typeω@i) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ (eb_motive b)[t1] ≈ (eb_motive b)[t2] : (abs_kind_sort r Typeω@i)[t2]) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' Γ t1 t2 ->
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) /\
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' Γ t1 t2 ->
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) /\
       ext_pairs Θ Ξ Γ'' Γ t1 t2 (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       Θ ⍮ Ξ ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       forall Γ'' t1 t2, sub_pair Θ Ξ Γ'' (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ) t1 t2 ->
       Θ ⍮ Ξ ⍮ Γ'' ⊢ B[t1] ≈ B[t2] : (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps))[t2]) ->
    motive_kind r ->
    Θ ⍮ Ξ ⍮ Γ' ⊢ (a_elim r p Us m Bks M)[τ1] ≈ (a_elim r p Us m Bks M)[τ2]
      : ((eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)])[τ2].
Proof.
  intros * Hp Hl HMm Hbm HlB HlP HPs IHPs HM IHM -> Hnm HZ IHZ HA IHA HΨ IHΨ Hn HΨB IHΨB Hk HB IHB Hr.
  pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hσ.
  assert (HD : decl_closed D) by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_cod _ _ _ _ _ Hσ) | exact Hl ]).
  assert (HUl : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite List.length_firstn; unfold im_np in HlP; lia).
  assert (Hbmc : eb_binder_count bm = S (im_nn Mm)) by exact (Hnm _ _ _ HMm Hbm).
  rewrite !exp_sub_elim, (elim_type_sub D Mm bm) by eauto.
  apply wf_exp_eq_sym.
  eapply wf_exp_eq_elim_cong with (Ps := List.map (fun P => P[τ2]) Ps) (Ps' := List.map (fun P => P[τ1]) Ps)
                                  (Bks' := blocks_sub Bks τ1) (M' := M[τ1]) (i := i).
  all: try first [ eassumption | reflexivity | rewrite nth_error_blocks_sub, Hbm; reflexivity
                 | rewrite length_blocks_sub; exact HlB | rewrite List.length_map; exact HlP
                 | rewrite List.firstn_map; reflexivity ].
  (** the right image's parameters *)
  all: try (match goal with |- forall k P T, nth_error (List.map _ _) k = Some P -> _ -> _ ⍮ _ ⍮ _ ⊢ P : T => idtac end;
            eapply (move_elim_params _ _ (sub_as_sub Θ Ξ)); [ exact HD | exact HMm | | exact Hσ ];
            intros * HP HT * Hs; eapply sub_preserves_exp; [ exact (HPs _ _ _ HP HT) | exact Hs ]).
  (** the right image's parameters equal to the left image's *)
  all: try (match goal with |- forall k P P' T, nth_error (List.map _ _) k = Some P -> nth_error _ k = Some P' -> _ -> _ => idtac end;
            let HP := fresh "HP" in let HP' := fresh "HP'" in let HT := fresh "HT" in
            let P0 := fresh "P0" in let HP0 := fresh "HP0" in let T0 := fresh "T0" in let HT0 := fresh "HT0" in
            let P1 := fresh "P1" in let HP1 := fresh "HP1" in
            intros k ? ? ? HP HP' HT; erewrite <- params_insts_sub in HT by eassumption;
            apply nth_error_map_inv in HP as (P0 & HP0 & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->);
            apply nth_error_map_inv in HP' as (P1 & HP1 & ->);
            rewrite HP0 in HP1; injection HP1 as <-; apply wf_exp_eq_sym; exact (IHPs _ _ _ HP0 HT0 _ _ _ Hp)).
  (** the scrutinee *)
  all: try (match goal with |- _ ⍮ _ ⍮ _ ⊢ ?X[_] ≈ ?X[_] : ind_mty _ _ _ _ _ => idtac end;
            rewrite <- ind_mty_split_sub by (try assumption; unfold im_np in HlP; lia); apply wf_exp_eq_sym; exact IHM).
  all: try (apply blocks_binder_count_ok_sub; exact Hnm).
  (** the right image's blocks *)
  all: try (match goal with |- forall k Mk b, _ -> nth_error (blocks_sub _ ?t) k = Some b -> _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _ => constr_eq t τ2 end;
            rewrite List.firstn_map; eapply (move_blocks_ann _ _ (sub_as_sub Θ Ξ)); [ exact HD | exact HUl | exact Hnm | exact Hσ | ];
            intros * HMk Hb * Hs; exact (sub_preserves_ext _ _ _ _ _ _ _ (HZ _ _ _ HMk Hb) Hs)).
  all: try (match goal with |- forall k Mk b, _ -> nth_error (blocks_sub _ _) k = Some b -> _ ⍮ _ ⍮ _ ⊢ _ : _ => idtac end;
            rewrite List.firstn_map; eapply (move_blocks_motive _ _ (sub_as_sub Θ Ξ) (sub_as_sub_ext Θ Ξ));
              [ exact HD | exact HUl | exact Hnm | exact Hσ | apply type_sort_abs_kind; constructor | exact HΨ
              | intros * HMk * Hs; exact (sub_preserves_ext _ _ _ _ _ _ _ (HΨ _ _ HMk) Hs)
              | intros * HMk Hb * Hs; exact (sub_preserves_exp _ _ _ _ _ _ _ (HA _ _ _ HMk Hb) Hs) ]).
  all: try (match goal with |- forall k Mk, _ -> _ ⍮ _ ⍮ _ ⊢ˣ elim_mctx _ _ _ _ _ ≈ _ => idtac end;
            intros k Mk HMk; rewrite List.firstn_map; erewrite <- elim_mctx_sub by eassumption;
            exact (sub_preserves_ext _ _ _ _ _ _ _ (HΨ _ _ HMk) Hσ)).
  all: try (apply move_blocks_names; exact Hn).
  all: try (match goal with |- forall k b b', nth_error (blocks_sub _ _) k = Some b -> _ -> List.map fst _ = _ => idtac end;
            let b1 := fresh "b1" in let b2 := fresh "b2" in let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
            let b0 := fresh "b0" in let Hb0 := fresh "Hb0" in
            intros k b1 b2 Hb1 Hb2; rewrite nth_error_blocks_sub in Hb1, Hb2;
            destruct (List.nth_error Bks k) as [b0 |]; cbn in Hb1, Hb2; [| discriminate ];
            injection Hb1 as <-; injection Hb2 as <-;
            destruct b0 as [nm Z0 A0 Bs]; cbn; unfold brs_sub; rewrite !brs_fst_map; reflexivity).
  all: try (match goal with |- forall k Mk c gs, _ -> _ -> _ ⍮ _ ⍮ _ ⊢ˣ elim_bctx _ _ _ _ _ _ _ ≈ _ => idtac end;
            rewrite List.firstn_map; eapply (move_blocks_bctx _ _ (sub_as_sub Θ Ξ)); [ exact HD | exact HUl | exact Hnm | exact Hσ | ];
            intros * HMk Hc * Hs; exact (sub_preserves_ext _ _ _ _ _ _ _ (HΨB _ _ _ _ HMk Hc) Hs)).
  all: try (apply move_blocks_counts; exact Hk).
  (** the two images' motives equal, under the right image of their
      telescope *)
  all: try (match goal with |- forall k Mk b b', _ -> nth_error (blocks_sub _ _) k = Some b -> _ -> _ ⍮ _ ⍮ _ ⊢ eb_motive _ ≈ _ : _ => idtac end;
            let b1 := fresh "b1" in let b2 := fresh "b2" in let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
            let HMk := fresh "HMk" in let X := fresh "X" in let b0 := fresh "b0" in let Hb0 := fresh "Hb0" in
            intros k Mk b1 b2 HMk Hb1 Hb2; rewrite nth_error_blocks_sub in Hb1, Hb2;
            destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb1, Hb2; [| discriminate ];
            injection Hb1 as <-; injection Hb2 as <-;
            pose proof (Hnm _ _ _ HMk Hb0) as Enm;
            pose proof (IHA _ _ _ HMk Hb0 _ _ _ (ext_pair_right _ _ _ _ _ _ _ (ext_pairs_full _ _ _ _ _ _ _ (proj1 (IHΨ _ _ HMk _ _ _ Hp))))) as X;
            destruct b0 as [nm Z0 A0 Bs]; cbn in Enm; subst nm; cbn [eblock_sub eb_motive] in *;
            rewrite List.firstn_map, <- (elim_mctx_sub _ _ _ _ _ _ HD HMk HUl);
            rewrite length_elim_mctx, abs_kind_sort_sub in X; cbn [exp_sub] in X;
            apply wf_exp_eq_sym; exact X).
  (** the two images' branches equal, alike *)
  all: try (match goal with |- forall k Mk b b' i c gs n B B', _ -> nth_error (blocks_sub _ _) k = Some b -> _ => idtac end;
            let b1 := fresh "b1" in let b2 := fresh "b2" in let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
            let HMk := fresh "HMk" in let X := fresh "X" in let b0 := fresh "b0" in let Hb0 := fresh "Hb0" in
            let Hi := fresh "Hi" in let Hi' := fresh "Hi'" in let Hc := fresh "Hc" in
            intros k Mk b1 b2 i0 c gs n B1 B2 HMk Hb1 Hb2 Hi Hi' Hc;
            rewrite nth_error_blocks_sub in Hb1, Hb2;
            destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb1, Hb2; [| discriminate ];
            injection Hb1 as <-; injection Hb2 as <-;
            pose proof (Hnm _ _ _ HMk Hb0) as Enm;
            destruct b0 as [nm Z0 A0 Bs]; cbn in Enm; subst nm;
            cbn [eblock_sub eb_brs eb_motive] in Hi, Hi' |- *; unfold brs_sub in Hi, Hi';
            apply nth_error_map_inv in Hi as ([[c1 n1] B0] & Hi & Heq1); cbn in Heq1; injection Heq1 as -> -> ->;
            apply nth_error_map_inv in Hi' as ([[c2 n2] B3] & Hi' & Heq2); cbn in Heq2; injection Heq2 as <- <- ->;
            rewrite Hi in Hi'; injection Hi' as <-;
            pose proof (Hk _ _ _ _ _ _ _ HMk Hb0 Hc (List.nth_error_In _ _ Hi)) as En; cbn in En; subst n1;
            rewrite List.firstn_map;
            erewrite <- (elim_bctx_sub _ _ _ _ _ _ _ (blocks_motives Bks)) by
              (first [ exact HD | exact HMk | apply cons_lookup_in; exact Hc | exact HUl
                     | intros j Mj HMj; eapply blocks_motives_sub; eassumption ]);
            erewrite <- (elim_branch_type_sub _ _ _ _ _ _ _ _ _ HD HMk HUl);
            pose proof (IHB _ _ _ _ _ _ _ HMk Hb0 Hc (List.nth_error_In _ _ Hi) _ _ _
                          (ext_pair_right _ _ _ _ _ _ _ (ext_pairs_full _ _ _ _ _ _ _ (proj1 (IHΨB _ _ _ _ HMk Hc _ _ _ Hp))))) as X;
            rewrite length_elim_bctx in X;
            replace (cargs_nrec D gs + List.length gs + im_nn Mk)%nat with (im_nn Mk + List.length gs + cargs_nrec D gs)%nat in X by lia;
            apply wf_exp_eq_sym; exact X).
  (** the left image's scrutinee types at the right image's parameters *)
  all: (match goal with |- forall k Mk b, _ -> nth_error (blocks_sub _ ?t) k = Some b -> _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _ => constr_eq t τ1 end;
            let HMk := fresh "HMk" in let Hb := fresh "Hb" in let Hv := fresh "Hv" in let H21 := fresh "H21" in
            let b0 := fresh "b0" in let Hb0 := fresh "Hb0" in
            intros k Mk b HMk Hb; rewrite nth_error_blocks_sub in Hb;
            destruct (List.nth_error Bks k) as [b0 |] eqn:Hb0; cbn in Hb; [| discriminate ]; injection Hb as <-;
            assert (Hv : Θ ⍮ Ξ ⍮ Γ' ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.map (fun U => U[τ2]) (List.firstn (ind_nu D) Ps)))
                           ▹{ak_relevant} eb_scrutinee_type (eblock_sub b0 τ2)
                         ≈ elim_mctx p D k Mk (List.map (fun U => U[τ2]) (List.firstn (ind_nu D) Ps)))
              by (eapply (move_blocks_ann _ _ (sub_as_sub Θ Ξ)); [ exact HD | exact HUl | exact Hnm | exact Hσ | | exact HMk
                                                                  | rewrite nth_error_blocks_sub, Hb0; reflexivity ];
                  intros * HMk' Hb' * Hs; exact (sub_preserves_ext _ _ _ _ _ _ _ (HZ _ _ _ HMk' Hb') Hs));
            pose proof (ext_pair_eq _ _ _ _ _ _ _ (ext_pairs_full _ _ _ _ _ _ _ (proj1 (IHZ _ _ _ HMk Hb0 _ _ _ Hp)))) as H21;
            pose proof (Hnm _ _ _ HMk Hb0) as Enm;
            destruct b0 as [nm Z0 A0 Bs]; cbn in Enm; subst nm; cbn [eblock_sub eb_scrutinee_type] in Hv |- *;
            cbn [tele_sub centry_sub] in H21;
            rewrite !(nparams_sub _ _ _ _ _ HD HMk HUl), length_tele_sub, length_im_nparams in H21;
            replace (S (im_nn Mk) - 1) with (im_nn Mk) in Hv |- * by lia;
            rewrite List.firstn_map;
            eapply ext_eq_last_swap;
              [ apply all_assumptions_sub; eapply decl_closed_nparams_ass; eassumption
              | apply all_assumptions_sub; eapply decl_closed_nparams_ass; eassumption
              | eapply elim_mctx_ass; eassumption | exact H21 | exact Hv ]).
Qed.

(** The induction hypotheses at a pair: the same context, or one more
    binder, lifted along it. *)
Ltac pair_ih Hp :=
  repeat match goal with
    | IH : forall Γ' τ1 τ2, sub_pair ?T ?X Γ' ?G τ1 τ2 -> _,
      Hp0 : sub_pair ?T ?X _ ?G _ _ |- _ => specialize (IH _ _ _ Hp0)
    end;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.

(** A hypothesis under one more binder, read at the pair lifted over the
    right image of the binder ([sub_pair_q], [sub_pair_q_def],
    [sub_pair_q_mod]); the hypothesis itself is kept, for a reading at
    another lifting. *)
Ltac pair_lift :=
  repeat match goal with
    | Hp : sub_pair ?T ?X ?G' ?G ?t1 ?t2,
      IH : forall Γ' τ1 τ2, sub_pair ?T ?X Γ' (?G ▹{?κ} ?A) τ1 τ2 -> _,
      HJ : ?T ⍮ ?X ⍮ ?G ▹{?κ} ?A ⊢ _ : _ |- _ =>
        lazymatch goal with _ : sub_pair T X (G' ▹{κ} A[t2]) (G ▹{κ} A) (q t1) (q t2) |- _ => fail | _ => idtac end;
        (** the binder's sort, of its kind, from the extended context *)
        let HS := fresh "HS" in let HA := fresh "HA" in let S := fresh "S" in
        destruct (ctx_decomp_sort_kind (presup_exp_ctx HJ)) as [_ (S & HS & HA)];
        let Hq := fresh "Hq" in
        pose proof (sub_pair_q _ _ _ _ _ _ _ _ _ Hp HA HS) as Hq;
        pose proof (IH _ _ _ Hq)
    | Hp : sub_pair ?T ?X ?G' ?G ?t1 ?t2,
      IH : forall Γ' τ1 τ2, sub_pair ?T ?X Γ' (?G ▸ ?A ≔ ?M) τ1 τ2 -> _,
      HA : ?T ⍮ ?X ⍮ ?G ⊢ ?A : ?S, HS : type_sort ?S, HM : ?T ⍮ ?X ⍮ ?G ⊢ ?M : ?A |- _ =>
        lazymatch goal with _ : sub_pair T X (G' ▸ A[t2] ≔ M[t2]) (G ▸ A ≔ M) (q t1) (q t2) |- _ => fail | _ => idtac end;
        let Hq := fresh "Hq" in
        pose proof (sub_pair_q_def _ _ _ _ _ _ _ _ _ Hp HA HS HM) as Hq;
        pose proof (IH _ _ _ Hq)
    | Hp : sub_pair ?T ?X ?G' ?G ?t1 ?t2,
      IH : forall Γ' τ1 τ2, sub_pair ?T ?X Γ' (?G ▹ₘ ?U) τ1 τ2 -> _,
      HU : ?T ⍮ ?X ⍮ ?G ⊢ᵘ ?U ≈ ?U, HUU : ?T ⍮ ?X ⍮ ?G' ⊢ᵘ ?U[?t1]ᵘ ≈ ?U[?t2]ᵘ |- _ =>
        lazymatch goal with _ : sub_pair T X (G' ▹ₘ U[t2]ᵘ) (G ▹ₘ U) (q t1) (q t2) |- _ => fail | _ => idtac end;
        let Hq := fresh "Hq" in
        pose proof (sub_pair_q_mod _ _ _ _ _ _ _ Hp HU HUU) as Hq;
        pose proof (IH _ _ _ Hq)
    end;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.

(** A premise of a rule applied at the right images: an induction
    hypothesis turned round, the right side of one, the right image of a
    premise, or a side condition the premise is. *)
Ltac pair_prem :=
  solve [ first
    [ eassumption
    | apply wf_exp_eq_sym; eassumption
    | eapply presup_exp_eq_right; eassumption
    | eapply presup_exp_eq_left; eassumption
    | eapply sub_preserves_univ; eassumption
    | match goal with Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _, HS : type_sort ?S |- _ ⍮ _ ⍮ _ ⊢ _ : ?S =>
        eapply sub_preserves_sort; [ eassumption | exact HS | exact Hr ] end
    | match goal with Hq : sub_pair _ _ _ _ _ _, HS : type_sort ?S |- _ ⍮ _ ⍮ _ ⊢ _ : ?S =>
        eapply sub_preserves_sort; [ eassumption | exact HS | exact (sub_pair_right _ _ _ _ _ _ Hq) ] end
    | match goal with Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ => eapply sub_preserves_exp; [ eassumption | exact Hr ] end
    | match goal with Hq : sub_pair _ _ _ _ _ _ |- _ =>
        eapply sub_preserves_exp; [ eassumption | exact (sub_pair_right _ _ _ _ _ _ Hq) ] end
    | match goal with Hq : sub_pair _ _ _ _ _ _ |- _ =>
        eapply sub_preserves_sort; [ eassumption | apply type_sort_abs_kind, type_sort_universe
                                   | exact (sub_pair_right _ _ _ _ _ _ Hq) ] end
    | constructor
    | apply sort_kind_abs_kind_sort
    | eapply sort_kind_type_sort; eassumption
    | match goal with HS : type_sort ?S |- context [ ?S[?σ] ] => rewrite (type_sort_sub S σ HS); eassumption end ] ].

(** The images of sorts are the sorts, and a weakening inside a lifted
    substitution is outside it. *)
Ltac pair_norm :=
  repeat match goal with
    | Hl : level_closed_sort _ ?S |- _ =>
        lazymatch goal with _ : type_sort S |- _ => fail | _ => pose proof (level_closed_sort_type_sort _ _ Hl) end
    | Hl : module_body_sort ?S |- _ =>
        lazymatch goal with _ : type_sort S |- _ => fail | _ => pose proof (module_body_sort_type_sort _ Hl) end
    end;
  cbn [exp_sub] in *;
  repeat progress (rewrite ?exp_wk_shift_sub_q, ?abs_kind_sort_sub in *);
  cbn [exp_sub] in *;
  repeat match goal with
    | HS : type_sort ?S |- context [ ?S[?σ] ] => rewrite (type_sort_sub S σ HS)
    | HS : type_sort ?S, H : context [ ?S[?σ] ] |- _ => rewrite (type_sort_sub S σ HS) in H
    | HS : sort_kind ?S _ |- context [ ?S[?σ] ] => rewrite (type_sort_sub S σ (sort_kind_type_sort _ _ HS))
    | HS : sort_kind ?S _, H : context [ ?S[?σ] ] |- _ => rewrite (type_sort_sub S σ (sort_kind_type_sort _ _ HS)) in H
    end.

Theorem pair_transport_all :
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> forall Γ' τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
     Θ ⍮ Ξ ⍮ Γ' ⊢ M[τ1] ≈ M[τ2] : A[τ2]) /\
  (forall Θ Ξ Γ A M N, Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A -> True) /\
  (forall Θ Ξ Γ A B, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> True) /\
  (forall Θ Ξ Γ A, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ A -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> forall Γ' τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
     ext_pairs Θ Ξ Γ' Γ τ1 τ2 Ψ /\ ext_pairs Θ Ξ Γ' Γ τ1 τ2 Ψ') /\
  (forall Θ Ξ Γ U V, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ V -> forall Γ' τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
     Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ U[τ1]ᵘ ≈ U[τ2]ᵘ /\ Θ ⍮ Ξ ⍮ Γ' ⊢ᵘ V[τ1]ᵘ ≈ V[τ2]ᵘ) /\
  (forall Θ Ξ Γ H K, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ K -> forall Γ' τ1 τ2, sub_pair Θ Ξ Γ' Γ τ1 τ2 ->
     Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ H[τ1]ᵐ ≈ H[τ2]ᵐ /\ Θ ⍮ Ξ ⍮ Γ' ⊢ᵐ K[τ1]ᵐ ≈ K[τ2]ᵐ) /\
  (forall Θ Ξ Γ R, Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R -> True).
Proof.
  apply syntactic_wf_mut_ind'; intros; try exact I.
  all: match goal with Hp : sub_pair _ _ _ _ _ _ |- _ =>
         let Hr := fresh "Hr" in pose proof (sub_pair_right _ _ _ _ _ _ Hp) as Hr; pair_ih Hp end.
  all: pair_lift.
  (** each telescope's hypothesis, whole *)
  all: repeat match goal with
         | HX : ext_pairs ?T ?X ?G' ?G ?t1 ?t2 ?Y |- _ =>
             lazymatch goal with _ : ext_pair T X G' G t1 t2 Y |- _ => fail | _ => pose proof (ext_pairs_full _ _ _ _ _ _ _ HX) end
         end.
  (** Units and module expressions: symmetry and transitivity read the
      sides' own hypotheses *)
  all: try solve [ split; assumption ].
  (** A closed former, or one whose images agree: reflexivity at the
      right image of the typing *)
  all: try solve [ match goal with |- _ ⍮ _ ⍮ _ ⊢ ?X[?t1] ≈ ?X[?t2] : _ =>
                     replace (X[t1]) with (X[t2]) by (cbn [exp_sub]; reflexivity) end;
                   apply wf_exp_eq_refl; eapply sub_preserves_exp; [ econstructor; eassumption | exact Hr ] ].
  (** Levels and the universe of a level: the congruence, each component
      by its hypothesis *)
  all: try solve [ apply wf_exp_eq_sym; cbn [exp_sub] in *;
                   first [ eapply wf_exp_eq_univ_cong | eapply wf_exp_eq_succl_cong | eapply wf_exp_eq_maxl_cong ];
                   apply wf_exp_eq_sym; eassumption ].
  (** The formers with binders: the congruence at the right images, each
      premise the right image of a premise or a hypothesis, under the
      binder at the lifted pair *)
  all: try solve [ apply wf_exp_eq_sym; rewrite <- ?exp_sub_extend_comm; pair_norm;
                   first [ eapply wf_exp_eq_and_cong | eapply wf_exp_eq_pi_cong | eapply wf_exp_eq_fn_cong
                         | eapply wf_exp_eq_app_cong | eapply wf_exp_eq_absurd_cong ];
                   pair_prem ].
  all: try solve [ apply wf_exp_eq_sym; rewrite <- ?exp_sub_extend_comm; pair_norm;
                   eapply wf_exp_eq_let_cong; pair_prem ].
  (** A constructor, a record type former: closed, at closed types *)
  all: try solve [
    match goal with
    | Hl : ind_lookup _ _ _ = Some ?D, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ (a_con _ _ _)[_] ≈ _ : _ =>
        let HD := fresh "HD" in
        assert (HD : decl_closed D)
          by (eapply gctx_closed_ind; [ eapply wf_gctx_closed, (wf_sub_dom _ _ _ _ _ Hr) | exact Hl ]);
        erewrite (con_ty_sub _ D) by eassumption; cbn [exp_sub];
        eapply wf_exp_eq_con_cong; [ exact (wf_sub_dom _ _ _ _ _ Hr) | eassumption .. ]
    | Hl : record_lookup _ _ _ = Some ?Rd, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ (a_record _)[_] ≈ _ : _ =>
        rewrite record_ty_sub by (eapply wf_record_closed; [ exact (wf_sub_dom _ _ _ _ _ Hr) | exact Hl ]);
        cbn [exp_sub]; eapply wf_exp_eq_record_cong; [ exact (wf_sub_dom _ _ _ _ _ Hr) | eassumption .. ]
    end ].
  (** A record element: by [pair_tuple], its fields' hypotheses at the
      pair *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ (a_tuple _ _)[_] ≈ _ : _ =>
      cbn [exp_sub] in * |-;
      eapply pair_tuple; [ exact Hr | eassumption .. | ];
      let HA := fresh "HA" in let HB := fresh "HB" in intros ? ? ? ? HA HB;
      match goal with IH : forall a b c d, _ -> _ -> forall x y z, sub_pair _ _ x _ y z -> _ |- _ =>
        exact (IH _ _ _ _ HA HB _ _ _ Hp) end
    end ].
  (** A projection: by [pair_proj], the parameters' hypotheses at the
      pair *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ (a_proj _ _)[_] ≈ _ : _ =>
      eapply pair_proj; [ exact Hr | eassumption | eassumption | eassumption | eassumption | eassumption
                        | | eassumption .. ];
      let HA := fresh "HA" in let HB := fresh "HB" in intros ? ? ? HA HB;
      match goal with IH : forall a b c, _ -> _ -> forall x y z, sub_pair _ _ x _ y z -> _ |- _ =>
        exact (IH _ _ _ HA HB _ _ _ Hp) end
    end ].
  (** An alias unit: each side by [pair_unit_alias] *)
  all: try solve [
    match goal with
    | Hp : sub_pair _ _ _ _ _ _ |- _ ⍮ _ ⍮ _ ⊢ᵘ (gu_mk ?Δ (md_alias ?E))[_]ᵘ ≈ _ /\ _ ⍮ _ ⍮ _ ⊢ᵘ (gu_mk ?Δ' (md_alias ?E'))[_]ᵘ ≈ _ =>
        match goal with
        | HΔ : _ ⍮ _ ⍮ _ ⊢ˣ Δ ≈ Δ', HE : _ ⍮ _ ⍮ _ ⊢ᵐ E ≈ E', HE' : _ ⍮ _ ⍮ _ ⊢ᵐ E' ≈ E',
          IHE : forall a b c, sub_pair _ _ a (Δ ++ _) b c -> _ ⍮ _ ⍮ a ⊢ᵐ E[b]ᵐ ≈ E[c]ᵐ /\ _,
          IHE' : forall a b c, sub_pair _ _ a (Δ' ++ _) b c -> _ ⍮ _ ⍮ a ⊢ᵐ E'[b]ᵐ ≈ E'[c]ᵐ /\ _,
          XΔ : ext_pair _ _ _ _ _ _ Δ, XΔ' : ext_pair _ _ _ _ _ _ Δ' |- _ =>
            split;
            [ eapply (pair_unit_alias _ _ _ _ _ _ Δ E); first
                [ exact Hp | exact XΔ | eassumption | exact (wf_modexp_eq_refl_left HE)
                | exact (fun a b c h => proj1 (IHE a b c h)) | eassumption ]
            | eapply (pair_unit_alias _ _ _ _ _ _ Δ' E'); first
                [ exact Hp | exact XΔ' | eassumption | exact HE'
                | exact (fun a b c h => proj1 (IHE' a b c h)) | eassumption ] ]
        end
    end ].
  (** A body unit: by [pair_unit_body_case] *)
  all: try solve [
    match goal with
    | Hp : sub_pair _ _ _ _ _ _ |- _ ⍮ _ ⍮ _ ⊢ᵘ (gu_open _ _)[_]ᵘ ≈ _ /\ _ ⍮ _ ⍮ _ ⊢ᵘ (gu_open _ _)[_]ᵘ ≈ _ =>
        eapply pair_unit_body_case; [ exact Hp | .. ]; first [ eassumption | eapply wf_unit_eq_body; eassumption ]
    end ].
  (** An alias of a literal: by [pair_unit_flatten] *)
  all: try solve [
    match goal with
    | Hp : sub_pair _ _ _ _ _ _, XΔ : ext_pair _ _ _ _ _ _ ?Δ, HΔ : _ ⍮ _ ⍮ _ ⊢ˣ ?Δ ≈ ?Δ,
      HV : _ ⍮ _ ⍮ _ ⊢ᵘ gu_mk ?Δ' ?D ≈ gu_mk ?Δ' ?D,
      IHV : forall a b c, sub_pair _ _ a (?Δ ++ _) b c -> _ ⍮ _ ⍮ a ⊢ᵘ (gu_mk ?Δ' ?D)[b]ᵘ ≈ _ /\ _
      |- _ ⍮ _ ⍮ _ ⊢ᵘ (gu_mk ?Δ (md_alias (me_lit (gu_mk ?Δ' ?D))))[_]ᵘ ≈ _ /\ _ =>
        eapply (pair_unit_flatten _ _ _ _ _ _ Δ Δ' D);
          first [ exact Hp | exact XΔ | exact HΔ | exact HV | exact (fun a b c h => proj1 (IHV a b c h)) | eassumption ]
    end ].
  (** [β] for a literal: by [pair_beta] *)
  all: try solve [
    match goal with
    | Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _, HU : _ ⍮ _ ⍮ _ ⊢ᵘ gu_mk (?Δ ++ ce_ass ?κ ?X :: nil) ?D ≈ _, HN : _ ⍮ _ ⍮ _ ⊢ ?N : ?X,
      IHU : _ ⍮ _ ⍮ _ ⊢ᵘ (gu_mk (?Δ ++ ce_ass ?κ ?X :: nil) ?D)[_]ᵘ ≈ _, IHN : _ ⍮ _ ⍮ _ ⊢ ?N[_] ≈ _ : _
      |- _ ⍮ _ ⍮ _ ⊢ᵐ (me_app (me_lit (gu_mk (?Δ ++ ce_ass ?κ ?X :: nil) ?D)) ?N)[_]ᵐ ≈ _ /\ _ =>
        let HD := fresh "HD" in
        assert (HD : md_open D) by (cbn [md_open]; first [ exact I | reflexivity ]);
        exact (pair_beta _ _ _ _ _ _ Δ κ X D N HD Hr HU HN IHU IHN)
    end ].
  (** An alias with no parameter: by [pair_beta_alias0] *)
  all: try solve [
    match goal with
    | Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _, HE : _ ⍮ _ ⍮ _ ⊢ᵐ ?E ≈ ?E, Hf : frame_free_target _ _ _ ?E, IH : _ ⍮ _ ⍮ _ ⊢ᵐ ?E[_]ᵐ ≈ _
      |- _ ⍮ _ ⍮ _ ⊢ᵐ (me_lit (gu_mk nil (md_alias ?E)))[_]ᵐ ≈ _ /\ _ =>
        split; [ exact (pair_beta_alias0 _ _ _ _ _ _ _ Hr HE Hf IH) | exact IH ]
    end ].
  (** A body unit's expansion: by [pair_unit_expand] *)
  all: try solve [
    match goal with
    | Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _, HU : _ ⍮ _ ⍮ _ ⊢ᵘ gu_open ?Δ ?Φ ≈ gu_open ?Δ ?Φ, IH : _ ⍮ _ ⍮ _ ⊢ᵘ (gu_open ?Δ ?Φ)[_]ᵘ ≈ _
      |- _ ⍮ _ ⍮ _ ⊢ᵘ (gu_open ?Δ ?Φ)[_]ᵘ ≈ _ /\ _ ⍮ _ ⍮ _ ⊢ᵘ (gu_open ?Δ (gm_expand ?Φ))[_]ᵘ ≈ _ =>
        split; [ exact IH | exact (pair_unit_expand _ _ _ _ _ _ _ _ Hr HU IH) ]
    end ].
  (** The eliminator: by [pair_elim] *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _ |- _ ⍮ _ ⍮ _ ⊢ (a_elim _ _ _ _ _ _)[_] ≈ _ : _ =>
      eapply pair_elim; [ exact Hp | .. ]; first [ eassumption | reflexivity ]
    end ].
  (** A member: by [pair_mem] *)
  all: try solve [
    match goal with
    | HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ ?H, Hm : mdenote _ _ _ (me_mem ?H ?x) _, Ht : mdesc_type _ = Some _,
      Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ (a_mem ?H ?x)[_] ≈ _ : _ =>
        eapply pair_mem; [ exact Hr | exact HH | exact Hm | exact Ht | eassumption ]
    end ].
  (** A local module: by [pair_let_mod] *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _ |- _ ⍮ _ ⍮ _ ⊢ (ℓₘ ?U in ?B)[_] ≈ _ : _ =>
      eapply (pair_let_mod _ _ _ _ _ _ U _ _ B Hp); eassumption end ].
  (** A local definition with a module part: by [pair_let_dm] *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _
      |- _ ⍮ _ ⍮ _ ⊢ (ℓᵈ ?A ≔ ?M ‖ (gu_mk nil (md_alias ?E)) in ?B)[_] ≈ _ : _ =>
      cbn [exp_sub] in * |-; eapply (pair_let_dm _ _ _ _ _ _ A M E _ _ _ B Hp); eassumption end ].
  (** A variable: the pair sends it to equal terms *)
  all: try solve [ eapply sub_pair_apply; eassumption ].
  (** Telescopes: each side entry by entry ([ext_pair_nil], [ext_pair_ass],
      [ext_pair_def], [ext_pair_mod], [ext_pair_dm]); a unit's hypothesis
      is its side's half *)
  all: try solve [ split; apply ext_pairs_nil; assumption ].
  all: try solve [
    split; apply ext_pairs_cons; [ eassumption | | eassumption |];
    first
    [ eapply ext_pair_ass; eassumption
    | eapply ext_pair_def; eassumption
    | eapply ext_pair_mod;
        [ eassumption | first [ eapply wf_unit_eq_refl_left; eassumption | eapply wf_unit_eq_refl_right; eassumption ]
        | let Hq := fresh "Hq" in intros ? ? ? Hq;
          match goal with IH : forall a b c, sub_pair _ _ a _ b c -> _ /\ _ |- _ =>
            first [ exact (proj1 (IH _ _ _ Hq)) | exact (proj2 (IH _ _ _ Hq)) ] end ]
    | eapply ext_pair_dm;
        [ eassumption | eassumption | eassumption
        | first [ eapply wf_unit_eq_refl_left; eassumption | eapply wf_unit_eq_refl_right; eassumption ]
        | eassumption | eassumption
        | let Hq := fresh "Hq" in intros ? ? ? Hq;
          match goal with IH : forall a b c, sub_pair _ _ a _ b c -> _ /\ _ |- _ =>
            first [ exact (proj1 (IH _ _ _ Hq)) | exact (proj2 (IH _ _ _ Hq)) ] end ] ] ].
  (** Module expressions with no part to move, a slot and its δ, a
      literal: what the pair sends a slot to, the slot's unit across the
      pair, the literal's unit by its hypothesis *)
  all: try solve [
    match goal with Hp : sub_pair _ _ _ _ _ _, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _ |- _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ /\ _ =>
      split; cbn [modexp_sub];
      first [ eapply (sub_pair_apply_mod _ _ _ _ _ _ Hp); eassumption
            | apply wf_me_lit; first [ eassumption | eapply (sub_pair_apply_unit _ _ _ _ _ _ Hp); eassumption ]
            | eapply wf_me_unit; [ exact (wf_sub_dom _ _ _ _ _ Hr) | eassumption ] ]
    end ].
  (** An application of a module: each side by [pair_me_app], the side's
      own reflexivity from the rule *)
  all: try solve [
    match goal with
    | HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ ?H', Hm : mdenote _ _ _ ?H _, Ht : mdesc_mod_tele _ = Some _, Hv : tele_view _ = Some (_, _),
      Hm' : mdenote _ _ _ ?H' _, Ht' : mdesc_mod_tele _ = Some _, Hv' : tele_view _ = Some (_, _),
      HNN : _ ⍮ _ ⍮ _ ⊢ ?N ≈ ?N' : _, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _
      |- _ ⍮ _ ⍮ _ ⊢ᵐ (me_app ?H ?N)[?t1]ᵐ ≈ _ /\ _ =>
        let HA := fresh "HA" in
        assert (HA : _ ⍮ _ ⍮ _ ⊢ᵐ me_app H N ≈ me_app H' N') by (eapply wf_me_app; eassumption);
        split;
        [ eapply (pair_me_app _ _ _ _ H N (H[t1]ᵐ) (N[t1]));
            [ exact Hr | exact (wf_modexp_eq_refl_left HA) | exact (wf_modexp_eq_refl_left HH) | exact Hm | exact Ht | exact Hv
            | eassumption | eassumption ]
        | eapply (pair_me_app _ _ _ _ H' N' (H'[t1]ᵐ) (N'[t1]));
            [ exact Hr | exact (wf_modexp_eq_refl_right HA) | exact (wf_modexp_eq_refl_right HH) | exact Hm' | exact Ht' | exact Hv'
            | eassumption | eassumption ] ]
    end ].
  (** A selection of a module: each side by [pair_me_mem] *)
  all: try solve [
    match goal with
    | HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ ?H', Hm : mdenote _ _ _ (me_mem ?H ?y) _, Ht : mdesc_mod_tele _ = Some _,
      Hm' : mdenote _ _ _ (me_mem ?H' ?y) _, Ht' : mdesc_mod_tele _ = Some _, Hr : _ ⍮ _ ⍮ _ ⊢ˢ _ : _
      |- _ ⍮ _ ⍮ _ ⊢ᵐ (me_mem ?H ?y)[_]ᵐ ≈ _ /\ _ =>
        split;
        [ eapply pair_me_mem; [ exact Hr | exact (wf_modexp_eq_refl_left HH) | exact Hm | exact Ht | eassumption ]
        | eapply pair_me_mem; [ exact Hr | exact (wf_modexp_eq_refl_right HH) | exact Hm' | exact Ht' | eassumption ] ]
    end ].
  (** A proof: by irrelevance, the left image typed at the left images *)
  all: try solve [ cbn [exp_sub] in * |-;
                   match goal with Hp : sub_pair _ _ _ _ _ _ |- _ =>
                     first [ eapply (pair_proof_tag _ _ _ _ _ _ Hp); eassumption
                           | eapply (pair_conj _ _ _ _ _ _ Hp); eassumption
                           | eapply (pair_left _ _ _ _ _ _ Hp); eassumption
                           | match goal with HM : _ ⍮ _ ⍮ _ ⊢ ?M : Σₚ ?P ?Q |- _ ⍮ _ ⍮ _ ⊢ (a_right ?M)[_] ≈ _ : _ =>
                               eapply (pair_right _ _ _ _ _ _ Hp P Q M); eassumption end ] end ].
  (** Subsumption: the hypothesis, along the right image of the
      refinement *)
  all: try solve [
    match goal with
    | HA : _ ⍮ _ ⍮ _ ⊢ ?A' : ?S, HS : type_sort ?S, Hs : _ ⍮ _ ⍮ _ ⊢ ?A ⊆ ?A',
      IH : _ ⍮ _ ⍮ _ ⊢ ?M[?t1] ≈ ?M[?t2] : ?A[?t2], Hr : _ ⍮ _ ⍮ _ ⊢ˢ ?t2 : _
      |- _ ⍮ _ ⍮ _ ⊢ ?M[?t1] ≈ ?M[?t2] : ?A'[?t2] =>
        eapply wf_exp_eq_subtyp;
          [ exact IH | exact (sub_preserves_sort _ _ _ _ _ _ _ HA HS Hr) | exact HS
          | exact (sub_preserves_subtyp _ _ _ _ _ _ _ Hs Hr) ]
    end ].
  (** An application: at the domain and codomain the function is typed at *)
  all: try solve [
    match goal with
    | HM : _ ⍮ _ ⍮ _ ⊢ ?M : a_pi ?κd ?κc ?A ?B, Hr : _ ⍮ _ ⍮ _ ⊢ˢ ?t2 : _
      |- _ ⍮ _ ⍮ _ ⊢ (a_app ?M ?N)[_] ≈ _ : _ =>
        apply wf_exp_eq_sym; rewrite <- exp_sub_extend_comm; pair_norm;
        eapply wf_exp_eq_app_cong with (A := A[t2]) (B := B[q t2]); pair_prem
    end ].
Qed.

(** ** Moving a Typing to Equal Module Slots *)

(** A typing in [Δ ++ Γ] holds in [Δ2 ++ Γ] for a telescope [Δ2] related
    to [Δ] ([tele_rel]): the term and its type are equal to their images
    along [inline_sub Δ] there ([pair_transport_all] at [sub_pair_inline]),
    so the term is of its type. *)
Theorem slot_transport_exp : forall Θ Ξ Γ Δ Δ2 M T,
    tele_rel Θ Ξ Γ Δ Δ2 -> ⊢ Θ ⍮ Ξ ⍮ Δ2 ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : T -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ M : T.
Proof.
  intros * HR H2 HM.
  pose proof (sub_pair_inline _ _ _ _ _ HR (presup_exp_ctx HM) H2) as Hp.
  pose proof (proj1 pair_transport_all _ _ _ _ _ HM _ _ _ Hp) as X; rewrite exp_sub_id in X.
  pose proof (presup_exp_eq_left X) as HM2.
  pose proof (presup_exp_typ HM) as HTy; inversion HTy as [? S HS HT | HΓ]; subst.
  - pose proof (proj1 pair_transport_all _ _ _ _ _ HT _ _ _ Hp) as Y; rewrite exp_sub_id, (type_sort_sub _ _ HS) in Y.
    exact (tr_conv_back _ _ _ _ _ _ _ HM2 Y HS).
  - exact HM2.
Qed.

(** The context-equivalence transport for a module slot: a typing under a
    slot holds under the slot holding an equal unit. *)
Corollary slot_conv_exp : forall Θ Ξ Γ U U' M T,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ M : T -> Θ ⍮ Ξ ⍮ Γ ▹ₘ U' ⊢ M : T.
Proof.
  intros * HU HM.
  refine (slot_transport_exp _ _ _ (ce_mod U :: nil) (ce_mod U' :: nil) _ _ _ _ HM).
  - constructor; [ constructor | | ]; cbn [inline_sub]; rewrite gunit_sub_id;
      [ apply wf_unit_eq_sym; exact HU | exact (wf_unit_eq_refl_left HU) ].
  - apply wf_ctx_extend_mod; exact (wf_unit_eq_refl_right HU).
Qed.

(** The same for a definition with a module part: its type, its body and
    its unit replaced by equal ones. *)
Corollary slot_conv_exp_dm : forall Θ Ξ Γ A A' N N' E E' i M T,
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E') ->
    Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ N ‖ gu_mk nil (md_alias E) ⊢ M : T ->
    Θ ⍮ Ξ ⍮ Γ ▸ₘ A' ≔ N' ‖ gu_mk nil (md_alias E') ⊢ M : T.
Proof.
  intros * HA HN HU HM.
  refine (slot_transport_exp _ _ _ (ce_dm A N (gu_mk nil (md_alias E)) :: nil) (ce_dm A' N' (gu_mk nil (md_alias E')) :: nil)
            _ _ _ _ HM).
  - eapply tele_rel_dm with (i := i); [ constructor | .. ]; cbn [inline_sub]; rewrite ?exp_sub_id, ?gunit_sub_id.
    + apply wf_exp_eq_sym; exact HA.
    + apply wf_exp_eq_sym; exact HN.
    + exact (wf_exp_eq_refl (presup_exp_eq_left HN)).
    + apply wf_unit_eq_sym; exact HU.
    + exact (wf_unit_eq_refl_left HU).
  - eapply wf_ctx_extend_dm; [ exact (presup_exp_eq_right HA) | | exact (wf_unit_eq_refl_right HU) ].
    exact (tr_conv _ _ _ _ _ _ _ (presup_exp_eq_right HN) HA ltac:(constructor)).
Qed.

(** ** The Example of a Local Open

    In the empty global context and the empty context, [U] is the body
    defining [a : Typeω@1 ≔ Typeω@0] and [U'] the body defining
    [a : (λ X. X) Typeω@1 ≔ Typeω@0]: the two types of [a] differ only by
    [β], so [⊢ᵘ U ≈ U'] ([example_units_eq]).  [L] is the body
    [module where open #0 (a) end] under a slot, storing the definition
    [a : Typeω@1 ≔ #0.a] its open generates.  Under [▹ₘ U], [L.a] is of
    the type [Typeω@1] ([example_member_typed]); under [▹ₘ U'] the open
    would generate [a] at the type [(λ X. X) Typeω@1], so the stored
    definition is no longer the generated one, and [L.a] keeps its type
    all the same ([example_open_member], by [slot_conv_exp]): the stored
    type need only be convertible to the member's ([body_xp_open],
    [gmod_retyped]).  The large universes stand in for a library type such
    as [ℕ], whose declaration would add nothing here.  Every derivation is
    built from the rules, with no hypothesis. *)
Module LocalOpenExample.
Import Stdlib.Strings.String.
#[local] Open Scope string_scope.

(** [U]: the body defining [a : Typeω@1 ≔ Typeω@0] *)
Definition example_unit : gunit :=
  gu_open nil (gm_ext gm_nil "a" (ge_def true false ak_relevant Typeω@1 (Some Typeω@0))).

(** [U']: the body defining [a : (λ X. X) Typeω@1 ≔ Typeω@0] *)
Definition example_unit' : gunit :=
  gu_open nil (gm_ext gm_nil "a" (ge_def true false ak_relevant ((λ Typeω@2 (a_var 0)) $ Typeω@1) (Some Typeω@0))).

(** The definitions [L]'s open stores: [a : Typeω@1 ≔ #0.a] *)
Definition example_open_expansion : gmod :=
  gm_ext gm_nil "a" (ge_def true false ak_relevant Typeω@1 (Some (a_mem (me_var 0) "a"))).

(** [L]: the body [module where open #0 (a) end], storing
    [example_open_expansion] *)
Definition example_open : gunit :=
  gu_open nil (gm_open gm_nil (me_var 0) ((Some "a", "a", false) :: nil) example_open_expansion).

(** The empty global context is well formed. *)
Lemma example_gctx_wf : ⊢ᵍ nil ⍮ nil.
Proof. constructor; constructor. Qed.

(** The empty context is well formed. *)
Lemma example_ctx_wf : ⊢ nil ⍮ nil ⍮ ⋅.
Proof. constructor; exact example_gctx_wf. Qed.

(** The context of the bound variable of [λ X. X]. *)
Lemma example_binder_ctx_wf : ⊢ nil ⍮ nil ⍮ ⋅ ▹{ak_relevant} Typeω@2.
Proof. eapply wf_ctx_extend; [ apply wf_typ; exact example_ctx_wf | constructor ]. Qed.

(** The type of [a] in [U'] is the one in [U], by [β]. *)
Lemma example_redex_eq : nil ⍮ nil ⍮ ⋅ ⊢ (λ Typeω@2 #0) $ Typeω@1 ≈ Typeω@1 : Typeω@2.
Proof.
  assert (H : nil ⍮ nil ⍮ ⋅ ⊢ (λ Typeω@2 #0) $ Typeω@1 ≈ (a_var 0)[Id,,Typeω@1] : (Typeω@2)[Id,,Typeω@1]).
  { eapply wf_exp_eq_pi_beta with (Srt := Typeω@3) (κd := ak_relevant) (κc := ak_relevant) (i := 3).
    - apply wf_typ; exact example_ctx_wf.
    - constructor.
    - apply wf_typ; exact example_binder_ctx_wf.
    - constructor.
    - eapply wf_vlookup; [ exact example_binder_ctx_wf |].
      change (⋅ ▹{ak_relevant} Typeω@2 ∋ #0 : (Typeω@2)[↑]ʷ); constructor.
    - apply wf_typ; exact example_ctx_wf. }
  cbn in H; exact H.
Qed.

(** The premises of [wf_unit_eq_body] on the entries named [y]: [y] is
    [a], whose prefixes, terms and fills are computed, or no entry. *)
Ltac example_entry_cases :=
  intros;
  match goal with y : string |- _ =>
    let Ey := fresh "Ey" in
    destruct (String.eqb y "a") eqn:Ey; [ apply String.eqb_eq in Ey; subst y | ];
    repeat match goal with H : gm_prefix_upto _ _ = Some _ |- _ =>
      cbn in H; rewrite ?String.eqb_refl in H; try rewrite Ey in H; cbn in H;
      first [ discriminate H | inversion H; subst; clear H ] end end;
  repeat match goal with H : entry_tm _ = Some _ |- _ => cbn in H; inversion H; subst; clear H end;
  repeat match goal with H : entry_unit _ = Some _ |- _ => cbn in H; discriminate H end;
  repeat match goal with H : gm_fill _ = Some _ |- _ => cbn in H; inversion H; subst; clear H end;
  rewrite ?exp_sub_id; cbn [List.app entry_kind].

(** [⊢ᵘ U ≈ U']: one entry each, of types equal by [β]. *)
Lemma example_units_eq : nil ⍮ nil ⍮ ⋅ ⊢ᵘ example_unit ≈ example_unit'.
Proof.
  unfold example_unit, example_unit'.
  eapply wf_unit_eq_body with (entry_sort := fun _ => Typeω@2) (param_level := 0) (param_sorts := fun _ => Typeω@0)
    (lv := true) (lv' := true) (Rt := mdesc_open nil gm_nil gm_nil) (Rt' := mdesc_open nil gm_nil gm_nil)
    (Φx := gm_ext gm_nil "a" (ge_def true false ak_relevant Typeω@1 (Some Typeω@0)))
    (Φx' := gm_ext gm_nil "a" (ge_def true false ak_relevant ((λ Typeω@2 (a_var 0)) $ Typeω@1) (Some Typeω@0))).
  all: try example_entry_cases.
  all: try solve [ constructor ].
  all: try solve [ apply wf_typ; exact example_ctx_wf ].
  all: try solve [ apply wf_exp_eq_refl; apply wf_typ; exact example_ctx_wf ].
  all: try solve [ intros [| k] ? ? H; cbn in H; discriminate H ].
  all: try solve [ intros [| k] ? ? ? ? ? ? H; cbn in H; discriminate H ].
  all: try solve [ intros ? ? ? ? H; destruct Δ1; discriminate H ].
  all: try solve [ intros; discriminate ].
  all: try solve [ cbn; repeat split ].
  all: try solve [ apply body_xp_ext, body_xp_nil ].
  all: try solve [ cbn; constructor; [ intros [] | constructor ] ].
  all: try solve [ intros _ ? ? ? ? H; destruct Δ1; discriminate H ].
  all: try solve [ apply wf_exp_eq_sym; exact example_redex_eq ].
  all: try solve [ exact (presup_exp_eq_left example_redex_eq) ].
  all: try solve [ eapply wf_conv_sort; [ apply wf_typ; exact example_ctx_wf | exact (presup_exp_eq_left example_redex_eq)
                                        | constructor | apply wf_exp_eq_sym; exact example_redex_eq ] ].
  all: try solve [ constructor; exact example_ctx_wf ].
  all: apply ext_of_ctx'; cbn [body_ctx List.app].
  - eapply wf_ctx_extend_def; [ apply wf_typ; exact example_ctx_wf | constructor | apply wf_typ; exact example_ctx_wf ].
  - eapply wf_ctx_extend_def;
      [ exact (presup_exp_eq_left example_redex_eq) | constructor
      | eapply wf_conv_sort; [ apply wf_typ; exact example_ctx_wf | exact (presup_exp_eq_left example_redex_eq)
                             | constructor | apply wf_exp_eq_sym; exact example_redex_eq ] ].
Qed.

(** The context [⋅ ▹ₘ U] is well formed. *)
Lemma example_slot_ctx_wf : ⊢ nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit.
Proof. apply wf_ctx_extend_mod; exact (wf_unit_eq_refl_left example_units_eq). Qed.

(** The large universes under the slot. *)
Lemma example_slot_universe : forall i, nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit ⊢ Typeω@i : Typeω@(S i).
Proof. intros; apply wf_typ; exact example_slot_ctx_wf. Qed.

(** The slot is a module expression. *)
Lemma example_slot_var : nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit ⊢ᵐ me_var 0 ≈ me_var 0.
Proof. eapply wf_me_var; [ exact example_slot_ctx_wf | constructor ]. Qed.

(** [#0.a] denotes [U]'s [a]. *)
Lemma example_slot_denote :
  mdenote nil nil (⋅ ▹ₘ example_unit) (me_mem (me_var 0) "a") (mdesc_term ak_relevant Typeω@1 (Some Typeω@0)).
Proof.
  eapply mdenote_mem.
  - eapply mdenote_slot; [ constructor |]; eapply udenote_body; [| reflexivity ]; cbn; apply body_xp_ext, body_xp_nil.
  - reflexivity.
  - cbn; reflexivity.
  - cbn; apply edenote_def.
  - cbn; reflexivity.
Qed.

(** [#0.a : Typeω@1] under the slot. *)
Lemma example_slot_member : nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit ⊢ a_mem (me_var 0) "a" : Typeω@1.
Proof.
  eapply wf_mem; [ exact example_slot_var | exact example_slot_denote | reflexivity | apply example_slot_universe | constructor |].
  intros M HM; cbn in HM; injection HM as <-; apply example_slot_universe.
Qed.

(** [L]'s open expands to the stored definition, the one it generates. *)
Lemma example_open_xp :
  body_xp nil nil (⋅ ++ ⋅ ▹ₘ example_unit) (gm_open gm_nil (me_var 0) ((Some "a", "a", false) :: nil) example_open_expansion)
    example_open_expansion.
Proof.
  change example_open_expansion with (gm_graft gm_nil example_open_expansion) at 2.
  eapply body_xp_open with (gs := generated_item_def "a" false ak_relevant Typeω@1 (a_mem (me_var 0) "a") :: nil).
  - apply body_xp_nil.
  - cbn; eapply mdenote_slot; [ constructor |]; eapply udenote_body; [| reflexivity ]; cbn; apply body_xp_ext, body_xp_nil.
  - reflexivity.
  - eapply items_gen_def; [ exact example_slot_denote | apply items_gen_nil ].
  - cbn; split; reflexivity.
  - cbn; repeat constructor.
Qed.

(** [L] is a unit under the slot. *)
Lemma example_open_unit : nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit ⊢ᵘ example_open ≈ example_open.
Proof.
  unfold example_open.
  eapply wf_unit_eq_body with (entry_sort := fun _ => Typeω@2) (param_level := 0) (param_sorts := fun _ => Typeω@0)
    (lv := true) (lv' := true) (Rt := mdesc_open nil gm_nil gm_nil) (Rt' := mdesc_open nil gm_nil gm_nil)
    (Φx := example_open_expansion) (Φx' := example_open_expansion); unfold example_open_expansion.
  all: try exact example_open_xp.
  all: try example_entry_cases.
  all: try solve [ constructor ].
  all: try solve [ apply example_slot_universe ].
  all: try solve [ apply wf_exp_eq_refl; apply example_slot_universe ].
  all: try solve [ exact example_slot_member ].
  all: try solve [ apply wf_exp_eq_refl; exact example_slot_member ].
  all: try solve [ intros ? ? ? ? H; destruct Δ1; discriminate H ].
  all: try solve [ intros; discriminate ].
  all: try solve [ intros _ ? ? ? ? H; destruct Δ1; discriminate H ].
  all: try solve [ cbn; repeat split ].
  all: try solve [ cbn; constructor; [ intros [] | constructor ] ].
  (** the open's target, the slot: a module expression, no open frame *)
  all: try solve [ intros [| [| k]] ? ? H; cbn in H; try discriminate H; injection H as <- <-; exact example_slot_var ].
  all: try solve [ intros [| [| k]] ? ? H; cbn in H; try discriminate H; injection H as <- <-;
                   eexists; split;
                   [ cbn; eapply mdenote_slot; [ constructor | eapply udenote_body; [ cbn; apply body_xp_ext, body_xp_nil | reflexivity ] ]
                   | intros (? & ? & ? & ? & ? & Hc & _); discriminate Hc ] ].
  all: try solve [ intros [| [| k]] ? ? ? ? ? ? H H'; cbn in H, H'; try discriminate H; injection H as <- <-; injection H' as <- <-;
                   intros Hs Hs'; cbn in Hs, Hs'; injection Hs as <-; injection Hs' as <-; rewrite modexp_sub_id; exact example_slot_var ].
  all: try solve [ constructor; exact example_slot_ctx_wf ].
  all: apply ext_of_ctx'; cbn [body_ctx List.app];
    eapply wf_ctx_extend_def; [ apply example_slot_universe | constructor | exact example_slot_member ].
Qed.

(** [L.a] denotes the stored definition. *)
Lemma example_open_denote :
  mdenote nil nil (⋅ ▹ₘ example_unit) (me_mem (me_lit example_open) "a")
    (mdesc_term ak_relevant Typeω@1 (Some (a_mem (me_var 0) "a"))).
Proof.
  eapply mdenote_mem.
  - apply mdenote_lit; eapply udenote_body; [ exact example_open_xp | reflexivity ].
  - reflexivity.
  - cbn; reflexivity.
  - cbn; apply edenote_def.
  - cbn; reflexivity.
Qed.

(** [L.a : Typeω@1] under [▹ₘ U]. *)
Lemma example_member_typed : nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit ⊢ a_mem (me_lit example_open) "a" : Typeω@1.
Proof.
  eapply wf_mem; [ apply wf_me_lit; exact example_open_unit | exact example_open_denote | reflexivity
                 | apply example_slot_universe | constructor |].
  intros M HM; cbn in HM; injection HM as <-; exact example_slot_member.
Qed.

(** [L.a : Typeω@1] under [▹ₘ U'], by the transport. *)
Example example_open_member : nil ⍮ nil ⍮ ⋅ ▹ₘ example_unit' ⊢ a_mem (me_lit example_open) "a" : Typeω@1.
Proof. exact (slot_conv_exp _ _ _ _ _ _ _ example_units_eq example_member_typed). Qed.
End LocalOpenExample.
