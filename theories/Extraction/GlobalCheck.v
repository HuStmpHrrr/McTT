From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Extraction Require Import PseudoMonadic TypeCheck.
From Mctt.Frontend Require Import Elaborator.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding the Global-Context Judgments

    The elaborator hands the driver a [gstack] and one obligation per [eval],
    and nothing proves that stack well formed — so the driver has to check it.
    These are the decision procedures for the six judgments it needs, on top of
    [Extraction.TypeCheck]: [⊢ Θ ⍮ Ξ ⍮ Γ], [⊢e], [⊢m], [⊢u], [wf_gstack] and
    [⊢g].

    [wf_gdep]/[wf_gdeps] are *not* decided here: the levels are what a unit is
    compiled against, so the driver is given them already checked ([nil], for
    now — see deviation 3 in [AGENT/modules.md]).  [Θ] is therefore a parameter
    of everything below, and only [Ξ] and the local context are traversed. *)

(** [wf_gctx] is the one judgment of the block whose constructor is not a global
    hint — nothing in the metatheory builds a [⊢g] forwards.  Every decision
    procedure below does. *)
#[local]
Hint Constructors wf_gctx : mctt.
#[local]
Hint Resolve wf_gctx_stack : mctt.

(** ** The Bridge to the Algorithmic Judgments

    Everything algorithmic fixes its global context as an instance and so reads
    it as [gc_deps GC]/[gc_stack GC].  Unifying that against an explicit
    [Θ ⍮ Ξ] would ask for a solution of [gc_deps ?GC ≟ Θ], which no unifier
    finds, so each crossing instantiates [GC] by hand — once, here.  Below this
    section only the long forms appear. *)

Section Bridge.

  Lemma alg_type_infer_sound' : forall Θ Ξ Γ (A : nf) M,
      @alg_type_infer (gc_mk Θ Ξ) Γ A M ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
  Proof.
    intros; eapply (alg_type_infer_sound (GC := gc_mk Θ Ξ)); eassumption.
  Qed.

  Lemma alg_type_infer_typ_sound' : forall Θ Ξ Γ i A,
      @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@i A ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
  Proof.
    (** [exact], not [eapply]: [nf_to_exp Typeⁿ@i] and [Type@i] are convertible
        but unifying them the other way round is beyond the unifier. *)
    intros * H HΓ; exact (alg_type_infer_sound' _ _ _ Typeⁿ@i _ H HΓ).
  Qed.

  Lemma alg_type_check_sound' : forall Θ Ξ Γ i A M,
      @alg_type_check (gc_mk Θ Ξ) Γ A M ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
  Proof.
    intros; eapply (alg_type_check_sound (GC := gc_mk Θ Ξ)); eassumption.
  Qed.

  (** [user_exp] no longer restricts anything ([user_exp_all]), so completeness
      of the algorithm carries no side condition on this side of the bridge. *)
  Lemma alg_type_check_complete' : forall Θ Ξ Γ A M,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      @alg_type_check (gc_mk Θ Ξ) Γ A M.
  Proof.
    intros; eapply (alg_type_check_complete (GC := gc_mk Θ Ξ));
      [ apply user_exp_all | eassumption ].
  Qed.

  Lemma alg_type_infer_typ_complete' : forall Θ Ξ Γ i A,
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i ->
      exists j, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@j A.
  Proof.
    intros * H.
    assert (exists j, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@j A /\ j <= i) as [j []]
        by (eapply (alg_type_infer_typ_complete (GC := gc_mk Θ Ξ));
            [ apply user_exp_all | eassumption ]).
    eauto.
  Qed.

  (** The two ways "is [A] a type?" fails: nothing is inferred for [A], or what
      is inferred is not a universe.  Each contradicts completeness, the second
      through functionality of inference. *)
  Lemma not_wf_typ_of_no_infer : forall Θ Ξ Γ A,
      (forall B : nf, ~ @alg_type_infer (gc_mk Θ Ξ) Γ B A) ->
      forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
  Proof.
    intros * Hno * H.
    assert (exists j, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@j A) as [j]
        by eauto using alg_type_infer_typ_complete'.
    firstorder.
  Qed.

  Lemma not_wf_typ_of_infer_not_typ : forall Θ Ξ Γ A (B : nf),
      @alg_type_infer (gc_mk Θ Ξ) Γ B A ->
      (forall i, B <> Typeⁿ@i) ->
      forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i.
  Proof.
    intros * HB Hne * H.
    assert (exists j, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@j A) as [j HA]
        by eauto using alg_type_infer_typ_complete'.
    assert (B = Typeⁿ@j)
      by (eapply (functional_alg_type_infer (GC := gc_mk Θ Ξ)); eassumption).
    firstorder.
  Qed.

End Bridge.

#[local]
Hint Resolve alg_type_infer_typ_sound' alg_type_check_sound'
  alg_type_check_complete' not_wf_typ_of_no_infer not_wf_typ_of_infer_not_typ : mctt.

(** ** Types and Terms at an Explicit Global Context *)

(** [get_level_of_type_nf] hands its witness back as an equation between two
    [nf]s; every obligation that uses it wants the levels instead. *)
#[local]
Ltac invert_nf_typ_eq :=
  subst;
  repeat match goal with
    | H : Typeⁿ@?i = Typeⁿ@?j |- _ => assert (i = j) by congruence; clear H; subst
    end.

Section check_exp.

  #[local]
  Ltac check_typ_tac :=
    intros;
    cbn beta in *;
    destruct_conjs;
    invert_nf_typ_eq;
    try eassumption;
    lazymatch goal with
    | |- type_infer_order _ => apply user_exp_to_type_infer_order, user_exp_all
    | _ => mautosolve 3
    end.

  (** "Is [A] a type?", asked exactly as [type_check]'s Π case asks it: infer a
      type for [A], then insist the answer is a universe. *)
  #[tactic="check_typ_tac",derive(equations=no,eliminator=no)]
  Equations check_typ Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A :
    { i | Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i } + { forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@i } :=
  | Θ, Ξ, Γ, HΓ, A =>
      let*o (exist _ UA _) := @type_infer (gc_mk Θ Ξ) Γ _ A _ while _ in
      let*o (exist _ i _) := get_level_of_type_nf UA while _ in
      pureo (exist _ i _)
  .

  #[local]
  Ltac check_exp_tac :=
    intros;
    cbn beta in *;
    destruct_conjs;
    invert_nf_typ_eq;
    try eassumption;
    lazymatch goal with
    | |- type_check_order _ => apply tc_ti, user_exp_to_type_infer_order, user_exp_all
    | |- exists _, _ => eexists; eassumption
    (** The type of a well-typed term is a type, so failing to see that [A] is
        one already rules the judgment out. *)
    | |- ~ _ ⍮ _ ⍮ _ ⊢ _ : _ => intro; gen_presups; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  #[tactic="check_exp_tac",derive(equations=no,eliminator=no)]
  Equations check_exp Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A M :
    { Θ ⍮ Ξ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A } :=
  | Θ, Ξ, Γ, HΓ, A, M =>
      let*o->b (exist _ i _) := check_typ Θ Ξ Γ HΓ A while _ in
      let*b _ := @type_check (gc_mk Θ Ξ) Γ A _ M _ while _ in
      pureb _
  .

End check_exp.

(** ** Local Contexts

    Structural on [Γ]: the base case is where the global context is appealed to,
    and the step case is one call of [check_typ]. *)

Section check_ctx.

  #[local]
  Ltac check_ctx_tac :=
    intros;
    cbn beta in *;
    try eassumption;
    lazymatch goal with
    | |- ~ ⊢ _ ⍮ _ ⍮ _ => intro; gen_presups; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  #[tactic="check_ctx_tac",derive(equations=no,eliminator=no)]
  Equations check_ctx Θ Ξ (HΞ : ⊢g Θ ⍮ Ξ) Γ :
    { ⊢ Θ ⍮ Ξ ⍮ Γ } + { ~ ⊢ Θ ⍮ Ξ ⍮ Γ } :=
  | Θ, Ξ, HΞ, ⋅ => pureb _
  | Θ, Ξ, HΞ, Γ ▹ A =>
      let*b HΓ := check_ctx Θ Ξ HΞ Γ while _ in
      let*o->b (exist _ i _) := check_typ Θ Ξ Γ HΓ A while _ in
      pureb _
  .

End check_ctx.

(** ** Pushing a Frame

    An entry of [Φ ⊳ x ↦ E] is checked with [gu_mk Δ Φ] as the innermost frame,
    so the recursion has to *build* a global context out of the module it has
    checked so far. *)
Lemma wf_gctx_push : forall Θ Ξ Δ Φ,
    ⊢g Θ ⍮ Ξ ->
    Θ ⍮ Ξ ⍮ Δ ⊢m Φ ->
    ⊢g Θ ⍮ (gu_mk Δ Φ :: Ξ).
Proof.
  intros * HΞ HΦ.
  apply wf_gctx_intro, wf_gstack_cons;
    [ now apply wf_gctx_stack | now apply wf_gunit_intro ].
Qed.

#[local]
Hint Resolve wf_gctx_push : mctt.

(** Freshness is a non-membership of [gm_names], so [in_dec] decides it; the
    orientation is the only thing to fix. *)
Definition check_gm_fresh (x : string) (Φ : gmod) : { gm_fresh x Φ } + { ~ gm_fresh x Φ } :=
  match List.in_dec String.string_dec x (gm_names Φ) with
  | left h => right (fun hfresh => hfresh h)
  | right h => left h
  end.

(** ** Entries and Modules

    Mutually structural on the [gentry]/[gmod] being checked.  The stack is a
    *parameter*, not the measure: [wf_gmod_ext] checks its entry one frame
    deeper, so [Ξ] grows exactly where [Φ] shrinks. *)

Section check_gmod.

  #[local]
  Ltac check_gmod_tac :=
    intros;
    cbn beta in *;
    try eassumption;
    lazymatch goal with
    | |- ~ _ => intro; progressive_inversion; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  #[tactic="check_gmod_tac",derive(equations=no,eliminator=no)]
  Equations check_gmod Θ Ξ (HΞ : ⊢g Θ ⍮ Ξ) Δ Φ :
    { Θ ⍮ Ξ ⍮ Δ ⊢m Φ } + { ~ Θ ⍮ Ξ ⍮ Δ ⊢m Φ } by struct Φ :=
  | Θ, Ξ, HΞ, Δ, ⋄ =>
      let*b _ := check_ctx Θ Ξ HΞ Δ while _ in
      pureb _
  | Θ, Ξ, HΞ, Δ, Φ ⊳ x ↦ E =>
      let*b HΦ := check_gmod Θ Ξ HΞ Δ Φ while _ in
      let*b _ := check_entry Θ (gu_mk Δ Φ :: Ξ) _ E while _ in
      let*b _ := check_gm_fresh x Φ while _ in
      pureb _
  with check_entry Θ Ξ (HΞ : ⊢g Θ ⍮ Ξ) E :
    { Θ ⍮ Ξ ⊢e E } + { ~ Θ ⍮ Ξ ⊢e E } by struct E :=
  | Θ, Ξ, HΞ, ge_def b pv A None =>
      let*o->b (exist _ i _) := check_typ Θ Ξ ⋅ _ A while _ in
      pureb _
  | Θ, Ξ, HΞ, ge_def b pv A (Some M) =>
      let*b _ := check_exp Θ Ξ ⋅ _ A M while _ in
      pureb _
  | Θ, Ξ, HΞ, ge_mod Δ Φ =>
      let*b _ := check_gmod Θ Ξ HΞ Δ Φ while _ in
      pureb _
  .

End check_gmod.

(** ** Units, the Stack, and the Global Context *)

Section check_gctx.

  #[local]
  Ltac check_gctx_tac :=
    intros;
    cbn beta in *;
    try eassumption;
    lazymatch goal with
    | |- ~ _ => intro; progressive_inversion; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  (** A unit's parameters are its whole telescope, so there is no ambient one to
      extend: the module is checked at [gu_params U] and nowhere else. *)
  #[tactic="check_gctx_tac",derive(equations=no,eliminator=no)]
  Equations check_gunit Θ Ξ (HΞ : ⊢g Θ ⍮ Ξ) U :
    { Θ ⍮ Ξ ⊢u U } + { ~ Θ ⍮ Ξ ⊢u U } :=
  | Θ, Ξ, HΞ, U =>
      let*b _ := check_gmod Θ Ξ HΞ (gu_params U) (gu_mod U) while _ in
      pureb _
  .

  (** Structural on [Ξ]: a frame is checked against the frames outside it, which
      are exactly the ones already checked. *)
  #[tactic="check_gctx_tac",derive(equations=no,eliminator=no)]
  Equations check_gstack Θ (HΘ : wf_gdeps Θ) Ξ :
    { wf_gstack Θ Ξ } + { ~ wf_gstack Θ Ξ } :=
  | Θ, HΘ, nil => pureb _
  | Θ, HΘ, U :: Ξ =>
      let*b HΞ := check_gstack Θ HΘ Ξ while _ in
      let*b _ := check_gunit Θ Ξ _ U while _ in
      pureb _
  .

  #[tactic="check_gctx_tac",derive(equations=no,eliminator=no)]
  Equations check_gctx Θ (HΘ : wf_gdeps Θ) Ξ :
    { ⊢g Θ ⍮ Ξ } + { ~ ⊢g Θ ⍮ Ξ } :=
  | Θ, HΘ, Ξ =>
      let*b _ := check_gstack Θ HΘ Ξ while _ in
      pureb _
  .

End check_gctx.

(** ** What the Driver Calls

    One compilation unit at a time, so there are no dependency levels to check
    (deviation 3 in [AGENT/modules.md]).  A checked global context is what
    [type_check_closed] and [type_infer_closed] ask for, and [wf_ctx_empty]
    turns it into the empty local context an [eval] obligation is checked in. *)

Lemma wf_gctx_empty : ⊢g nil ⍮ nil.
Proof. mauto 3. Qed.

Definition check_gctx_closed : forall Ξ, { ⊢g nil ⍮ Ξ } + { ~ ⊢g nil ⍮ Ξ } :=
  check_gctx nil wf_gdeps_nil.

(** The definitions that follow the last [eval] are seen by no obligation, so
    the unit is checked too — on the empty stack, a unit's parameters being its
    whole telescope. *)
Definition check_gunit_closed : forall U, { nil ⍮ nil ⊢u U } + { ~ nil ⍮ nil ⊢u U } :=
  check_gunit nil nil wf_gctx_empty.

Section check_ctx_closed.

  #[local]
  Ltac check_ctx_closed_tac :=
    intros;
    cbn beta in *;
    lazymatch goal with
    | |- ~ _ => intro; progressive_inversion; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  #[tactic="check_ctx_closed_tac",derive(equations=no,eliminator=no)]
  Equations check_ctx_closed Ξ : { ⊢ nil ⍮ Ξ ⍮ ⋅ } + { ~ ⊢ nil ⍮ Ξ ⍮ ⋅ } :=
  | Ξ =>
      let*b _ := check_gctx_closed Ξ while _ in
      pureb _
  .

End check_ctx_closed.

Extraction Inline check_gmod_functional check_entry_functional.
Extraction Inline check_gctx check_gctx_closed.

(** The decision procedures above carry their soundness proofs; completeness is
    the usual [dec_complete]. *)

Lemma check_gctx_complete : forall Θ (HΘ : wf_gdeps Θ) Ξ,
    ⊢g Θ ⍮ Ξ ->
    exists H, check_gctx Θ HΘ Ξ = left H.
Proof. intros; dec_complete. Qed.

Lemma check_gctx_closed_complete : forall Ξ,
    ⊢g nil ⍮ Ξ ->
    exists H, check_gctx_closed Ξ = left H.
Proof. intros; dec_complete. Qed.

Lemma check_ctx_closed_complete : forall Ξ,
    ⊢ nil ⍮ Ξ ⍮ ⋅ ->
    exists H, check_ctx_closed Ξ = left H.
Proof. intros; dec_complete. Qed.

Lemma check_gunit_closed_complete : forall U,
    nil ⍮ nil ⊢u U ->
    exists H, check_gunit_closed U = left H.
Proof. intros; dec_complete. Qed.
