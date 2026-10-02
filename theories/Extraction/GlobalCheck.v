From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Extraction Require Import PseudoMonadic TypeCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding the Global-Context Judgments

    The decision procedures the command interpreter needs, built on
    [Extraction.TypeCheck]: well-formedness of local contexts [⊢ Θ ⍮ Ξ ⍮ Γ],
    of types and of terms.

    [wf_gdep] and [wf_gdeps] are not decided here: the levels are what a unit
    is compiled against, and they are given already checked.  [Θ] is
    therefore a parameter of everything below, and only [Ξ] and the local
    context are traversed. *)

(** [wf_gctx] is the only judgment of its block whose constructor is not a
    global hint, since nothing in the metatheory builds a [⊢g] forwards.  The
    decision procedures below do, so it is a local hint here. *)
#[local]
Hint Constructors wf_gctx : mctt.
#[local]
Hint Resolve wf_gctx_stack : mctt.

(** ** The Bridge to the Algorithmic Judgments

    The algorithmic judgments take their global context as an instance [GC]
    and read it as [gc_deps GC] and [gc_stack GC].  Unifying that with an
    explicit [Θ ⍮ Ξ] would require solving [gc_deps ?GC ≟ Θ], which no
    unifier does, so this section instantiates [GC] by hand.  Below it, only
    the explicit forms appear. *)

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
    (** [exact] rather than [eapply]: [nf_to_exp Typeⁿ@i] and [Type@i] are
        convertible, but the unifier cannot unify them in this direction. *)
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

  (** Every expression is a [user_exp] ([user_exp_all]), so completeness has
      no side condition on this side of the bridge. *)
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

  (** The two ways "is [A] a type?" can fail: nothing is inferred for [A], or
      what is inferred is not a universe.  Each contradicts completeness, the
      second through functionality of inference. *)
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

(** [get_level_of_type_nf] returns its witness as an equation between two
    [nf]s; the obligations that use it need the levels instead. *)
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

  (** "Is [A] a type?", decided as in the Π case of [type_check]: infer a type
      for [A], then require it to be a universe. *)
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
    (** The type of a well-typed term is a type, so if [A] is not one, the
        judgment cannot hold. *)
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

    By structural recursion on [Γ]: the base case appeals to the
    well-formedness of the global context, and each step is one call of
    [check_typ]. *)

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

(** Freshness is non-membership in [gm_names], so [in_dec] decides it, with
    the two outcomes swapped. *)
Definition check_gm_fresh (x : string) (Φ : gmod) : { gm_fresh x Φ } + { ~ gm_fresh x Φ } :=
  match List.in_dec String.string_dec x (gm_names Φ) with
  | left h => right (fun hfresh => hfresh h)
  | right h => left h
  end.

(** [Extraction.Command] checks one command at a time, so these are all the
    decision procedures it needs: a context, a type, a term, and freshness of
    a member's name.  The global judgments themselves are never decided; the
    interpreter builds them command by command. *)
