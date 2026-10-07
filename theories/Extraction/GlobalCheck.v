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

    [⊢g Θ ⍮ nil] is not decided here: the filed units are what a unit is
    compiled against, and they are given already checked.  [Θ] is
    therefore a parameter of everything below, and only [Ξ] and the local
    context are traversed. *)

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

  Lemma alg_type_infer_large_typ_sound' : forall Θ Ξ Γ i A,
      @alg_type_infer (gc_mk Θ Ξ) Γ Typeωⁿ@i A ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
  Proof.
    (** [exact] rather than [eapply]: [nf_to_exp Typeωⁿ@i] and [Typeω@i] are
        convertible, but the unifier cannot unify them in this direction. *)
    intros * H HΓ; exact (alg_type_infer_sound' _ _ _ Typeωⁿ@i _ H HΓ).
  Qed.

  (** Soundness at the inferred universe, precisely: a type that infers the
      universe [u] is a type of [unf_tm u], at either tier. *)
  Lemma alg_type_infer_typ_sound' : forall Θ Ξ Γ UA u A,
      @alg_type_infer (gc_mk Θ Ξ) Γ UA A ->
      is_univ_nf UA u ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : unf_tm u.
  Proof.
    intros * H Hu HΓ.
    rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu).
    exact (alg_type_infer_sound' _ _ _ UA _ H HΓ).
  Qed.

  (** The same at an index of either tier: a type of [unf_tm u] is one of the
      large universe [Typeω@(unf_large u)] the index lives at. *)
  Lemma alg_type_infer_univ_sound' : forall Θ Ξ Γ UA u A,
      @alg_type_infer (gc_mk Θ Ξ) Γ UA A ->
      is_univ_nf UA u ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(unf_large u).
  Proof.
    intros * H Hu HΓ.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : unf_tm u)
      by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
          exact (alg_type_infer_sound' _ _ _ UA _ H HΓ)).
    exact (wf_exp_unf_large (GC := gc_mk Θ Ξ) ltac:(eassumption)).
  Qed.

  Lemma alg_type_check_sound' : forall Θ Ξ Γ i A M,
      @alg_type_check (gc_mk Θ Ξ) Γ A M ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
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

  (** A type of a large universe infers a universe, at either tier. *)
  Lemma alg_type_infer_large_typ_complete' : forall Θ Ξ Γ i A,
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
      exists UA u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_univ_nf UA u.
  Proof.
    intros * H.
    assert (exists UA u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]]
        by (eapply (alg_type_infer_large_typ_complete (GC := gc_mk Θ Ξ));
            [ apply user_exp_all | eassumption ]).
    eauto.
  Qed.

  (** A small type infers a small universe at a literal level below its own. *)
  Lemma alg_type_infer_typ_complete' : forall Θ Ξ Γ n A,
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@n ->
      exists m, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@m A /\ m <= n.
  Proof.
    intros * H.
    exact (alg_type_infer_typ_complete (GC := gc_mk Θ Ξ) (user_exp_all _) H).
  Qed.

  (** The two ways "is [A] a type?" can fail: nothing is inferred for [A], or
      what is inferred is not a universe.  Each contradicts completeness, the
      second through functionality of inference. *)
  Lemma not_wf_typ_of_no_infer : forall Θ Ξ Γ A,
      (forall B : nf, ~ @alg_type_infer (gc_mk Θ Ξ) Γ B A) ->
      forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
  Proof.
    intros * Hno * H.
    assert (exists UA u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_univ_nf UA u) as [UA [u []]]
        by eauto using alg_type_infer_large_typ_complete'.
    firstorder.
  Qed.

  Lemma not_wf_typ_of_infer_not_typ : forall Θ Ξ Γ A (B : nf),
      @alg_type_infer (gc_mk Θ Ξ) Γ B A ->
      (forall u, ~ is_univ_nf B u) ->
      forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
  Proof.
    intros * HB Hne * H.
    assert (exists UA u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_univ_nf UA u) as [UA [u [HA Hu]]]
        by eauto using alg_type_infer_large_typ_complete'.
    assert (B = UA)
      by (eapply (functional_alg_type_infer (GC := gc_mk Θ Ξ)); eassumption).
    subst; exact (Hne _ Hu).
  Qed.

  Lemma alg_ext_sound' : forall Θ Ξ Γ Ψ,
      @alg_ext (gc_mk Θ Ξ) Γ Ψ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
  Proof. intros; eapply (alg_ext_sound (GC := gc_mk Θ Ξ)); eassumption. Qed.

  Lemma alg_ext_complete' : forall Θ Ξ Γ Ψ,
      Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> @alg_ext (gc_mk Θ Ξ) Γ Ψ.
  Proof. intros; eapply (alg_ext_complete (GC := gc_mk Θ Ξ)); eassumption. Qed.

  Lemma alg_unit_sound' : forall Θ Ξ Γ U,
      @alg_unit (gc_mk Θ Ξ) Γ U -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
  Proof. intros; eapply (alg_unit_sound (GC := gc_mk Θ Ξ)); eassumption. Qed.

  Lemma alg_unit_complete' : forall Θ Ξ Γ U,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U -> @alg_unit (gc_mk Θ Ξ) Γ U.
  Proof. intros; eapply (alg_unit_complete (GC := gc_mk Θ Ξ)); eassumption. Qed.

  Lemma alg_modexp_sound' : forall Θ Ξ Γ H,
      @alg_modexp (gc_mk Θ Ξ) Γ H -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H.
  Proof. intros; eapply (alg_modexp_sound (GC := gc_mk Θ Ξ)); eassumption. Qed.

  Lemma alg_modexp_complete' : forall Θ Ξ Γ H,
      Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H -> @alg_modexp (gc_mk Θ Ξ) Γ H.
  Proof. intros; eapply (alg_modexp_complete (GC := gc_mk Θ Ξ)); eassumption. Qed.

End Bridge.

#[local]
Hint Resolve alg_type_infer_large_typ_sound' alg_type_infer_univ_sound' alg_type_check_sound'
  alg_type_check_complete' not_wf_typ_of_no_infer not_wf_typ_of_infer_not_typ : mctt.

(** ** Types and Terms at an Explicit Global Context *)

(** [univ_nf_idx_dec] returns the index of the universe it found as a
    [is_univ_nf] fact; the obligations that use it need the large level. *)
#[local]
Ltac invert_nf_typ_eq :=
  subst;
  repeat match goal with
    | H : Typeωⁿ@?i = Typeωⁿ@?j |- _ => assert (i = j) by congruence; clear H; subst
    end.

Section check_exp.

  (** "Is [A] a type?", decided as in the Π case of [type_check]: infer a type
      for [A], then require it to be a universe. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_typ Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A :
    { i | Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i } + { forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i } :=
  | Θ, Ξ, Γ, HΓ, A =>
      let*o (exist _ UA _) := @type_infer (gc_mk Θ Ξ) Γ _ A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureo (exist _ (unf_large u) _)
  .
  Obligation 1. Qed.
  (** Every user term has an inference order. *)
  Obligation 2. (* type_infer_order A *)
    apply user_exp_to_type_infer_order, user_exp_all.
  Defined.
  Obligation 3. (* nothing is inferred for [A] *)
    eapply not_wf_typ_of_no_infer; eassumption.
  Qed.
  Obligation 4. (* what is inferred for [A] is not a universe *)
    match goal with
    | Ha : _ ⊢a _ ⟹ ?UA, Hn : forall u, ~ is_univ_nf ?UA u |- False =>
        eapply not_wf_typ_of_infer_not_typ; [ exact Ha | exact Hn | eassumption ]
    end.
  Qed.
  (** The inferred universe gives the typing at its own large level. *)
  Obligation 5. (* Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(unf_large u) *)
    eapply alg_type_infer_univ_sound'; eassumption.
  Qed.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_exp Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A M :
    { Θ ⍮ Ξ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A } :=
  | Θ, Ξ, Γ, HΓ, A, M =>
      let*o->b (exist _ i _) := check_typ Θ Ξ Γ HΓ A while _ in
      let*b _ := @type_check (gc_mk Θ Ξ) Γ A _ M _ while _ in
      pureb _
  .
  (** The type of a well-typed term is a type, so if [A] is not one, the
      judgment cannot hold. *)
  Obligation 1. (* [A] is no type *)
    gen_presups; eapply H; eassumption.
  Qed.
  Obligation 2. (* exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i *)
    eexists; eassumption.
  Defined.
  Obligation 3. (* type_check_order M *)
    apply tc_ti, user_exp_to_type_infer_order, user_exp_all.
  Defined.
  Obligation 4. (* the algorithmic check fails *)
    eapply H, alg_type_check_complete'; eassumption.
  Qed.
  Obligation 5. (* Θ ⍮ Ξ ⍮ Γ ⊢ M : A *)
    eapply alg_type_check_sound'; eassumption.
  Qed.

  (** A unit and a module expression, through their algorithmic checks. *)
  Definition check_unit Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) U :
      { Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U } :=
    match @unit_check (gc_mk Θ Ξ) Γ HΓ U (unit_order_all U) with
    | left H => left (alg_unit_sound' _ _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_unit_complete' _ _ _ _ H'))
    end.

  Definition check_ext Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) Ψ :
      { Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } :=
    match @ext_check (gc_mk Θ Ξ) Γ HΓ Ψ (ext_order_all Ψ) with
    | left H => left (alg_ext_sound' _ _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_ext_complete' _ _ _ _ H'))
    end.

  Definition check_modexp Θ Ξ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) E :
      { Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E } :=
    match @modexp_check (gc_mk Θ Ξ) Γ HΓ E (modexp_order_all E) with
    | left H => left (alg_modexp_sound' _ _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_modexp_complete' _ _ _ _ H'))
    end.

End check_exp.

(** ** Local Contexts

    By structural recursion on [Γ]: the base case appeals to the
    well-formedness of the global context.  An assumption is one call of
    [check_typ], a definition one call of [check_exp], and a module slot one
    call of [check_unit]. *)

Section check_ctx.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_ctx Θ Ξ (HΞ : ⊢g Θ ⍮ Ξ) Γ :
    { ⊢ Θ ⍮ Ξ ⍮ Γ } + { ~ ⊢ Θ ⍮ Ξ ⍮ Γ } :=
  | Θ, Ξ, HΞ, ⋅ => pureb _
  | Θ, Ξ, HΞ, Γ ▹ A =>
      let*b HΓ := check_ctx Θ Ξ HΞ Γ while _ in
      let*o->b (exist _ i _) := check_typ Θ Ξ Γ HΓ A while _ in
      pureb _
  | Θ, Ξ, HΞ, Γ ▸ A ≔ M =>
      let*b HΓ := check_ctx Θ Ξ HΞ Γ while _ in
      let*b _ := check_exp Θ Ξ Γ HΓ A M while _ in
      pureb _
  | Θ, Ξ, HΞ, Γ ▹ₘ U =>
      let*b HΓ := check_ctx Θ Ξ HΞ Γ while _ in
      let*b _ := check_unit Θ Ξ Γ HΓ U while _ in
      pureb _
  .
  (** The empty context is well formed by the global context's. *)
  Obligation 1. (* ⊢ Θ ⍮ Ξ ⍮ ⋅ *)
    mauto 2.
  Qed.
  (** Each extension fails in two ways: the prefix, or the new entry.  Both
      contradict a decomposition of the extended context. *)
  Obligation 2. (* the prefix of an assumption is no context *)
    eapply H; mauto 2.
  Qed.
  Obligation 3. (* the assumption is no type *)
    destruct (ctx_decomp H0) as [? [? ?]]; eapply H; eassumption.
  Qed.
  Obligation 4. (* ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A *)
    mauto 2.
  Qed.
  Obligation 5. (* the prefix of a definition is no context *)
    eapply H; mauto 2.
  Qed.
  Obligation 6. (* the definiens is not of the declared type *)
    inversion H0; subst; eapply H; eassumption.
  Qed.
  Obligation 7. (* ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M *)
    mauto 2.
  Qed.
  Obligation 8. (* the prefix of a module slot is no context *)
    destruct (ctx_decomp_mod H0); contradiction.
  Qed.
  Obligation 9. (* the unit of a module slot is not well formed *)
    destruct (ctx_decomp_mod H0); contradiction.
  Qed.
  Obligation 10. (* ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U *)
    apply wf_ctx_extend_mod; assumption.
  Qed.

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
