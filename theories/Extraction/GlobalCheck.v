From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Semantic Require Import MemberWf.
From Mctt.Extraction Require Import PseudoMonadic TypeCheck SynEq.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding the Global-Context Judgments

    The decision procedures the command interpreter needs, built on
    [Extraction.TypeCheck]: well-formedness of local contexts [⊢ Θ ⍮ Γ],
    of types and of terms.

    [⊢g Θ] is not decided here: the interpreter builds it command by
    command.  [Θ] is therefore a parameter of everything below, and only the
    local context is traversed. *)

(** ** The Bridge to the Algorithmic Judgments

    The algorithmic judgments take their global context as an instance [GC]
    and read it as [gc_ctx GC].  Unifying that with an explicit [Θ] would
    require solving [gc_ctx ?GC ≟ Θ], which no unifier does, so this section instantiates [GC] by hand.  Below it, only
    the explicit forms appear. *)

Section Bridge.

  Lemma alg_type_infer_sound' : forall Θ Γ (A : nf) M,
      @alg_type_infer (gc_mk Θ) Γ A M ->
      ⊢ Θ ⍮ Γ ->
      Θ ⍮ Γ ⊢ M : A.
  Proof.
    intros; eapply (alg_type_infer_sound (GC := gc_mk Θ)); eassumption.
  Qed.

  Lemma alg_type_infer_typ_sound' : forall Θ Γ i A,
      @alg_type_infer (gc_mk Θ) Γ Typeⁿ@i A ->
      ⊢ Θ ⍮ Γ ->
      Θ ⍮ Γ ⊢ A : Type@i.
  Proof.
    (** [exact] rather than [eapply]: [nf_to_exp Typeⁿ@i] and [Type@i] are
        convertible, but the unifier cannot unify them in this direction. *)
    intros * H HΓ; exact (alg_type_infer_sound' _ _ Typeⁿ@i _ H HΓ).
  Qed.

  Lemma alg_type_check_sound' : forall Θ Γ i A M,
      @alg_type_check (gc_mk Θ) Γ A M ->
      ⊢ Θ ⍮ Γ ->
      Θ ⍮ Γ ⊢ A : Type@i ->
      Θ ⍮ Γ ⊢ M : A.
  Proof.
    intros; eapply (alg_type_check_sound (GC := gc_mk Θ)); eassumption.
  Qed.

  (** Every expression is a [user_exp] ([user_exp_all]), so completeness has
      no side condition on this side of the bridge. *)
  Lemma alg_type_check_complete' : forall Θ Γ A M,
      Θ ⍮ Γ ⊢ M : A ->
      @alg_type_check (gc_mk Θ) Γ A M.
  Proof.
    intros; eapply (alg_type_check_complete (GC := gc_mk Θ));
      [ apply user_exp_all | eassumption ].
  Qed.

  Lemma alg_type_infer_typ_complete' : forall Θ Γ i A,
      Θ ⍮ Γ ⊢ A : Type@i ->
      exists j, @alg_type_infer (gc_mk Θ) Γ Typeⁿ@j A.
  Proof.
    intros * H.
    assert (exists j, @alg_type_infer (gc_mk Θ) Γ Typeⁿ@j A /\ j <= i) as [j []]
        by (eapply (alg_type_infer_typ_complete (GC := gc_mk Θ));
            [ apply user_exp_all | eassumption ]).
    eauto.
  Qed.

  (** The two ways "is [A] a type?" can fail: nothing is inferred for [A], or
      what is inferred is not a universe.  Each contradicts completeness, the
      second through functionality of inference. *)
  Lemma not_wf_typ_of_no_infer : forall Θ Γ A,
      (forall B : nf, ~ @alg_type_infer (gc_mk Θ) Γ B A) ->
      forall i, ~ Θ ⍮ Γ ⊢ A : Type@i.
  Proof.
    intros * Hno * H.
    assert (exists j, @alg_type_infer (gc_mk Θ) Γ Typeⁿ@j A) as [j]
        by eauto using alg_type_infer_typ_complete'.
    firstorder.
  Qed.

  Lemma not_wf_typ_of_infer_not_typ : forall Θ Γ A (B : nf),
      @alg_type_infer (gc_mk Θ) Γ B A ->
      (forall i, B <> Typeⁿ@i) ->
      forall i, ~ Θ ⍮ Γ ⊢ A : Type@i.
  Proof.
    intros * HB Hne * H.
    assert (exists j, @alg_type_infer (gc_mk Θ) Γ Typeⁿ@j A) as [j HA]
        by eauto using alg_type_infer_typ_complete'.
    assert (B = Typeⁿ@j)
      by (eapply (functional_alg_type_infer (GC := gc_mk Θ)); eassumption).
    firstorder.
  Qed.

  Lemma alg_ext_sound' : forall Θ Γ Ψ,
      @alg_ext (gc_mk Θ) Γ Ψ -> ⊢ Θ ⍮ Γ -> Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
  Proof. intros; eapply (alg_ext_sound (GC := gc_mk Θ)); eassumption. Qed.

  Lemma alg_ext_complete' : forall Θ Γ Ψ,
      Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> @alg_ext (gc_mk Θ) Γ Ψ.
  Proof. intros; eapply (alg_ext_complete (GC := gc_mk Θ)); eassumption. Qed.

  Lemma alg_unit_sound' : forall Θ Γ U,
      @alg_unit (gc_mk Θ) Γ U -> ⊢ Θ ⍮ Γ -> Θ ⍮ Γ ⊢ᵘ U ≈ U.
  Proof. intros; eapply (alg_unit_sound (GC := gc_mk Θ)); eassumption. Qed.

  Lemma alg_unit_complete' : forall Θ Γ U,
      Θ ⍮ Γ ⊢ᵘ U ≈ U -> @alg_unit (gc_mk Θ) Γ U.
  Proof. intros; eapply (alg_unit_complete (GC := gc_mk Θ)); eassumption. Qed.

  Lemma alg_modexp_sound' : forall Θ Γ H,
      @alg_modexp (gc_mk Θ) Γ H -> ⊢ Θ ⍮ Γ -> Θ ⍮ Γ ⊢ᵐ H ≈ H.
  Proof. intros; eapply (alg_modexp_sound (GC := gc_mk Θ)); eassumption. Qed.

  Lemma alg_modexp_complete' : forall Θ Γ H,
      Θ ⍮ Γ ⊢ᵐ H ≈ H -> @alg_modexp (gc_mk Θ) Γ H.
  Proof. intros; eapply (alg_modexp_complete (GC := gc_mk Θ)); eassumption. Qed.

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
  Equations check_typ Θ Γ (HΓ : ⊢ Θ ⍮ Γ) A :
    { i | Θ ⍮ Γ ⊢ A : Type@i } + { forall i, ~ Θ ⍮ Γ ⊢ A : Type@i } :=
  | Θ, Γ, HΓ, A =>
      let*o (exist _ UA _) := @type_infer (gc_mk Θ) Γ _ A _ while _ in
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
    | |- ~ _ ⍮ _ ⊢ _ : _ => intro; gen_presups; firstorder (mautosolve 3)
    | _ => mautosolve 3
    end.

  #[tactic="check_exp_tac",derive(equations=no,eliminator=no)]
  Equations check_exp Θ Γ (HΓ : ⊢ Θ ⍮ Γ) A M :
    { Θ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Γ ⊢ M : A } :=
  | Θ, Γ, HΓ, A, M =>
      let*o->b (exist _ i _) := check_typ Θ Γ HΓ A while _ in
      let*b _ := @type_check (gc_mk Θ) Γ A _ M _ while _ in
      pureb _
  .

  (** A unit and a module expression, through their algorithmic checks. *)
  Definition check_unit Θ Γ (HΓ : ⊢ Θ ⍮ Γ) U :
      { Θ ⍮ Γ ⊢ᵘ U ≈ U } + { ~ Θ ⍮ Γ ⊢ᵘ U ≈ U } :=
    match @unit_check (gc_mk Θ) Γ HΓ U (unit_order_all U) with
    | left H => left (alg_unit_sound' _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_unit_complete' _ _ _ H'))
    end.

  Definition check_ext Θ Γ (HΓ : ⊢ Θ ⍮ Γ) Ψ :
      { Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } + { ~ Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } :=
    match @ext_check (gc_mk Θ) Γ HΓ Ψ (ext_order_all Ψ) with
    | left H => left (alg_ext_sound' _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_ext_complete' _ _ _ H'))
    end.

  Definition check_modexp Θ Γ (HΓ : ⊢ Θ ⍮ Γ) E :
      { Θ ⍮ Γ ⊢ᵐ E ≈ E } + { ~ Θ ⍮ Γ ⊢ᵐ E ≈ E } :=
    match @modexp_check (gc_mk Θ) Γ HΓ E (modexp_order_all E) with
    | left H => left (alg_modexp_sound' _ _ _ H HΓ)
    | right H => right (fun H' => H (alg_modexp_complete' _ _ _ H'))
    end.

End check_exp.

(** ** Members at Known Types

    A member of a module without arguments is of its member type ([wf_mem],
    by [member_wf]), so when the type it is to be checked against is that
    member type, no check is needed: in particular, its literal prefixes
    ([umt_def]) are not checked again.  Otherwise, it is checked. *)

Lemma member_typed : forall Θ Γ H R pre x A,
    modexp_spine H = (R, nil, pre) -> Θ ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type Θ Γ H (x :: nil) (mr_term A) -> Θ ⍮ Γ ⊢ a_mem H x : A.
Proof.
  intros * Hs HH Hmt.
  destruct (proj1 (@member_wf (gc_mk Θ)) _ _ _ _ Hmt HH ltac:(intros; discriminate)) as ([i HA] & HMu & _); cbn [mres_ty] in *.
  destruct (HMu eq_refl) as (M & HMe & HMt).
  eapply wf_mem; [ eapply spine_nil_noargs; eassumption | eassumption .. ].
Qed.

Definition member_at (Θ : gctx) (Γ : ctx) (H : modexp) (x : string) (A A' : typ) (R : modexp) (pre : path)
  (Hs : modexp_spine H = (R, nil, pre)) (HH : Θ ⍮ Γ ⊢ᵐ H ≈ H)
  (HA' : member_type Θ Γ H (x :: nil) (mr_term A')) (E : A' = A) : Θ ⍮ Γ ⊢ a_mem H x : A :=
  eq_rect A' (fun B => Θ ⍮ Γ ⊢ a_mem H x : B) (member_typed _ _ _ _ _ _ _ Hs HH HA') A E.

(** The root and the selections of a module expression without arguments. *)
Definition spine_case (H : modexp) : {p : modexp * path | modexp_spine H = (fst p, nil, snd p)} + {True} :=
  match modexp_spine H as sp return modexp_spine H = sp -> _ with
  | (R, nil, pre) => fun E => inleft (exist _ (R, pre) E)
  | _ => fun _ => inright I
  end eq_refl.

Definition check_exp_fast Θ Γ (HΓ : ⊢ Θ ⍮ Γ) A M : { Θ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Γ ⊢ M : A } :=
  match M as M0 return { Θ ⍮ Γ ⊢ M0 : A } + { ~ Θ ⍮ Γ ⊢ M0 : A } with
  | a_mem H x =>
      match spine_case H with
      | inleft (exist _ (R, pre) Es) =>
          match check_modexp Θ Γ HΓ H with
          | left HH =>
              match @member_term_dec (gc_mk Θ) (ctx_wf_gctx _ _ HΓ) Γ H (x :: nil) HH with
              | inleft (exist _ A' HA') =>
                  match exp_eq_test A' A with
                  | left E => left (member_at Θ Γ H x A A' R pre Es HH HA' E)
                  | right _ => check_exp Θ Γ HΓ A (a_mem H x)
                  end
              | inright _ => check_exp Θ Γ HΓ A (a_mem H x)
              end
          | right _ => check_exp Θ Γ HΓ A (a_mem H x)
          end
      | inright _ => check_exp Θ Γ HΓ A (a_mem H x)
      end
  | M0 => check_exp Θ Γ HΓ A M0
  end.

(** ** Local Contexts

    By structural recursion on [Γ]: the base case appeals to the
    well-formedness of the global context.  An assumption is one call of
    [check_typ], a definition one call of [check_exp], and a module slot one
    call of [check_unit]. *)

Section check_ctx.

  #[local]
  Ltac check_ctx_tac :=
    intros;
    cbn beta in *;
    try eassumption;
    lazymatch goal with
    | |- ~ ⊢ _ ⍮ (_ ▹ₘ _) =>
        let H := fresh "H" in intro H; destruct (ctx_decomp_mod H); contradiction
    | |- ~ ⊢ _ ⍮ _ => intro; gen_presups; firstorder (mautosolve 3)
    | |- ⊢ _ ⍮ (_ ▹ₘ _) => apply wf_ctx_extend_mod; assumption
    | _ => mautosolve 3
    end.

  #[tactic="check_ctx_tac",derive(equations=no,eliminator=no)]
  Equations check_ctx Θ (HΞ : ⊢g Θ) Γ :
    { ⊢ Θ ⍮ Γ } + { ~ ⊢ Θ ⍮ Γ } :=
  | Θ, HΞ, ⋅ => pureb _
  | Θ, HΞ, Γ ▹ A =>
      let*b HΓ := check_ctx Θ HΞ Γ while _ in
      let*o->b (exist _ i _) := check_typ Θ Γ HΓ A while _ in
      pureb _
  | Θ, HΞ, Γ ▸ A ≔ M =>
      let*b HΓ := check_ctx Θ HΞ Γ while _ in
      let*b _ := check_exp Θ Γ HΓ A M while _ in
      pureb _
  | Θ, HΞ, Γ ▹ₘ U =>
      let*b HΓ := check_ctx Θ HΞ Γ while _ in
      let*b _ := check_unit Θ Γ HΓ U while _ in
      pureb _
  .

  (** One entry more on a context known to be well formed. *)
  #[tactic="check_ctx_tac",derive(equations=no,eliminator=no)]
  Equations check_centry Θ Γ (HΓ : ⊢ Θ ⍮ Γ) (e : centry) :
    { ⊢ Θ ⍮ e :: Γ } + { ~ ⊢ Θ ⍮ e :: Γ } :=
  | Θ, Γ, HΓ, ce_ass A =>
      let*o->b (exist _ i _) := check_typ Θ Γ HΓ A while _ in
      pureb _
  | Θ, Γ, HΓ, ce_def A M =>
      let*b _ := check_exp_fast Θ Γ HΓ A M while _ in
      pureb _
  | Θ, Γ, HΓ, ce_mod U =>
      let*b _ := check_unit Θ Γ HΓ U while _ in
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
