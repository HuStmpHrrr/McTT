From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Completeness.Consequences Require Import Types.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Extraction Require Import Lookup PseudoMonadic TypeCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding the Global-Context Judgments

    The decision procedures the command interpreter needs, built on
    [Extraction.TypeCheck]: well-formedness of local contexts [⊢ Θ ⍮ Ξ ⍮ Γ],
    of types and of terms.

    [⊢ᵍ Θ ⍮ nil] is not decided here: the filed units are what a unit is
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
      universe [u] is a type of [universe_nf_tm u], at either tier. *)
  Lemma alg_type_infer_typ_sound' : forall Θ Ξ Γ UA u A,
      @alg_type_infer (gc_mk Θ Ξ) Γ UA A ->
      is_univ_nf UA u ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : universe_nf_tm u.
  Proof.
    intros * H Hu HΓ.
    rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu).
    exact (alg_type_infer_sound' _ _ _ UA _ H HΓ).
  Qed.

  (** The same at an index of either tier: a type of [universe_nf_tm u] is one of the
      large universe [Typeω@(universe_nf_large_index u)] the index lives at. *)
  Lemma alg_type_infer_univ_sound' : forall Θ Ξ Γ UA u A,
      @alg_type_infer (gc_mk Θ Ξ) Γ UA A ->
      is_univ_nf UA u ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(universe_nf_large_index u).
  Proof.
    intros * H Hu HΓ.
    assert (Θ ⍮ Ξ ⍮ Γ ⊢ A : universe_nf_tm u)
      by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
          exact (alg_type_infer_sound' _ _ _ UA _ H HΓ)).
    exact (wf_exp_universe_nf_large_index (GC := gc_mk Θ Ξ) ltac:(eassumption)).
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
    assert (exists UA u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i))
        as [UA [u [? []]]]
        by (eapply (alg_type_infer_large_typ_complete (GC := gc_mk Θ Ξ));
            [ apply user_exp_all | eassumption ]).
    eauto.
  Qed.

  (** A type of a universe term infers a universe below the normal form of
      the term. *)
  Lemma alg_type_infer_typ_complete' : forall Θ Ξ Γ T A,
      univ_term T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : T ->
      exists u v, nbe_ty Θ Ξ Γ T (universe_nf_to_nf u) /\ @alg_type_infer (gc_mk Θ Ξ) Γ (universe_nf_to_nf v) A /\ universe_nf_le v u.
  Proof.
    intros * HT H.
    exact (alg_type_infer_typ_complete (GC := gc_mk Θ Ξ) (user_exp_all _) HT H).
  Qed.

  (** A small type infers a small universe at a literal level below its own. *)
  Lemma alg_type_infer_typ_complete_lit' : forall Θ Ξ Γ n A,
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Type@n ->
      exists m, @alg_type_infer (gc_mk Θ Ξ) Γ Typeⁿ@m A /\ m <= n.
  Proof.
    intros * H.
    exact (alg_type_infer_typ_complete_lit (GC := gc_mk Θ Ξ) (user_exp_all _) H).
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
      by (eapply (functional_alg_type_infer (GC := gc_mk Θ Ξ)); [ exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) | eassumption .. ]).
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

(** The same at the global context found by instance resolution, which is
    how the checks below, at the Core context of a fast context
    ([fc_gctx F]), read them. *)
Section BridgeInstance.
  Context {GC : GCtx}.

  (** [alg_type_infer_univ_sound'] *)
  Lemma alg_type_infer_univ_sound_gc : forall Γ UA u A,
      Γ ⊢a A ⟹ UA -> is_univ_nf UA u -> ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Typeω@(universe_nf_large_index u).
  Proof.
    intros * H Hu HΓ.
    assert (gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : universe_nf_tm u)
      by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); exact (alg_type_infer_sound H HΓ)).
    exact (wf_exp_universe_nf_large_index ltac:(eassumption)).
  Qed.

  (** [alg_type_check_complete'] *)
  Lemma alg_type_check_complete_gc : forall Γ A M, gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A -> Γ ⊢a M ⟸ A.
  Proof. intros; eapply alg_type_check_complete; [ apply user_exp_all | eassumption ]. Qed.

  (** [alg_type_infer_large_typ_complete'] *)
  Lemma alg_type_infer_large_typ_complete_gc : forall Γ i A,
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Typeω@i -> exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u.
  Proof.
    intros * H.
    assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i)) as [UA [u [? []]]]
      by (eapply alg_type_infer_large_typ_complete; [ apply user_exp_all | eassumption ]).
    eauto.
  Qed.

  (** [not_wf_typ_of_no_infer] *)
  Lemma not_wf_typ_of_no_infer_gc : forall Γ A,
      (forall B : nf, ~ Γ ⊢a A ⟹ B) -> forall i, ~ gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Typeω@i.
  Proof.
    intros * Hno * H.
    destruct (alg_type_infer_large_typ_complete_gc _ _ _ H) as [UA [u [HA _]]].
    exact (Hno _ HA).
  Qed.

  (** A type of the sort of a kind infers a sort of that kind. *)
  Lemma alg_type_infer_sort_complete_gc : forall Γ κ i A,
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i -> exists UA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA κ u.
  Proof.
    intros * HA.
    assert (⊢ gc_deps ⍮ gc_stack ⍮ Γ) by (gen_presups; assumption).
    destruct (alg_type_check_kind_sort_infer ltac:(eassumption) (alg_type_check_complete_gc _ _ _ HA)) as (UA & u & ? & ? & _).
    eauto.
  Qed.

  (** The two ways "is [A] a type of a sort?" can fail, as for a type of a
      universe. *)
  Lemma not_wf_type_of_no_infer_gc : forall Γ A,
      (forall B : nf, ~ Γ ⊢a A ⟹ B) -> forall κ i, ~ gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i.
  Proof.
    intros * Hno κ i H.
    destruct (alg_type_infer_sort_complete_gc _ _ _ _ H) as (UA & u & HA & _).
    exact (Hno _ HA).
  Qed.

  Lemma not_wf_type_of_infer_not_sort_gc : forall Γ A (B : nf),
      Γ ⊢a A ⟹ B -> (forall r u, ~ is_sort_nf B r u) -> forall κ i, ~ gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i.
  Proof.
    intros * HB Hne κ i H.
    destruct (alg_type_infer_sort_complete_gc _ _ _ _ H) as (UA & u & HA & Hu).
    assert (B = UA)
      by (eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) | eassumption .. ]).
    subst; exact (Hne _ _ Hu).
  Qed.

  (** A type is of the sort of one kind ([nbe_ty_kind]). *)
  Lemma kind_sort_unique : forall Γ A κ κ' i j,
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : abs_kind_sort κ' Typeω@j ->
      κ = κ'.
  Proof. intros * H H'; exact (nbe_ty_kind_functional (nbe_ty_kind_of_typed H) (nbe_ty_kind_of_typed H')). Qed.

  (** [not_wf_typ_of_infer_not_typ] *)
  Lemma not_wf_typ_of_infer_not_typ_gc : forall Γ A (B : nf),
      Γ ⊢a A ⟹ B -> (forall u, ~ is_univ_nf B u) -> forall i, ~ gc_deps ⍮ gc_stack ⍮ Γ ⊢ A : Typeω@i.
  Proof.
    intros * HB Hne * H.
    destruct (alg_type_infer_large_typ_complete_gc _ _ _ H) as [UA [u [HA Hu]]].
    assert (B = UA)
      by (eapply functional_alg_type_infer; [ exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) | eassumption .. ]).
    subst; exact (Hne _ Hu).
  Qed.
End BridgeInstance.

(** A blamed level, in [Γ]: a context [Δ] extending [Γ], innermost entry
    first, and a [t] of no type of levels in [Δ ++ Γ]. *)
Definition level_blame Θ Ξ Γ : Set :=
  { p : ctx * exp | forall n, ~ Θ ⍮ Ξ ⍮ (fst p ++ Γ) ⊢ snd p : Level@n }.

(** Reassociating the context of a blamed level *)
Lemma level_blame_app_ok : forall Θ Ξ Γ Δ Δ' t,
    (forall n, ~ Θ ⍮ Ξ ⍮ (Δ' ++ (Δ ++ Γ)) ⊢ t : Level@n) ->
    forall n, ~ Θ ⍮ Ξ ⍮ ((Δ' ++ Δ) ++ Γ) ⊢ t : Level@n.
Proof. intros *; rewrite <- app_assoc; exact (fun H => H). Qed.

(** A level blamed in an extension [Δ ++ Γ] is blamed in [Γ].  The global
    context is that of a fast context [F], which is all the function is
    passed of it. *)
Definition level_blame_app {F : FCtx} {Γ} Δ (b : level_blame (fc_deps F) (fc_stack F) (Δ ++ Γ)) :
    level_blame (fc_deps F) (fc_stack F) Γ :=
  match b with
  | exist _ (Δ', t) Ht => exist _ (Δ' ++ Δ, t) (level_blame_app_ok _ _ _ _ _ _ Ht)
  end.

(** A sort of types is the sort of a kind at a universe. *)
Lemma type_sort_kind_sort : forall S, type_sort S -> exists κ i, S = abs_kind_sort κ Typeω@i.
Proof. intros S [i | |]; [ exists ak_relevant, i | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity. Qed.

(** The type of a well-typed term, no [LevelSort], is a type of a sort. *)
Lemma not_exp_of_not_type : forall Θ Ξ Γ A M,
    (forall κ i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κ Typeω@i) -> A <> LevelSort -> ~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HA HnL HM; destruct (presup_exp_typ_sorted HM HnL) as (S & HS & HA').
  destruct (type_sort_kind_sort _ HS) as (κ & i & ->); exact (HA _ _ HA').
Qed.

(** ** Types and Terms at the Core Context of a Fast Context *)

Section check_exp.
  (** The fast context each check looks names up in ([Extraction.Lookup]);
      the judgments decided are at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G -> Θ ⍮ Ξ ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.

  (** "Is [A] a type?", decided as in the Π case of [type_check]: infer a type
      for [A], then require it to be a universe. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_typ Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A :
    { i | Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i } + { forall i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i } :=
  | Γ, HΓ, A =>
      let*o (exist _ UA _) := type_infer F levels_abstractable_dec Γ _ A _ while _ in
      let*o (exist _ u _) := univ_nf_idx_dec UA while _ in
      pureo (exist _ (universe_nf_large_index u) _)
  .
  Obligation 1. Qed.
  (** Every user term has an inference order. *)
  Obligation 2. (* type_infer_order A *)
    apply type_infer_order_all.
  Defined.
  Obligation 3. (* nothing is inferred for [A] *)
    eapply not_wf_typ_of_no_infer_gc; eassumption.
  Qed.
  Obligation 4. (* what is inferred for [A] is not a universe *)
    match goal with
    | Ha : _ ⊢a _ ⟹ ?UA, Hn : forall u, ~ is_univ_nf ?UA u |- False =>
        eapply not_wf_typ_of_infer_not_typ_gc; [ exact Ha | exact Hn | eassumption ]
    end.
  Qed.
  (** The inferred universe gives the typing at its own large level. *)
  Obligation 5. (* Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@(universe_nf_large_index u) *)
    eapply alg_type_infer_univ_sound_gc; eassumption.
  Qed.

  (** "Is [A] a type of a sort?": infer a type for [A], then require it to
      be a sort ([is_sort_nf]); the answer is the sort, by its kind, at a
      universe. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_type Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A :
    { r & { i | Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i } } + { forall r i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i } :=
  | Γ, HΓ, A =>
      let*o (exist _ UA _) := type_infer F levels_abstractable_dec Γ _ A _ while _ in
      let*o (existT _ r (exist _ u _)) := sort_nf_dec UA while _ in
      pureo (existT _ r (exist _ (universe_nf_large_index u) _))
  .
  Obligation 1. Qed.
  Obligation 2. (* type_infer_order A *)
    apply type_infer_order_all.
  Defined.
  Obligation 3. (* nothing is inferred for [A] *)
    eapply not_wf_type_of_no_infer_gc; eassumption.
  Qed.
  Obligation 4. (* what is inferred for [A] is no sort *)
    match goal with
    | Ha : _ ⊢a _ ⟹ ?UA, Hn : forall r u, ~ is_sort_nf ?UA r u |- False =>
        eapply not_wf_type_of_infer_not_sort_gc; [ exact Ha | exact Hn | eassumption ]
    end.
  Qed.
  (** The inferred sort gives the typing at its own large level. *)
  Obligation 5. (* Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@(universe_nf_large_index u) *)
    destruct_conjs; eapply sort_typed_of_is_sort_nf; [ eapply alg_type_infer_sound; eassumption | eassumption ].
  Qed.

  (** ** Blaming the Level of a Universe

      When "is [A] a type?" fails, [find_level_blame] looks for the reason
      most often met in practice: a small universe [Type@{t}] in [A] whose
      [t] is of no type of levels, such as the natural number [0] in
      [Type@{0}].  It only serves the error message; the decision itself
      stays [check_typ]'s. *)

  (** The two ways "is [t] a level?" can fail, as for [check_typ]: nothing
      is inferred for [t], or what is inferred is no type of levels.  Each
      contradicts completeness, through [alg_type_check_level_infer]. *)
  Lemma not_level_of_no_infer : forall Γ t,
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      (forall B : nf, ~ Γ ⊢a t ⟹ B) ->
      forall n, ~ Θ ⍮ Ξ ⍮ Γ ⊢ t : Level@n.
  Proof.
    intros * HΓ Hno n H.
    destruct (alg_type_check_level_infer HΓ (alg_type_check_complete_gc _ _ _ H)) as [m [Hm _]].
    exact (Hno _ Hm).
  Qed.

  Lemma not_level_of_infer_not_level : forall Γ t (B : nf),
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Γ ⊢a t ⟹ B ->
      (forall k, B <> Levelⁿ@k) ->
      forall n, ~ Θ ⍮ Ξ ⍮ Γ ⊢ t : Level@n.
  Proof.
    intros * HΓ HB Hne n H.
    destruct (alg_type_check_level_infer HΓ (alg_type_check_complete_gc _ _ _ H)) as [m [Hm _]].
    exact (Hne m (functional_alg_type_infer (ctx_wf_gctx _ _ _ HΓ) HB Hm)).
  Qed.

  (** "Is [t] a level?", decided as the premise of [alg_type_infer_suniv]: infer a type
      for [t], then require it to be a type of levels. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_level Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) t :
    { n | Θ ⍮ Ξ ⍮ Γ ⊢ t : Level@n } + { forall n, ~ Θ ⍮ Ξ ⍮ Γ ⊢ t : Level@n } :=
  | Γ, HΓ, t =>
      let*o (exist _ B _) := type_infer F levels_abstractable_dec Γ _ t _ while _ in
      let*o (exist _ n _) := get_level_sort_nf B while _ in
      pureo (exist _ n _)
  .
  Obligation 1. Qed.
  Obligation 2. (* type_infer_order t *)
    apply type_infer_order_all.
  Defined.
  Obligation 3. (* nothing is inferred for [t] *)
    eapply not_level_of_no_infer; eassumption.
  Qed.
  Obligation 4. (* what is inferred for [t] is no type of levels *)
    match goal with
    | Hn : forall k, ?B <> _, Ha : _ ⊢a _ ⟹ ?B |- False =>
        eapply not_level_of_infer_not_level; [ exact HΓ | exact Ha | exact Hn | eassumption ]
    end.
  Qed.
  Obligation 5. (* Θ ⍮ Ξ ⍮ Γ ⊢ t : Level@n *)
    subst; match goal with
    | Ha : _ ⊢a _ ⟹ Levelⁿ@_ |- _ => exact (alg_type_infer_sound Ha HΓ)
    end.
  Qed.

  (** The search: a universe whose level fails [check_level], at the
      universe itself, or in either part of a [Π], the codomain once the
      domain is a type.  Elsewhere, and below a universe whose level is a
      level, it finds nothing. *)
  Fixpoint find_level_blame Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) (A : exp) {struct A} : option (level_blame Θ Ξ Γ) :=
    match A with
    | a_univ t =>
        match check_level Γ HΓ t with
        | inleft _ => None
        | inright Ht => Some (exist _ (nil, t) Ht)
        end
    | a_pi κd _ A' B =>
        match find_level_blame Γ HΓ A' with
        | Some b => Some b
        | None =>
            match check_type Γ HΓ A' with
            | inleft (existT _ r (exist _ i HA)) =>
                option_map (level_blame_app (ce_ass r A' :: nil))
                  (find_level_blame (Γ ▹{r} A') (wf_ctx_extend _ _ _ _ _ _ HA (sort_kind_abs_kind_sort r i)) B)
            | inright _ => None
            end
        end
    | _ => None
    end.

  (** The same in a telescope [Δ] over a well-formed [Γ]: the first
      assumption that is no type, searched by [find_level_blame].  The
      result is the blame, if any, or that [Δ ++ Γ] is well formed.  A
      definition or a module slot is not searched. *)
  Fixpoint find_tele_blame Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) (Δ : ctx) {struct Δ} :
      option (level_blame Θ Ξ Γ) + { ⊢ Θ ⍮ Ξ ⍮ (Δ ++ Γ) } :=
    match Δ as Δ0 return option (level_blame Θ Ξ Γ) + { ⊢ Θ ⍮ Ξ ⍮ (Δ0 ++ Γ) } with
    | nil => inright HΓ
    | ce_ass κ A :: Δ' =>
        match find_tele_blame Γ HΓ Δ' with
        | inleft b => inleft b
        | inright HΔ' =>
            match check_type (Δ' ++ Γ) HΔ' A with
            | inleft (existT _ r (exist _ i HA)) =>
                match abs_kind_eq_dec r κ with
                | left E => inright (wf_ctx_extend _ _ _ _ _ _ HA (eq_rect r (sort_kind (abs_kind_sort r Typeω@i)) (sort_kind_abs_kind_sort r i) κ E))
                | right _ => inleft None
                end
            | inright _ => inleft (option_map (level_blame_app Δ') (find_level_blame (Δ' ++ Γ) HΔ' A))
            end
        end
    | _ :: Δ' =>
        match find_tele_blame Γ HΓ Δ' with
        | inleft b => inleft b
        | inright _ => inleft None
        end
    end.

  (** "Is [M] of type [A]?", for [A] known to be a type: [check_exp] once
      [check_typ] has succeeded, so that a caller can tell the two failures
      apart without inferring [A] twice. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_exp_typed Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A (HA : Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A) M :
    { Θ ⍮ Ξ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A } :=
  | Γ, HΓ, A, HA, M =>
      let*b _ := type_check F levels_abstractable_dec Γ A HA M _ while _ in
      pureb _
  .
  Obligation 1. (* type_check_order M *)
    apply type_check_order_ti, type_infer_order_all.
  Defined.
  Obligation 2. (* the algorithmic check fails *)
    eapply H, alg_type_check_complete_gc; eassumption.
  Qed.
  Obligation 3. (* Θ ⍮ Ξ ⍮ Γ ⊢ M : A *)
    destruct HA as [? S HS HA' | HG].
    - eapply alg_type_check_sound_sort; eassumption.
    - (** At [LevelSort]: the inferred type is below it, so it is it *)
      match goal with Hc : _ ⊢a M ⟸ _ |- _ => inversion Hc; subst end.
      match goal with Hs : _ ⊢a _ ⊆ LevelSort |- _ => destruct Hs as [B' W HB HW Hsub] end.
      pose proof (nbe_ty_level_sort_self HG) as HL.
      assert (W = LevelSortⁿ) as -> by (eapply functional_nbe_ty; eassumption).
      inversion Hsub; subst;
        try (match goal with HE : nf_eq_upto_proofs _ LevelSortⁿ |- _ => destruct B'; cbn in HE; try discriminate end).
      match goal with HMi : _ ⊢a M ⟹ ?A0 |- _ =>
        pose proof (wf_type_of_infer _ _ _ HG HMi) as HBt;
        assert (HAL : nf_to_exp A0 = LevelSort);
        [ destruct HBt as [A1 S HS HBs | ]; [| reflexivity ];
          pose proof (soundness_ty_at_sort HS HBs HB) as HE; cbn [nf_to_exp] in HE;
          exfalso; eapply level_sort_untyped; eapply presup_exp_eq_right; exact HE
        | pose proof (alg_type_infer_sound HMi HG) as HM'; rewrite HAL in HM'; exact HM' ] end.
  Qed.

  (** A type of the sort of [r] at a universe is a type. *)
  Definition type_of_check_type Γ A r i (HA : Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i) : Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A :=
    wf_type_of_sort _ (type_sort_kind_universe r i) HA.

  (** "Is [M] of type [A]?": at [LevelSort], or at a type of a sort. *)
  Definition check_exp Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) A M :
      { Θ ⍮ Ξ ⍮ Γ ⊢ M : A } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A } :=
    match exp_eq_dec A LevelSort with
    | left E => check_exp_typed Γ HΓ A (eq_rect_r (fun X => Θ ⍮ Ξ ⍮ Γ ⊢ᵗ X) (wf_type_level_sort HΓ) E) M
    | right HnL =>
        match check_type Γ HΓ A with
        | inleft (existT _ r (exist _ i HA)) => check_exp_typed Γ HΓ A (type_of_check_type Γ A r i HA) M
        | inright HA => right (not_exp_of_not_type _ _ _ _ _ HA HnL)
        end
    end.

  (** A unit and a module expression, through their algorithmic checks. *)
  Definition check_unit Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) U :
      { Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U } :=
    match unit_check F levels_abstractable_dec Γ HΓ U (unit_order_all U) with
    | left H => left (alg_unit_sound H HΓ)
    | right H => right (fun H' => H (alg_unit_complete H'))
    end.

  Definition check_ext Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) Ψ :
      { Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ } :=
    match ext_check F levels_abstractable_dec Γ HΓ Ψ (ext_order_all Ψ) with
    | left H => left (alg_ext_sound H HΓ)
    | right H => right (fun H' => H (alg_ext_complete H'))
    end.

  Definition check_modexp Γ (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) E :
      { Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E } :=
    match modexp_check F levels_abstractable_dec Γ HΓ E (modexp_order_all E) with
    | left H => left (alg_modexp_sound H HΓ)
    | right H => right (fun H' => H (alg_modexp_complete H'))
    end.

End check_exp.

(** ** Local Contexts

    By structural recursion on [Γ]: the base case appeals to the
    well-formedness of the global context.  An assumption is one call of
    [check_typ], a definition one call of [check_exp], a module slot one
    call of [check_unit], and a definition with a module part one of each
    of the last two. *)

Section check_ctx.
  (** The fast context each check looks names up in ([Extraction.Lookup]);
      the judgments decided are at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G -> Θ ⍮ Ξ ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.

  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations check_ctx (HΞ : ⊢ᵍ Θ ⍮ Ξ) Γ :
    { ⊢ Θ ⍮ Ξ ⍮ Γ } + { ~ ⊢ Θ ⍮ Ξ ⍮ Γ } :=
  | HΞ, ⋅ => pureb _
  (** An assumption: a type of the sort of the kind it says *)
  | HΞ, Γ ▹{κ} A =>
      let*b HΓ := check_ctx HΞ Γ while _ in
      let*o->b (existT _ r (exist _ i _)) := check_type F levels_abstractable_dec Γ HΓ A while _ in
      let*b _ := abs_kind_eq_dec r κ while _ in
      pureb _
  (** A definition: a type of a sort, and the body at it *)
  | HΞ, Γ ▸ A ≔ M =>
      let*b HΓ := check_ctx HΞ Γ while _ in
      let*o->b (existT _ r (exist _ i HA)) := check_type F levels_abstractable_dec Γ HΓ A while _ in
      let*b _ := check_exp_typed F levels_abstractable_dec Γ HΓ A (type_of_check_type F Γ A r i HA) M while _ in
      pureb _
  | HΞ, Γ ▹ₘ U =>
      let*b HΓ := check_ctx HΞ Γ while _ in
      let*b _ := check_unit F levels_abstractable_dec Γ HΓ U while _ in
      pureb _
  (** A definition with a module part: its type is one of a universe, its
      unit an alias under no parameters ([wf_ctx_extend_dm]) *)
  | HΞ, Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) =>
      let*b HΓ := check_ctx HΞ Γ while _ in
      let*o->b (exist _ i _) := check_typ F levels_abstractable_dec Γ HΓ A while _ in
      let*b _ := check_exp_typed F levels_abstractable_dec Γ HΓ A _ M while _ in
      let*b _ := check_unit F levels_abstractable_dec Γ HΓ (gu_mk nil (md_alias E)) while _ in
      pureb _
  (** A unit of another shape is rejected *)
  | HΞ, Γ ▸ₘ A ≔ M ‖ U => right _
  .
  (** A success is the context rule of the entry; a failure contradicts
      a decomposition of the extended context: its prefix, or its new
      entry. *)
  Solve All Obligations with
    intros; repeat match goal with |- ~ _ => intro end;
    first
      [ (** The empty context, by the global context's *)
        solve [ apply wf_ctx_empty; assumption ]
      | solve [ subst; eapply wf_ctx_extend; [ eassumption | apply sort_kind_abs_kind_sort ] ]
      | solve [ eapply wf_ctx_extend_def; [ eassumption | apply type_sort_kind_universe | eassumption ] ]
      | solve [ apply wf_ctx_extend_mod; assumption ]
      | solve [ eapply wf_ctx_extend_dm; eassumption ]
      | solve [ eapply wf_type_of_sort; [ apply type_sort_universe | eassumption ] ]
      (** The prefix *)
      | solve [ match goal with H : ~ ⊢ _ ⍮ _ ⍮ ?G, Hc : ⊢ _ ⍮ _ ⍮ _ :: ?G |- False => exact (H (ctx_decomp_tail Hc)) end ]
      (** An assumption *)
      | solve [ match goal with Hc : ⊢ _ ⍮ _ ⍮ _ ▹{_} _ |- False =>
                  destruct (ctx_decomp_kind Hc) as (S & Hk & HA0);
                  destruct (sort_kind_abs_kind_sort_inv _ _ Hk) as [j ->];
                  first [ match goal with Hn : forall r i, ~ _ |- _ => exact (Hn _ _ HA0) end
                        | match goal with Hne : ?r <> _, HA : _ ⍮ _ ⍮ _ ⊢ _ : abs_kind_sort ?r _ |- _ =>
                            exact (Hne (kind_sort_unique _ _ _ _ _ _ HA HA0)) end ] end ]
      (** A definition, with a module part or not, and a module slot *)
      | solve [ match goal with Hc : ⊢ _ ⍮ _ ⍮ _ :: _ |- False =>
                  inversion Hc; subst;
                  first [ contradiction
                        | match goal with Hn : forall r i, ~ _, HS : type_sort ?S |- _ =>
                            destruct (type_sort_kind_sort _ HS) as (κ0 & j & ->); eapply Hn; eassumption end
                        | match goal with Hn : forall i, ~ _ |- _ => eapply Hn; eassumption end ] end ] ].

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
