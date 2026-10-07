From Stdlib Require Import List Morphisms Morphisms_Relations RelationClasses Relation_Definitions.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** Context PERs are only ever determined up to [<~>] ([per_ctx_env_right_irrel]),
    so every judgment must be transportable along it.  For [rel_wk] both
    arguments are relations on environments; for the other two layers only the
    result PER is. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism φ : (rel_wk φ)
    with signature (@relation_equivalence env) ==> (@relation_equivalence env) ==> iff as rel_wk_morphism.
Proof.
  intros R1 R1' H1 R2 R2' H2.
  split; intros [Hm H]; split; auto; intros ρ ρ' Hρ; apply H2; apply H; now apply H1.
Qed.

Add Parametric Morphism M σ ρ ρσ M' σ' ρ' ρ'σ' : (rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; try eassumption;
    (eapply rel_chain_mono; [| eassumption]); intros; now apply HRR'.
Qed.

Add Parametric Morphism σ φ ρ σ' ρ' : (rel_sub σ φ ρ σ' ρ')
    with signature (@relation_equivalence env) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; try eassumption;
    (eapply rel_chain_mono; [| eassumption]); intros; now apply HRR'.
Qed.

(** The four values of a type chain in [per_univ i] each come with their own
    element PER; irrelevance identifies them, giving a single [R] for the term
    chain to live in. *)
Lemma rel_exp_implies_rel_typ : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ'},
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i) ->
    exists R, rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R.
Proof.
  intros * H.
  destruct H as [aσ a a' a'σ' ? ? ? ? Hchain].
  simpl in Hchain.
  destruct Hchain as [[? ?] [[? ?] [? ?]]].
  handle_per_univ_elem_irrel.
  eexists; econstructor; try eassumption.
  simpl; repeat split; eassumption.
Qed.

Hint Resolve rel_exp_implies_rel_typ : mctt.

Lemma rel_typ_implies_rel_exp : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof.
  intros * H.
  destruct H as [aσ a a' a'σ' ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros; eexists; eassumption.
Qed.

Hint Resolve rel_typ_implies_rel_exp : mctt.

(** The element PER of a type chain is a PER, which is the precondition of every
    [rel_chain] lemma applied to the term chain. *)
Lemma rel_typ_elem_PER : forall {i : nat} {A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    PER R.
Proof.
  intros * H.
  destruct H as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain.
  destruct Hchain as [? [? ?]].
  eauto using per_elem_PER.
Qed.

Hint Resolve rel_typ_elem_PER : mctt.

(** * Semantic Weakenings

    All three lemmas concern the bare [rel_wk], the form the proofs use: the two
    context witnesses of [rel_wk_under_ctx] are carried by whatever produced them.
    Each holds because [eval_wk] is a function and the corresponding equation for
    [⟪_⟫] ([eval_wk_id], [eval_wk_shift], [eval_wk_compose]) holds by
    [reflexivity], which is what fails for substitutions. *)

(** [⟪wk_id⟫ ρ] is [ρ], so this is the identity. *)
Lemma rel_wk_id : forall R, rel_wk wk_id R R.
Proof.
  intros R; split; [ apply wk_mono_id |]; intros ρ ρ' H; rewrite !eval_wk_id; exact H.
Qed.

Hint Resolve rel_wk_id : mctt.

(** A weakening acts contravariantly on environments, so the
    composite [φ ⊙ ψ] — [ψ] after [φ] on variables — is [φ] after [ψ] here. *)
Lemma rel_wk_compose : forall {φ ψ R R' R''},
    rel_wk ψ R R' ->
    rel_wk φ R' R'' ->
    rel_wk (φ ⊙ ψ) R R''.
Proof.
  intros * [Hψm Hψ] [Hφm Hφ]; split; [ apply wk_mono_compose; assumption |].
  intros ρ ρ' H; rewrite !eval_wk_compose by assumption.
  exact (Hφ _ _ (Hψ _ _ H)).
Qed.

(** [⟪↑⟫ ρ] is [ρ↯], and the Ctx-Ext biconditional says precisely
    that an environment of an extended context has a related tail.  This holds
    for an assumption entry and a definition entry alike. *)
Lemma rel_wk_shift : forall {Γ e R R'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R' ->
    rel_wk ↑ R' R.
Proof.
  intros * HΓ HΓA; split; [ apply wk_mono_shift |]; intros ρ ρ' H; rewrite !eval_wk_shift.
  inversion HΓA; subst; handle_per_ctx_env_irrel;
    apply_relation_equivalence; destruct_conjs; eassumption.
Qed.

(** The tail of an extended context, with [rel_wk_shift] for it.  Inverting
    the extension rule produces the tail PER, so unlike [rel_wk_shift] this needs
    no externally supplied witness for [Γ]; this is what allows
    [rel_sub_under_ctx_shift] its premise. *)
Corollary rel_wk_shift_tail : forall {Γ e R},
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    exists R', EF Γ ≈ Γ ∈ per_ctx_env ↘ R' /\ rel_wk ↑ R R'.
Proof.
  intros * H.
  inversion H; subst;
    (eexists; split; [ eassumption | eapply rel_wk_shift; eassumption ]).
Qed.

(** The introduction rule of [Γ ⊨w φ : Δ], packaging its three components.
    Kripke-style premises provide a [rel_wk] together with the two context PERs
    it connects, not the judgment itself, so each substitution case needs this
    step. *)
Lemma rel_wk_under_ctx_intro : forall {Γ Δ φ R R'},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ R' ->
    rel_wk φ R R' ->
    Γ ⊨w φ : Δ.
Proof.
  intros * ? ? ?.
  eexists_rel_wk.
  eassumption.
Qed.

(** * Reading a Context PER off [⊨ Γ]

    [sem_ctx] stores the witness in the extension rule, so there is nothing to
    reconstruct. *)

Lemma sem_ctx_per_ctx_env : forall {Γ},
    ⊨ Γ ->
    exists R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R.
Proof.
  induction 1; [| eexists; eassumption .. ].
  eexists; econstructor; apply Equivalence_Reflexive.
Qed.

Hint Resolve sem_ctx_per_ctx_env : mctt.

Corollary sem_ctx_per_ctx : forall {Γ},
    ⊨ Γ ->
    ⊨ Γ ≈ Γ.
Proof.
  intros * H. apply sem_ctx_per_ctx_env in H. exact H.
Qed.

Hint Resolve sem_ctx_per_ctx : mctt.

(** * Semantic Weakenings are Semantic Substitutions

    The degenerate four-value pattern.  Both commutation obligations are
    discharged by [eval_sub_of_wk] alone, because [sb_wk (ι ψ) φ] is
    [ι (ψ ⊙ φ)] and [⟪ψ ⊙ φ⟫ ρ] is [⟪ψ⟫ (⟪φ⟫ ρ)] by conversion: a weakening
    substitutes only variables, and a variable carries no environment into a
    closure.  So the four values are the same two, and [rel_chain_4_of_2]
    finishes. *)

Lemma rel_sub_of_wk : forall {Δ ψ Γ},
    Δ ⊨w ψ : Γ ->
    Δ ⊨s (ι ψ) ≈ (ι ψ) : Γ.
Proof.
  intros * [env_relΔ [HΔ [env_relΓ [HΓ [Hψm Hψ]]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ [Hφm Hφ] ρ ρ' Hρ.
  apply mk_rel_sub with (ρσφ := ⟪ψ ⊙ φ⟫ ρ) (ρσ := ⟪ψ⟫ (⟪φ⟫ ρ)) (ρ'σ' := ⟪ψ⟫ (⟪φ⟫ ρ')) (ρ'σ'φ := ⟪ψ ⊙ φ⟫ ρ');
    try (apply eval_sub_of_wk; try typeclasses eauto); try (apply wk_mono_compose; assumption); try assumption.
  rewrite !eval_wk_compose by assumption.
  apply rel_chain_4_of_2; [ solve_chain_PER |].
  exact (Hψ _ _ (Hφ _ _ Hρ)).
Qed.

Corollary rel_sub_id : forall {Γ},
    ⊨ Γ ≈ Γ ->
    Γ ⊨s Id ≈ Id : Γ.
Proof.
  intros * [env_relΓ HΓ].
  apply (rel_sub_of_wk (ψ := wk_id)).
  eexists_rel_wk.
  apply rel_wk_id.
Qed.

Hint Resolve rel_sub_id : mctt.

(** The tail of a semantically well-formed context is semantically
    well-formed. *)
Lemma sem_ctx_tail : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    ⊨ Γ.
Proof.
  intros * H; inversion H; assumption.
Qed.

(** [⇑] as a weakening judgment — the form the weakening lemmas below, and
    soundness through them, are instantiated at. *)
Corollary rel_wk_under_ctx_shift : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    (e :: Γ)%list ⊨w ↑ : Γ.
Proof.
  intros * H.
  pose proof (sem_ctx_per_ctx_env H) as [env_relΓA HΓA].
  pose proof (sem_ctx_per_ctx_env (sem_ctx_tail H)) as [env_relΓ HΓ'].
  eapply rel_wk_under_ctx_intro; try eassumption.
  eapply rel_wk_shift; eassumption.
Qed.

Hint Resolve rel_wk_under_ctx_shift : mctt.

Corollary rel_sub_shift : forall {Γ e},
    ⊨ (e :: Γ)%list ->
    (e :: Γ)%list ⊨s Wk : Γ.
Proof.
  intros * H.
  apply (rel_sub_of_wk (rel_wk_under_ctx_shift H)).
Qed.

Hint Resolve rel_sub_shift : mctt.

(** * Instantiation at the Identity

    A semantic judgment quantifies over semantic substitutions; instantiating it
    at [Id] gives a two-value statement.  The Kripke quantification is
    instantiated at [wk_id] via [rel_wk_id], and [Id] evaluates to the environment
    itself ([eval_sub_id]), which the universal form of [rel_exp_under_ctx] allows
    naming as the substituted environment.  Since [M[Id]] is syntactically [M]
    ([exp_sub_id]), both commutation obligations of each chain compare a value
    with itself, and only the middle link remains.  The case files and
    [Core/Completeness.v] use these forms. *)

Lemma rel_sub_under_ctx_simple : forall {Γ Δ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ)
       env_relΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists ρσ ρ'σ',
        ⟦ σ ⟧s ρ ↘ ρσ /\
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' /\
        Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ wk_id (rel_wk_id _) _ _ Hρ) as [? ρσ ρ'σ' ? ? ? ? ? Hchain].
  rewrite !eval_wk_id in *.
  exists ρσ, ρ'σ'.
  repeat split; try eassumption.
  pairwise.
Qed.

(** The companion of [rel_exp_under_ctx_simple] for substitutions.
    [rel_sub_under_ctx] keeps the two substituted environments existential, since
    their existence is real content there, but a caller with its own evaluations
    needs to relate those.  Both forms are needed, and reconciling them is easy at
    this layer, because a context PER, unlike evaluation, respects [env_eq]
    ([per_ctx_env_Proper]). *)
Lemma rel_sub_under_ctx_at : forall {Γ Δ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ)
       env_relΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ),
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_simple H) as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (Hσ _ _ Hρ) as [ρσ0 [ρ'σ'0 [Hev0 [Hev'0 Hrel]]]].
  assert (Heq : env_eq ρσ ρσ0) by (eapply functional_eval_sub; eassumption).
  assert (Heq' : env_eq ρ'σ' ρ'σ'0) by (eapply functional_eval_sub; eassumption).
  now rewrite Heq, Heq'.
Qed.

(** The same at the caller's own context PERs, the form every case file uses.
    Taking the two witnesses as arguments confines [handle_per_ctx_env_irrel],
    which renames hypotheses and so breaks proof scripts that mention them later,
    to this proof. *)
Corollary rel_sub_under_ctx_at' : forall {Γ Δ σ σ' env_relΓ env_relΔ},
    Γ ⊨s σ ≈ σ' : Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    forall ρ ρ' ρσ ρ'σ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      Dom ρσ ≈ ρ'σ' ∈ env_relΔ.
Proof.
  intros * H ? ? * ? ? ?.
  pose proof (rel_sub_under_ctx_at H) as [? [? [? [? Hat]]]].
  handle_per_ctx_env_irrel.
  eapply Hat; eassumption.
Qed.

Lemma rel_exp_under_ctx_simple : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A ⟧ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        exists m m',
          ⟦ M ⟧ ρ ↘ m /\
          ⟦ M' ⟧ ρ' ↘ m' /\
          Dom m ≈ m' ∈ R.
Proof.
  intros * [env_relΓ [HΓ [i HM]]].
  eexists_rel_exp_with i.
  intros ρ ρ' Hρ.
  destruct (HM _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [R [Htyp Hexp]].
  destruct Htyp as [aσ a a' a'σ' ? ? ? ? Htychain].
  destruct Hexp as [mσ m m' m'σ' ? ? ? ? Hmchain].
  exists a, a', R.
  repeat split; try eassumption.
  - pairwise.
  - exists m, m'.
    repeat split; try eassumption.
    pairwise.
Qed.

(** The same with the element PER replaced by the canonical head PER of the
    type, at any context PER of [Γ].  Taking the context PER as an argument
    lets several such instances be read at one relation. *)
Corollary rel_exp_under_ctx_simple_at : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A A ρ ρ'.
Proof.
  intros * HΓ H.
  pose proof (rel_exp_under_ctx_simple H) as [env_relΓ' [HΓ' [i HM]]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  destruct (HM _ _ Hρ) as [a [a' [R [Ha [Ha' [HR [m [m' [Hm [Hm' Hmm']]]]]]]]]].
  exists m, m'; repeat split; try eassumption.
  eapply per_head_of; eassumption.
Qed.

Lemma subtyp_under_ctx_simple : forall {Γ A A'},
    Γ ⊨ A ⊆ A' ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Sub a <: a' at i.
Proof.
  intros * [env_relΓ [HΓ [i HA]]].
  eexists_subtyp_with i.
  intros ρ ρ' Hρ.
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ [a [a'σ' [a' [HaσI [? [Ha'σ'I [? [Hl [Hr Hsub]]]]]]]]]].
  (** Both commutation obligations of [subtyp_under_ctx] compare a value with
    itself, so the subtyping need not be transported. *)
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; eassumption.
Qed.

(** * Precomposition with a Weakening

    Two instantiations of the same hypothesis at two weakenings.  Given
    [Γ' ⊨w φ : Γ] and [ρ ≈ ρ' ∈ R_Γ'], instantiate [Δ ⊨s σ ≈ σ' : Δ']:

    - at [Γ'] with the composite [ψ ⊙ φ] ([rel_wk_compose]), whose outer values
      are the outer values wanted, because [σ[ψ][φ]] is [σ[ψ ⊙ φ]] ([sb_wk_wk]);
    - at [Δ] with [ψ] and the weakened pair [⟪φ⟫ ρ ≈ ⟪φ⟫ ρ'], whose outer values
      are the inner values wanted.

    Their inner values coincide, since [⟪ψ ⊙ φ⟫ ρ] and [⟪ψ⟫ (⟪φ⟫ ρ)] are
    convertible, so both chains contain the value of [σ] at that environment.  The
    chains then merge, up to [env_eq] as in transitivity, because
    [functional_eval_sub] is all that identifies two evaluations of [σ]. *)

Lemma rel_sub_under_ctx_wk : forall {Γ ψ Δ σ σ' Δ'},
    Δ ⊨s σ ≈ σ' : Δ' ->
    Γ ⊨w ψ : Δ ->
    Γ ⊨s (sb_wk σ ψ) ≈ (sb_wk σ' ψ) : Δ'.
Proof.
  intros * [env_relΔ [HΔ [env_relΔ' [HΔ' Hσ]]]] [env_relΓ [HΓ [env_relΔ2 [HΔ2 Hψ]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ (rel_wk_compose Hφ Hψ) _ _ Hρ) as [a1 a2 ? a4 Ha1 Ha2 ? Ha4 Ha].
  rewrite eval_wk_compose in Ha2 by (eapply rel_wk_mono; eassumption).
  destruct (Hσ _ _ HΓ _ Hψ _ _ (Hφ _ _ Hρ)) as [b1 b2 ? b4 Hb1 Hb2 ? Hb4 Hb].
  apply (mk_rel_sub a1 b1 b4 a4);
    [ rewrite sb_wk_wk; exact Ha1 | exact Hb1 | exact Hb4 | rewrite sb_wk_wk; exact Ha4 |].
  assert (Heq : env_eq a2 b2) by (eapply functional_eval_sub; eassumption).
  assert (Hlink : Dom a2 ≈ b2 ∈ env_relΔ') by (rewrite Heq; pairwise).
  assert (Hb' : rel_chain env_relΔ' ([b2; b1; b4])) by solve_rel_chain.
  assert (Hc : rel_chain env_relΔ' ([a2; b2; b1; b4]))
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Hc Ha a2.
Qed.

(** Precomposition by a weakening, which, unlike general composition of two
    semantic substitutions, is semantic.  Nothing is instantiated twice: the four
    environments wanted are the [⟪φ⟫]-images of the four the hypothesis supplies,
    by [eval_sub_wk_pre] on the inner two and by the same lemma after
    [sb_wk_wk_pre] on the outer two.  The chain is transported member by member by
    [rel_chain_map], whose hypothesis is [rel_wk φ].

    The general case fails because [Γ'' ⊨s σ ⨟ τ : Γ] would need the value of
    [(σ x)[τ]] for every index [x], a statement about terms that the substitution
    judgment does not make.  This is why the [ℕ]-elimination [β]-rule goes
    through the generic recursor. *)

Lemma rel_sub_under_ctx_wk_pre : forall {Γ Δ Δ' φ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨w φ : Δ' ->
    Γ ⊨s (ι φ) ⨟ σ ≈ (ι φ) ⨟ σ' : Δ'.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]] [env_relΔ2 [HΔ2 [env_relΔ' [HΔ' Hφ]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' ψ Hψ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hψ _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  pose proof (rel_chain_map _ _ (eval_wk φ) (rel_wk_app _ _ _ Hφ) _ Hchain) as Hchain'.
  simpl in Hchain'.
  apply (mk_rel_sub ⟪φ⟫ v1 ⟪φ⟫ v2
                    ⟪φ⟫ v3 ⟪φ⟫ v4);
    [ rewrite sb_wk_wk_pre | | | rewrite sb_wk_wk_pre |];
    try ((apply eval_sub_wk_pre; try typeclasses eauto); eassumption).
  exact Hchain'.
Qed.

(** * Semantic Weakening of a Term Judgment

    A term judgment may be weakened along [Γ ⊨w φ : Δ].  The equation
    [⟦M[φ]ʷ⟧(ρ) = ⟦M⟧(⟪φ⟫ ρ)] fails (in the [λ] case the two sides are different
    closures), so the two values must be related instead, by the judgment about
    [M] instantiated twice:

    - along [ι φ ⨟ τ] at [(ρ, ρ')], whose outer values are the goal's outer ones
      ([exp_sub_wk]: [M[φ]ʷ[τ]] is [M[ι φ ⨟ τ]]);
    - along [ι φ] at [(ρτ, ρ'τ')], whose outer values are the goal's inner ones
      ([exp_sub_of_wk]: [M[ι φ]] is [M[φ]ʷ]).

    Both are read at the same pair of inner environments, [⟪φ⟫ ρτ] and
    [⟪φ⟫ ρ'τ'] (named by [eval_sub_wk_pre] and [eval_sub_of_wk] respectively), so
    their inner values coincide and the two chains merge.  This relies on the
    universal form of [rel_exp_under_ctx]: with existential environments the two
    instantiations would concern merely pointwise-equal environments, hence
    unrelated closures. *)

Lemma rel_exp_under_ctx_wk : forall {Γ Δ φ A M M'},
    Γ ⊨w φ : Δ ->
    Δ ⊨ M ≈ M' : A ->
    Γ ⊨ M[φ]ʷ ≈ M'[φ]ʷ : A[φ]ʷ.
Proof.
  intros * Hφj HM.
  pose proof Hφj as [env_relΓ [HΓ [env_relΔ [HΔ Hφ]]]].
  pose proof HM as [env_relΔ2 [HΔ2 [i HMgen]]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' τ τ' Hτj ρ ρ' ρτ ρ'τ' Hρ Hev Hev'.
  assert (Hρτ : Dom ρτ ≈ ρ'τ' ∈ env_relΓ)
    by (eapply rel_sub_under_ctx_at'; eassumption).
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk_pre Hτj Hφj) _ _ _ _ Hρ
              (eval_sub_wk_pre _ _ _ _ Hev) (eval_sub_wk_pre _ _ _ _ Hev'))
    as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓ _ _ (rel_sub_of_wk Hφj) _ _ _ _ Hρτ
              (eval_sub_of_wk _ _) (eval_sub_of_wk _ _))
    as [R2 [Htyp2 Hexp2]].
  destruct Htyp1 as [a1 a2 a3 a4 Ha1 ? ? Ha4 Hty1].
  destruct Htyp2 as [b1 b2 b3 b4 Hb1 ? ? Hb4 Hty2].
  destruct Hexp1 as [v1 v2 v3 v4 Hv1 ? ? Hv4 Hc1].
  destruct Hexp2 as [w1 w2 w3 w4 Hw1 ? ? Hw4 Hc2].
  (** The two commutation obligations of each chain, read as rewritings of the
      substitution that produced it. *)
  rewrite <- exp_sub_wk in Ha1, Ha4, Hv1, Hv4.
  rewrite exp_sub_of_wk in Hb1, Hb4, Hw1, Hw4.
  functional_eval_rewrite_clear.
  (** The middle link of each type chain, which is where the two element PERs
      overlap: both are read at the same pair of inner environments. *)
  assert (Hmid1 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  exists R1.
  split.
  - apply (mk_rel_exp a1 b1 b4 a4); try eassumption.
    merge_rel_chain Hty1 Hty2 a2.
  - apply (mk_rel_exp v1 w1 w4 v4); try eassumption.
    merge_rel_chain Hc1 Hc2 v2.
Qed.

(** The form the variable case of soundness uses: the failing equation
    [⟦M[φ]ʷ⟧(ρ) = ⟦M⟧(⟪φ⟫ ρ)] as a relatedness.  This is [rel_exp_under_ctx] at
    [ι φ], where both commutation obligations vanish ([exp_sub_of_wk]) and
    [eval_sub_of_wk] names both inner environments, so the wanted pair (an outer
    value against the opposite inner one) is one [pairwise] away. *)
Lemma rel_exp_under_ctx_wk_simple : forall {Γ Δ φ A M M'},
    Γ ⊨w φ : Δ ->
    Δ ⊨ M ≈ M' : A ->
    exists env_relΓ (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) (i : nat),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A[φ]ʷ ⟧ ρ ↘ a /\
        ⟦ A ⟧ ⟪φ⟫ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        exists m m',
          ⟦ M[φ]ʷ ⟧ ρ ↘ m /\
          ⟦ M' ⟧ ⟪φ⟫ ρ' ↘ m' /\
          Dom m ≈ m' ∈ R.
Proof.
  intros * Hφj HM.
  pose proof Hφj as [env_relΓ [HΓ [env_relΔ [HΔ Hφ]]]].
  pose proof HM as [env_relΔ2 [HΔ2 [i HMgen]]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros ρ ρ' Hρ.
  destruct (HMgen _ _ HΓ _ _ (rel_sub_of_wk Hφj) _ _ _ _ Hρ
              (eval_sub_of_wk _ _) (eval_sub_of_wk _ _)) as [R [Htyp Hexp]].
  destruct Htyp as [a1 a2 a3 a4 Ha1 ? Ha3 ? Hty].
  destruct Hexp as [v1 v2 v3 v4 Hv1 ? Hv3 ? Hc].
  rewrite exp_sub_of_wk in Ha1, Hv1.
  (** The type pair first: it puts [per_univ_elem i R] in context, which is what
      resolves the [PER R] obligation of the element pair. *)
  assert (Hmid : DF a1 ≈ a3 ∈ per_univ_elem i ↘ R) by pairwise.
  exists a1, a3, R.
  repeat split; try eassumption.
  exists v1, v3.
  repeat split; try eassumption.
  pairwise.
Qed.

(** * Precomposition by [⇑]

    Nothing is instantiated twice: once dropped, the four values of the hypothesis
    are the four values wanted.  Two facts do the work, each the [⇑] case of
    something that fails in general:

    - [eval_sub_shift_pre]: [⟦⇑ ⨟ σ⟧(ρ)] is [⟦σ⟧(ρ)↯], because [⇑] substitutes
      only variables (and [sb_wk_shift_pre] says postcomposition by [φ] slides
      past, so the same holds of the two [φ]-weakened values);
    - [rel_wk_shift_tail]: the Ctx-Ext biconditional, which says that dropping
      takes [R_{Δ ▹ A}] to [R_Δ].

    The second is a [rel_wk], the hypothesis of [rel_chain_map], so the chain is
    transported along the drop member by member. *)

Lemma rel_sub_under_ctx_shift : forall {Γ Δ e σ σ'},
    Γ ⊨s σ ≈ σ' : (e :: Δ)%list ->
    Γ ⊨s Wk ⨟ σ ≈ Wk ⨟ σ' : Δ.
Proof.
  intros * [env_relΓ [HΓ [env_relΔA [HΔA Hσ]]]].
  pose proof (rel_wk_shift_tail HΔA) as [env_relΔ [HΔ Hdrop]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  assert (Hdrop' : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔA -> Dom ρ↯ ≈ ρ'↯ ∈ env_relΔ)
    by (intros; rewrite <- !eval_wk_shift; apply Hdrop; assumption).
  pose proof (rel_chain_map _ _ drop_env Hdrop' _ Hchain) as Hchain'.
  simpl in Hchain'.
  apply (mk_rel_sub v1↯ v2↯ v3↯ v4↯);
    [ rewrite sb_wk_shift_pre | | | rewrite sb_wk_shift_pre |];
    try (apply eval_sub_shift_pre; eassumption).
  exact Hchain'.
Qed.

(** * Symmetry

    The four values of the symmetric judgment are the same four in the opposite
    order, so symmetry is [rel_chain_4_sym]. *)

Lemma rel_exp_sym : forall {M σ ρ ρσ M' σ' ρ' ρ'σ' R},
    PER R ->
    rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' R ->
    rel_exp M' σ' ρ' ρ'σ' M σ ρ ρσ R.
Proof.
  intros * ? [].
  econstructor; try eassumption.
  now apply rel_chain_4_sym.
Qed.

Lemma rel_sub_sym : forall {σ φ ρ σ' ρ' R},
    PER R ->
    rel_sub σ φ ρ σ' ρ' R ->
    rel_sub σ' φ ρ' σ ρ R.
Proof.
  intros * ? [].
  econstructor; try eassumption.
  now apply rel_chain_4_sym.
Qed.

Lemma rel_sub_under_ctx_sym : forall {Γ Δ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Γ ⊨s σ' ≈ σ : Δ.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  apply rel_sub_sym; [ solve_chain_PER |].
  apply (Hσ _ _ HΓ' _ Hφ).
  symmetry; eassumption.
Qed.

(** Instantiate the hypothesis at the swapped substitution pair and the swapped
    environment pair; both chains come out reversed, and reversing them again is
    [rel_exp_sym].  The universal form of [rel_exp_under_ctx] makes the swap
    possible: the caller's two evaluations serve, read in the other order. *)
Lemma rel_exp_under_ctx_sym : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M' ≈ M : A.
Proof.
  intros * [env_relΓ [HΓ [i HM]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : Dom ρ' ≈ ρ ∈ env_rel') by (symmetry; eassumption).
  destruct (HM _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ Hρ' Hev' Hev)
    as [R [Htyp Hexp]].
  exists R.
  split; apply rel_exp_sym;
    first [ eassumption | solve_chain_PER | eauto using rel_typ_elem_PER ].
Qed.

(** * Transitivity

    Two four-value chains, sharing the value both sides evaluate [σ2[φ]] to.  It
    is shared only up to [env_eq] ([functional_eval_sub] determines an evaluated
    substitution no further), hence [per_ctx_env_resp_env_eq]; with that link
    prefixed the two chains overlap, [rel_chain_merge] joins them, and
    [rel_chain_incl] selects the four values wanted. *)

Lemma rel_sub_under_ctx_trans : forall {Γ Δ σ1 σ2 σ3},
    Γ ⊨s σ1 ≈ σ2 : Δ ->
    Γ ⊨s σ2 ≈ σ3 : Δ ->
    Γ ⊨s σ1 ≈ σ3 : Δ.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ H12]]]] H23'.
  pose proof H23' as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 H23]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  assert (Hρ' : Dom ρ' ≈ ρ' ∈ env_rel')
    by (etransitivity; [ symmetry | ]; eassumption).
  destruct (H12 _ _ HΓ' _ Hφ _ _ Hρ) as [ρσ1φ ρσ1 ρ'σ2 ρ'σ2φ ? ? ? Hev2 Ha].
  destruct (H23 _ _ HΓ' _ Hφ _ _ Hρ') as [ρ'σ2φb ρ'σ2b ρ'σ3 ρ'σ3φ Hev2b ? ? ? Hb].
  econstructor; try eassumption.
  assert (Heq : env_eq ρ'σ2φ ρ'σ2φb) by (eapply functional_eval_sub; eassumption).
  assert (Hlink : Dom ρ'σ2φ ≈ ρ'σ2φb ∈ env_relΔ) by (rewrite Heq; pairwise).
  assert (Hc : rel_chain env_relΔ ([ρ'σ2φ; ρ'σ2φb; ρ'σ2b; ρ'σ3; ρ'σ3φ]))
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Ha Hc ρ'σ2φ.
Qed.

(** The reflexive instances of a substitution judgment.  The substitution
    cases and [rel_exp_under_ctx_trans] instantiate a second judgment at one side
    of a given substitution pair; symmetry and transitivity supply these. *)

Corollary rel_sub_under_ctx_refl_left : forall {Γ Δ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Γ ⊨s σ : Δ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

Corollary rel_sub_under_ctx_refl_right : forall {Γ Δ σ σ'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Γ ⊨s σ' : Δ.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

(** Two four-value chains, this time sharing values exactly.  The second
    judgment is instantiated at the reflexive right-hand substitution [σ'] and the
    reflexive right-hand environment pair [ρ' ≈ ρ'], with the caller's [ρ'σ']
    named on both sides, so its first two values are [⟦M2[σ']⟧(ρ')] and
    [⟦M2⟧(ρ'σ')], the last two of the first chain.  With existential environments
    they would only be values of [M2] at [env_eq]-related environments, and the
    chains would not join.

    The two element PERs are identified through the type chains, which overlap in
    [⟦A⟧(ρ'σ')]; irrelevance is cross-level, so the two judgments' universe levels
    need not agree. *)

Lemma rel_exp_under_ctx_trans : forall {Γ A M1 M2 M3},
    Γ ⊨ M1 ≈ M2 : A ->
    Γ ⊨ M2 ≈ M3 : A ->
    Γ ⊨ M1 ≈ M3 : A.
Proof.
  intros * [env_relΓ [HΓ [i H12]]] H23'.
  pose proof H23' as [env_relΓ2 [HΓ2 [j H23]]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : Dom ρ' ≈ ρ' ∈ env_rel')
    by (etransitivity; [ symmetry | ]; eassumption).
  destruct (H12 _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Htyp1 Hexp1]].
  destruct (H23 _ _ HΓ' _ _ (rel_sub_under_ctx_refl_right Hσ) _ _ _ _ Hρ' Hev' Hev')
    as [R2 [Htyp2 Hexp2]].
  destruct Htyp1 as [aσ a a' a'σ' ? ? ? ? Hty1].
  destruct Htyp2 as [b'σ' b' b'' b''σ' ? ? ? ? Hty2].
  destruct Hexp1 as [v1 v2 v3 v4 ? ? ? ? Hc1].
  destruct Hexp2 as [w1 w2 w3 w4 ? ? ? ? Hc2].
  functional_eval_rewrite_clear.
  simpl in Hty1, Hty2.
  destruct Hty1 as [? [? ?]], Hty2 as [? [? ?]].
  handle_per_univ_elem_irrel.
  exists R1.
  split.
  - econstructor; try eassumption.
    simpl; repeat split; eassumption.
  - econstructor; try eassumption.
    merge_rel_chain Hc1 Hc2 v3.
Qed.

(** The term-level reflexive instances.  The substitution cases use one to
    bridge the values of a term at two different environments. *)

Corollary rel_exp_under_ctx_refl_left : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M : A.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.

Corollary rel_exp_under_ctx_refl_right : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    Γ ⊨ M' : A.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.

(** * Changing the Context PER

    A substitution judgment may be read with a smaller domain relation or a
    larger codomain relation, and a term judgment in any context whose
    relation is included in that of its own context.  This is how a judgment
    about [Γ ▹ A] serves for [Γ ▸ A ≔ M], and a judgment about [Γ ▸ A ≔ M] for
    [Γ ▸ A ≔ M'] when [M] and [M'] are related. *)

Lemma rel_sub_under_ctx_restrict : forall {Γ1 Γ2 Δ1 Δ2 σ σ' R1 R2 S1 S2},
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    EF Γ2 ≈ Γ2 ∈ per_ctx_env ↘ R2 ->
    EF Δ1 ≈ Δ1 ∈ per_ctx_env ↘ S1 ->
    EF Δ2 ≈ Δ2 ∈ per_ctx_env ↘ S2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R1 -> Dom ρ ≈ ρ' ∈ R2) ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ S1 -> Dom ρ ≈ ρ' ∈ S2) ->
    Γ2 ⊨s σ ≈ σ' : Δ1 ->
    Γ1 ⊨s σ ≈ σ' : Δ2.
Proof.
  intros * HΓ1 HΓ2 HΔ1 HΔ2 HR HS [R2' [HΓ2' [S1' [HΔ1' Hσ]]]].
  assert (ER : R2' <~> R2) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (ES : S1' <~> S1) by (eapply per_ctx_env_right_irrel; eassumption).
  exists R1, HΓ1, S2, HΔ2.
  intros Γ' env_rel' HΓ' φ [Hφm Hφ] ρ ρ' Hρ.
  assert (Hφ' : rel_wk φ env_rel' R2')
    by (split; [ assumption | intros; apply ER, HR, Hφ; assumption ]).
  destruct (Hσ _ _ HΓ' _ Hφ' _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption ].
  intros; apply HS, ES; assumption.
Qed.

Lemma rel_exp_under_ctx_restrict : forall {Γ1 Γ2 R1 R2 A M M'},
    EF Γ1 ≈ Γ1 ∈ per_ctx_env ↘ R1 ->
    EF Γ2 ≈ Γ2 ∈ per_ctx_env ↘ R2 ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ R1 -> Dom ρ ≈ ρ' ∈ R2) ->
    Γ2 ⊨ M ≈ M' : A ->
    Γ1 ⊨ M ≈ M' : A.
Proof.
  intros * HΓ1 HΓ2 HR [R2' [HΓ2' [i HM]]].
  exists R1, HΓ1, i.
  intros Γ' env_rel' HΓ' σ σ' Hσ.
  apply (HM _ _ HΓ').
  eapply rel_sub_under_ctx_restrict; [ eassumption | eassumption | exact HΓ1 | exact HΓ2 | | exact HR | exact Hσ ].
  auto.
Qed.

(** * Equality from Pointwise Relatedness

    Two valid terms of [T] are equal when their values at related environments
    are related.  The commutation obligations come from the two validity
    judgments, and the relatedness obligation from the pointwise premise read
    at the substituted environments. *)
Lemma rel_exp_under_ctx_of_simple : forall {Γ T N N' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ N : T ->
    Γ ⊨ N' : T ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ env_relΓ ->
        exists n n', ⟦ N ⟧ ρ ↘ n /\ ⟦ N' ⟧ ρ' ↘ n' /\ Dom n ≈ n' ∈ per_head T T ρ ρ') ->
    Γ ⊨ N ≈ N' : T.
Proof.
  intros * HΓ [R1' [HΓ1 [i HN]]] [R2' [HΓ2 [j HN']]] Hpt.
  exists env_relΓ, HΓ, i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HN _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R1 [Ht1 He1]].
  destruct (HN' _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R2 [Ht2 He2]].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  destruct (Hpt _ _ Hρσ) as [n [n' [Hn [Hn' Hnn']]]].
  destruct Ht1 as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hty1].
  destruct Ht2 as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hty2].
  destruct He1 as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hc1].
  destruct He2 as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hc2].
  functional_eval_rewrite_clear.
  assert (Hmid1 : DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF a2 ≈ a3 ∈ per_univ_elem j ↘ R2) by pairwise.
  assert (HPER : PER R1) by (eapply per_elem_PER; eassumption).
  apply (per_head_iff Ha2 Ha3 Hmid1) in Hnn'.
  assert (E : R2 <~> R1) by (eapply per_univ_elem_right_irrel; eassumption).
  exists R1; split.
  - econstructor; eassumption.
  - apply (mk_rel_exp v1 v2 w3 w4); try eassumption.
    apply rel_chain_4; [ pairwise | eassumption | apply E; pairwise ].
Qed.

End Fixed_GCtx.

#[export] Existing Instance rel_wk_morphism_Proper.
#[export] Existing Instance rel_exp_morphism_Proper.
#[export] Existing Instance rel_sub_morphism_Proper.
#[export]
Hint Resolve rel_exp_implies_rel_typ : mctt.
#[export]
Hint Resolve rel_typ_implies_rel_exp : mctt.
#[export]
Hint Resolve rel_typ_elem_PER : mctt.
#[export]
Hint Resolve rel_wk_id : mctt.
#[export]
Hint Resolve sem_ctx_per_ctx_env : mctt.
#[export]
Hint Resolve sem_ctx_per_ctx : mctt.
#[export]
Hint Resolve rel_sub_id : mctt.
#[export]
Hint Resolve rel_wk_under_ctx_shift : mctt.
#[export]
Hint Resolve rel_sub_shift : mctt.
