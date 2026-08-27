From Stdlib Require Import List Morphisms Morphisms_Relations RelationClasses Relation_Definitions.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations.
Import Wk_Notations.

(** Context PERs are only ever determined up to [<~>] ([per_ctx_env_right_irrel]),
    so every judgment must be transportable along it.  For [rel_wk] both
    arguments are relations on environments; for the other two layers only the
    result PER is. *)
Add Parametric Morphism φ : (rel_wk φ)
    with signature (@relation_equivalence env) ==> (@relation_equivalence env) ==> iff as rel_wk_morphism.
Proof.
  intros R1 R1' H1 R2 R2' H2.
  unfold rel_wk; split; intros H ρ ρ' Hρ; apply H2; apply H; now apply H1.
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
    element PER; irrelevance identifies them, and only then is there a single [R]
    for the term chain to live in.  With explicit substitutions this lemma was a
    one-liner because the chain had a single link. *)
Lemma rel_exp_implies_rel_typ : forall {i A σ ρ ρσ A' σ' ρ' ρ'σ'},
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

#[export]
Hint Resolve rel_exp_implies_rel_typ : mctt.

Lemma rel_typ_implies_rel_exp : forall {i A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof.
  intros * H.
  destruct H as [aσ a a' a'σ' ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros; eexists; eassumption.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_exp : mctt.

(** The element PER of a type chain is a PER, which is the precondition of every
    [rel_chain] lemma applied to the term chain. *)
Lemma rel_typ_elem_PER : forall {i A σ ρ ρσ A' σ' ρ' ρ'σ' R},
    rel_typ i A σ ρ ρσ A' σ' ρ' ρ'σ' R ->
    PER R.
Proof.
  intros * H.
  destruct H as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain.
  destruct Hchain as [? [? ?]].
  eauto using per_elem_PER.
Qed.

#[export]
Hint Resolve rel_typ_elem_PER : mctt.

(** * Semantic Weakenings

    All three are about the bare [rel_wk], because that is the form the proofs
    use: the two context witnesses of [rel_wk_under_ctx] are carried by whatever
    produced them.  Each holds because [eval_wk] is a *function* and the
    corresponding equation for [⟦_⟧w] ([eval_wk_id], [eval_wk_shift],
    [eval_wk_compose]) is a [reflexivity] — which is exactly what fails one layer up, for
    substitutions. *)

(** [⟦wk_id⟧w ρ] is [fun x => ρ x], so this is the identity. *)
Lemma rel_wk_id : forall R, rel_wk wk_id R R.
Proof.
  intros R ρ ρ' H. exact H.
Qed.

#[export]
Hint Resolve rel_wk_id : mctt.

(** A weakening acts contravariantly on environments, so the
    composite [φ ⊙ ψ] — [ψ] after [φ] on variables — is [φ] after [ψ] here. *)
Lemma rel_wk_compose : forall {φ ψ R R' R''},
    rel_wk ψ R R' ->
    rel_wk φ R' R'' ->
    rel_wk (φ ⊙ ψ) R R''.
Proof.
  intros * Hψ Hφ ρ ρ' H.
  exact (Hφ _ _ (Hψ _ _ H)).
Qed.

(** [⟦↑⟧w ρ] is [ρ↯], and the Ctx-Ext biconditional says precisely
    that a [Γ, A]-environment has a related tail. *)
Lemma rel_wk_shift : forall {Γ A R R'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R }} ->
    {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ R' }} ->
    rel_wk ↑ R' R.
Proof.
  intros * HΓ HΓA ρ ρ' H.
  invert_per_ctx_env HΓA.
  apply_relation_equivalence.
  destruct H as [? ?].
  eassumption.
Qed.

(** The tail of an extended context, together with [rel_wk_shift] for it.
    Inverting the extension rule produces the tail PER, so — unlike
    [rel_wk_shift] — this needs no witness for [Γ] supplied from outside, which is what lets
    [rel_sub_under_ctx_shift] be stated with the premise it has. *)
Corollary rel_wk_shift_tail : forall {Γ A R},
    {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ R }} ->
    exists R', {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R' }} /\ rel_wk ↑ R R'.
Proof.
  intros * H.
  inversion H; subst.
  eexists; split; [ eassumption |].
  eapply rel_wk_shift; eassumption.
Qed.

(** The introduction rule of [Γ ⊨w φ : Δ], packaging its three components.  Every
    Kripke-style premise in the development hands out a [rel_wk] together with
    the two context PERs it connects — never the judgment itself — so recovering
    the judgment is a step that recurs in each of the substitution cases. *)
Lemma rel_wk_under_ctx_intro : forall {Γ Δ φ R R'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R }} ->
    {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ R' }} ->
    rel_wk φ R R' ->
    {{ Γ ⊨w φ : Δ }}.
Proof.
  intros * ? ? ?.
  eexists_rel_wk.
  eassumption.
Qed.

(** * Reading a Context PER off [⊨ Γ]

    [sem_ctx] stores the witness in the extension rule, so there is nothing to
    reconstruct. *)

Lemma sem_ctx_per_ctx_env : forall {Γ},
    {{ ⊨ Γ }} ->
    exists R, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ R }}.
Proof.
  induction 1; [| eexists; eassumption ].
  eexists; econstructor; apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve sem_ctx_per_ctx_env : mctt.

Corollary sem_ctx_per_ctx : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ ⊨ Γ ≈ Γ }}.
Proof.
  intros * H. apply sem_ctx_per_ctx_env in H. exact H.
Qed.

#[export]
Hint Resolve sem_ctx_per_ctx : mctt.

(** * Semantic Weakenings are Semantic Substitutions

    The degenerate four-value pattern.  Both commutation obligations are
    discharged by [eval_sub_of_wk] alone, because

      [sb_wk (ι ψ) φ] is [ι (ψ ⊙ φ)]   and   [⟦ψ ⊙ φ⟧w ρ] is [⟦ψ⟧w (⟦φ⟧w ρ)]

    both hold by conversion — a weakening substitutes only variables, and a
    variable carries no environment into a closure.  So all four values are
    literally the same two, and [rel_chain_4_of_2] finishes. *)

Lemma rel_sub_of_wk : forall {Δ ψ Γ},
    {{ Δ ⊨w ψ : Γ }} ->
    {{ Δ ⊨s ^(ι ψ) ≈ ^(ι ψ) : Γ }}.
Proof.
  intros * [env_relΔ [HΔ [env_relΓ [HΓ Hψ]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  econstructor; try apply eval_sub_of_wk.
  apply rel_chain_4_of_2; [ solve_chain_PER |].
  exact (Hψ _ _ (Hφ _ _ Hρ)).
Qed.

Corollary rel_sub_id : forall {Γ},
    {{ ⊨ Γ ≈ Γ }} ->
    {{ Γ ⊨s Id ≈ Id : Γ }}.
Proof.
  intros * [env_relΓ HΓ].
  apply (rel_sub_of_wk (ψ := wk_id)).
  eexists_rel_wk.
  apply rel_wk_id.
Qed.

#[export]
Hint Resolve rel_sub_id : mctt.

(** [⇑] as a weakening judgment — the form the weakening lemmas below, and
    soundness through them, are instantiated at. *)
Corollary rel_wk_under_ctx_shift : forall {Γ A},
    {{ ⊨ Γ, A }} ->
    {{ Γ, A ⊨w ↑ : Γ }}.
Proof.
  intros * H.
  pose proof (sem_ctx_per_ctx_env H) as [env_relΓA HΓA].
  inversion H as [| ? ? ? ? HΓ ? ?]; subst.
  pose proof (sem_ctx_per_ctx_env HΓ) as [env_relΓ HΓ'].
  eapply rel_wk_under_ctx_intro; try eassumption.
  eapply rel_wk_shift; eassumption.
Qed.

#[export]
Hint Resolve rel_wk_under_ctx_shift : mctt.

Corollary rel_sub_shift : forall {Γ A},
    {{ ⊨ Γ, A }} ->
    {{ Γ, A ⊨s Wk : Γ }}.
Proof.
  intros * H.
  apply (rel_sub_of_wk (rel_wk_under_ctx_shift H)).
Qed.

#[export]
Hint Resolve rel_sub_shift : mctt.

(** * Instantiation at the Identity

    A semantic judgment is a statement about arbitrary semantic substitutions;
    instantiating it at [Id] recovers the two-value statement of the
    explicit-substitution presentation.  Two things make the collapse work: the
    Kripke quantification is instantiated at [wk_id] via [rel_wk_id], and [Id]
    evaluates to the environment itself ([eval_sub_id]), which the universal form
    of [rel_exp_under_ctx] lets us name as the substituted environment.  Then [M[Id]] is
    *syntactically* [M] ([exp_sub_id]), so both commutation obligations of each
    chain compare a value with itself and only the middle link survives.  These
    are the forms the case files and [Core/Completeness.v] consume. *)

Lemma rel_sub_under_ctx_simple : forall {Γ Δ σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΓ (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }})
       env_relΔ (_ : {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }}),
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      exists ρσ ρ'σ',
        {{ ⟦ σ ⟧s ρ ↘ ρσ }} /\
        {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} /\
        {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }}.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ wk_id (rel_wk_id _) _ _ Hρ) as [? ρσ ρ'σ' ? ? ? ? ? Hchain].
  exists ρσ, ρ'σ'.
  repeat split; try eassumption.
  eapply rel_chain_4_related; eassumption.
Qed.

(** The companion to [rel_exp_under_ctx_simple] for substitutions:
    [rel_sub_under_ctx] keeps the
    two substituted environments existential — the *existence* of [⟦σ⟧(ρ)] is
    genuine content there, so there is nothing to remove — but a caller with
    evaluations of its own needs to relate *those*.  Both forms are needed, and
    reconciling them is easy at this layer, because a context PER, unlike
    evaluation, does respect [env_eq] ([per_ctx_env_Proper]). *)
Lemma rel_sub_under_ctx_at : forall {Γ Δ σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΓ (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }})
       env_relΔ (_ : {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }}),
    forall ρ ρ' ρσ ρ'σ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
      {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
      {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }}.
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

(** The same at the caller's own context PERs rather than at ones it must then
    identify with its own.  This is the form every case file wants: taking the two
    witnesses as arguments confines [handle_per_ctx_env_irrel] — which renames
    hypotheses, and so breaks any proof script that mentions them afterwards — to
    this proof. *)
Corollary rel_sub_under_ctx_at' : forall {Γ Δ σ σ' env_relΓ env_relΔ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    forall ρ ρ' ρσ ρ'σ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
      {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
      {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }}.
Proof.
  intros * H ? ? * ? ? ?.
  pose proof (rel_sub_under_ctx_at H) as [? [? [? [? Hat]]]].
  handle_per_ctx_env_irrel.
  eapply Hat; eassumption.
Qed.

Lemma rel_exp_under_ctx_simple : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists env_relΓ (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }}) i,
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      exists a a' R,
        {{ ⟦ A ⟧ ρ ↘ a }} /\
        {{ ⟦ A ⟧ ρ' ↘ a' }} /\
        {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} /\
        exists m m',
          {{ ⟦ M ⟧ ρ ↘ m }} /\
          {{ ⟦ M' ⟧ ρ' ↘ m' }} /\
          {{ Dom m ≈ m' ∈ R }}.
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
  - eapply rel_chain_4_related; eassumption.
  - exists m, m'.
    repeat split; try eassumption.
    eapply rel_chain_4_related; eassumption.
Qed.

Lemma subtyp_under_ctx_simple : forall {Γ A A'},
    {{ Γ ⊨ A ⊆ A' }} ->
    exists env_relΓ (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }}) i,
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      exists a a',
        {{ ⟦ A ⟧ ρ ↘ a }} /\
        {{ ⟦ A' ⟧ ρ' ↘ a' }} /\
        {{ Sub a <: a' at i }}.
Proof.
  intros * [env_relΓ [HΓ [i HA]]].
  eexists_subtyp_with i.
  intros ρ ρ' Hρ.
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ [a [a'σ' [a' [HaσI [? [Ha'σ'I [? [Hl [Hr Hsub]]]]]]]]]].
  (** Both commutation obligations of [subtyp_under_ctx] now compare a value
      with itself, so there is nothing to transport the subtyping along. *)
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; eassumption.
Qed.

(** * Precomposition with a Weakening

    Two instantiations of the same hypothesis, at two different weakenings.  Take
    an arbitrary [Γ' ⊨w φ : Γ] and [ρ ≈ ρ' ∈ R_Γ'], and instantiate
    [Δ ⊨s σ ≈ σ' : Δ']

    - at [Γ'] with the composite [ψ ⊙ φ] ([rel_wk_compose]), whose *outer* values are
      the outer values wanted — because [σ[ψ][φ]] is [σ[ψ ⊙ φ]] ([sb_wk_wk]);
    - at [Δ] with [ψ] itself and the weakened pair [⟦φ⟧w ρ ≈ ⟦φ⟧w ρ'], whose
      outer values are the *inner* values wanted.

    Their inner values coincide, since [⟦ψ ⊙ φ⟧w ρ] and [⟦ψ⟧w (⟦φ⟧w ρ)] are
    convertible: both chains contain the value of [σ] at that one environment.
    So this is again a merge — up to [env_eq], as in transitivity, because
    [functional_eval_sub] is all that identifies two evaluations of [σ]. *)

Lemma rel_sub_under_ctx_wk : forall {Γ ψ Δ σ σ' Δ'},
    {{ Δ ⊨s σ ≈ σ' : Δ' }} ->
    {{ Γ ⊨w ψ : Δ }} ->
    {{ Γ ⊨s ^(sb_wk σ ψ) ≈ ^(sb_wk σ' ψ) : Δ' }}.
Proof.
  intros * [env_relΔ [HΔ [env_relΔ' [HΔ' Hσ]]]] [env_relΓ [HΓ [env_relΔ2 [HΔ2 Hψ]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ (rel_wk_compose Hφ Hψ) _ _ Hρ) as [a1 a2 ? a4 Ha1 Ha2 ? Ha4 Ha].
  destruct (Hσ _ _ HΓ _ Hψ _ _ (Hφ _ _ Hρ)) as [b1 b2 ? b4 Hb1 Hb2 ? Hb4 Hb].
  apply (mk_rel_sub a1 b1 b4 a4);
    [ rewrite sb_wk_wk; exact Ha1 | exact Hb1 | exact Hb4 | rewrite sb_wk_wk; exact Ha4 |].
  assert (Heq : env_eq a2 b2) by (eapply functional_eval_sub; eassumption).
  assert (Hlink : {{ Dom a2 ≈ b2 ∈ env_relΔ' }}) by (rewrite Heq; pairwise).
  assert (Hb' : rel_chain env_relΔ' [b2; b1; b4]) by solve_rel_chain.
  assert (Hc : rel_chain env_relΔ' [a2; b2; b1; b4])
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Hc Ha a2.
Qed.

(** *Pre*composition by a weakening, which — unlike the general composition of
    two semantic substitutions — *is* semantic.  Nothing has to be instantiated
    twice: the four environments wanted are the [⟦φ⟧w]-images of the four the
    hypothesis supplies, by [eval_sub_wk_pre] on the two inner ones and by the
    same lemma after [sb_wk_wk_pre] on the two outer ones.  The chain then
    transports member by member along [rel_chain_map], whose hypothesis is
    literally [rel_wk φ].

    That the general case fails is what forces the generic-recursor detour in the
    [ℕ]-elimination [β]-rule: [Γ'' ⊨s σ ⨟ τ : Γ] would need the value of
    [(σ x)[τ]] for every index [x], which is a statement about *terms* that the
    substitution judgment does not make. *)

Lemma rel_sub_under_ctx_wk_pre : forall {Γ Δ Δ' φ σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Δ ⊨w φ : Δ' }} ->
    {{ Γ ⊨s ^(ι φ) ⨟ σ ≈ ^(ι φ) ⨟ σ' : Δ' }}.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]] [env_relΔ2 [HΔ2 [env_relΔ' [HΔ' Hφ]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' ψ Hψ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hψ _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  pose proof (rel_chain_map _ _ (eval_wk φ) Hφ _ Hchain) as Hchain'.
  simpl in Hchain'.
  apply (mk_rel_sub d{{{ ⟦ φ ⟧w v1 }}} d{{{ ⟦ φ ⟧w v2 }}}
                    d{{{ ⟦ φ ⟧w v3 }}} d{{{ ⟦ φ ⟧w v4 }}});
    [ rewrite sb_wk_wk_pre | | | rewrite sb_wk_wk_pre |];
    try (apply eval_sub_wk_pre; eassumption).
  exact Hchain'.
Qed.

(** * Semantic Weakening of a Term Judgment

    A term judgment may be weakened along [Γ ⊨w φ : Δ].  Recall that the
    equation [⟦M⟨φ⟩⟧(ρ) = ⟦M⟧(⟦φ⟧w ρ)] fails — the two sides of the [λ]-case are
    different closures — so the two values must be *related* instead, and the
    only thing that relates them is the judgment about [M] itself, instantiated
    twice:

    - along [ι φ ⨟ τ] at [(ρ, ρ')], whose outer values are the goal's outer ones
      ([exp_sub_wk]: [M⟨φ⟩[τ]] is [M[ι φ ⨟ τ]]);
    - along [ι φ] at [(ρτ, ρ'τ')], whose outer values are the goal's *inner* ones
      ([exp_sub_of_wk]: [M[ι φ]] is [M⟨φ⟩]).

    Both are read at the *same* pair of inner environments, [⟦φ⟧w ρτ] and
    [⟦φ⟧w ρ'τ'] — the first because [eval_sub_wk_pre] names them, the second
    because [eval_sub_of_wk] does — so their inner values coincide on the nose
    and the two chains merge.  This is where the universal form of
    [rel_exp_under_ctx] pays
    off: with existential environments the two instantiations would have spoken
    about merely pointwise-equal environments, hence about unrelated closures. *)

Lemma rel_exp_under_ctx_wk : forall {Γ Δ φ A M M'},
    {{ Γ ⊨w φ : Δ }} ->
    {{ Δ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }}.
Proof.
  intros * Hφj HM.
  pose proof Hφj as [env_relΓ [HΓ [env_relΔ [HΔ Hφ]]]].
  pose proof HM as [env_relΔ2 [HΔ2 [i HMgen]]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' τ τ' Hτj ρ ρ' ρτ ρ'τ' Hρ Hev Hev'.
  assert (Hρτ : {{ Dom ρτ ≈ ρ'τ' ∈ env_relΓ }})
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
  assert (Hmid1 : {{ DF a2 ≈ a3 ∈ per_univ_elem i ↘ R1 }}) by pairwise.
  assert (Hmid2 : {{ DF a2 ≈ a3 ∈ per_univ_elem i ↘ R2 }}) by pairwise.
  handle_per_univ_elem_irrel.
  exists R1.
  split.
  - apply (mk_rel_exp a1 b1 b4 a4); try eassumption.
    merge_rel_chain Hty1 Hty2 a2.
  - apply (mk_rel_exp v1 w1 w4 v4); try eassumption.
    merge_rel_chain Hc1 Hc2 v2.
Qed.

(** The form soundness's variable case consumes: the failing equation
    [⟦M⟨φ⟩⟧(ρ) = ⟦M⟧(⟦φ⟧w ρ)] as a *relatedness*.  This is [rel_exp_under_ctx]
    at [ι φ],
    where both commutation obligations vanish ([exp_sub_of_wk]) and
    [eval_sub_of_wk] names both inner environments, so the wanted pair — an outer
    value against the opposite inner one — is one [pairwise] away. *)
Lemma rel_exp_under_ctx_wk_simple : forall {Γ Δ φ A M M'},
    {{ Γ ⊨w φ : Δ }} ->
    {{ Δ ⊨ M ≈ M' : A }} ->
    exists env_relΓ (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }}) i,
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_relΓ }} ->
      exists a a' R,
        {{ ⟦ A⟨φ⟩ ⟧ ρ ↘ a }} /\
        {{ ⟦ A ⟧ ⟦ φ ⟧w ρ' ↘ a' }} /\
        {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} /\
        exists m m',
          {{ ⟦ M⟨φ⟩ ⟧ ρ ↘ m }} /\
          {{ ⟦ M' ⟧ ⟦ φ ⟧w ρ' ↘ m' }} /\
          {{ Dom m ≈ m' ∈ R }}.
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
  assert (Hmid : {{ DF a1 ≈ a3 ∈ per_univ_elem i ↘ R }}) by pairwise.
  exists a1, a3, R.
  repeat split; try eassumption.
  exists v1, v3.
  repeat split; try eassumption.
  pairwise.
Qed.

(** * Precomposition by [⇑]

    Nothing is instantiated twice here: the four values of the hypothesis are
    *already* the four values wanted, once each is dropped.  Two facts do the
    work, and both are the [⇑] case of something that fails in general:

    - [eval_sub_shift_pre] — [⟦⇑ ⨟ σ⟧(ρ)] is [⟦σ⟧(ρ)↯], because [⇑] substitutes
      only variables (and [sb_wk_shift_pre] says postcomposing by [φ] slides
      past, so the same holds of the two [φ]-weakened values);
    - [rel_wk_shift_tail] — the Ctx-Ext biconditional, which is exactly the
      statement that dropping takes [R_{Δ,A}] to [R_Δ].

    The second is a [rel_wk], i.e. precisely the hypothesis of [rel_chain_map],
    so the chain transports along the drop member by member. *)

Lemma rel_sub_under_ctx_shift : forall {Γ Δ A σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ, A }} ->
    {{ Γ ⊨s Wk ⨟ σ ≈ Wk ⨟ σ' : Δ }}.
Proof.
  intros * [env_relΓ [HΓ [env_relΔA [HΔA Hσ]]]].
  pose proof (rel_wk_shift_tail HΔA) as [env_relΔ [HΔ Hdrop]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  pose proof (rel_chain_map _ _ drop_env Hdrop _ Hchain) as Hchain'.
  simpl in Hchain'.
  apply (mk_rel_sub d{{{ v1 ↯ }}} d{{{ v2 ↯ }}} d{{{ v3 ↯ }}} d{{{ v4 ↯ }}});
    [ rewrite sb_wk_shift_pre | | | rewrite sb_wk_shift_pre |];
    try (apply eval_sub_shift_pre; eassumption).
  exact Hchain'.
Qed.

(** * Symmetry

    The four values of the symmetric judgment are the *same* four in the
    opposite order, so symmetry is [rel_chain_4_sym] and nothing else. *)

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
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ : Δ }}.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  apply rel_sub_sym; [ solve_chain_PER |].
  apply (Hσ _ _ HΓ' _ Hφ).
  symmetry; eassumption.
Qed.

(** Instantiate the hypothesis at the swapped substitution pair and
    the swapped environment pair; both of its chains then come out reversed, and
    reversing them again is [rel_exp_sym].  The universal form of
    [rel_exp_under_ctx] is
    what makes the swap legal at all: the caller's two evaluations serve, read in
    the other order. *)
Lemma rel_exp_under_ctx_sym : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' ≈ M : A }}.
Proof.
  intros * [env_relΓ [HΓ [i HM]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : {{ Dom ρ' ≈ ρ ∈ env_rel' }}) by (symmetry; eassumption).
  destruct (HM _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ _ _ _ Hρ' Hev' Hev)
    as [R [Htyp Hexp]].
  exists R.
  split; apply rel_exp_sym;
    first [ eassumption | solve_chain_PER | eauto using rel_typ_elem_PER ].
Qed.

(** * Transitivity

    Two four-value chains, and the value they share is the one both sides
    evaluate [σ2[φ]] to.  It is shared only up to [env_eq]
    ([functional_eval_sub] pins an evaluated substitution down no further), which
    is why this needs [per_ctx_env_resp_env_eq]; with that link prefixed, the two
    chains genuinely overlap and [rel_chain_merge] joins them into one, from
    which [rel_chain_incl] selects the four values wanted. *)

Lemma rel_sub_under_ctx_trans : forall {Γ Δ σ1 σ2 σ3},
    {{ Γ ⊨s σ1 ≈ σ2 : Δ }} ->
    {{ Γ ⊨s σ2 ≈ σ3 : Δ }} ->
    {{ Γ ⊨s σ1 ≈ σ3 : Δ }}.
Proof.
  intros * [env_relΓ [HΓ [env_relΔ [HΔ H12]]]] H23'.
  pose proof H23' as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 H23]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  assert (Hρ' : {{ Dom ρ' ≈ ρ' ∈ env_rel' }})
    by (etransitivity; [ symmetry | ]; eassumption).
  destruct (H12 _ _ HΓ' _ Hφ _ _ Hρ) as [ρσ1φ ρσ1 ρ'σ2 ρ'σ2φ ? ? ? Hev2 Ha].
  destruct (H23 _ _ HΓ' _ Hφ _ _ Hρ') as [ρ'σ2φb ρ'σ2b ρ'σ3 ρ'σ3φ Hev2b ? ? ? Hb].
  econstructor; try eassumption.
  assert (Heq : env_eq ρ'σ2φ ρ'σ2φb) by (eapply functional_eval_sub; eassumption).
  assert (Hlink : {{ Dom ρ'σ2φ ≈ ρ'σ2φb ∈ env_relΔ }}) by (rewrite Heq; pairwise).
  assert (Hc : rel_chain env_relΔ [ρ'σ2φ; ρ'σ2φb; ρ'σ2b; ρ'σ3; ρ'σ3φ])
    by (apply rel_chain_cons; assumption).
  merge_rel_chain Ha Hc ρ'σ2φ.
Qed.

(** The reflexive instances of a substitution judgment.  The substitution cases
    and [rel_exp_under_ctx_trans]
    both need to instantiate a second judgment at *one* side of a given
    substitution pair; symmetry and transitivity supply them. *)

Corollary rel_sub_under_ctx_refl_left : forall {Γ Δ σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ : Δ }}.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

Corollary rel_sub_under_ctx_refl_right : forall {Γ Δ σ σ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' : Δ }}.
Proof.
  intros * H.
  pose proof (rel_sub_under_ctx_sym H).
  eapply rel_sub_under_ctx_trans; eassumption.
Qed.

(** Two four-value chains again, but this time the shared values are
    shared *on the nose*: the second judgment is instantiated at the reflexive
    right-hand substitution [σ'] and the reflexive right-hand environment pair
    [ρ' ≈ ρ'] — with the caller's own [ρ'σ'] named on both sides — so its first
    two values are literally [⟦M2[σ']⟧(ρ')] and [⟦M2⟧(ρ'σ')], which are the last
    two of the first chain.  Under the existential form of [rel_exp_under_ctx]
    they would
    only have been [env_eq]-related environments, hence merely *some* pair of
    values of [M2], and nothing would join.

    The two element PERs are identified through the type chains, which overlap in
    [⟦A⟧(ρ'σ')] — cross-level irrelevance, so the two judgments' universe levels
    need not agree. *)

Lemma rel_exp_under_ctx_trans : forall {Γ A M1 M2 M3},
    {{ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ Γ ⊨ M1 ≈ M3 : A }}.
Proof.
  intros * [env_relΓ [HΓ [i H12]]] H23'.
  pose proof H23' as [env_relΓ2 [HΓ2 [j H23]]].
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρ' : {{ Dom ρ' ≈ ρ' ∈ env_rel' }})
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

(** The term-level reflexive instances.  The substitution cases need one: it
    bridges the
    values of a term at two different environments, and the bridge is that same
    term judgment taken reflexively. *)

Corollary rel_exp_under_ctx_refl_left : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M : A }}.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.

Corollary rel_exp_under_ctx_refl_right : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' : A }}.
Proof.
  intros * H.
  pose proof (rel_exp_under_ctx_sym H).
  eapply rel_exp_under_ctx_trans; eassumption.
Qed.
