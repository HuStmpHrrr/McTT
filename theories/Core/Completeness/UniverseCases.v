(** * The Universe

    Two of the typing rules mention the universe directly ([wf_typ] and
    [wf_exp_eq_typ_cong]), and cumulativity ([rel_exp_cumu]) is what lets any two
    type judgments be brought to a common level.  The old [rel_exp_typ_sub] is
    gone: [Type@i[σ]] *is* [Type@i], since [exp_sub] computes on a constructor
    that binds nothing, so the rule it validated no longer exists.

    Everything here is organised around the pair [rel_exp_of_typ_inversion] /
    [rel_exp_of_typ], which are exact converses.  They say that a judgment
    [Γ ⊨ A ≈ A' : Type@i] is nothing more than the four-value pattern of [A] and
    [A'] in [per_univ i]: the type chain of [rel_exp_under_ctx] is forced (all
    four of its values are [𝕌@i], since substitution does not touch [Type@i]), and
    it pins the
    element PER down to [per_univ i].  So the universe is the one place where the
    two chains of a term judgment decouple, and stripping the trivial one is what
    makes the type-level lemmas of the following files readable. *)

From Stdlib Require Import Lia List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations.
Import Wk_Notations.

Lemma rel_exp_of_typ_inversion : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    forall Γ' env_rel' (_ : {{ EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' }}) σ σ',
      {{ Γ' ⊨s σ ≈ σ' : Γ }} ->
      forall ρ ρ' ρσ ρ'σ',
        {{ Dom ρ ≈ ρ' ∈ env_rel' }} ->
        {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
        {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof.
  intros * [env_relΓ [HΓ [j HA]]].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  (** The type chain is a chain of universes, so inverting it identifies [R]
      with [per_univ i] — and then [Hexp] already is the goal. *)
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  invert_rel_typ_body.
  eassumption.
Qed.

(** The instance of the above at [Id], as [rel_exp_under_ctx_simple] is the
    instance of a general judgment at [Id].  This is the form a *context* PER
    wants, because
    [per_ctx_env_cons] asks for the evaluations of [A] and [A'] in the
    environments themselves and not in some substituted pair — and at [Id] they
    coincide, since [Id] evaluates to the environment itself and [A[Id]] is
    [A].  So the whole chain collapses onto its middle link. *)
Corollary rel_exp_of_typ_inversion_simple : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_rel }} ->
      exists a a',
        {{ ⟦ A ⟧ ρ ↘ a }} /\
        {{ ⟦ A' ⟧ ρ' ↘ a' }} /\
        {{ Dom a ≈ a' ∈ per_univ i }}.
Proof.
  intros * H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a' a'σ' HaσI ? ? Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; try eassumption.
  pairwise.
Qed.

(** The same instance at a weakening instead of at [Id], which is what the gluing
    model needs: it reads a type's value at [ρ] after [⟨φ⟩], while the context
    relation it recurses on supplies the value at [⟦φ⟧w ρ].  The two are not
    equal, and [per_univ i] is what relates them. *)
Corollary rel_exp_of_typ_inversion_wk : forall {Γ Δ φ A A' i},
    {{ Γ ⊨w φ : Δ }} ->
    {{ Δ ⊨ A ≈ A' : Type@i }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    forall ρ ρ',
      {{ Dom ρ ≈ ρ' ∈ env_rel }} ->
      exists a a',
        {{ ⟦ A⟨φ⟩ ⟧ ρ ↘ a }} /\
        {{ ⟦ A' ⟧ ⟦ φ ⟧w ρ' ↘ a' }} /\
        {{ Dom a ≈ a' ∈ per_univ i }}.
Proof.
  intros * Hφ H%rel_exp_of_typ_inversion.
  destruct H as [env_relΔ [HΔ HA]].
  pose proof Hφ as [env_relΓ [HΓ [env_relΔ2 [HΔ2 _]]]].
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  destruct (HA _ _ HΓ _ _ (rel_sub_of_wk Hφ) _ _ _ _ Hρ
              (eval_sub_of_wk _ _) (eval_sub_of_wk _ _))
    as [a1 a2 a3 a4 Ha1 ? Ha3 ? Hchain].
  rewrite exp_sub_of_wk in Ha1.
  exists a1, a3.
  repeat split; try eassumption.
  pairwise.
Qed.

(** [per_head_resp] in the form a type *judgment* supplies its premises in: the
    four values it asks for are four instances of the judgment, and what selects
    the pairs to instantiate at is a chain of environments.

    Every rule with a premise in an extended context needs this, because the
    environments [q σ] evaluates to are related to the ones the goal names without
    being equal to them, so a head PER read at the former has to be moved
    to the latter.  Stated over an arbitrary context PER rather than at the shape
    of one particular extension, since the movement happens at each level of a
    nested [q]. *)
Lemma per_head_of_typ_resp : forall {Γ A A' i env_relΓ},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain env_relΓ [ρ1; ρ2; ρ3; ρ4] ->
      per_head A A' ρ1 ρ2 <~> per_head A A' ρ3 ρ4.
Proof.
  intros * HΓ HA * Hchain.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ2 [HΓ2 HAsimple]].
  handle_per_ctx_env_irrel.
  assert (H12 : {{ Dom ρ1 ≈ ρ2 ∈ env_relΓ }}) by pairwise.
  assert (H32 : {{ Dom ρ3 ≈ ρ2 ∈ env_relΓ }}) by pairwise.
  assert (H34 : {{ Dom ρ3 ≈ ρ4 ∈ env_relΓ }}) by pairwise.
  destruct (HAsimple _ _ H12) as [a1 [a2 [Ha1 [Ha2 Ha12]]]].
  destruct (HAsimple _ _ H32) as [a3 [a2' [Ha3 [Ha2' Ha32]]]].
  destruct (HAsimple _ _ H34) as [a3' [a4 [Ha3' [Ha4 Ha34]]]].
  (** The middle link runs the *wrong way*: [A] is on the left of the judgment and
      [A'] on the right, so the only instance whose values are [⟦A'⟧ρ2] and
      [⟦A⟧ρ3] is the one at [(ρ3, ρ2)]. *)
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 |].
  apply rel_chain_4; [ exact Ha12 | symmetry; exact Ha32 | exact Ha34 ].
Qed.

(** The shape a caller of the above always wants it in: a member of the extended
    context PER of [Γ, A] whose *head* pair was read at some other pair of tails
    than the one the goal names.  Every eliminator's premises are in that
    position, because the head pair they have comes from a domain PER or from
    [per_nat] and is stated at the environments the [q] of the rule reached, not at
    the ones the goal does. *)
Corollary per_env_extend_move : forall {Γ A i env_relΓ},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨ A ≈ A : Type@i }} ->
    forall ρ1 ρ2 ρ3 ρ4 c c',
      rel_chain env_relΓ [ρ1; ρ2; ρ3; ρ4] ->
      {{ Dom c ≈ c' ∈ per_head A A ρ1 ρ2 }} ->
      {{ Dom ρ3 ↦ c ≈ ρ4 ↦ c' ∈ per_env_extend A A env_relΓ }}.
Proof.
  intros * HΓ HA * Hchain Hc.
  apply per_env_extend_intro'; [ pairwise |].
  apply (per_head_of_typ_resp HΓ HA _ _ _ _ Hchain); exact Hc.
Qed.

Lemma rel_exp_of_typ : forall {Γ A A' i},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
      forall Γ' env_rel' (_ : {{ EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' }}) σ σ',
        {{ Γ' ⊨s σ ≈ σ' : Γ }} ->
        forall ρ ρ' ρσ ρ'σ',
          {{ Dom ρ ≈ ρ' ∈ env_rel' }} ->
          {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
          {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i)) ->
    {{ Γ ⊨ A ≈ A' : Type@i }}.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (S i).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_univ i).
  split; [| eapply H; eassumption].
  assert (Hu : per_univ_elem (S i) (per_univ i) d{{{ 𝕌@i }}} d{{{ 𝕌@i }}})
    by (apply per_univ_elem_core_univ'; [ lia | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

#[export]
Hint Resolve rel_exp_of_typ : mctt.

(** The semantic presupposition: a term judgment carries a type judgment inside
    it, namely its own type chain, which lives in [per_univ_elem i elem_rel] and
    so — forgetting the element PER — in [per_univ i].  This is the semantic
    counterpart of [presup_exp_eq], and it is what lets the substitution cases build
    the context PER of [Δ, T] from a judgment about a *term* of [T]. *)
Corollary presup_rel_exp_under_ctx : forall {Γ A M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists i, {{ Γ ⊨ A ≈ A : Type@i }}.
Proof.
  intros * [env_relΓ [HΓ [i HM]]].
  exists i.
  apply rel_exp_of_typ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HM _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp _]].
  eapply rel_typ_implies_rel_exp; eassumption.
Qed.

Ltac eexists_rel_exp_of_typ :=
  apply rel_exp_of_typ;
  eexists;
  eexists; [eassumption |].

Lemma valid_exp_typ : forall {i Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ Type@i : Type@(S i) }}.
Proof.
  intros * H.
  pose proof (sem_ctx_per_ctx_env H) as [env_relΓ HΓ].
  eexists_rel_exp_of_typ.
  (** [Type@i] ignores every environment, so the two substituted ones — which
      the caller now names — are not used at all. *)
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hu : per_univ (S i) d{{{ 𝕌@i }}} d{{{ 𝕌@i }}})
    by (eexists; apply per_univ_elem_core_univ'; [ lia | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

#[export]
Hint Resolve valid_exp_typ : mctt.

(** Cumulativity acts on the chain member by member, which is [rel_chain_mono]
    at [per_univ_elem_cumu]. *)
Lemma rel_exp_cumu : forall {i Γ A A'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@(S i) }}.
Proof.
  intros * H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [? ? ? ? ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros ? ? [R HR]; exists R; now apply per_univ_elem_cumu.
Qed.

#[export]
Hint Resolve rel_exp_cumu : mctt.

(** Iterated, which is how a Π-type reconciles the level of its domain with that
    of its codomain: [per_univ_elem_pi_canonical] insists the two agree, while the
    syntax lets [A] and [B] be typed at unrelated levels. *)
Corollary rel_exp_cumu_ge : forall {i j Γ A A'},
    i <= j ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@j }}.
Proof.
  induction 1; eauto using rel_exp_cumu.
Qed.

#[export]
Hint Resolve rel_exp_cumu_ge : mctt.
