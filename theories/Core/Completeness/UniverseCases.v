(** * The Universe

    The rules that mention the universe directly ([wf_typ] and
    [wf_exp_eq_typ_cong]), and cumulativity ([rel_exp_cumu]), which brings any two
    type judgments to a common level.  [Typeω@i[σ]] is [Typeω@i] because [exp_sub]
    computes on it, so the universe has no substitution rule.

    The file is organised around the converse pair [rel_exp_of_typ_inversion] /
    [rel_exp_of_typ]: the relation [Γ ⊨ A ≈ A' : Typeω@i] is exactly the four-value
    pattern of [A] and [A'] in [per_univ i].  The type chain of [rel_exp_under_ctx]
    is forced (all four of its values are [𝕌ω@i]) and fixes the element PER to
    [per_univ i].  So the universe is where the two chains of a term judgment
    decouple, and stripping the trivial one keeps the type-level lemmas of the
    later files readable. *)

From Stdlib Require Import Lia List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The relevant pairs of a PER form a PER. *)
#[export] Instance per_relevant_PER {R : relation domain} `{HR : PER domain R} : PER (per_relevant R).
Proof.
  split.
  - intros a b [Hab Ha Hb]; constructor; [ symmetry; exact Hab | exact Hb | exact Ha ].
  - intros a b c [Hab Ha _] [Hbc _ Hc]; constructor; [ etransitivity; eassumption | exact Ha | exact Hc ].
Qed.

(** The elements of a universe are its relevant types: a related pair of
    them is a related pair of types. *)
Lemma per_relevant_univ_rel : forall {u a a'}, Dom a ≈ a' ∈ per_relevant (per_univ u) -> Dom a ≈ a' ∈ per_univ u.
Proof. intros * []; assumption. Qed.

(** A sort is closed: weakening leaves it unchanged. *)
Lemma type_sort_wk : forall {S} φ, type_sort S -> S[φ]ʷ = S.
Proof. intros * []; reflexivity. Qed.

(** The same for a chain. *)
Corollary rel_chain_relevant_univ : forall {u l},
    rel_chain (per_relevant (per_univ u)) l -> rel_chain (per_univ u) l.
Proof. intros u; apply rel_chain_mono; intros; apply per_relevant_univ_rel; assumption. Qed.

(** A chain of types of a universe is a chain of relevant types once one of
    its values is relevant: related types are of one sort. *)
Lemma rel_exp_univ_relevant : forall {A σ ρ ρσ A' σ' ρ' ρ'σ' u},
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ u) ->
    (forall a, ⟦ A[σ] ⟧ ρ ↘ a -> domain_relevance a = relevant) ->
    rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant (per_univ u)).
Proof.
  intros * [a1 a2 a3 a4 E1 E2 E3 E4 Hc] Hr.
  pose proof (Hr _ E1) as Hr1.
  econstructor; try eassumption.
  assert (H12 : Dom a1 ≈ a2 ∈ per_univ u) by pairwise.
  assert (H23 : Dom a2 ≈ a3 ∈ per_univ u) by pairwise.
  assert (H34 : Dom a3 ≈ a4 ∈ per_univ u) by pairwise.
  destruct H12 as [? H12'], H23 as [? H23'], H34 as [? H34'].
  pose proof (per_univ_elem_relevance _ _ _ _ H12').
  pose proof (per_univ_elem_relevance _ _ _ _ H23').
  pose proof (per_univ_elem_relevance _ _ _ _ H34').
  apply rel_chain_4; constructor; first [ eexists; eassumption | congruence ].
Qed.

Lemma rel_exp_of_univ_inversion : forall {Γ A A' u},
    Γ ⊨ A ≈ A' : universe_index_term u ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant (per_univ u)).
Proof.
  intros * [env_relΓ HΓ j HA].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  (** The type is a universe, a relevant type: the term is related. *)
  destruct Hexp as [(? & ? & Hp) | Hexp]; [ destruct u; cbn [universe_index_term] in *; simplify_evals; discriminate Hp |].
  destruct u; cbn [universe_index_term] in *; invert_rel_typ_body; eassumption.
Qed.

Corollary rel_exp_of_univ_inversion_simple : forall {Γ A A' u},
    Γ ⊨ A ≈ A' : universe_index_term u ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ u.
Proof.
  intros * H%rel_exp_of_univ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ Hid Hid')
    as [aσ a a' a'σ' HaσI ? ? Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; try eassumption.
  apply per_relevant_univ_rel; pairwise.
Qed.

Lemma rel_exp_of_univ : forall {Γ A A' u},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant (per_univ u))) ->
    Γ ⊨ A ≈ A' : universe_index_term u.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (large_level_above u).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_relevant (per_univ u)).
  split; [| right; eapply H; eassumption].
  pose proof (per_univ_elem_universe_index_value u _ (universe_index_lt_large_level_above u)) as Hu.
  destruct u; econstructor; try apply (eval_universe_index_term _ _ (us _)); try apply (eval_universe_index_term _ _ (ul _));
    apply rel_chain_4; assumption.
Qed.

(** Cumulativity across the tiers, in particular from a small universe to
    every large one. *)
Lemma rel_exp_under_ctx_univ_cumu : forall {Γ A A' u v},
    universe_index_le u v ->
    Γ ⊨ A ≈ A' : universe_index_term u ->
    Γ ⊨ A ≈ A' : universe_index_term v.
Proof.
  intros * Huv H%rel_exp_of_univ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  apply rel_exp_of_univ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [? ? ? ? ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros ? ? [[R HR] Hl Hr]; constructor; [ exists R; eapply per_univ_elem_cumu_universe_index; eassumption | assumption | assumption ].
Qed.

Corollary rel_exp_under_ctx_small_large : forall {Γ A A' n} {i : nat},
    Γ ⊨ A ≈ A' : Type⟨𝕃ᵒ n⟩ ->
    Γ ⊨ A ≈ A' : Typeω@i.
Proof. intros * H; exact (rel_exp_under_ctx_univ_cumu (u := us n) (v := ul i) I H). Qed.

Lemma valid_exp_under_ctx_univ : forall {a n Γ},
    ⊨ Γ ->
    Γ ⊨ Type⟨𝕃ᵒ(a, n)⟩ : Type⟨𝕃ᵒ(a, S n)⟩.
Proof.
  intros * H.
  pose proof (rel_ctx_wf_per_ctx_env H) as [env_relΓ HΓ].
  apply (rel_exp_of_univ (u := us (a, S n))).
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hu : per_relevant (per_univ (us (a, S n))) 𝕌@(domain_level_lit (a, n)) 𝕌@(domain_level_lit (a, n)))
    by (constructor; [| reflexivity | reflexivity ];
        eexists; apply per_univ_elem_core_suniv';
        [ apply per_lvl_lit | cbn; ordinal_solve | reflexivity ]).
  econstructor; try (apply eval_exp_univ, eval_exp_llit).
  apply rel_chain_4; assumption.
Qed.

Lemma rel_exp_of_typ_inversion : forall {Γ A A'} {i : nat},
    Γ ⊨ A ≈ A' : Typeω@i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant (per_univ i)).
Proof.
  intros * [env_relΓ HΓ j HA].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  (** The type chain is a chain of universes, so inverting it identifies [R]
    with the relevant types of [per_univ i], and then [Hexp] is the goal:
    a universe is no proposition. *)
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  destruct Hexp as [(? & ? & Hp) | Hexp]; [ simplify_evals; discriminate Hp |].
  invert_rel_typ_body.
  eassumption.
Qed.

(** A type of a universe, or a proposition, is a type of an index. *)
Lemma rel_type_of_typ : forall {Γ A A'} {i : nat},
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  econstructor; [ exact HΓ |].
  intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| exact Hc ]; intros ? ? []; assumption.
Qed.

(** The instance of the above at [Id].  This is the form a context PER needs:
    [per_ctx_env_cons] asks for the values of [A] and [A'] in the environments
    themselves, and at [Id] these coincide with the substituted ones, since [Id]
    evaluates to the environment itself and [A[Id]] is [A].  The chain collapses
    onto its middle link. *)
(** The judgment taken apart, in the form [rel_exp_of_typ_inversion] has. *)
Lemma rel_type_inversion : forall {Γ A A'} {i : nat},
    Γ ⊨ᵗ A ≈ A' at i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof. intros * [env_relΓ HΓ HA]; exists env_relΓ, HΓ; exact HA. Qed.

(** And put together. *)
Lemma rel_type_intro : forall {Γ A A'} {i : nat},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i)) ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof. intros * [env_relΓ [HΓ HA]]; econstructor; [ exact HΓ | exact HA ]. Qed.

Lemma rel_type_inversion_simple : forall {Γ A A'} {i : nat},
    Γ ⊨ᵗ A ≈ A' at i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * [env_relΓ HΓ HA].
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ Hid Hid')
    as [aσ a a' a'σ' HaσI ? ? Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; try eassumption.
  pairwise.
Qed.

Corollary rel_exp_of_typ_inversion_simple : forall {Γ A A'} {i : nat},
    Γ ⊨ A ≈ A' : Typeω@i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ i.
Proof. intros * H; exact (rel_type_inversion_simple (rel_type_of_typ H)). Qed.

(** The same at any context PER of [Γ]. *)
Corollary rel_type_inversion_simple_at : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A' at i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HΓ H.
  pose proof (rel_type_inversion_simple H) as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  exact (HA _ _ Hρ).
Qed.

Corollary rel_exp_of_typ_inversion_simple_at : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof. intros * HΓ H; exact (rel_type_inversion_simple_at HΓ (rel_type_of_typ H)). Qed.

(** A type of a universe is relevant at every environment of the
    context. *)
Corollary rel_exp_of_typ_relevant_at : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A ρ relevant.
Proof.
  intros * HΓ H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  destruct (eval_sub_id_rel HΓ' Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ' _ _ (rel_sub_id (ex_intro _ _ HΓ')) _ _ _ _ Hρ Hid Hid')
    as [aσ a a' a'σ' HaσI Ha Ha' Ha'σ'I Hchain].
  assert (Hr : Dom a ≈ a' ∈ per_relevant (per_univ i)) by pairwise.
  exists a; split; [ exact Ha | exact (per_relevant_left _ _ _ Hr) ].
Qed.

(** A type of a universe is no proposition at an environment a context PER
    relates. *)
Corollary not_rel_typ_propositional_of_typ : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> ~ rel_typ_propositional A ρ.
Proof.
  intros * HΓ HA ρ ρ' Hρ (a & Ea & Hp).
  destruct (rel_exp_of_typ_relevant_at HΓ (rel_exp_under_ctx_refl_left HA) _ _ Hρ) as (a0 & Ea0 & Hr).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  congruence.
Qed.

(** So an entry of a type of a universe is no proposition, at either
    environment of a related pair. *)
Corollary head_not_propositional_of_typ : forall {Γ e A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    ctx_entry_type (e :: nil) 0 = Some A ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
      ~ head_propositional gc_deps gc_stack e Γ ρ /\ ~ head_propositional gc_deps gc_stack e Γ ρ'.
Proof.
  intros * HΓ He HA ρ ρ' Hρ.
  pose proof (rel_exp_of_typ_relevant_at HΓ (rel_exp_under_ctx_refl_left HA)) as HArel.
  assert (HAs : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ ->
                  exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i).
  { pose proof (rel_type_inversion_simple (rel_type_of_typ (rel_exp_under_ctx_refl_left HA))) as [env_relΓ5 [HΓ5 HAs]].
    assert (E5 : env_relΓ <~> env_relΓ5) by (eapply per_ctx_env_right_irrel; eassumption).
    intros ρ1 ρ1' Hρ1%E5; exact (HAs _ _ Hρ1). }
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  assert (Hnp : forall ρ1 ρ1', Dom ρ1 ≈ ρ1' ∈ env_relΓ -> ~ head_propositional gc_deps gc_stack e Γ ρ1).
  { intros ρ1 ρ1' Hρ1 Hp.
    destruct (HArel _ _ Hρ1) as (a0 & Ea0 & Er0).
    apply (head_propositional_iff HΓ He HAs Hρ1 Ea0) in Hp; congruence. }
  split; [ exact (Hnp _ _ Hρ) | apply (Hnp ρ' ρ'); etransitivity; [ symmetry |]; exact Hρ ].
Qed.

(** The same instance at a weakening instead of [Id], as the gluing model needs:
    it reads a type's value at [ρ] after [[φ]ʷ], while the context relation
    supplies the value at [⟪φ⟫ ρ].  The two values are not equal; [per_univ i]
    relates them. *)
Corollary rel_type_inversion_wk : forall {Γ Δ φ A A'} {i : nat},
    Γ ⊨ʷ φ : Δ ->
    Δ ⊨ᵗ A ≈ A' at i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A[φ]ʷ ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ⟪φ⟫ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * Hφ [env_relΔ HΔ HA].
  pose proof Hφ as [env_relΓ HΓ env_relΔ2 HΔ2 Hφw _].
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  pose proof (rel_wk_mono _ _ _ Hφw) as Hφm.
  assert (Hρ' : Dom ρ' ≈ ρ ∈ env_relΓ) by (symmetry; exact Hρ).
  destruct (HA _ _ HΓ _ _ (rel_sub_of_wk Hφ) _ _ _ _ Hρ
              ltac:(eval_wk_at (Hφw _ _ Hρ)) ltac:(eval_wk_at (Hφw _ _ Hρ')))
    as [a1 a2 a3 a4 Ha1 ? Ha3 ? Hchain].
  rewrite exp_sub_of_wk in Ha1.
  exists a1, a3.
  repeat split; try eassumption.
  pairwise.
Qed.

Corollary rel_exp_of_typ_inversion_wk : forall {Γ Δ φ A A'} {i : nat},
    Γ ⊨ʷ φ : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A[φ]ʷ ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ⟪φ⟫ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ i.
Proof. intros * Hφ H; exact (rel_type_inversion_wk Hφ (rel_type_of_typ H)). Qed.

(** [per_head_resp] in the form a type judgment supplies its premises: the four
    values it asks for are four instances of the judgment, at pairs selected by a
    chain of environments.

    Every rule with a premise in an extended context needs this, because the
    environments [q σ] evaluates to are related to, but not equal to, the ones the
    goal names, so a head PER read at the former must be moved to the latter.  It
    is stated over an arbitrary context PER because the move happens at each level
    of a nested [q]. *)
Lemma per_head_of_type_resp : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A' at i ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain env_relΓ ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head A A' ρ1 ρ2 <~> per_head A A' ρ3 ρ4.
Proof.
  intros * HΓ HA * Hchain.
  pose proof (rel_type_inversion_simple HA) as [env_relΓ2 [HΓ2 HAsimple]].
  handle_per_ctx_env_irrel.
  assert (H12 : Dom ρ1 ≈ ρ2 ∈ env_relΓ) by pairwise.
  assert (H32 : Dom ρ3 ≈ ρ2 ∈ env_relΓ) by pairwise.
  assert (H34 : Dom ρ3 ≈ ρ4 ∈ env_relΓ) by pairwise.
  destruct (HAsimple _ _ H12) as [a1 [a2 [Ha1 [Ha2 Ha12]]]].
  destruct (HAsimple _ _ H32) as [a3 [a2' [Ha3 [Ha2' Ha32]]]].
  destruct (HAsimple _ _ H34) as [a3' [a4 [Ha3' [Ha4 Ha34]]]].
  (** The middle link runs the other way: [A] is on the left of the judgment and
    [A'] on the right, so the instance whose values are [⟦A'⟧ρ2] and [⟦A⟧ρ3] is
    the one at [(ρ3, ρ2)]. *)
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  eapply per_head_resp; [ exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 |].
  apply rel_chain_4; [ exact Ha12 | symmetry; exact Ha32 | exact Ha34 ].
Qed.

Corollary per_head_of_typ_resp : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain env_relΓ ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head A A' ρ1 ρ2 <~> per_head A A' ρ3 ρ4.
Proof. intros * HΓ HA; exact (per_head_of_type_resp HΓ (rel_type_of_typ HA)). Qed.

Lemma rel_exp_of_typ : forall {Γ A A'} {i : nat},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant (per_univ i))) ->
    Γ ⊨ A ≈ A' : Typeω@i.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (S i).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_relevant (per_univ i)).
  split; [| right; eapply H; eassumption].
  assert (Hu : per_univ_elem (S i) (per_relevant (per_univ i)) 𝕌ω@i 𝕌ω@i)
    by (apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ : mctt.

(** Semantic presupposition: a term judgment contains a type judgment, its own
    type chain, which lives in [per_univ_elem i elem_rel] and hence in
    [per_univ i].  This is the semantic counterpart of [presup_exp_eq]; the
    substitution cases use it to build the context PER of [Δ ▹ T] from a judgment
    about a term of [T].  The type is of either sort, so the judgment is the
    sort-blind [⊨ᵗ]. *)
Corollary presup_rel_exp_under_ctx : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    exists i, Γ ⊨ᵗ A ≈ A at i.
Proof.
  intros * [env_relΓ HΓ i HM].
  exists i.
  econstructor; [ exact HΓ |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HM _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp _]].
  eapply rel_typ_implies_rel_exp; eassumption.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve rel_exp_of_typ : mctt.
Ltac eexists_rel_exp_of_typ :=
  apply rel_exp_of_typ;
  eexists;
  eexists; [eassumption |].

#[local] Generalizable All Variables.

Lemma sem_typ :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i : Typeω@(S i) ).
Proof.
  intros * H; sem_intro; [ assumption |].
  pose proof (rel_ctx_wf_per_ctx_env H) as [env_relΓ HΓ].
  eexists_rel_exp_of_typ.
  (** [Typeω@i] ignores the environment, so the two substituted environments
    named by the caller are unused. *)
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hu : per_relevant (per_univ (S i)) 𝕌ω@i 𝕌ω@i)
    by (constructor; [| reflexivity | reflexivity ];
        eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

Lemma sem_exp_eq_typ_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i ≈ Typeω@i : Typeω@(S i) ).
Proof. intros; eapply sem_typ; eassumption. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Hint Resolve valid_exp_under_ctx_univ rel_exp_under_ctx_small_large : mctt.

(** Cumulativity acts on the chain member by member: [rel_chain_mono] at
    [per_univ_elem_cumu]. *)
Lemma rel_exp_cumu : forall {i : nat} {Γ A A'},
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ A ≈ A' : Typeω@(S i).
Proof.
  intros * H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [? ? ? ? ? ? ? ? Hchain].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption].
  intros ? ? [[R HR] Hl Hr]; constructor; [ exists R; now apply per_univ_elem_cumu | assumption | assumption ].
Qed.

Hint Resolve rel_exp_cumu : mctt.

(** Iterated cumulativity.  This is how a Π-type reconciles the levels of its
    domain and codomain: [per_univ_elem_pi_canonical] requires them to agree,
    while the syntax allows [A] and [B] at unrelated levels. *)
Corollary rel_exp_cumu_ge : forall {i : nat} {j Γ A A'},
    i <= j ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ A ≈ A' : Typeω@j.
Proof.
  induction 1; eauto using rel_exp_cumu.
Qed.

Hint Resolve rel_exp_cumu_ge : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve valid_exp_under_ctx_univ rel_exp_under_ctx_small_large : mctt.
#[export]
Hint Resolve rel_exp_cumu : mctt.
#[export]
Hint Resolve rel_exp_cumu_ge : mctt.

(** ** The Universes as Judgments *)

Lemma sem_is_univ_large :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Typeω@i ).
Proof. intros * H; sem_intro; [ assumption | left; eexists; reflexivity ]. Qed.

Lemma sem_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Type⟨L⟩ ).
Proof. intros * H; sem_intro; [ assumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ]. Qed.

(** ** [Prop]

    [Γ ⊨ A ≈ A' : Prop] is exactly the four-value pattern of [A] and [A']
    in [per_prop]: [Prop]'s elements are the propositions, which read back
    alike.  A proposition is a type of every index, its elements the
    proof. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [Prop] is a type of every positive index, its elements the
    propositions. *)
Lemma per_univ_elem_prop_univ : forall i, DF Propᵈ ≈ Propᵈ ∈ per_univ_elem i ↘ per_prop.
Proof. intros; basic_per_univ_elem_econstructor; reflexivity. Qed.

(** Related propositions are types of every index, of the proof. *)
Lemma per_univ_elem_of_prop : forall i a a', Dom a ≈ a' ∈ per_prop -> DF a ≈ a' ∈ per_univ_elem i ↘ per_proof.
Proof. intros * H; eapply per_univ_elem_core_prop; [ exact H | reflexivity ]. Qed.

Lemma rel_exp_of_prop_inversion : forall {Γ A A'},
    Γ ⊨ A ≈ A' : Propₘ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' per_prop.
Proof.
  intros * [env_relΓ HΓ j HA].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  destruct Hexp as [(? & ? & Hp) | Hexp]; [ simplify_evals; discriminate Hp |].
  invert_rel_typ_body.
  eassumption.
Qed.

Lemma rel_exp_of_prop : forall {Γ A A'},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' per_prop) ->
    Γ ⊨ A ≈ A' : Propₘ.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with 1.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists per_prop.
  split; [| right; eapply H; eassumption].
  pose proof (per_univ_elem_prop_univ 1) as Hu.
  econstructor; try apply eval_exp_prop.
  apply rel_chain_4; assumption.
Qed.

(** The instance at [Id], at any context PER of [Γ]. *)
Lemma rel_exp_of_prop_inversion_simple_at : forall {Γ A A' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Propₘ ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_prop.
Proof.
  intros * HΓ H%rel_exp_of_prop_inversion.
  destruct H as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  destruct (eval_sub_id_rel HΓ' Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ' _ _ (rel_sub_id (ex_intro _ _ HΓ')) _ _ _ _ Hρ Hid Hid')
    as [aσ a a' a'σ' HaσI Ha Ha' Ha'σ'I Hchain].
  exists a, a'.
  split; [ exact Ha | split; [ exact Ha' | pairwise ] ].
Qed.

(** The same for a proposition moved along a semantic substitution, at
    any related pair of environments of its domain. *)
Lemma rel_exp_of_prop_sub_simple : forall {Γ Δ σ σ' A A' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Propₘ ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A[σ] ⟧ ρ ↘ a /\ ⟦ A'[σ] ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_prop.
Proof.
  intros * HΓ Hσj HA ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' _]]]].
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct (HAgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  exists a1, a4; split; [ exact Ha1 | split; [ exact Ha4 | pairwise ] ].
Qed.

(** A proposition is a type of every index. *)
Lemma rel_type_of_prop : forall {Γ A A'} (i : nat),
    Γ ⊨ A ≈ A' : Propₘ ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * H%rel_exp_of_prop_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  econstructor; [ exact HΓ |].
  intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| exact Hc ]; intros ? ? Hp; eexists; exact (per_univ_elem_of_prop _ _ _ Hp).
Qed.

(** A type of a universe, or a proposition, as its tag says, is of the
    tag's sort at every environment of the context. *)
Corollary rel_exp_of_relevance_sort_at : forall {Γ A A' r} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : relevance_sort r Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A ρ r.
Proof.
  intros * HΓ H ρ ρ' Hρ; destruct r; cbn [relevance_sort] in H.
  - exact (rel_exp_of_typ_relevant_at HΓ H _ _ Hρ).
  - destruct (rel_exp_of_prop_inversion_simple_at HΓ H _ _ Hρ) as (a & a' & Ea & _ & Hp).
    exists a; split; [ exact Ea | exact (per_prop_left _ _ Hp) ].
Qed.

(** So a type of a universe, or a proposition, as its tag says, is a type
    of the universe. *)
Corollary rel_type_of_relevance : forall {Γ A A' r} {i : nat},
    Γ ⊨ A ≈ A' : relevance_sort r Typeω@i ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof. intros * H; destruct r; [ exact (rel_type_of_typ H) | exact (rel_type_of_prop i H) ]. Qed.

(** A type of an index is a type of every larger one. *)
Lemma rel_type_cumu_ge : forall {Γ A A'} {i j : nat},
    i <= j ->
    Γ ⊨ᵗ A ≈ A' at i ->
    Γ ⊨ᵗ A ≈ A' at j.
Proof.
  intros * Hij [env_relΓ HΓ HA].
  econstructor; [ exact HΓ |].
  intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| exact Hc ]; intros ? ? [R HR]; exists R.
  eapply per_univ_elem_cumu_ge; [ exact Hij | exact HR ].
Qed.

(** A type of either sort is a type of an index. *)
Lemma rel_type_of_sort : forall {Γ A A' S},
    type_sort S ->
    Γ ⊨ A ≈ A' : S ->
    exists i, Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * [i | ] H; [ exists i; exact (rel_type_of_typ H) | exists 0; exact (rel_type_of_prop 0 H) ].
Qed.

(** A type keeps its sort along a semantic substitution: the value of
    [A[σ]] at an environment and the value of [A] at the substitution's
    value there have the same relevance. *)
Lemma rel_type_sub_relevance : forall {Γ Δ A S σ σ' R ρ ρ' ρσ a a'},
    type_sort S -> Δ ⊨ A : S -> Γ ⊨ˢ σ ≈ σ' : Δ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R ->
    ⟦ σ : Δ ⟧s ρ ↘ ρσ -> ⟦ A[σ] ⟧ ρ ↘ a -> ⟦ A ⟧ ρσ ↘ a' -> domain_relevance a = domain_relevance a'.
Proof.
  intros * HS HA Hσ HΓ Hρ Hev Ea Ea'.
  destruct (rel_type_of_sort HS HA) as [i [RΔ HΔ HAgen]].
  assert (HP : PER R) by (eapply per_env_PER; exact HΓ).
  assert (Hρρ : Dom ρ ≈ ρ ∈ R) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (HAgen _ _ HΓ _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρρ Hev Hev)
    as [a1 a2 a3 a4 E1 E2 E3 E4 ([R12 H12] & _)].
  functional_eval_rewrite_clear.
  exact (per_univ_elem_relevance _ _ _ _ H12).
Qed.

(** The same, at one index for all the types of the sort. *)
Lemma rel_type_of_sort_at : forall {S}, type_sort S ->
    exists i, forall Γ A A', Γ ⊨ A ≈ A' : S -> Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * [i | ]; [ exists i; intros; apply rel_type_of_typ; assumption | exists 0; intros; apply rel_type_of_prop; assumption ].
Qed.

(** The innermost parameter of relevant parameters is relevant, and the
    parameters before it are relevant over it. *)
Lemma rel_params_relevant_snoc_inv : forall Γ Δ A l,
    rel_params_relevant Γ (Δ ++ ce_ass A :: nil) l ->
    Γ ⊨ A : Typeω@l /\ rel_params_relevant (Γ ▹ A) Δ l.
Proof.
  intros * H; split; [ exact (H Δ A nil eq_refl) |].
  intros Δ1 B Δ2 ->.
  pose proof (H Δ1 B (Δ2 ++ ce_ass A :: nil) ltac:(rewrite <- app_assoc; reflexivity)) as HB.
  rewrite <- app_assoc in HB; exact HB.
Qed.

End Fixed_GCtx.
