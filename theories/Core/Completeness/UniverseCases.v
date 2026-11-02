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
#[export] Instance per_relevant_nonlevel_PER {R : relation domain} `{HR : PER domain R} : PER (per_relevant_nonlevel R).
Proof.
  split.
  - intros a b [Hab Ha Hb Hna Hnb]; constructor; [ symmetry; exact Hab | exact Hb | exact Ha | exact Hnb | exact Hna ].
  - intros a b c [Hab Ha _ Hna _] [Hbc _ Hc _ Hnc]; constructor;
      [ etransitivity; eassumption | exact Ha | exact Hc | exact Hna | exact Hnc ].
Qed.

(** The elements of a universe are its relevant types: a related pair of
    them is a related pair of types. *)
Lemma per_relevant_nonlevel_univ_rel : forall {u a a'}, Dom a ≈ a' ∈ per_relevant_nonlevel (per_univ u) -> Dom a ≈ a' ∈ per_univ u.
Proof. intros * []; assumption. Qed.

(** A sort is closed: weakening leaves it unchanged. *)
Lemma type_sort_wk : forall {S} φ, type_sort S -> S[φ]ʷ = S.
Proof. intros * []; reflexivity. Qed.

(** The same for a chain. *)
Corollary rel_chain_relevant_univ : forall {u l},
    rel_chain (per_relevant_nonlevel (per_univ u)) l -> rel_chain (per_univ u) l.
Proof. intros u; apply rel_chain_mono; intros; apply per_relevant_nonlevel_univ_rel; assumption. Qed.

Lemma rel_exp_of_univ_inversion : forall {Γ A A' u},
    Γ ⊨ A ≈ A' : universe_index_term u ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant_nonlevel (per_univ u)).
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
  exists aσ, a'σ'.
  repeat split; try eassumption.
  apply per_relevant_nonlevel_univ_rel; pairwise.
Qed.

Lemma rel_exp_of_univ : forall {Γ A A' u},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant_nonlevel (per_univ u))) ->
    Γ ⊨ A ≈ A' : universe_index_term u.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (large_level_above u).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_relevant_nonlevel (per_univ u)).
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
  intros ? ? [[R HR] Hl Hr Hnl Hnr]; constructor;
    [ exists R; eapply per_univ_elem_cumu_universe_index; eassumption | assumption .. ].
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
  assert (Hu : per_relevant_nonlevel (per_univ (us (a, S n))) 𝕌@(domain_level_lit (a, n)) 𝕌@(domain_level_lit (a, n)))
    by (constructor; [| reflexivity | reflexivity | solve_not_level_code | solve_not_level_code ];
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
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant_nonlevel (per_univ i)).
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
  exists aσ, a'σ'.
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
  rewrite exp_sub_id in HaσI.
  assert (Hr : Dom aσ ≈ a ∈ per_relevant_nonlevel (per_univ i)) by pairwise.
  exists aσ; split; [ exact HaσI | exact (per_relevant_nonlevel_left _ _ _ Hr) ].
Qed.

(** Nor a type of levels ([per_relevant_nonlevel]). *)
Corollary rel_exp_of_typ_nonlevel_at : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> forall a, ⟦ A ⟧ ρ ↘ a -> ~ level_code a.
Proof.
  intros * HΓ H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E a Ea.
  destruct (eval_sub_id_rel HΓ' Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ' _ _ (rel_sub_id (ex_intro _ _ HΓ')) _ _ _ _ Hρ Hid Hid')
    as [aσ a0 a' a'σ' HaσI Ha Ha' Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI.
  assert (aσ = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hr : Dom a ≈ a0 ∈ per_relevant_nonlevel (per_univ i)) by pairwise.
  exact (per_relevant_nonlevel_left_nonlevel _ _ _ Hr).
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
  intros * Hφ HAj.
  pose proof HAj as [env_relΔ HΔ HA].
  pose proof Hφ as [env_relΓ HΓ env_relΔ2 HΔ2 Hφw _].
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  pose proof (rel_wk_mono _ _ _ Hφw) as Hφm.
  assert (Hρ' : Dom ρ' ≈ ρ ∈ env_relΓ) by (symmetry; exact Hρ).
  destruct (HA _ _ HΓ _ _ (rel_sub_of_wk Hφ) _ _ _ _ Hρ
              ltac:(eval_wk_at (Hφw _ _ Hρ)) ltac:(eval_wk_at (Hφw _ _ Hρ')))
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 ? Hchain].
  rewrite exp_sub_of_wk in Ha1.
  (** The inner values are at the restampings; the judgment at the
      restamping of [⟪φ⟫ ρ] against [⟪φ⟫ ρ'] bridges them. *)
  assert (HΔk : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ) by eassumption.
  pose proof (per_ctx_env_restamp_left HΔk _ _ (Hφw _ _ Hρ)) as Hrφρ.
  destruct (rel_type_inversion_simple HAj) as [env_relΔ3 [HΔ3 HAs]].
  assert (E3 : env_relΔ <~> env_relΔ3) by (eapply per_ctx_env_right_irrel; [ exact HΔk | exact HΔ3 ]).
  destruct (HAs _ _ (proj1 (E3 _ _) Hrφρ)) as (b & b' & Hb & Hb' & Hbb').
  assert (b = a2) as -> by (eapply functional_eval_exp; eassumption).
  exists a1, b'.
  repeat split; try eassumption.
  etransitivity; [| exact Hbb' ].
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
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_relevant_nonlevel (per_univ i))) ->
    Γ ⊨ A ≈ A' : Typeω@i.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (S i).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_relevant_nonlevel (per_univ i)).
  split; [| right; eapply H; eassumption].
  assert (Hu : per_univ_elem (S i) (per_relevant_nonlevel (per_univ i)) 𝕌ω@i 𝕌ω@i)
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
  assert (Hu : per_relevant_nonlevel (per_univ (S i)) 𝕌ω@i 𝕌ω@i)
    by (constructor; [| reflexivity | reflexivity | solve_not_level_code | solve_not_level_code ];
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
  intros ? ? [[R HR] Hl Hr Hnl Hnr]; constructor; [ exists R; now apply per_univ_elem_cumu | assumption .. ].
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
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists aσ, a'σ'.
  split; [ exact HaσI | split; [ exact Ha'σ'I | pairwise ] ].
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

(** [LevelSort] is a type of every large index, its elements the types of
    levels. *)
Lemma per_univ_elem_level_sort_univ : forall i, universe_index_large i ->
    DF LevelSortᵈ ≈ LevelSortᵈ ∈ per_univ_elem i ↘ per_level_sort.
Proof. intros * Hi; basic_per_univ_elem_econstructor; [ exact Hi | reflexivity ]. Qed.

(** The elements of [LevelSort] form a PER, as the elements of a type do. *)
#[export] Instance per_level_sort_PER : PER per_level_sort.
Proof. exact (per_elem_PER (per_univ_elem_level_sort_univ 0 I)). Qed.

(** Related types of levels are types of every index. *)
Lemma per_univ_elem_of_level_sort : forall i a a', Dom a ≈ a' ∈ per_level_sort ->
    exists R, DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  intros * (Hl & Hl' & [R HR]).
  exists R; exact (per_level_code_univ_elem _ _ _ (per_univ_elem_level_code _ _ _ _ HR Hl Hl') i).
Qed.

Lemma rel_exp_of_level_sort_inversion : forall {Γ A A'},
    Γ ⊨ A ≈ A' : LevelSort ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' per_level_sort.
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

Lemma rel_exp_of_level_sort : forall {Γ A A'},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
          ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' per_level_sort) ->
    Γ ⊨ A ≈ A' : LevelSort.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists per_level_sort.
  split; [| right; eapply H; eassumption].
  pose proof (per_univ_elem_level_sort_univ 0 I) as Hu.
  econstructor; try apply eval_exp_level_sort.
  apply rel_chain_4; assumption.
Qed.

(** The instance at [Id], at any context PER of [Γ]. *)
Lemma rel_exp_of_level_sort_inversion_simple_at : forall {Γ A A' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : LevelSort ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_level_sort.
Proof.
  intros * HΓ H%rel_exp_of_level_sort_inversion.
  destruct H as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  destruct (eval_sub_id_rel HΓ' Hρ) as [Hid Hid'].
  destruct (HA _ _ HΓ' _ _ (rel_sub_id (ex_intro _ _ HΓ')) _ _ _ _ Hρ Hid Hid')
    as [aσ a a' a'σ' HaσI Ha Ha' Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists aσ, a'σ'.
  split; [ exact HaσI | split; [ exact Ha'σ'I | pairwise ] ].
Qed.

(** A type of levels is relevant at every environment of its context. *)
Corollary rel_exp_of_level_sort_relevant_at : forall {Γ A A' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : LevelSort ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A ρ relevant.
Proof.
  intros * HΓ HA ρ ρ' Hρ.
  destruct (rel_exp_of_level_sort_inversion_simple_at HΓ HA _ _ Hρ) as (a & a' & Ea & _ & (Hl & _)).
  exists a; split; [ exact Ea | exact (level_code_relevant _ Hl) ].
Qed.

(** A type of levels is a type of every index. *)
Lemma rel_type_of_level_sort : forall {Γ A A'} (i : nat),
    Γ ⊨ A ≈ A' : LevelSort ->
    Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * H%rel_exp_of_level_sort_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  econstructor; [ exact HΓ |].
  intros * HΓ' * Hσ * Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| exact Hc ]; intros ? ? Hp; exact (per_univ_elem_of_level_sort _ _ _ Hp).
Qed.

(** A type of a sort is a type of an index. *)
Lemma rel_type_of_sort : forall {Γ A A' S},
    type_sort S ->
    Γ ⊨ A ≈ A' : S ->
    exists i, Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * [i | | ] H;
    [ exists i; exact (rel_type_of_typ H) | exists 0; exact (rel_type_of_prop 0 H)
    | exists 0; exact (rel_type_of_level_sort 0 H) ].
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
  intros * [i | | ];
    [ exists i; intros; apply rel_type_of_typ; assumption | exists 0; intros; apply rel_type_of_prop; assumption
    | exists 0; intros; apply rel_type_of_level_sort; assumption ].
Qed.

(** A type of a sort whose values at every environment are of the
    relevance [r] is a type of the sort at [r]: at an environment, a value
    of the other relevance contradicts the sort.  Not at [LevelSort]: a
    type of levels is no element of a universe. *)
Lemma rel_exp_sort_of_relevance : forall Γ A S r, type_sort S -> S <> LevelSort -> Γ ⊨ A : S ->
    (forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ -> rel_typ_sort A ρ r) ->
    exists i : nat, Γ ⊨ A : relevance_sort r Typeω@i.
Proof.
  intros * [i | |] Hnl HA Hr; [| | contradiction ];
    destruct r; cbn [relevance_sort]; [ exists i; exact HA | | | exists 0; exact HA ].
  - exists 0; apply rel_exp_of_prop.
    destruct (rel_exp_of_typ_inversion HA) as [R [HR H]].
    exists R, HR; intros Γ' R' HR' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'; exfalso.
    assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
    assert (HP : PER R) by (eapply per_env_PER; exact HR).
    destruct (Hr _ HR ρσ ltac:(etransitivity; [ exact Hρσ | symmetry; exact Hρσ ])) as (a & Ea & Hra).
    destruct (H _ _ HR' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & _)].
    destruct T12 as [_ _ Hr2].
    assert (a = a2) as -> by (eapply functional_eval_exp; eassumption); congruence.
  - exists 0; apply rel_exp_of_typ.
    destruct (rel_exp_of_prop_inversion HA) as [R [HR H]].
    exists R, HR; intros Γ' R' HR' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'; exfalso.
    assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
    assert (HP : PER R) by (eapply per_env_PER; exact HR).
    destruct (Hr _ HR ρσ ltac:(etransitivity; [ exact Hρσ | symmetry; exact Hρσ ])) as (a & Ea & Hra).
    destruct (H _ _ HR' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & _)].
    destruct T12 as [_ Hr2 _].
    assert (a = a2) as -> by (eapply functional_eval_exp; eassumption); congruence.
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

(** Relevant parameters, read from the innermost: the innermost entry, if
    an assumption, is relevant over the rest, and the rest are relevant. *)
Lemma rel_params_relevant_cons_iff : forall Γ e Ψ l,
    rel_params_relevant Γ (e :: Ψ) l <->
    (forall A, e = ce_ass A -> Ψ ++ Γ ⊨ A : Typeω@l) /\ rel_params_relevant Γ Ψ l.
Proof.
  intros *; split.
  - intros H; split; [ intros A ->; exact (H nil A Ψ eq_refl) |].
    intros Δ1 A Δ2 ->; exact (H (e :: Δ1) A Δ2 eq_refl).
  - intros [Hh Ht] [| e' Δ1] A Δ2 HE; cbn in HE; injection HE as -> HE; [ subst; exact (Hh A eq_refl) |].
    exact (Ht Δ1 A Δ2 HE).
Qed.

(** No parameters are relevant at every level. *)
Lemma rel_params_relevant_nil : forall Γ l, rel_params_relevant Γ nil l.
Proof. intros * [| ? ?] ? ? HE; discriminate. Qed.

(** Relevant parameters are relevant at a larger level. *)
Lemma rel_params_relevant_ge : forall Γ Ψ l l', l <= l' -> rel_params_relevant Γ Ψ l -> rel_params_relevant Γ Ψ l'.
Proof. intros * Hl H Δ1 A Δ2 HE; exact (rel_exp_cumu_ge Hl (H _ _ _ HE)). Qed.

(** Relevant parameters over relevant parameters are relevant, at the
    larger level. *)
Lemma rel_params_relevant_app : forall Γ Δy Δ l l',
    rel_params_relevant (Δ ++ Γ) Δy l -> rel_params_relevant Γ Δ l' ->
    rel_params_relevant Γ (Δy ++ Δ) (max l l').
Proof.
  induction Δy as [| e Δy IH]; intros * Hy HΔ; cbn [List.app].
  - exact (rel_params_relevant_ge _ _ l' (max l l') ltac:(lia) HΔ).
  - apply rel_params_relevant_cons_iff in Hy as [Hh Ht].
    apply rel_params_relevant_cons_iff; split; [| exact (IH _ _ _ Ht HΔ) ].
    intros A HA; rewrite <- app_assoc; exact (rel_exp_cumu_ge (i := l) (j := max l l') ltac:(lia) (Hh A HA)).
Qed.

(** ** Antisymmetry

    A telescope equation states that its heads are each below the other
    ([wf_ext_eq_ass]); the PER model reads that back as an equation of
    types, as related environments of its two sides need. *)

(** A level reads back in canonical form: the canonical form of its
    constant and atoms, or a single atom at offset [0]. *)
Lemma read_nf_level_canonical : forall s n l L,
    Rnf ⇓ (Levelᵈ@n) l in gc_deps ⍮ gc_stack ⍮ s ↘ nf_lvl_of L ->
    lvl_canonical L.
Proof.
  intros * H; inversion H; subst; try discriminate; destruct L as [c' ys']; cbn in *; subst.
  - change (lvl_canonical (lvl_canon (c, ys))); apply lvl_canon_canonical.
  - constructor; cbn.
    + split; [ intros * Hin; cbn in Hin; first [ contradiction | inversion Hin ] | exact I ].
    + intros * Hin; cbn; lia.
    + left; reflexivity.
    + split; [ apply ne_erase_idem | exact I ].
Qed.

(** Two levels each below the other are related: at every length their
    canonical forms are ordered both ways, so they are equal. *)
Lemma per_sublvl_antisym : forall l l',
    per_sublvl l l' -> per_sublvl l' l -> Dom l ≈ l' ∈ per_lvl.
Proof.
  intros * H H' s.
  destruct (H s) as [L L' HL HL' Hle]; destruct (H' s) as [K K' HK HK' Hle'].
  functional_read_rewrite_clear.
  repeat match goal with Heq : nf_lvl_of _ = nf_lvl_of _ |- _ => apply nf_lvl_of_inj in Heq; subst end.
  pose proof (lvl_le_antisym _ _ Hle Hle') as Hc.
  rewrite (lvl_canonical_canon _ (read_nf_level_canonical _ _ _ _ HL)),
    (lvl_canonical_canon _ (read_nf_level_canonical _ _ _ _ HL')) in Hc.
  subst; apply (mk_normal_reads_alike _ _ _ (nf_lvl_of L') (nf_lvl_of L')); [ assumption | assumption | reflexivity ].
Qed.

(** Two types each below the other are related types.  The second
    refinement is inverted at the head of the first:
    - two neutral relevant types are related by [per_bot] already;
    - types of levels, universes and small universes have equal indices,
      the levels of two small universes by [per_sublvl_antisym];
    - a small universe is never above a large one;
    - two [Π]s have related domains, and codomains each below the other at
      related arguments, related by induction;
    - inductive and record types are invariant, so already related;
    - two propositions are related by [per_prop], as the proposition clause
      of [per_univ_elem] relates them;
    - a relevant type and a proposition are never one below the other
      ([per_subtyp_relevance]), so the mixed pairs are impossible
      ([clear_wrong_relevance]). *)
Lemma per_subtyp_antisym : forall i a a',
    Sub a <: a' at i -> Sub a' <: a at i -> exists R, DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  induction 1; intros Hsub; dependent destruction Hsub; try solve [ exfalso; clear_wrong_relevance ].
  - eexists; per_univ_elem_econstructor; [ assumption | assumption | assumption | reflexivity ].
  - assert (m = n) as -> by lia; eexists; per_univ_elem_econstructor; reflexivity.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - eexists; per_univ_elem_econstructor; [ assumption | reflexivity ].
  - eexists; per_univ_elem_econstructor; reflexivity.
  - assert (i = j) as -> by lia; eexists; per_univ_elem_econstructor; [ eassumption | reflexivity | reflexivity ].
  - eexists; per_univ_elem_econstructor; [ eassumption | apply per_sublvl_antisym; assumption | reflexivity ].
  - rename H into Haa', H0 into Hsub_cod, H1 into IHcod, H2 into HΠ, H3 into HΠ', H4 into Ha'a, H5 into Hsub_cod'.
    basic_invert_per_univ_elem HΠ.
    rename in_rel0 into in_relL, out_rel into out_relL, H0 into HBB, H1 into HBsort, equiv_a_a' into Haa.
    basic_invert_per_univ_elem HΠ'.
    rename in_rel0 into in_relR, out_rel into out_relR, equiv_a_a' into Ha'a'.
    match goal with HX : forall c c' (e : in_relR c c'), rel_mod_eval _ B' _ B' _ _ |- _ => rename HX into HB'B' end.
    (** The three relations of the domains agree. *)
    assert (HiL : in_rel <~> in_relL) by (eapply per_univ_elem_right_irrel; [ exact Haa' | exact Haa ]).
    assert (HiR : in_rel <~> in_relR) by (eapply per_univ_elem_left_irrel; [ exact Haa' | exact Ha'a' ]).
    assert (Hi1 : in_rel <~> in_rel1)
      by (eapply per_univ_elem_right_irrel; [ exact Haa' | exact (proj1 (per_univ_elem_sym _ _ _ _ Ha'a)) ]).
    assert (HPin : PER in_rel) by (eapply per_elem_PER; exact Haa').
    (** The codomains' relations are the left side's. *)
    exists (pi_elements a a' in_rel (fun c c' Hc => out_relL c c' (proj1 (HiL c c') Hc))).
    eapply per_univ_elem_pi' with (out_rel := fun c c' Hc => out_relL c c' (proj1 (HiL c c') Hc)); [ exact Haa' | | | reflexivity ].
    + intros c c' Hcc.
      destruct (HBB _ _ (proj1 (HiL c c') Hcc)) as [b b0 Hb Hb0 Hbb0].
      assert (Hc'c' : in_rel c' c') by (etransitivity; [ symmetry |]; exact Hcc).
      destruct (HB'B' _ _ (proj1 (HiR c' c') Hc'c')) as [b' b'' Hb' Hb'' _].
      pose proof (Hsub_cod _ _ _ _ Hcc Hb Hb') as Hs1.
      pose proof (Hsub_cod' _ _ _ _ (proj1 (Hi1 c' c) (symmetry Hcc)) Hb' Hb) as Hs2.
      destruct (IHcod _ _ _ _ Hcc Hb Hb' Hs2) as [R HR].
      assert (HRR : R <~> out_relL c c' (proj1 (HiL c c') Hcc)) by (eapply per_univ_elem_right_irrel; [ exact HR | exact Hbb0 ]).
      econstructor; [ exact Hb | exact Hb' | eapply per_univ_elem_resp_iff; [ exact HR | exact HRR ] ].
    + intros c c' Hcc; exact (HBsort _ _ (proj1 (HiL c c') Hcc)).
  - eexists; eassumption.
  - eexists; eassumption.
  - eexists; simp per_univ_elem; eapply per_univ_elem_core_prop; [ symmetry; assumption | reflexivity ].
Qed.

(** Two types each below the other in the PER model are equal types there,
    at a level containing both refinements ([per_subtyp_antisym]). *)
Lemma rel_type_of_mutual_subtyp : forall {Γ A A'},
    Γ ⊨ A ⊆ A' -> Γ ⊨ A' ⊆ A -> exists i : nat, Γ ⊨ᵗ A ≈ A' at i.
Proof.
  intros * [R HR i Hsub] [R' HR' i' Hsub'].
  exists (max i i'); econstructor; [ exact HR |].
  intros Γ' env_rel' HΓ' σ σ' Hσσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HPρ : PER env_rel') by (eapply per_env_PER; exact HΓ').
  destruct (Hsub _ _ HΓ' _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [aσ a a'σ' a' Haσ Ha Ha'σ' Ha' [Ra Hl] [Ra' Hr] Hs].
  destruct (Hsub' _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσσ) _ _ _ _ (symmetry Hρ) Hev' Hev)
    as [b'σ' b' bσ b Hb'σ' Hb' Hbσ Hb _ _ Hs'].
  functional_eval_rewrite_clear.
  destruct (per_subtyp_antisym (max i i') a a'
              (per_subtyp_cumu _ _ _ Hs (max i i') ltac:(lia)) (per_subtyp_cumu _ _ _ Hs' (max i i') ltac:(lia)))
    as [Rm HRm].
  econstructor; [ exact Haσ | exact Ha | exact Ha' | exact Ha'σ' |].
  cbn; repeat split.
  - exists Ra; exact (per_univ_elem_cumu_max_left _ _ _ _ _ Hl).
  - exists Rm; exact HRm.
  - exists Ra'; exact (per_univ_elem_cumu_max_left _ _ _ _ _ (proj1 (per_univ_elem_sym _ _ _ _ Hr))).
Qed.

End Fixed_GCtx.
