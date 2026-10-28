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


Lemma rel_exp_of_univ_inversion : forall {Γ A A' u},
    Γ ⊨ A ≈ A' : universe_index_term u ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨ˢ σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ u).
Proof.
  intros * [env_relΓ HΓ j HA].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
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
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [aσ a a' a'σ' HaσI ? ? Ha'σ'I Hchain].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a'.
  repeat split; try eassumption.
  pairwise.
Qed.

Lemma rel_exp_of_univ : forall {Γ A A' u},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ u)) ->
    Γ ⊨ A ≈ A' : universe_index_term u.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (large_level_above u).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_univ u).
  split; [| eapply H; eassumption].
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
  intros ? ? [R HR]; exists R; eapply per_univ_elem_cumu_universe_index; eassumption.
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
  assert (Hu : per_univ (us (a, S n)) 𝕌@(dlvl_lit (a, n)) 𝕌@(dlvl_lit (a, n)))
    by (eexists; apply per_univ_elem_core_suniv';
        [ apply per_lvl_lit | cbn; ord | reflexivity ]).
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
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i).
Proof.
  intros * [env_relΓ HΓ j HA].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  (** The type chain is a chain of universes, so inverting it identifies [R]
    with [per_univ i], and then [Hexp] is the goal. *)
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  invert_rel_typ_body.
  eassumption.
Qed.

(** The instance of the above at [Id].  This is the form a context PER needs:
    [per_ctx_env_cons] asks for the values of [A] and [A'] in the environments
    themselves, and at [Id] these coincide with the substituted ones, since [Id]
    evaluates to the environment itself and [A[Id]] is [A].  The chain collapses
    onto its middle link. *)
Corollary rel_exp_of_typ_inversion_simple : forall {Γ A A'} {i : nat},
    Γ ⊨ A ≈ A' : Typeω@i ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a',
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A' ⟧ ρ' ↘ a' /\
        Dom a ≈ a' ∈ per_univ i.
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

(** The same at any context PER of [Γ]. *)
Corollary rel_exp_of_typ_inversion_simple_at : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HΓ H.
  pose proof (rel_exp_of_typ_inversion_simple H) as [env_relΓ' [HΓ' HA]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  intros ρ ρ' Hρ%E.
  exact (HA _ _ Hρ).
Qed.

(** The same instance at a weakening instead of [Id], as the gluing model needs:
    it reads a type's value at [ρ] after [[φ]ʷ], while the context relation
    supplies the value at [⟪φ⟫ ρ].  The two values are not equal; [per_univ i]
    relates them. *)
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
Proof.
  intros * Hφ H%rel_exp_of_typ_inversion.
  destruct H as [env_relΔ [HΔ HA]].
  pose proof Hφ as [env_relΓ HΓ env_relΔ2 HΔ2 _].
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

(** [per_head_resp] in the form a type judgment supplies its premises: the four
    values it asks for are four instances of the judgment, at pairs selected by a
    chain of environments.

    Every rule with a premise in an extended context needs this, because the
    environments [q σ] evaluates to are related to, but not equal to, the ones the
    goal names, so a head PER read at the former must be moved to the latter.  It
    is stated over an arbitrary context PER because the move happens at each level
    of a nested [q]. *)
Lemma per_head_of_typ_resp : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    forall ρ1 ρ2 ρ3 ρ4,
      rel_chain env_relΓ ([ρ1; ρ2; ρ3; ρ4]) ->
      per_head A A' ρ1 ρ2 <~> per_head A A' ρ3 ρ4.
Proof.
  intros * HΓ HA * Hchain.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΓ2 [HΓ2 HAsimple]].
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

Lemma rel_exp_of_typ : forall {Γ A A'} {i : nat},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ i)) ->
    Γ ⊨ A ≈ A' : Typeω@i.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with (S i).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_univ i).
  split; [| eapply H; eassumption].
  assert (Hu : per_univ_elem (S i) (per_univ i) 𝕌ω@i 𝕌ω@i)
    by (apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ : mctt.

(** Semantic presupposition: a term judgment contains a type judgment, its own
    type chain, which lives in [per_univ_elem i elem_rel] and hence in
    [per_univ i].  This is the semantic counterpart of [presup_exp_eq]; the
    substitution cases use it to build the context PER of [Δ ▹ T] from a judgment
    about a term of [T]. *)
Corollary presup_rel_exp_under_ctx : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    exists i, Γ ⊨ A ≈ A : Typeω@i.
Proof.
  intros * [env_relΓ HΓ i HM].
  exists i.
  apply rel_exp_of_typ.
  eexists; eexists; [eassumption |].
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
  assert (Hu : per_univ (S i) 𝕌ω@i 𝕌ω@i)
    by (eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
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
  intros ? ? [R HR]; exists R; now apply per_univ_elem_cumu.
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
