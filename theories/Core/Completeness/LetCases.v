(** * Fundamental Theorem: Local Definitions

    A substitution into [Δ ▸ A ≔ M] is a substitution into [Δ ▹ A] whose
    values satisfy the tie of the entry.  The two substitutions every rule
    needs are the extension [σ,,M[σ]] and the lifting [q σ]; each is built
    from its counterpart for [Δ ▹ A] by [rel_sub_under_ctx_into_def].

    The let rules are then derived from one lemma, [rel_exp_let_gen], which
    relates the instance [B[Id,,M]] of a judgment of [B] in [Γ ▸ A ≔ M] to a
    [let].  The value of [ℓ A ≔ M in B] at [ρ] is the value of [B] at
    [ρ ↦ ⟦M⟧ρ], and the value of [(ℓ A ≔ M in B)[σ]] at [ρ] is the value of
    [B[q σ]] at [ρ ↦ ⟦M[σ]⟧ρ]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases LogicalRelation SubstitutionCases UniverseCases VariableCases.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Simple Forms at a Substitution

    The outer values of a judgment instantiated along [σ ≈ σ], at an
    arbitrary related pair of environments. *)

Lemma rel_exp_of_typ_sub_simple : forall {Γ Δ σ σ' A A' i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Type@i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A[σ] ⟧ ρ ↘ a /\ ⟦ A'[σ] ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HΓ Hσj HA ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' _]]]].
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct (HAgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  exists a1, a4; repeat split; try eassumption.
  pairwise.
Qed.

Lemma rel_exp_under_ctx_sub_simple : forall {Γ Δ σ σ' A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M[σ] ⟧ ρ ↘ m /\ ⟦ M'[σ] ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A[σ] A[σ] ρ ρ'.
Proof.
  intros * HΓ Hσj HM ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' _]]]].
  destruct HM as [env_relΔ' [HΔ' [j HMgen]]].
  destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Ha14 : DF a1 ≈ a4 ∈ per_univ_elem j ↘ R) by pairwise.
  exists m1, m4; repeat split; try eassumption.
  eapply per_head_of; [ exact Ha1 | exact Ha4 | exact Ha14 | pairwise ].
Qed.

(** The [Id] instance with the values of the type and the element PER, at any
    context PER of [Γ]. *)
Corollary rel_exp_under_ctx_simple_full_at : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ M ≈ M' : A ->
    exists i,
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A ⟧ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ R.
Proof.
  intros * HΓ H.
  pose proof (rel_exp_under_ctx_simple H) as [env_relΓ' [HΓ' [i HM]]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  exists i; intros ρ ρ' Hρ%E.
  exact (HM _ _ Hρ).
Qed.

(** The canonical context PER of a substituted definition entry. *)
Lemma per_ctx_env_of_def_sub : forall {Γ Δ σ σ' A i M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A : Type@i ->
    Δ ⊨ M : A ->
    EF Γ ▸ A[σ] ≔ M[σ] ≈ Γ ▸ A[σ] ≔ M[σ] ∈ per_ctx_env
       ↘ per_env_extend_def A[σ] M[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA HM.
  eapply per_ctx_env_extend_def; [ exact HΓ | |].
  - exact (rel_exp_of_typ_sub_simple HΓ Hσj HA).
  - exact (rel_exp_under_ctx_sub_simple HΓ Hσj HM).
Qed.

(** A member of the canonical context PER of a definition entry, from a
    member of that of the assumption entry and the tie at the left
    environment. *)
Lemma per_env_extend_def_intro : forall {S M R i ρ ρ' c c' m},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    Dom ρ ≈ ρ' ∈ R ->
    Dom c ≈ c' ∈ per_head S S ρ ρ' ->
    ⟦ M ⟧ ρ ↘ m ->
    Dom m ≈ c ∈ per_head S S ρ ρ' ->
    Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend_def S M R.
Proof.
  intros * HPER HS HM Hρ Hc Hm Hmc.
  assert (Hρρ : Dom ρ ≈ ρ ∈ R) by solve_per.
  assert (E : per_head S S ρ ρ <~> per_head S S ρ ρ')
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  assert (Hext : Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend S S R)
    by (apply per_env_extend_intro'; assumption).
  assert (Ht : def_tie S M (ρ ↦ c)) by (exists m; split; [ exact Hm | apply E; exact Hmc ]).
  split; [ exact Hext | split; [ exact Ht | exact (def_tie_resp _ HS HM Hext Ht) ] ].
Qed.

(** ** Substitutions into a Definition Entry *)

Lemma rel_sub_under_ctx_into_def : forall {Γ Δ A i M σ σ' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Δ ⊨ A : Type@i ->
    Δ ⊨ M : A ->
    Γ ⊨s σ ≈ σ' : Δ ▹ A ->
    (forall ρ ρσ, Dom ρ ≈ ρ ∈ env_relΓ -> ⟦ σ ⟧s ρ ↘ ρσ -> def_tie A M ρσ) ->
    Γ ⊨s σ ≈ σ' : Δ ▸ A ≔ M.
Proof.
  intros * HΓ HA HM [env_relΓ' [HΓ' [env_relΔA [HΔA Hσ]]]] Htie.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΔ [HΔ HAs]].
  pose proof (per_ctx_env_extend HΔ HAs) as HΔAc.
  pose proof (per_ctx_env_of_def HΔ HA HM) as HΔd.
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at HΔ HM) as HMat.
  assert (EΓ : env_relΓ' <~> env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EΔ : env_relΔA <~> per_env_extend A A env_relΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΔ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΔ)) by (eapply per_env_PER; eassumption).
  exists env_relΓ', HΓ', (per_env_extend_def A M env_relΔ), HΔd.
  intros Γ'' env_rel'' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [v1 v2 v3 v4 H1 H2 H3 H4 Hchain].
  econstructor; try eassumption.
  assert (PER env_rel'') by (eapply per_env_PER; eassumption).
  assert (Hρρ : Dom ρ ≈ ρ ∈ env_rel'') by solve_per.
  pose proof (Htie _ _ (proj1 (EΓ _ _) (rel_wk_app _ _ _ Hφ _ _ Hρρ)) H2) as Ht2.
  assert (Hc : rel_chain (per_env_extend A A env_relΔ) ([v1; v2; v3; v4]))
    by (eapply rel_chain_mono; [| exact Hchain ]; intros; apply EΔ; assumption).
  (** The tie at the value of [σ] at the weakened environment propagates
      along the chain. *)
  assert (T1 : def_tie A M v1) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  assert (T3 : def_tie A M v3) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  assert (T4 : def_tie A M v4) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  apply rel_chain_4; (split; [ pairwise | split; assumption ]).
Qed.

(** [σ,,M[σ]] into [Δ ▸ A ≔ M]: the tie is the left commutation of [M]
    along [σ]. *)
Lemma rel_sub_under_ctx_extend_sub_def : forall {Γ Δ σ σ' A i M M'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A : Type@i ->
    Δ ⊨ M ≈ M' : A ->
    Γ ⊨s σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HM.
  pose proof Hσj as [env_relΓ [HΓ _]].
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  eapply rel_sub_under_ctx_into_def; [ exact HΓ | exact HA | exact HMl | |].
  - exact (rel_sub_under_ctx_extend_sub Hσj HM).
  - intros ρ ρτ Hρ Hev.
    assert (Hev1 : ⟦ σ ⟧s ρ ↘ ρτ↯) by (intros x; rewrite env_var_drop; exact (Hev (S x))).
    pose proof (Hev 0) as Hev0; cbn in Hev0.
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    destruct HMl as [env_relΔ [HΔ [j HMgen]]].
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev1 Hev1) as [R [Htyp Hexp]].
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
    functional_eval_rewrite_clear.
    assert (Ha22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ R) by pairwise.
    eexists; split; [ eassumption |].
    eapply per_head_of; [ eassumption | eassumption | exact Ha22 | pairwise ].
Qed.

(** [q σ] from [Γ ▸ A[σ] ≔ M[σ]] into [Δ ▸ A ≔ M].  The tie at [⟦q σ⟧ρ]
    is the tie at [ρ] moved along the left commutation of [M] at [σ], read at
    the tail [ρ↯]. *)
Lemma rel_sub_under_ctx_q_def : forall {Γ Δ σ σ' A i M},
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A : Type@i ->
    Δ ⊨ M : A ->
    Γ ▸ A[σ] ≔ M[σ] ⊨s q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HM.
  pose proof Hσj as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  pose proof (per_ctx_env_of_def_sub HΓ Hσj HA HM) as HΓd.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓa.
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  eapply rel_sub_under_ctx_into_def; [ exact HΓd | exact HA | exact HM | |].
  - eapply rel_sub_under_ctx_restrict;
      [ exact HΓd | exact HΓa | exact HΔA | exact HΔA
      | intros ? ? []; assumption | intros; assumption
      | exact (rel_sub_under_ctx_q Hσj HA) ].
  - intros ρ ρq Hρ Hev.
    assert (Hev1 : ⟦ sb_wk σ ↑ ⟧s ρ ↘ ρq↯)
      by (intros x; rewrite env_var_drop; pose proof (Hev (S x)) as Hx; rewrite sb_q_succ in Hx; exact Hx).
    assert (Hev0 : ρq 0 = ρ 0)
      by (pose proof (Hev 0) as Hx; rewrite sb_q_zero in Hx;
          eapply functional_eval_exp; [ exact Hx | apply eval_exp_var ]).
    pose proof Hρ as [[Ht Hh] [[t [Ht0 Htie]] _]].
    (** [σ] at the Kripke stage [↑], which relates [⟦σ[↑]ʷ⟧ρ] to
        [⟦σ⟧(ρ↯)]. *)
    pose proof (rel_wk_shift HΓ HΓd) as Hshift.
    destruct (Hσ _ _ HΓd _ Hshift _ _ Hρ) as [x1 u u' x4 Hx1 Hu Hu' Hx4 Htails].
    rewrite ?eval_wk_shift in *.
    assert (Heq : env_eq ρq↯ x1) by (eapply functional_eval_sub; eassumption).
    assert (Hqu : Dom ρq↯ ≈ u ∈ env_relΔ) by (rewrite Heq; pairwise).
    (** [M] along [σ] at the tail. *)
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    pose proof HM as [env_relΔ' [HΔ' [j HMgen]]].
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Ht Hu Hu) as [RN [Htyp Hexp]].
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
    assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
    destruct (rel_exp_under_ctx_simple_at HΔ HM _ _ Hqu) as [m [mu [Hm [Hmu Hmmu]]]].
    destruct (rel_exp_of_typ_inversion_simple_at HΔ HA _ _ Hqu) as [b [b' [Hb [Hb' [Rb HRb]]]]].
    functional_eval_rewrite_clear.
    exists m; split; [ eassumption |].
    rewrite Hev0.
    assert (Ha11 : DF a1 ≈ a1 ∈ per_univ_elem j ↘ RN) by pairwise.
    assert (Ha12 : DF a1 ≈ a2 ∈ per_univ_elem j ↘ RN) by pairwise.
    assert (Hbb : DF b ≈ b ∈ per_univ_elem i ↘ Rb) by (etransitivity; [| symmetry]; eassumption).
    apply (per_head_iff Ha1 Ha1 Ha11) in Htie.
    apply (per_head_iff Hb Ha2 HRb) in Hmmu.
    apply (per_head_iff Hb Hb Hbb).
    try handle_per_univ_elem_irrel.
    match goal with |- ?R _ _ => assert (PER R) by (eapply per_elem_PER; eassumption) end.
    solve_per.
Qed.

(** ** The Let Rules

    The instance [B[Id,,M]] against a [let] whose body [B'] is related to [B]
    and whose definiens [M'] is related to [M].  The annotation [A'] of the
    [let] is never evaluated, so it is arbitrary.  The four values of the
    terms are [⟦B[σ,,M[σ]]⟧ρ], [⟦B[Id,,M]⟧ρσ], [⟦B'⟧(ρ'σ' ↦ ⟦M'⟧ρ'σ')] and
    [⟦B'[q σ']⟧(ρ' ↦ ⟦M'[σ']⟧ρ')].

    - The first link comes from [B] along [σ,,M[σ]] and along [Id,,M], bridged
      by [B] at the two heads [⟦M[σ]⟧ρ] and [⟦M⟧ρσ].
    - The middle link is [B ≈ B'] at the substituted environments.
    - The last link comes from [B'] along [q σ'], bridged by [B'] at the tail
      [⟦q σ'⟧(ρ' ↦ ⟦M'[σ']⟧ρ')]. *)
Lemma rel_exp_let_gen : forall {Γ A i M M' B B' C A'},
    Γ ⊨ A : Type@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HA HM HB.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (per_ctx_env_of_def HΓ HA HMl) as HΓd.
  pose proof (per_ctx_env_of_def HΓ HA HMr) as HΓd'.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  (** [B'] in the context of the right-hand definiens. *)
  assert (HB'r : Γ ▸ A ≔ M' ⊨ B' ≈ B' : C)
    by (eapply rel_exp_under_ctx_restrict; [ exact HΓd' | exact HΓd | | exact HBr ];
        eapply per_ctx_env_def_conv; [ exact HA | exact (rel_exp_under_ctx_sym HM) | eassumption | eassumption ]).
  pose proof (rel_exp_of_typ_inversion_simple_at HΓ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at HΓ HMl) as HMlat.
  pose proof (rel_exp_under_ctx_simple_at HΓ HMr) as HMrat.
  destruct (rel_exp_under_ctx_simple_full_at HΓd HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓd HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓd' HB'r) as [kZ HZ].
  pose proof HBl as [? [? [k HBlgen]]].
  pose proof HB'r as [? [? [k3 HB'gen]]].
  exists env_relΓ, HΓ, k.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (PER env_rel') by (eapply per_env_PER; eassumption).
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Definientia

      The four values of [M ≈ M'] and the two inner values of [M] on the
      right, which the instances of [B] along [Id,,M] and [σ',,M[σ']] use. *)
  pose proof HM as [? [? [j HMgen]]].
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  pose proof HMl as [? [? [jl HMlgen]]].
  destruct (HMlgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RNl [HNltyp HNlexp]].
  destruct HNltyp as [a1' a2' a3' a4' Ha1' Ha2' Ha3' Ha4' Halchain].
  destruct HNlexp as [n1' n2' n3m n4m Hn1' Hn2' Hn3m Hn4m Hnlchain].
  assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (a4' = a4) as -> by (eapply functional_eval_exp; eassumption).
  assert (n1' = n1) as -> by (eapply functional_eval_exp; eassumption).
  assert (n2' = n2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ha22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha23 : DF a2 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha33 : DF a3 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha44 : DF a4 ≈ a4 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Ha23l : DF a2 ≈ a3 ∈ per_univ_elem jl ↘ RNl) by pairwise.
  assert (ERN : RNl <~> RN) by (eapply per_univ_elem_right_irrel; eassumption).
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn34 : Dom n3 ≈ n4 ∈ RN) by pairwise.
  assert (Hn44 : Dom n4 ≈ n4 ∈ RN) by pairwise.
  (** *** The Instance

      [B] along [σ,,M[σ]] gives the outer values of the type and the first
      value of the term, and [B] along [Id,,M] at the substituted environments
      gives the inner values of the type and the second value of the term. *)
  pose proof (rel_sub_under_ctx_extend_sub_def Hσj HA HMl) as Hτ.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend _ _ _ _ _ Hev Hn1) (eval_sub_extend _ _ _ _ _ Hev' Hn4m))
    as [R1 [HI1t HI1e]].
  destruct HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  destruct HI1e as [w1 bA2 bA3 w4 Hw1 HbA2 HbA3 Hw4 Hw1chain].
  rewrite <- exp_sub_extend_sub in Hc1, Hc4, Hw1.
  pose proof (rel_sub_under_ctx_extend_sub_def (rel_sub_id (ex_intro _ _ HΓ)) HA HMl) as HidM.
  rewrite exp_sub_id in HidM.
  destruct (HBlgen _ _ HΓ _ _ HidM _ _ _ _ Hρσ
              (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn2)
              (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn3m))
    as [R2 [HI2t HI2e]].
  destruct HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  destruct HI2e as [w2 bB2 bB3 w3 Hw2 HbB2 HbB3 Hw3 Hw2chain].
  (** *** The Bridges at the Substituted Environments

      [B] at the two heads [⟦M[σ]⟧ρ] and [⟦M⟧ρσ], and [B ≈ B'] at the
      substituted pair. *)
  assert (HY1 : Dom ρσ ↦ n1 ≈ ρσ ↦ n2 ∈ per_env_extend_def A M env_relΓ).
  { assert (Hρσρσ : Dom ρσ ≈ ρσ ∈ env_relΓ) by solve_per.
    eapply (per_env_extend_def_intro _ HAat HMlat Hρσρσ); [ | exact Hn2 | ].
    - eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | exact Hn12 ].
    - eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | symmetry; exact Hn12 ]. }
  assert (HX1 : Dom ρσ ↦ n2 ≈ ρ'σ' ↦ n3 ∈ per_env_extend_def A M env_relΓ).
  { eapply (per_env_extend_def_intro _ HAat HMlat Hρσ); [ | exact Hn2 | ].
    - eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23 | exact Hn23 ].
    - eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23 | solve_per ]. }
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY [by1 [by2 [Hby1 [Hby2 Hby]]]]]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ' ↦ ⟦M'[σ']⟧ρ'], whose inner value [⟦B'⟧(s ↦ ⟦M'[σ']⟧ρ')]
      is bridged to [⟦B'⟧(ρ'σ' ↦ ⟦M'⟧ρ'σ')] by [B'] itself. *)
  pose proof (per_ctx_env_of_def_sub HΓ' Hσ'σ' HA HMr) as HΓ'd.
  pose proof (rel_sub_under_ctx_q_def Hσ'σ' HA HMr) as Hq.
  pose proof (rel_exp_of_typ_sub_simple HΓ' Hσ'σ' HA) as HAσ'.
  pose proof (rel_exp_under_ctx_sub_simple HΓ' Hσ'σ' HMr) as HMσ'.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_rel') by solve_per.
  assert (Hpair : Dom ρ' ↦ n4 ≈ ρ' ↦ n4 ∈ per_env_extend_def A[σ'] M'[σ'] env_rel').
  { eapply (per_env_extend_def_intro _ HAσ' HMσ' Hρ'ρ'); [ | exact Hn4 | ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ]. }
  destruct (rel_sub_under_ctx_q_at HΓ' HΓA Hσ'σ' HA _ _ _ _ _ _ (proj1 Hpair) Hev' Hev')
    as [s [s' [Hqs [Hqs' Hqchain]]]].
  destruct (HB'gen _ _ HΓ'd _ _ Hq _ _ _ _ Hpair Hqs Hqs) as [R3 [HI3t HI3e]].
  destruct HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  destruct HI3e as [v4 f2 f3 v4' Hv4 Hf2 Hf3 Hv4' Hv4chain].
  assert (Hsq : Dom ρ'σ' ↦ n4 ≈ s ↦ n4 ∈ per_env_extend A A env_relΓ) by pairwise.
  destruct Hsq as [Hts _].
  destruct (HAat _ _ Hts) as [b3 [bs [Hb3 [Hbs [Rs HRs]]]]].
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  change (Dom ρ'σ' ≈ s ∈ env_relΓ) in Hts.
  assert (ERs : RN <~> Rs) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRs).
  assert (HZ1 : Dom ρ'σ' ↦ n3 ≈ s ↦ n4 ∈ per_env_extend_def A M' env_relΓ).
  { eapply (per_env_extend_def_intro _ HAat HMrat Hts); [ | exact Hn3 | ].
    - eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; exact Hn34 ].
    - eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; solve_per ]. }
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]]]]]].
  (** *** One Element PER

      The values the bridges share with the instances, and the irrelevance
      along each shared type value. *)
  assert (cy1 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cy2 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cx1 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz1 = cx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz2 = e2) as -> by (eapply functional_eval_exp; eassumption).
  assert (by1 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (by2 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bx1 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz1 = bx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz2 = f2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2 ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ v4 ∈ R3) by pairwise.
  assert (E1 : R1 <~> RY) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' HRY).
  assert (E2 : R2 <~> RY) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ Hp2' HRY).
  assert (E3 : R2 <~> RX) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (FY : RY <~> R2) by (rewrite E2; reflexivity).
  assert (FX : RX <~> R2) by (rewrite E3; reflexivity).
  assert (FZ : RZ <~> R2) by (rewrite E4, E3; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1, Hp14.
  apply F1 in Ht1.
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  exists R2; split.
  - apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2).
    { eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]. }
    apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ].
  - apply (mk_rel_exp w1 w2 bx2 v4); try eassumption.
    + eapply eval_exp_let; eassumption.
    + simpl; eapply eval_exp_let; eassumption.
    + apply rel_chain_4; solve_per.
Qed.

(** [ζ]. *)
Corollary rel_exp_let_zeta : forall {Γ A i M B C},
    Γ ⊨ A : Type@i ->
    Γ ⊨ M : A ->
    Γ ▸ A ≔ M ⊨ B : C ->
    Γ ⊨ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros * HA HM HB.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_gen HA HM HB).
Qed.

Hint Resolve rel_exp_let_zeta : mctt.

(** Congruence: both sides are related to the instance [B[Id,,M]]. *)
Corollary rel_exp_let_cong : forall {Γ A A' i M M' B B' C},
    Γ ⊨ A : Type@i ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HA HM HB.
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_gen (A' := A') HA HM HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_gen HA (rel_exp_under_ctx_refl_left HM) (rel_exp_under_ctx_refl_left HB)).
Qed.

Hint Resolve rel_exp_let_cong : mctt.

Corollary valid_exp_let : forall {Γ A i M B C},
    Γ ⊨ A : Type@i ->
    Γ ⊨ M : A ->
    Γ ▸ A ≔ M ⊨ B : C ->
    Γ ⊨ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros * HA HM HB.
  exact (rel_exp_let_cong HA HM HB).
Qed.

Hint Resolve valid_exp_let : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve rel_exp_let_zeta rel_exp_let_cong valid_exp_let : mctt.
