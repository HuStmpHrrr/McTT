(** * Fundamental Theorem: Local Definitions

    A substitution into [Δ ▸ A ≔ M] is a substitution into [Δ ▹ A] whose
    values satisfy the tie of the entry.  The two substitutions every rule
    needs are the extension [σ,,M[σ]] and the lifting [q σ]; each is built
    from its counterpart for [Δ ▹ A] by [rel_sub_under_ctx_into_def].

    The let rules are then derived from one lemma, [rel_exp_let_universe], which
    relates the instance [B[Id,,M]] of a judgment of [B] in [Γ ▸ A ≔ M] to a
    [let].  The value of [ℓ A ≔ M in B] at [ρ] is the value of [B] at
    [ρ ↦ ⟦M⟧ρ], and the value of [(ℓ A ≔ M in B)[σ]] at [ρ] is the value of
    [B[q σ]] at [ρ ↦ ⟦M[σ]⟧ρ]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases VariableCases.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Simple Forms at a Substitution

    The outer values of a judgment instantiated along [σ ≈ σ], at an
    arbitrary related pair of environments. *)

Lemma rel_exp_of_typ_sub_simple : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
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
  apply per_relevant_univ_rel; pairwise.
Qed.

(** A substituted type of a universe is relevant. *)
Lemma rel_exp_of_typ_sub_relevant : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A[σ] ρ relevant.
Proof.
  intros * HΓ Hσj HA ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' _]]]].
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct (HAgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  assert (Hr : Dom a1 ≈ a4 ∈ per_relevant (per_univ i)) by pairwise.
  exists a1; split; [ exact Ha1 | exact (per_relevant_left _ _ _ Hr) ].
Qed.

(** So it is no proposition. *)
Corollary not_rel_typ_propositional_of_typ_sub : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> ~ rel_typ_propositional A[σ] ρ.
Proof.
  intros * HΓ Hσj HA ρ ρ' Hρ (a & Ea & Hp).
  destruct (rel_exp_of_typ_sub_relevant HΓ Hσj HA _ _ Hρ) as (a0 & Ea0 & Hr).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
  congruence.
Qed.

(** At a type of a universe the term judgment relates the values. *)
Lemma rel_exp_under_ctx_sub_simple : forall {Γ Δ σ σ' A M M' env_relΓ} {i : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M[σ] ⟧ ρ ↘ m /\ ⟦ M'[σ] ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A[σ] A[σ] ρ ρ'.
Proof.
  intros * HΓ Hσj HA HM ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' Hρσ]]]].
  destruct HM as [env_relΔ' HΔ' j HMgen].
  destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  apply (rel_exp_or_prop_relevant Htyp (rel_exp_of_typ_relevant_at HΔ HA _ _ Hρσ)) in Hexp.
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
        (domain_relevance a = propositional \/
         exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ R).
Proof.
  intros * HΓ H.
  pose proof (rel_exp_under_ctx_simple H) as [env_relΓ' [HΓ' [i HM]]].
  assert (E : env_relΓ <~> env_relΓ') by (eapply per_ctx_env_right_irrel; eassumption).
  exists i; intros ρ ρ' Hρ%E.
  exact (HM _ _ Hρ).
Qed.

(** The canonical context PER of a substituted definition entry. *)
Lemma per_ctx_env_of_def_sub : forall {Γ Δ σ σ' A} {i : nat} {M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M : A ->
    EF Γ ▸ A[σ] ≔ M[σ] ≈ Γ ▸ A[σ] ≔ M[σ] ∈ per_ctx_env
       ↘ per_env_extend_def A[σ] M[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA HM.
  eapply per_ctx_env_extend_def; [ exact HΓ | | |].
  - exact (rel_exp_of_typ_sub_simple HΓ Hσj HA).
  - exact (rel_exp_of_typ_sub_relevant HΓ Hσj HA).
  - exact (rel_exp_under_ctx_sub_simple HΓ Hσj HA HM).
Qed.

(** A member of the canonical context PER of a definition entry, from a
    member of that of the assumption entry and the tie at the left
    environment. *)
Lemma per_env_extend_def_intro : forall {S M R} {i : nat} {ρ ρ' c c' m},
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
  constructor; [ exact Hext | exact Ht | exact (def_tie_resp _ HS HM Hext Ht) ].
Qed.

(** ** Substitutions into a Definition Entry *)

Lemma rel_sub_under_ctx_into_def : forall {Γ Δ A} {i : nat} {M σ σ' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M : A ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▹ A ->
    (forall ρ ρσ, Dom ρ ≈ ρ ∈ env_relΓ -> ⟦ σ : Δ ▹ A ⟧s ρ ↘ ρσ -> def_tie A M ρσ) ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▸ A ≔ M.
Proof.
  intros * HΓ HA HM [env_relΓ' HΓ' env_relΔA HΔA Hσ] Htie.
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΔ [HΔ HAs]].
  pose proof (per_ctx_env_extend HΔ HAs) as HΔAc.
  pose proof (per_ctx_env_of_def HΔ HA HM) as HΔd.
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at_rel HΔ HA HM) as HMat.
  assert (EΓ : env_relΓ' <~> env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EΔ : env_relΔA <~> per_env_extend A A env_relΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΔ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΔ)) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend_def A M env_relΔ)) by (eapply per_env_PER; eassumption).
  (** The two contexts have the same entry types, so the same propositional
      entries. *)
  assert (Hsame : forall v x, entry_propositional gc_deps gc_stack (Δ ▹ A) v x ->
                              entry_propositional gc_deps gc_stack (Δ ▸ A ≔ M) v x)
    by (intros v [| x] [T HT E HE a Ea Hp]; econstructor; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ env_relΓ' HΓ' (per_env_extend_def A M env_relΔ) HΔd _).
  intros Γ'' env_rel'' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [v1 v2 v3 v4 Hw1 Hw2 Hw3 Hw4 Hchain].
  assert (PER env_rel'') by (eapply per_env_PER; eassumption).
  assert (Hρρ : Dom ρ ≈ ρ ∈ env_rel'') by solve_per.
  pose proof (Htie _ _ (proj1 (EΓ _ _) (rel_wk_app _ _ _ Hφ _ _ Hρρ)) Hw2) as Ht2.
  assert (Hc : rel_chain (per_env_extend A A env_relΔ) ([v1; v2; v3; v4]))
    by (eapply rel_chain_mono; [| exact Hchain ]; intros; apply EΔ; assumption).
  (** The tie at the value of [σ] at the weakened environment propagates
      along the chain. *)
  assert (T1 : def_tie A M v1) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  assert (T3 : def_tie A M v3) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  assert (T4 : def_tie A M v4) by (eapply (def_tie_resp (ρ := v2) _ HAat HMat); [ pairwise | exact Ht2 ]).
  assert (Hc' : rel_chain (per_env_extend_def A M env_relΔ) ([v1; v2; v3; v4]))
    by (apply rel_chain_4; (constructor; [ pairwise | assumption | assumption ])).
  (** The four hold the definition's proofs, so they are its evaluations. *)
  assert (Hpf : forall v, Dom v ≈ v ∈ per_env_extend_def A M env_relΔ -> env_proofs gc_deps gc_stack (Δ ▸ A ≔ M) v)
    by (intros v Hv; exact (proj1 (per_ctx_env_proofs _ _ _ HΔd _ _ Hv))).
  apply (mk_rel_sub v1 v2 v3 v4); [ | | | | exact Hc' ];
    (eapply eval_sub_change_target; [ eassumption | apply Hpf; pairwise | apply Hsame ]).
Qed.

(** [σ,,M[σ]] into [Δ ▸ A ≔ M]: the tie is the left commutation of [M]
    along [σ]. *)
Lemma rel_sub_under_ctx_extend_sub_def : forall {Γ Δ σ σ' A} {i : nat} {M M'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    Γ ⊨ˢ σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HM.
  pose proof Hσj as [env_relΓ HΓ _ _ _].
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  eapply rel_sub_under_ctx_into_def; [ exact HΓ | exact HA | exact HMl | |].
  - exact (rel_sub_under_ctx_extend_sub Hσj HM).
  - intros ρ ρτ Hρ Hev.
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    destruct (eval_sub_extend_inv _ _ _ _ _ _ Hev) as [Hev1 Hev0].
    destruct HMl as [env_relΔ HΔ j HMgen].
    assert (Hτ : Dom ρτ↯ ≈ ρτ↯ ∈ env_relΔ)
      by (eapply (rel_sub_under_ctx_at' Hσσ HΓ HΔ); eassumption).
    destruct (head_not_propositional_of_typ (e := ce_ass A) HΔ eq_refl HA _ _ Hτ) as [Hnp _].
    specialize (Hev0 ltac:(rewrite entry_propositional_zero_head; exact Hnp)).
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev1 Hev1) as [R [Htyp Hexp]].
    apply (rel_exp_or_prop_relevant Htyp (rel_exp_of_typ_relevant_at HΔ HA _ _ Hτ)) in Hexp.
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
    functional_eval_rewrite_clear.
    assert (Ha22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ R) by pairwise.
    eexists; split; [ eassumption |].
    eapply per_head_of; [ eassumption | eassumption | exact Ha22 | pairwise ].
Qed.

(** What the gluing model needs of an instantiated type in a definition
    context, as [per_univ_of_instance] for an assumption: [⟦B[Id,,M]⟧ρ] and
    [⟦B⟧(ρ ↦ ⟦M⟧ρ)] are related. *)
Lemma per_univ_of_instance_def : forall {Γ A} {i : nat} {M B k env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    Γ ▸ A ≔ M ⊨ B : Typeω@k ->
    forall ρ n,
      Dom ρ ≈ ρ ∈ env_relΓ ->
      ⟦ M ⟧ ρ ↘ n ->
      exists a b,
        ⟦ B[Id,,M] ⟧ ρ ↘ a /\ ⟦ B ⟧ ρ ↦ n ↘ b /\
          Dom a ≈ a ∈ per_univ k /\ Dom a ≈ b ∈ per_univ k.
Proof.
  intros * HΓ HA HM HB * Hρ Hn.
  pose proof (rel_sub_under_ctx_extend_sub_def (rel_sub_id (ex_intro _ _ HΓ)) HA HM) as HidM.
  rewrite exp_sub_id in HidM.
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  destruct (head_not_propositional_of_typ (e := ce_def A M) HΓ eq_refl HA _ _ Hρ) as [Hnp _].
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid _].
  destruct (HBgen _ _ HΓ _ _ HidM _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ _ _ Hid Hnp Hn)
                  (eval_sub_extend _ _ _ _ _ _ _ Hid Hnp Hn))
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  apply rel_chain_relevant_univ in Hchain.
  destruct Hchain as [Ht12 _].
  exists t1, t2.
  do 2 (split; [ eassumption |]).
  split; [| eassumption ].
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

(** [q σ] from [Γ ▸ A[σ] ≔ M[σ]] into [Δ ▸ A ≔ M].  The tie at [⟦q σ⟧ρ]
    is the tie at [ρ] moved along the left commutation of [M] at [σ], read at
    the tail [ρ↯]. *)
Lemma rel_sub_under_ctx_q_def : forall {Γ Δ σ σ' A} {i : nat} {M},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M : A ->
    Γ ▸ A[σ] ≔ M[σ] ⊨ˢ q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HM.
  pose proof Hσj as [env_relΓ HΓ env_relΔ HΔ Hσ].
  pose proof (per_ctx_env_of_def_sub HΓ Hσj HA HM) as HΓd.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj (rel_type_of_typ HA)) as HΓa.
  pose proof (per_ctx_env_of_typ HΔ (rel_type_of_typ HA)) as HΔA.
  eapply rel_sub_under_ctx_into_def; [ exact HΓd | exact HA | exact HM | |].
  - eapply rel_sub_under_ctx_restrict;
      [ exact HΓd | exact HΓa | exact HΔA | exact HΔA
      | intros ? ? []; assumption | intros; assumption
      | intros ? ? _ ? Hp; exact Hp
      | exact (rel_sub_under_ctx_q Hσj (rel_type_of_typ HA)) ].
  - intros ρ ρq Hρ Hev.
    destruct (eval_sub_q_inv _ _ _ _ _ Hev) as [Hev1 Hev0'].
    pose proof Hρ as [[Ht Hh _ _] [t [Ht0 Htie]] _].
    (** [σ] at the Kripke stage [↑], which relates [⟦σ[↑]ʷ⟧ρ] to
        [⟦σ⟧(ρ↯)]. *)
    pose proof (rel_wk_shift HΓ HΓd) as Hshift.
    destruct (Hσ _ _ HΓd _ Hshift _ _ Hρ) as [x1 u u' x4 Hx1 Hu Hu' Hx4 Htails].
    rewrite ?eval_wk_shift in *.
    assert (Heq : env_eq ρq↯ x1) by (eapply functional_eval_sub; eassumption).
    assert (Hqu : Dom ρq↯ ≈ u ∈ env_relΔ) by (rewrite Heq; pairwise).
    assert (Huu : Dom u ≈ u ∈ env_relΔ) by pairwise.
    (** The head of the lifting is the environment's: [A] is no
        proposition. *)
    destruct (head_not_propositional_of_typ (e := ce_ass A) HΔ eq_refl HA _ _ Hqu) as [Hnp _].
    assert (Hev0 : ρq 0 = ρ 0)
      by (unfold env_var; rewrite (Hev0' ltac:(rewrite entry_propositional_zero_head; exact Hnp)); reflexivity).
    (** [M] along [σ] at the tail. *)
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    pose proof HM as [env_relΔ' HΔ' j HMgen].
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Ht Hu Hu) as [RN [Htyp Hexp]].
    apply (rel_exp_or_prop_relevant Htyp (rel_exp_of_typ_relevant_at HΔ HA _ _ Huu)) in Hexp.
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
    assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
    destruct (rel_exp_under_ctx_simple_at_rel HΔ HA HM _ _ Hqu) as [m [mu [Hm [Hmu Hmmu]]]].
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
Lemma rel_exp_let_universe : forall {Γ A A'} {i : nat} {M M' B B' C oA'},
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    let_ann oA' A' (Typeω@i) ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ a_let (b_def oA' M') B' : C[Id,,M].
Proof.
  intros * HA HAA' Hann HM HB.
  pose proof (rel_exp_under_ctx_refl_right HAA') as HA'.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (per_ctx_env_of_def HΓ HA HMl) as HΓd.
  pose proof (per_ctx_env_of_def HΓ HA HMr) as HΓd'.
  pose proof (per_ctx_env_of_typ HΓ (rel_type_of_typ HA)) as HΓA.
  (** [B'] in the context of the right-hand definiens. *)
  assert (HB'r : Γ ▸ A ≔ M' ⊨ B' ≈ B' : C)
    by (eapply rel_exp_under_ctx_restrict; [ exact HΓd' | exact HΓd | | | exact HBr ];
        [ eapply per_ctx_env_def_conv; [ exact HA | exact (rel_exp_under_ctx_sym HM) | eassumption | eassumption ]
        | intros ? ? _ [| x] [T HT E HE a Ea Hp]; econstructor; eassumption ]).
  pose proof (rel_exp_of_typ_inversion_simple_at HΓ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at_rel HΓ HA HMl) as HMlat.
  pose proof (rel_exp_under_ctx_simple_at_rel HΓ HA HMr) as HMrat.
  (** The entries are no propositions, and evaluation reads only the entry
      types. *)
  assert (Hty : forall N N' x, ctx_entry_type (Γ ▸ A ≔ N) x = ctx_entry_type (Γ ▸ A ≔ N') x)
    by (intros ? ? [| x]; reflexivity).
  assert (Htya : forall N x, ctx_entry_type (Γ ▹ A) x = ctx_entry_type (Γ ▸ A ≔ N) x)
    by (intros ? [| x]; reflexivity).
  destruct (rel_exp_under_ctx_simple_full_at HΓd HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓd HBl) as [kY HY].
  destruct (rel_exp_under_ctx_simple_full_at HΓd' HB'r) as [kZ HZ].
  pose proof HBl as [? ? k HBlgen].
  pose proof HB'r as [? ? k3 HB'gen].
  refine (mk_rel_exp_under_ctx _ _ _ _ env_relΓ HΓ k _).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (PER env_rel') by (eapply per_env_PER; eassumption).
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Definientia

      The four values of [M ≈ M'] and the two inner values of [M] on the
      right, which the instances of [B] along [Id,,M] and [σ',,M[σ']] use. *)
  pose proof (rel_exp_of_typ_relevant_at HΓ HA _ _ Hρσ) as HArel.
  destruct (head_not_propositional_of_typ (e := ce_def A M) HΓ eq_refl HA _ _ Hρσ) as [Hnp2 Hnp3].
  destruct (head_not_propositional_of_typ (e := ce_def A M') HΓ eq_refl HA _ _ Hρσ) as [Hnp2' Hnp3'].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  pose proof HM as [? ? j HMgen].
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  apply (rel_exp_or_prop_relevant HNtyp HArel) in HNexp.
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  pose proof HMl as [? ? jl HMlgen].
  destruct (HMlgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RNl [HNltyp HNlexp]].
  apply (rel_exp_or_prop_relevant HNltyp HArel) in HNlexp.
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
              (eval_sub_extend _ _ _ _ _ _ _ Hev Hnp2 Hn1) (eval_sub_extend _ _ _ _ _ _ _ Hev' Hnp3 Hn4m))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  rewrite <- exp_sub_extend_sub in Hc1, Hc4.
  pose proof (rel_sub_under_ctx_extend_sub_def (rel_sub_id (ex_intro _ _ HΓ)) HA HMl) as HidM.
  rewrite exp_sub_id in HidM.
  destruct (HBlgen _ _ HΓ _ _ HidM _ _ _ _ Hρσ
              (eval_sub_extend _ _ _ _ _ _ _ Hid2 Hnp2 Hn2)
              (eval_sub_extend _ _ _ _ _ _ _ Hid3 Hnp3 Hn3m))
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
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
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY HYd]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ' ↦ ⟦M'[σ']⟧ρ'], whose inner value [⟦B'⟧(s ↦ ⟦M'[σ']⟧ρ')]
      is bridged to [⟦B'⟧(ρ'σ' ↦ ⟦M'⟧ρ'σ')] by [B'] itself. *)
  pose proof (per_ctx_env_of_def_sub HΓ' Hσ'σ' HA HMr) as HΓ'd.
  pose proof (rel_sub_under_ctx_q_def Hσ'σ' HA HMr) as Hq.
  pose proof (rel_exp_of_typ_sub_simple HΓ' Hσ'σ' HA) as HAσ'.
  pose proof (rel_exp_under_ctx_sub_simple HΓ' Hσ'σ' HA HMr) as HMσ'.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_rel') by solve_per.
  assert (Hpair : Dom ρ' ↦ n4 ≈ ρ' ↦ n4 ∈ per_env_extend_def A[σ'] M'[σ'] env_rel').
  { eapply (per_env_extend_def_intro _ HAσ' HMσ' Hρ'ρ'); [ | exact Hn4 | ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ]. }
  destruct (rel_sub_under_ctx_q_at HΓ' HΓA Hσ'σ' (rel_type_of_typ HA) _ _ _ _ _ _ (per_env_extend_def_ext _ _ _ _ _ Hpair) Hev' Hev')
    as [s [s' [Hqs [Hqs' Hqchain]]]].
  apply (eval_sub_same_types (Htya M')) in Hqs.
  destruct (HB'gen _ _ HΓ'd _ _ Hq _ _ _ _ Hpair Hqs Hqs) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (Hsq : Dom ρ'σ' ↦ n4 ≈ s ↦ n4 ∈ per_env_extend A A env_relΓ) by pairwise.
  destruct Hsq as [Hts _ _ _].
  destruct (HAat _ _ Hts) as [b3 [bs [Hb3 [Hbs [Rs HRs]]]]].
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  change (Dom ρ'σ' ≈ s ∈ env_relΓ) in Hts.
  assert (ERs : RN <~> Rs) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRs).
  assert (HZ1 : Dom ρ'σ' ↦ n3 ≈ s ↦ n4 ∈ per_env_extend_def A M' env_relΓ).
  { eapply (per_env_extend_def_intro _ HAat HMrat Hts); [ | exact Hn3 | ].
    - eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; exact Hn34 ].
    - eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; solve_per ]. }
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ HZd]]]]]].
  (** *** One Element PER

      The values the bridges share with the instances, and the irrelevance
      along each shared type value. *)
  assert (cy1 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cy2 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cx1 = cB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz1 = cx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz2 = e2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cB2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cB2 ≈ cB3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  (** Whether [C] is a proposition, at the inner instance; the bridges
      carry it to every other value. *)
  pose proof (per_univ_elem_relevance _ _ _ _ Hp1) as Er1.
  pose proof (per_univ_elem_relevance _ _ _ _ HRY) as ErY.
  pose proof (per_univ_elem_relevance _ _ _ _ HRX) as ErX.
  pose proof (per_univ_elem_relevance _ _ _ _ HRZ) as ErZ.
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
  apply (fun H => per_univ_elem_resp_iff H FY) in HRY.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  exists R2; split.
  { apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2).
    { eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hp1 | exact HRY ] | exact Hp2 ]. }
    apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ]. }
  destruct (domain_relevance cB2) eqn:ErB.
  2:{ left; exists c1; split; [ exact Hc1 | congruence ]. }
  right.
  (** [C] is relevant: every instance and bridge relates the terms. *)
  assert (ErA : domain_relevance cA2 = relevant) by congruence.
  assert (Er2 : domain_relevance e2 = relevant) by congruence.
  apply (rel_exp_or_prop_relevant HI1t (ex_intro _ cA2 (conj HcA2 ErA))) in HI1e.
  apply (rel_exp_or_prop_relevant HI2t (ex_intro _ cB2 (conj HcB2 ErB))) in HI2e.
  apply (rel_exp_or_prop_relevant HI3t (ex_intro _ e2 (conj He2 Er2))) in HI3e.
  destruct HYd as [HYd | [by1 [by2 [Hby1 [Hby2 Hby]]]]]; [ congruence |].
  destruct HXd as [HXd | [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]; [ congruence |].
  destruct HZd as [HZd | [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]; [ congruence |].
  destruct HI1e as [w1 bA2 bA3 w4 Hw1 HbA2 HbA3 Hw4 Hw1chain].
  rewrite <- exp_sub_extend_sub in Hw1.
  destruct HI2e as [w2 bB2 bB3 w3 Hw2 HbB2 HbB3 Hw3 Hw2chain].
  destruct HI3e as [v4 f2 f3 v4' Hv4 Hf2 Hf3 Hv4' Hv4chain].
  assert (by1 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (by2 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bx1 = bB2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz1 = bx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz2 = f2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2 ≈ bB2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ v4 ∈ R3) by pairwise.
  apply F1 in Ht1.
  apply FY in Hby.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  (** The [let] on the right binds the value of its definiens: its
      annotation, if any, is relevant. *)
  assert (Hρ'σ' : Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ) by solve_per.
  assert (Hlet3 : ⟦ a_let (b_def oA' M') B' ⟧ ρ'σ' ↘ bx2).
  { destruct Hann as [[-> _] | ->]; [ eapply eval_exp_let; eassumption |].
    destruct (rel_exp_of_typ_relevant_at HΓ HA' _ _ Hρ'σ') as (a' & Ea' & Er').
    eapply eval_exp_let_ann; eassumption. }
  assert (Hlet4 : ⟦ (a_let (b_def oA' M') B')[σ'] ⟧ ρ' ↘ v4).
  { destruct Hann as [[-> _] | ->]; simpl; [ eapply eval_exp_let; eassumption |].
    destruct (rel_exp_of_typ_sub_relevant HΓ' Hσ'σ' HA' _ _ Hρ'ρ') as (a' & Ea' & Er').
    eapply eval_exp_let_ann; eassumption. }
  apply (mk_rel_exp w1 w2 bx2 v4); try eassumption.
  apply rel_chain_4; solve_per.
Qed.

(** A substitution into [Δ ▹ A] at a proposition [A] is one into
    [Δ ▸ A ≔ M]: the two context PERs are the same. *)
Lemma rel_sub_under_ctx_into_def_prop : forall {Γ Δ A M σ σ'},
    Δ ⊨ A : Propₘ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▹ A ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▸ A ≔ M.
Proof.
  intros * HA Hσj.
  pose proof Hσj as [env_relΓ HΓ env_relΔA HΔA _].
  pose proof (rel_type_inversion_simple (rel_type_of_prop 0 HA)) as [env_relΔ [HΔ HAs]].
  pose proof (per_ctx_env_extend HΔ HAs) as HΔAc.
  pose proof (per_ctx_env_of_def_prop (M := M) HΔ HA) as HΔd.
  eapply rel_sub_under_ctx_restrict;
    [ exact HΓ | exact HΓ | exact HΔAc | exact HΔd | intros; assumption | intros; assumption
    | intros ? ? _ [| x] [T HT E HE a Ea Hp]; econstructor; eassumption | exact Hσj ].
Qed.

(** The [let] rules at a proposition.  The body binds the proof [⋆ᵈ] on
    both sides, so the instance [B[Id,,M]] and the [let] meet at the
    environments extended by it: no definiens is evaluated.  The shape is
    that of [rel_exp_let_universe], with the bridges between heads gone. *)
Lemma rel_exp_let_prop : forall {Γ A A'} {M M' B B' C oA'},
    Γ ⊨ A : Propₘ ->
    Γ ⊨ A ≈ A' : Propₘ ->
    let_ann oA' A' Propₘ ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ a_let (b_def oA' M') B' : C[Id,,M].
Proof.
  intros * HA HAA' Hann HM HB.
  destruct Hann as [[_ [? Habs]] | ->]; [ discriminate Habs |].
  pose proof (rel_exp_under_ctx_refl_right HAA') as HA'.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  pose proof (rel_type_inversion_simple (rel_type_of_prop 0 HA)) as [env_relΓ [HΓ HAs]].
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (per_ctx_env_of_def_prop (M := M) HΓ HA) as HΓd.
  pose proof (per_ctx_env_of_def_prop (M := M') HΓ HA) as HΓd'.
  pose proof (per_ctx_env_extend HΓ HAs) as HΓA.
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; eassumption).
  (** [B'] in the context of the right-hand definiens: the same PER. *)
  assert (HB'r : Γ ▸ A ≔ M' ⊨ B' ≈ B' : C)
    by (eapply rel_exp_under_ctx_restrict; [ exact HΓd' | exact HΓd | intros; assumption
        | intros ? ? _ [| x] [T HT E HE a Ea Hp]; econstructor; eassumption | exact HBr ]).
  assert (Htya : forall N x, ctx_entry_type (Γ ▹ A) x = ctx_entry_type (Γ ▸ A ≔ N) x)
    by (intros ? [| x]; reflexivity).
  destruct (rel_exp_under_ctx_simple_full_at HΓd HB) as [kX HX].
  destruct (rel_exp_under_ctx_simple_full_at HΓd' HB'r) as [kZ HZ].
  pose proof HBl as [? ? k HBlgen].
  pose proof HB'r as [? ? k3 HB'gen].
  refine (mk_rel_exp_under_ctx _ _ _ _ env_relΓ HΓ k _).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (PER env_rel') by (eapply per_env_PER; eassumption).
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρ'σ' : Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ) by solve_per.
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Heads

      [A] is a proposition at the substituted environments, so every
      extension along a definition of it binds [⋆ᵈ]. *)
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HA _ _ Hρσ) as (a2 & a3 & Ha2 & Ha3 & [Hl2 Hr3 _]).
  assert (Hp : forall e, ctx_entry_type (e :: nil) 0 = Some A ->
                 head_propositional gc_deps gc_stack e ρσ /\ head_propositional gc_deps gc_stack e ρ'σ')
    by (intros e He; split;
        [ apply (proj2 (head_propositional_iff HΓ He HAs Hρσ Ha2)); exact Hl2
        | apply (proj2 (head_propositional_iff_right HΓ He HAs Hρσ Ha3)); exact Hr3 ]).
  destruct (Hp (ce_def A M) eq_refl) as [Hh2 Hh3].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** *** The Instances

      [B] along [σ,,M[σ]] gives the outer values of the type and the first
      value of the term, and [B] along [Id,,M] at the substituted environments
      gives the inner values of the type and the second value of the term. *)
  pose proof (rel_sub_under_ctx_into_def_prop (M := M) HA (rel_sub_under_ctx_extend_sub Hσj HMl)) as Hτ.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_proof _ _ _ _ _ _ Hev Hh2) (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hh3))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  rewrite <- exp_sub_extend_sub in Hc1, Hc4.
  pose proof (rel_sub_under_ctx_into_def_prop (M := M) HA
                (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HMl)) as HidM.
  rewrite exp_sub_id in HidM.
  destruct (HBlgen _ _ HΓ _ _ HidM _ _ _ _ Hρσ
              (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hh2) (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hh3))
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  (** *** The Middle Bridge: [B ≈ B'] at the extended substituted pair. *)
  assert (HX1 : Dom ρσ ↦ ⋆ᵈ ≈ ρ'σ' ↦ ⋆ᵈ ∈ per_env_extend A A env_relΓ)
    by (apply per_env_extend_intro'; [ exact Hρσ | eapply per_head_proof; eassumption ]).
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ' ↦ ⋆ᵈ], whose inner value [⟦B'⟧(s ↦ ⋆ᵈ)] is
      bridged to [⟦B'⟧(ρ'σ' ↦ ⋆ᵈ)] by [B'] itself. *)
  pose proof (per_ctx_env_of_typ_sub HΓ' Hσ'σ' (rel_type_of_prop 0 HA)) as HΓ'a.
  pose proof (rel_sub_under_ctx_into_def_prop (M := M') HA (rel_sub_under_ctx_q Hσ'σ' (rel_type_of_prop 0 HA))) as Hq.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ5 [HΓ5 HAgen]].
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_rel') by solve_per.
  destruct (HAgen _ _ HΓ' _ _ Hσ'σ' _ _ _ _ Hρ'ρ' Hev' Hev') as [a1' a2' a3' a4' Ha1' Ha2' Ha3' Ha4' Hachain'].
  assert (Ha4p : Dom a4' ≈ a4' ∈ per_prop) by pairwise.
  assert (Hpair : Dom ρ' ↦ ⋆ᵈ ≈ ρ' ↦ ⋆ᵈ ∈ per_env_extend A[σ'] A[σ'] env_rel')
    by (apply per_env_extend_intro'; [ exact Hρ'ρ' | eapply per_head_proof; [ exact Ha4' | exact (per_prop_left _ _ Ha4p) ] ]).
  destruct (rel_sub_under_ctx_q_at HΓ' HΓA Hσ'σ' (rel_type_of_prop 0 HA) _ _ _ _ _ _ Hpair Hev' Hev')
    as [s [s' [Hqs [Hqs' Hqchain]]]].
  apply (eval_sub_same_types (Htya M')) in Hqs.
  destruct (HB'gen _ _ HΓ'a _ _ Hq _ _ _ _ Hpair Hqs Hqs) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (HZ1 : Dom ρ'σ' ↦ ⋆ᵈ ≈ s ↦ ⋆ᵈ ∈ per_env_extend A A env_relΓ) by pairwise.
  destruct (HZ _ _ HZ1) as [cz1 [cz2 [RZ [Hcz1 [Hcz2 [HRZ HZd]]]]]].
  (** *** One Element PER

      The values the bridges share with the instances, and the irrelevance
      along each shared type value. *)
  assert (cB2 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cB3 = cA3) as -> by (eapply functional_eval_exp; eassumption).
  assert (cx1 = cA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz1 = cx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (cz2 = e2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hp1 : DF c1 ≈ cA2 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp1' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R1) by pairwise.
  assert (Hp2 : DF cA2 ≈ c2 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp2' : DF cA2 ≈ cA3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp23 : DF c2 ≈ c3 ∈ per_univ_elem k ↘ R2) by pairwise.
  assert (Hp3 : DF e1 ≈ e2 ∈ per_univ_elem k3 ↘ R3) by pairwise.
  pose proof (per_univ_elem_relevance _ _ _ _ Hp1) as Er1.
  pose proof (per_univ_elem_relevance _ _ _ _ HRX) as ErX.
  pose proof (per_univ_elem_relevance _ _ _ _ HRZ) as ErZ.
  assert (F1 : R1 <~> R2) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp1' Hp2').
  assert (FX : RX <~> R2) by (symmetry; exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hp2' HRX)).
  assert (E4 : RZ <~> RX) by exact (per_univ_elem_cross_irrel _ _ _ _ _ _ _ HRZ HRX).
  assert (E5 : R3 <~> RZ) by exact (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hp3 HRZ).
  assert (FZ : RZ <~> R2) by (rewrite E4, FX; reflexivity).
  assert (F3 : R3 <~> R2) by (rewrite E5, FZ; reflexivity).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hp1.
  assert (PER R2) by (eapply per_elem_PER; exact Hp23).
  exists R2; split.
  { apply (mk_rel_exp c1 c2 c3 c4); try eassumption.
    assert (Hc12 : DF c1 ≈ c2 ∈ per_univ_elem k ↘ R2) by (eapply per_univ_trans; [ exact Hp1 | exact Hp2 ]).
    assert (Hp14 : DF c1 ≈ c4 ∈ per_univ_elem k ↘ R1) by pairwise.
    apply (fun H => per_univ_elem_resp_iff H F1) in Hp14.
    apply rel_chain_4; [ exact Hc12 | exact Hp23 | solve_per ]. }
  destruct (domain_relevance cA2) eqn:ErA.
  2:{ left; exists c1; split; [ exact Hc1 | congruence ]. }
  right.
  (** [C] is relevant: every instance and bridge relates the terms. *)
  assert (Er2 : domain_relevance e2 = relevant) by congruence.
  apply (rel_exp_or_prop_relevant HI1t (ex_intro _ cA2 (conj HcA2 ErA))) in HI1e.
  apply (rel_exp_or_prop_relevant HI2t (ex_intro _ cA2 (conj HcB2 ErA))) in HI2e.
  apply (rel_exp_or_prop_relevant HI3t (ex_intro _ e2 (conj He2 Er2))) in HI3e.
  destruct HXd as [HXd | [bx1 [bx2 [Hbx1 [Hbx2 Hbx]]]]]; [ congruence |].
  destruct HZd as [HZd | [bz1 [bz2 [Hbz1 [Hbz2 Hbz]]]]]; [ congruence |].
  destruct HI1e as [w1 bA2 bA3 w4 Hw1 HbA2 HbA3 Hw4 Hw1chain].
  rewrite <- exp_sub_extend_sub in Hw1.
  destruct HI2e as [w2 bB2 bB3 w3 Hw2 HbB2 HbB3 Hw3 Hw2chain].
  destruct HI3e as [v4 f2 f3 v4' Hv4 Hf2 Hf3 Hv4' Hv4chain].
  assert (bB2 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bx1 = bA2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz1 = bx2) as -> by (eapply functional_eval_exp; eassumption).
  assert (bz2 = f2) as -> by (eapply functional_eval_exp; eassumption).
  assert (Ht1 : Dom w1 ≈ bA2 ∈ R1) by pairwise.
  assert (Ht2 : Dom w2 ≈ bA2 ∈ R2) by pairwise.
  assert (Ht3 : Dom f2 ≈ v4 ∈ R3) by pairwise.
  apply F1 in Ht1.
  apply FX in Hbx.
  apply FZ in Hbz.
  apply F3 in Ht3.
  (** The [let] on the right binds the proof: its annotation is a
      proposition. *)
  assert (Hlet3 : ⟦ a_let (b_def (Some A') M') B' ⟧ ρ'σ' ↘ bx2).
  { destruct (rel_exp_of_prop_inversion_simple_at HΓ HA' _ _ Hρ'σ') as (b & b' & Eb & Eb' & [Hlb _ _]).
    eapply eval_exp_let_proof; [ exact Eb | exact Hlb | exact Hbx2 ]. }
  assert (Hlet4 : ⟦ (a_let (b_def (Some A') M') B')[σ'] ⟧ ρ' ↘ v4).
  { simpl.
    pose proof (rel_exp_of_prop_inversion HA') as [env_relΓ6 [HΓ6 HA'gen]].
    destruct (HA'gen _ _ HΓ' _ _ Hσ'σ' _ _ _ _ Hρ'ρ' Hev' Hev') as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
    assert (Hb11 : Dom b1 ≈ b4 ∈ per_prop) by pairwise.
    eapply eval_exp_let_proof; [ exact Hb1 | exact (per_prop_left _ _ Hb11) | exact Hv4 ]. }
  apply (mk_rel_exp w1 w2 bx2 v4); try eassumption.
  apply rel_chain_4; solve_per.
Qed.

(** The two together: a definition of a type of either sort. *)
Corollary rel_exp_let_any_sort : forall {Γ A A' S} {M M' B B' C oA'},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ A ≈ A' : S ->
    let_ann oA' A' S ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ a_let (b_def oA' M') B' : C[Id,,M].
Proof.
  intros * [i |] HA HAA' Hann HM HB;
    [ exact (rel_exp_let_universe HA HAA' Hann HM HB) | exact (rel_exp_let_prop HA HAA' Hann HM HB) ].
Qed.

(** [ζ]. *)
Corollary rel_exp_under_ctx_let_zeta : forall {Γ oA A S} {M B C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    Γ ▸ A ≔ M ⊨ B : C ->
    let_ann oA A S ->
    Γ ⊨ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros * HS HA HM HB Hann.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_any_sort HS HA HA Hann HM HB).
Qed.

Hint Resolve rel_exp_under_ctx_let_zeta : mctt.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     let_ann oA A Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M] ).
Proof. intros * HA HS HM HB Hann; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_zeta HS HA HM HB Hann) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Congruence: both sides are related to the instance [B[Id,,M]]. *)
Corollary rel_exp_under_ctx_let_cong : forall {Γ oA oA' A A' S} {M M' B B' C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ A ≈ A' : S ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    let_ann oA A S ->
    let_ann oA' A' S ->
    Γ ⊨ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M].
Proof.
  intros * HS HA HAA' HM HB Hann Hann'.
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_any_sort HS HA HAA' Hann' HM HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_any_sort HS HA HA Hann (rel_exp_under_ctx_refl_left HM) (rel_exp_under_ctx_refl_left HB)).
Qed.

Hint Resolve rel_exp_under_ctx_let_cong : mctt.

End Fixed_GCtx.

Lemma sem_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
     let_ann oA A Srt ->
     let_ann oA' A' Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M] ).
Proof.
  intros * HA HS HAA' _ HM HB Hann Hann'; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_cong HS HA HAA' HM HB Hann Hann') ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary valid_exp_under_ctx_let : forall {Γ oA A S} {M B C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    Γ ▸ A ≔ M ⊨ B : C ->
    let_ann oA A S ->
    Γ ⊨ a_let (b_def oA M) B : C[Id,,M].
Proof.
  intros * HS HA HM HB Hann.
  exact (rel_exp_under_ctx_let_cong HS HA HA HM HB Hann Hann).
Qed.

Hint Resolve valid_exp_under_ctx_let : mctt.

End Fixed_GCtx.

Lemma sem_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     let_ann oA A Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_let (b_def oA M) B : C[Id,,M] ).
Proof. intros * HA HS HM HB Hann; sem_intro; [ assumption | exact (valid_exp_under_ctx_let HS HA HM HB Hann) ]. Qed.

#[export]
Hint Resolve rel_exp_under_ctx_let_zeta rel_exp_under_ctx_let_cong valid_exp_under_ctx_let : mctt.
