(** * Fundamental Theorem: Local Definitions

    A substitution into [Δ ▸ A ≔ M] is a substitution into [Δ ▹ A] whose
    values satisfy the tie of the entry.  The two substitutions every rule
    needs are the extension [σ,,M[σ]] and the lifting [q σ]; each is built
    from its counterpart for [Δ ▹ A] by [rel_sub_under_ctx_into_def].

    The let rules are then derived from two lemmas, [rel_exp_let_relevant]
    for a definition of a relevant type (of a universe, or of [LevelSort])
    and [rel_exp_let_prop] for one of a proposition, which relate the
    instance [B[Id,,M]] of a judgment of [B] in [Γ ▸ A ≔ M] to a [let].  At
    a relevant type the value of [ℓ A ≔ M in B] at [ρ] is the value of [B]
    at [ρ ↦ ⟦M⟧ρ ⦂ ⟦A⟧ρ], and the value of [(ℓ A ≔ M in B)[σ]] at [ρ] is the
    value of [B[q σ]] at [ρ ↦ ⟦M[σ]⟧ρ ⦂ ⟦A[σ]⟧ρ]; at a proposition the
    body is kept as the proof [⋆ᵈ⟨M, ρ⟩].  The kept proofs read back since
    the definientia are scoped by the context: the rules take
    [exp_scoped] premises, as [wf_scoped] provides. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Semantic Require Import Realizability.
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

Lemma rel_type_sub_simple : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A' at i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A[σ] ⟧ ρ ↘ a /\ ⟦ A'[σ] ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HΓ Hσj HA ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' _]]]].
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct (HAgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  exists a1, a4; repeat split; try eassumption.
  pairwise.
Qed.

Corollary rel_exp_of_typ_sub_simple : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a', ⟦ A[σ] ⟧ ρ ↘ a /\ ⟦ A'[σ] ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof. intros * HΓ Hσj HA; exact (rel_type_sub_simple HΓ Hσj (rel_type_of_typ HA)). Qed.

(** A substituted relevant type is relevant: at a substituted
    environment it is related to the type at the substitution's value
    there, which is relevant. *)
Lemma rel_type_sub_relevant : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A' at i ->
    rel_type_relevant Δ A ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A[σ] ρ relevant.
Proof.
  intros * HΓ Hσj HA HArel ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' Hρσ]]]].
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct (HAgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  assert (Hr : Dom a1 ≈ a2 ∈ per_univ i) by pairwise.
  destruct Hr as [R12 Hr].
  destruct (HArel _ HΔ _ _ Hρσ) as (b & Eb & Hb).
  assert (b = a2) as -> by (eapply functional_eval_exp; eassumption).
  exists a1; split; [ exact Ha1 | rewrite (per_univ_elem_relevance _ _ _ _ Hr); exact Hb ].
Qed.

Corollary rel_exp_of_typ_sub_relevant : forall {Γ Δ σ σ' A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A' : Typeω@i ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort A[σ] ρ relevant.
Proof.
  intros * HΓ Hσj HA.
  exact (rel_type_sub_relevant HΓ Hσj (rel_type_of_typ HA) (rel_type_relevant_of_typ (rel_exp_under_ctx_refl_left HA))).
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

(** At a relevant type the term judgment relates the values. *)
Lemma rel_exp_under_ctx_sub_simple_relevant : forall {Γ Δ σ σ' A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    rel_type_relevant Δ A ->
    Δ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M[σ] ⟧ ρ ↘ m /\ ⟦ M'[σ] ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A[σ] A[σ] ρ ρ'.
Proof.
  intros * HΓ Hσj HArel HM ρ ρ' Hρ.
  pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
  pose proof (rel_sub_under_ctx_simple Hσσ) as [env_relΓ1 [HΓ1 [env_relΔ [HΔ Hs]]]].
  assert (E : env_relΓ <~> env_relΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as [ρσ [ρ'σ [Hev [Hev' Hρσ]]]].
  destruct HM as [env_relΔ' HΔ' j HMgen].
  destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  apply (rel_exp_or_prop_relevant Htyp (HArel _ HΔ _ _ Hρσ)) in Hexp.
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Ha14 : DF a1 ≈ a4 ∈ per_univ_elem j ↘ R) by pairwise.
  exists m1, m4; repeat split; try eassumption.
  eapply per_head_of; [ exact Ha1 | exact Ha4 | exact Ha14 | pairwise ].
Qed.

Corollary rel_exp_under_ctx_sub_simple : forall {Γ Δ σ σ' A M M' env_relΓ} {i : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists m m', ⟦ M[σ] ⟧ ρ ↘ m /\ ⟦ M'[σ] ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head A[σ] A[σ] ρ ρ'.
Proof. intros * HΓ Hσj HA; exact (rel_exp_under_ctx_sub_simple_relevant HΓ Hσj (rel_type_relevant_of_typ HA)). Qed.

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

(** The same at a relevant type, where the values of the terms are
    related. *)
Corollary rel_exp_under_ctx_simple_full_at_relevant : forall {Γ A M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    rel_type_relevant Γ A ->
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
  intros * HΓ HA H.
  destruct (rel_exp_under_ctx_simple_full_at HΓ H) as [i HM].
  exists i; intros ρ ρ' Hρ.
  destruct (HM _ _ Hρ) as (a & a' & R & Ha & Ha' & HR & [Hp | Hm]); [| exists a, a', R; repeat split; assumption ].
  destruct (HA _ HΓ _ _ Hρ) as (a0 & Ea0 & Hr).
  assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption); congruence.
Qed.

Corollary rel_exp_under_ctx_simple_full_at_rel : forall {Γ A M M' env_relΓ} {k : nat},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A : Typeω@k ->
    Γ ⊨ M ≈ M' : A ->
    exists i,
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      exists a a' R,
        ⟦ A ⟧ ρ ↘ a /\
        ⟦ A ⟧ ρ' ↘ a' /\
        DF a ≈ a' ∈ per_univ_elem i ↘ R /\
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ R.
Proof. intros * HΓ HA; exact (rel_exp_under_ctx_simple_full_at_relevant HΓ (rel_type_relevant_of_typ HA)). Qed.

(** The canonical context PER of a substituted definition entry of a
    relevant type. *)
Lemma per_ctx_env_of_def_sub_relevant : forall {Γ Δ σ σ' A} {i : nat} {M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    rel_type_relevant Δ A ->
    Δ ⊨ M : A ->
    EF Γ ▸ A[σ] ≔ M[σ] ≈ Γ ▸ A[σ] ≔ M[σ] ∈ per_ctx_env
       ↘ per_env_extend_def A[σ] M[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA HArel HM.
  eapply (per_ctx_env_extend_def (i := i)); [ exact HΓ | | |].
  - exact (rel_type_sub_simple HΓ Hσj HA).
  - exact (rel_type_sub_relevant HΓ Hσj HA HArel).
  - exact (rel_exp_under_ctx_sub_simple_relevant HΓ Hσj HArel HM).
Qed.

(** The same at a type of a universe. *)
Corollary per_ctx_env_of_def_sub : forall {Γ Δ σ σ' A} {i : nat} {M env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M : A ->
    EF Γ ▸ A[σ] ≔ M[σ] ≈ Γ ▸ A[σ] ≔ M[σ] ∈ per_ctx_env
       ↘ per_env_extend_def A[σ] M[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA.
  exact (per_ctx_env_of_def_sub_relevant HΓ Hσj (rel_type_of_typ HA) (rel_type_relevant_of_typ HA)).
Qed.

(** A member of the canonical context PER of a definition entry, from a
    member of that of the assumption entry (related heads that read back
    at their stored types) and the tie at the left environment. *)
Lemma per_env_extend_def_intro : forall {S M R} {i : nat} {ρ ρ' c c' t t' m},
    PER R ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists a a', ⟦ S ⟧ ρ ↘ a /\ ⟦ S ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall ρ ρ',
        Dom ρ ≈ ρ' ∈ R ->
        exists m m', ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ Dom m ≈ m' ∈ per_head S S ρ ρ') ->
    Dom ρ ≈ ρ' ∈ R ->
    Dom c ≈ c' ∈ per_head S S ρ ρ' ->
    entry_readable (de_term c t) ->
    entry_readable (de_term c' t') ->
    ⟦ M ⟧ ρ ↘ m ->
    Dom m ≈ c ∈ per_head S S ρ ρ' ->
    Dom ρ ↦ c ⦂ t ≈ ρ' ↦ c' ⦂ t' ∈ per_env_extend_def S M R.
Proof.
  intros * HPER HS HM Hρ Hc Hrc Hrc' Hm Hmc.
  assert (Hρρ : Dom ρ ≈ ρ ∈ R) by solve_per.
  assert (E : per_head S S ρ ρ <~> per_head S S ρ ρ')
    by (eapply (per_head_resp_simple HPER HS); apply rel_chain_4; solve_per).
  assert (Hext : Dom ρ ↦ c ⦂ t ≈ ρ' ↦ c' ⦂ t' ∈ per_env_extend S S R)
    by (apply per_env_extend_intro'; assumption).
  assert (Ht : def_tie S M (ρ ↦ c ⦂ t)) by (exists m; split; [ exact Hm | apply E; exact Hmc ]).
  constructor; [ exact Hext | exact Ht | exact (def_tie_resp _ HS HM Hext Ht) ].
Qed.

(** ** Substitutions into a Definition Entry *)

(** A substitution into the assumption entry of a relevant type whose
    values at the left environments satisfy the tie is one into the
    definition entry. *)
Lemma rel_sub_under_ctx_into_def : forall {Γ Δ A} {i : nat} {M σ σ' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Δ ⊨ᵗ A ≈ A at i ->
    rel_type_relevant Δ A ->
    Δ ⊨ M : A ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▹ A ->
    (forall ρ ρσ, Dom ρ ≈ ρ ∈ env_relΓ -> ⟦ σ : Δ ▹ A ⟧s ρ ↘ ρσ -> def_tie A M ρσ) ->
    Γ ⊨ˢ σ ≈ σ' : Δ ▸ A ≔ M.
Proof.
  intros * HΓ HA HArel HM [env_relΓ' HΓ' env_relΔA HΔA Hσ Hσs] Htie.
  pose proof (rel_type_inversion_simple HA) as [env_relΔ [HΔ HAs]].
  pose proof (per_ctx_env_extend HΔ HAs) as HΔAc.
  pose proof (per_ctx_env_of_def_relevant HΔ HA (HArel _ HΔ) HM) as HΔd.
  pose proof (rel_type_inversion_simple_at HΔ HA) as HAat.
  pose proof (rel_exp_under_ctx_simple_at_of_relevant HΔ (HArel _ HΔ) HM) as HMat.
  assert (EΓ : env_relΓ' <~> env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (EΔ : env_relΔA <~> per_env_extend A A env_relΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (PER env_relΔ) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend A A env_relΔ)) by (eapply per_env_PER; eassumption).
  assert (PER (per_env_extend_def A M env_relΔ)) by (eapply per_env_PER; eassumption).
  (** The two contexts have the same entry types, so the same propositional
      entries. *)
  assert (Hsame : forall v x, x < List.length (Δ ▸ A ≔ M) ->
                    entry_propositional gc_deps gc_stack (Δ ▹ A) v x <->
                    entry_propositional gc_deps gc_stack (Δ ▸ A ≔ M) v x)
    by (intros v [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption).
  refine (mk_rel_sub_under_ctx _ _ _ _ env_relΓ' HΓ' (per_env_extend_def A M env_relΔ) HΔd _ Hσs).
  intros Γ'' env_rel'' HΓ'' φ Hφ Hφb ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ'' _ Hφ Hφb _ _ Hρ) as [v1 v2 v3 v4 Hw1 Hw2 Hw3 Hw4 Hchain].
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
  apply (mk_rel_sub v1 v2 v3 v4); [ | | | | exact Hc' ];
    (eapply (eval_sub_same_types (Δ1 := Δ ▹ A)); [ intros [| x]; reflexivity | reflexivity | intros [| x]; reflexivity | eassumption ]).
Qed.

(** [σ,,M[σ]] into [Δ ▸ A ≔ M], at a relevant type: the tie is the left
    commutation of [M] along [σ]. *)
Lemma rel_sub_under_ctx_extend_sub_def_relevant : forall {Γ Δ σ σ' A} {i : nat} {M M'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    rel_type_relevant Δ A ->
    Δ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Δ) M ->
    exp_scoped (List.length Δ) M' ->
    Γ ⊨ˢ σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HArel HM HMs HMs'.
  pose proof Hσj as [env_relΓ HΓ _ _ _ _].
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  eapply rel_sub_under_ctx_into_def; [ exact HΓ | exact HA | exact HArel | exact HMl | |].
  - exact (rel_sub_under_ctx_extend_sub Hσj HM HMs HMs').
  - intros ρ ρτ Hρ Hev.
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    destruct (eval_sub_extend_inv _ _ _ _ _ _ Hev) as [Hev1 Hev0].
    destruct HMl as [env_relΔ HΔ j HMgen].
    assert (Hτ : Dom ρτ↯ ≈ ρτ↯ ∈ env_relΔ)
      by (eapply (rel_sub_under_ctx_at' Hσσ HΓ HΔ); eassumption).
    destruct (head_not_propositional_of_relevant (e := ce_ass A) HΔ eq_refl HA HArel _ _ Hτ) as [Hnp _].
    specialize (Hev0 ltac:(rewrite entry_propositional_zero_head; exact Hnp)).
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Hρ Hev1 Hev1) as [R [Htyp Hexp]].
    apply (rel_exp_or_prop_relevant Htyp (HArel _ HΔ _ _ Hτ)) in Hexp.
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
    functional_eval_rewrite_clear.
    assert (Ha22 : DF a2 ≈ a2 ∈ per_univ_elem j ↘ R) by pairwise.
    eexists; split; [ eassumption |].
    eapply per_head_of; [ eassumption | eassumption | exact Ha22 | pairwise ].
Qed.

(** The same at a type of a universe. *)
Corollary rel_sub_under_ctx_extend_sub_def : forall {Γ Δ σ σ' A} {i : nat} {M M'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Δ) M ->
    exp_scoped (List.length Δ) M' ->
    Γ ⊨ˢ σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA.
  exact (rel_sub_under_ctx_extend_sub_def_relevant Hσj (rel_type_of_typ HA) (rel_type_relevant_of_typ HA)).
Qed.

(** [q σ] from [Γ ▸ A[σ] ≔ M[σ]] into [Δ ▸ A ≔ M], at a relevant type.
    The tie at [⟦q σ⟧ρ] is the tie at [ρ] moved along the left commutation
    of [M] at [σ], read at the tail [ρ↯]. *)
Lemma rel_sub_under_ctx_q_def_relevant : forall {Γ Δ σ σ' A} {i : nat} {M},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    rel_type_relevant Δ A ->
    Δ ⊨ M : A ->
    Γ ▸ A[σ] ≔ M[σ] ⊨ˢ q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA HArel HM.
  pose proof Hσj as [env_relΓ HΓ env_relΔ HΔ Hσ _].
  pose proof (per_ctx_env_of_def_sub_relevant HΓ Hσj HA HArel HM) as HΓd.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓa.
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  eapply rel_sub_under_ctx_into_def; [ exact HΓd | exact HA | exact HArel | exact HM | |].
  - eapply rel_sub_under_ctx_restrict;
      [ exact HΓd | exact HΓa | exact HΔA | exact HΔA
      | intros ? ? []; assumption | intros; assumption | cbn; lia | cbn; lia
      | intros ? ? _ ? _; reflexivity
      | exact (rel_sub_under_ctx_q Hσj HA) ].
  - intros ρ ρq Hρ Hev.
    destruct (eval_sub_q_inv _ _ _ _ _ Hev) as [Hev1 Hev0'].
    pose proof Hρ as [[Ht Hh _ _ _ _] [t [Ht0 Htie]] _].
    (** [σ] at the Kripke stage [↑], which relates [⟦σ[↑]ʷ⟧ρ] to
        [⟦σ⟧(ρ↯)]. *)
    pose proof (rel_wk_shift HΓ HΓd) as Hshift.
    destruct (Hσ _ _ HΓd _ Hshift (fun x Hx => ltac:(cbn; lia)) _ _ Hρ) as [x1 u u' x4 Hx1 Hu Hu' Hx4 Htails].
    rewrite ?eval_wk_shift in *.
    assert (Hqu : Dom ρq↯ ≈ u ∈ env_relΔ).
    { assert (Hxu : Dom x1 ≈ u ∈ env_relΔ) by pairwise.
      exact (per_ctx_env_resp_agree HΔ _ _ _ _ (functional_eval_sub _ _ _ _ _ Hx1 Hev1) (reflexivity _) Hxu). }
    assert (Huu : Dom u ≈ u ∈ env_relΔ) by pairwise.
    (** The head of the lifting is the environment's: [A] is no
        proposition. *)
    destruct (head_not_propositional_of_relevant (e := ce_ass A) HΔ eq_refl HA HArel _ _ Hqu) as [Hnp _].
    assert (Hev0 : ρq 0 = ρ 0)
      by (unfold env_var; rewrite (Hev0' ltac:(rewrite entry_propositional_zero_head; exact Hnp));
          destruct (env_entry ρ 0); reflexivity).
    (** [M] along [σ] at the tail. *)
    pose proof (rel_sub_under_ctx_refl_left Hσj) as Hσσ.
    pose proof HM as [env_relΔ' HΔ' j HMgen].
    destruct (HMgen _ _ HΓ _ _ Hσσ _ _ _ _ Ht Hu Hu) as [RN [Htyp Hexp]].
    apply (rel_exp_or_prop_relevant Htyp (HArel _ HΔ _ _ Huu)) in Hexp.
    destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
    destruct Hexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
    assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
    destruct (rel_exp_under_ctx_simple_at_of_relevant HΔ (HArel _ HΔ) HM _ _ Hqu) as [m [mu [Hm [Hmu Hmmu]]]].
    destruct (rel_type_inversion_simple_at HΔ HA _ _ Hqu) as [b [b' [Hb [Hb' [Rb HRb]]]]].
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

(** The same at a type of a universe. *)
Corollary rel_sub_under_ctx_q_def : forall {Γ Δ σ σ' A} {i : nat} {M},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Typeω@i ->
    Δ ⊨ M : A ->
    Γ ▸ A[σ] ≔ M[σ] ⊨ˢ q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA.
  exact (rel_sub_under_ctx_q_def_relevant Hσj (rel_type_of_typ HA) (rel_type_relevant_of_typ HA)).
Qed.

(** ** The Let Rules

    The instance [B[Id,,M]] against a [let] whose annotation [A'] is
    related to [A], whose body [B'] is related to [B] and whose definiens
    [M'] is related to [M].  The four values of the terms are
    [⟦B[σ,,M[σ]]⟧ρ], [⟦B[Id,,M]⟧ρσ], [⟦B'⟧(ρ'σ' ↦ ⟦M'⟧ρ'σ' ⦂ ⟦A'⟧ρ'σ')] and
    [⟦B'[q σ']⟧(ρ' ↦ ⟦M'[σ']⟧ρ' ⦂ ⟦A'[σ']⟧ρ')].

    - The first link comes from [B] along [σ,,M[σ]] and along [Id,,M], bridged
      by [B] at the two heads [⟦M[σ]⟧ρ] and [⟦M⟧ρσ].
    - The middle link is [B ≈ B'] at the substituted environments.
    - The last link comes from [B'] along [q σ'], bridged by [B'] at the tail
      [⟦q σ'⟧(ρ' ↦ ⟦M'[σ']⟧ρ' ⦂ ⟦A'[σ']⟧ρ')].

    The heads the [let] binds are stored at the values of the annotation,
    at which they read back, as related elements of its type do. *)
Lemma rel_exp_let_relevant : forall {Γ A A'} {i : nat} {M M' B B' C},
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ᵗ A ≈ A' at i ->
    rel_type_relevant Γ A ->
    Γ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Γ) M ->
    exp_scoped (List.length Γ) M' ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HA HAA' HArel HM HMs HMs' HB.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  pose proof (rel_exp_under_ctx_refl_left HB) as HBl.
  pose proof (rel_exp_under_ctx_refl_right HB) as HBr.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
  pose proof (HArel _ HΓ) as HArelΓ.
  pose proof (per_ctx_env_of_def_relevant HΓ HA HArelΓ HMl) as HΓd.
  pose proof (per_ctx_env_of_def_relevant HΓ HA HArelΓ HMr) as HΓd'.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  assert (PER (per_env_extend A A env_relΓ)) by (eapply per_env_PER; eassumption).
  (** [B'] in the context of the right-hand definiens. *)
  assert (HB'r : Γ ▸ A ≔ M' ⊨ B' ≈ B' : C)
    by (eapply rel_exp_under_ctx_restrict; [ exact HΓd' | exact HΓd | | cbn; lia | | exact HBr ];
        [ eapply per_ctx_env_def_conv_relevant;
          [ exact HA | exact HArel | exact (rel_exp_under_ctx_sym HM) | eassumption | eassumption ]
        | intros ? ? _ [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption ]).
  pose proof (rel_type_inversion_simple_at HΓ HA) as HAat.
  pose proof (rel_type_inversion_simple_at HΓ HAA') as HAA'at.
  pose proof (rel_exp_under_ctx_simple_at_of_relevant HΓ HArelΓ HMl) as HMlat.
  pose proof (rel_exp_under_ctx_simple_at_of_relevant HΓ HArelΓ HMr) as HMrat.
  (** Evaluation reads only the entry types. *)
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
  assert (Hρ'σ' : Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ) by solve_per.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_rel') by solve_per.
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Definientia

      The four values of [M ≈ M'] and the two inner values of [M] on the
      right, which the instances of [B] along [Id,,M] and [σ',,M[σ']] use. *)
  pose proof (HArelΓ _ _ Hρσ) as HArelρσ.
  destruct (head_not_propositional_of_relevant (e := ce_def A M) HΓ eq_refl HA HArel _ _ Hρσ) as [Hnp2 Hnp3].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  pose proof HM as [? ? j HMgen].
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  apply (rel_exp_or_prop_relevant HNtyp HArelρσ) in HNexp.
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  pose proof HMl as [? ? jl HMlgen].
  destruct (HMlgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RNl [HNltyp HNlexp]].
  apply (rel_exp_or_prop_relevant HNltyp HArelρσ) in HNlexp.
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
  assert (Hn33 : Dom n3 ≈ n3 ∈ RN) by pairwise.
  assert (Hn44 : Dom n4 ≈ n4 ∈ RN) by pairwise.
  (** *** The Annotation

      [A'] at the two environments the [let] is evaluated at: relevant, as
      [A] is, and the definientia read back at its values. *)
  destruct (HAA'at _ _ Hρ'σ') as (b3 & b3' & Hb3 & Hb3' & [RA3 HRA3]).
  destruct (rel_type_sub_simple HΓ' Hσ'σ' HAA' _ _ Hρ'ρ') as (b4 & b4' & Hb4 & Hb4' & [RA4 HRA4]).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (b4 = a4) as -> by (eapply functional_eval_exp; eassumption).
  assert (ERA3 : RN <~> RA3) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRA3).
  assert (ERA4 : RN <~> RA4) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha44 HRA4).
  assert (Er3 : domain_relevance b3' = relevant).
  { destruct (HArelΓ _ _ Hρ'σ') as (a0 & Ea0 & Er0).
    assert (a0 = a3) as -> by (eapply functional_eval_exp; eassumption).
    rewrite <- (per_univ_elem_relevance _ _ _ _ HRA3); exact Er0. }
  assert (Er4 : domain_relevance b4' = relevant).
  { destruct (rel_type_sub_relevant HΓ' Hσ'σ' HA HArel _ _ Hρ'ρ') as (a0 & Ea0 & Er0).
    assert (a0 = a4) as -> by (eapply functional_eval_exp; eassumption).
    rewrite <- (per_univ_elem_relevance _ _ _ _ HRA4); exact Er0. }
  assert (Hrd3 : entry_readable (de_term n3 (entry_type_value b3')))
    by exact (proj2 (entry_readable_of_elem HRA3 (proj1 (ERA3 _ _) Hn33))).
  assert (Hrd4 : entry_readable (de_term n4 (entry_type_value b4')))
    by exact (proj2 (entry_readable_of_elem HRA4 (proj1 (ERA4 _ _) Hn44))).
  (** *** The Instance

      [B] along [σ,,M[σ]] gives the outer values of the type and the first
      value of the term, and [B] along [Id,,M] at the substituted environments
      gives the inner values of the type and the second value of the term. *)
  pose proof (rel_sub_under_ctx_extend_sub_def_relevant Hσj HA HArel HMl HMs HMs) as Hτ.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend _ _ _ _ _ _ _ Hev Hnp2 Hn1) (eval_sub_extend _ _ _ _ _ _ _ Hev' Hnp3 Hn4m))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  rewrite <- exp_sub_extend_sub in Hc1, Hc4.
  pose proof (rel_sub_under_ctx_extend_sub_def_relevant (rel_sub_id (ex_intro _ _ HΓ)) HA HArel HMl HMs HMs) as HidM.
  rewrite exp_sub_id in HidM.
  (** [Id,,M] evaluates to the extensions of the retagged environments;
      the instance is read at the extensions of [ρσ] and [ρ'σ'] themselves
      ([rel_exp_body_of_retagged]). *)
  destruct (head_not_propositional_of_relevant (e := ce_def A M) HΓ eq_refl HA HArel _ _ (per_ctx_env_retag HΓ _ _ Hρσ))
    as [Hnp2r Hnp3r].
  assert (PER RNl) by (eapply per_elem_PER; exact Ha23l).
  assert (HId2 : Dom ρσ ↦ n2 ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρ'σ' ↦ n3m ⦂ centry_tag (ce_def A M) Γ ρ'σ'
                   ∈ per_env_extend_def A M env_relΓ).
  { assert (Hh : Dom n2 ≈ n3m ∈ per_head A A ρσ ρ'σ')
      by (eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23l | pairwise ]).
    destruct (per_head_closure_readable HΓA HΓ Hρσ Hh) as [Hr2 Hr3].
    eapply (per_env_extend_def_intro _ HAat HMlat Hρσ); [ exact Hh | exact Hr2 | exact Hr3 | exact Hn2 | ].
    eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23l | pairwise ]. }
  destruct (rel_exp_body_of_retagged HΓd HBlgen _ _ HΓ _ _ HidM ρσ ρ'σ'
              (ρσ ↦ n2 ⦂ centry_tag (ce_def A M) Γ ρσ) (ρ'σ' ↦ n3m ⦂ centry_tag (ce_def A M) Γ ρ'σ') Hρσ
              (eval_sub_extend _ _ _ _ _ _ _ Hid2 Hnp2r Hn2)
              (eval_sub_extend _ _ _ _ _ _ _ Hid3 Hnp3r Hn3m) HId2)
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  (** *** The Bridges at the Substituted Environments

      [B] at the two heads [⟦M[σ]⟧ρ] and [⟦M⟧ρσ], and [B ≈ B'] at the
      substituted pair. *)
  assert (HY1 : Dom ρσ ↦ n1 ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρσ ↦ n2 ⦂ centry_tag (ce_def A M) Γ ρσ
                  ∈ per_env_extend_def A M env_relΓ).
  { assert (Hρσρσ : Dom ρσ ≈ ρσ ∈ env_relΓ) by solve_per.
    assert (Hh : Dom n1 ≈ n2 ∈ per_head A A ρσ ρσ)
      by (eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | exact Hn12 ]).
    destruct (per_head_closure_readable HΓA HΓ Hρσρσ Hh) as [Hr1 Hr2].
    eapply (per_env_extend_def_intro _ HAat HMlat Hρσρσ); [ exact Hh | exact Hr1 | exact Hr2 | exact Hn2 | ].
    eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 | symmetry; exact Hn12 ]. }
  assert (HX1 : Dom ρσ ↦ n2 ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρ'σ' ↦ n3 ⦂ entry_type_value b3'
                  ∈ per_env_extend_def A M env_relΓ).
  { assert (Hh : Dom n2 ≈ n3 ∈ per_head A A ρσ ρ'σ')
      by (eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23 | exact Hn23 ]).
    eapply (per_env_extend_def_intro _ HAat HMlat Hρσ);
      [ exact Hh | exact (proj1 (per_head_closure_readable HΓA HΓ Hρσ Hh)) | exact Hrd3 | exact Hn2 | ].
    eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Ha23 | solve_per ]. }
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY HYd]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ' ↦ ⟦M'[σ']⟧ρ'], whose inner value [⟦B'⟧(s ↦ ⟦M'[σ']⟧ρ')]
      is bridged to [⟦B'⟧(ρ'σ' ↦ ⟦M'⟧ρ'σ')] by [B'] itself. *)
  pose proof (per_ctx_env_of_def_sub_relevant HΓ' Hσ'σ' HA HArel HMr) as HΓ'd.
  pose proof (rel_sub_under_ctx_q_def_relevant Hσ'σ' HA HArel HMr) as Hq.
  pose proof (rel_type_sub_simple HΓ' Hσ'σ' HA) as HAσ'.
  pose proof (rel_exp_under_ctx_sub_simple_relevant HΓ' Hσ'σ' HArel HMr) as HMσ'.
  assert (Hpair : Dom ρ' ↦ n4 ⦂ entry_type_value b4' ≈ ρ' ↦ n4 ⦂ entry_type_value b4'
                    ∈ per_env_extend_def A[σ'] M'[σ'] env_rel').
  { eapply (per_env_extend_def_intro _ HAσ' HMσ' Hρ'ρ'); [ | exact Hrd4 | exact Hrd4 | exact Hn4 | ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ].
    - eapply per_head_of; [ exact Ha4 | exact Ha4 | exact Ha44 | exact Hn44 ]. }
  assert (Hts : args_readable_at n4 n4 ([entry_type_value b4'; entry_type_value b4'; entry_type_value b4'; entry_type_value b4']))
    by (repeat constructor; exact Hrd4).
  destruct (rel_sub_under_ctx_q_at HΓ' HΓA Hσ'σ' HA _ _ _ _ _ _ _ _ _ _ (per_env_extend_def_ext _ _ _ _ _ Hpair) Hts Hev' Hev')
    as [s [s' [Hqs [Hqs' Hqchain]]]].
  apply (eval_sub_same_types (Htya M') eq_refl ltac:(intros [| x]; reflexivity)) in Hqs.
  destruct (HB'gen _ _ HΓ'd _ _ Hq _ _ _ _ Hpair Hqs Hqs) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (Hsq : Dom ρ'σ' ↦ n4 ⦂ entry_type_value b4' ≈ s ↦ n4 ⦂ centry_tag (ce_ass A) Γ s ∈ per_env_extend A A env_relΓ)
    by pairwise.
  destruct Hsq as [Hts' _ _ _ _ _].
  change (Dom ρ'σ' ≈ s ∈ env_relΓ) in Hts'.
  destruct (HAat _ _ Hts') as [b3x [bs [Hb3x [Hbs [Rs HRs]]]]].
  assert (b3x = a3) as -> by (eapply functional_eval_exp; eassumption).
  assert (ERs : RN <~> Rs) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Ha33 HRs).
  assert (HZ1 : Dom ρ'σ' ↦ n3 ⦂ entry_type_value b3' ≈ s ↦ n4 ⦂ centry_tag (ce_ass A) Γ s
                  ∈ per_env_extend_def A M' env_relΓ).
  { assert (Hh : Dom n3 ≈ n4 ∈ per_head A A ρ'σ' s)
      by (eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; exact Hn34 ]).
    eapply (per_env_extend_def_intro _ HAat HMrat Hts');
      [ exact Hh | exact Hrd3 | exact (proj2 (per_head_closure_readable HΓA HΓ Hts' Hh)) | exact Hn3 | ].
    eapply per_head_of; [ exact Ha3 | exact Hbs | exact HRs | apply ERs; solve_per ]. }
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
  (** The [let] on the right binds the value of its definiens, at the
      value of its annotation, which is relevant. *)
  assert (Hlet3 : ⟦ ℓ A' ≔ M' in B' ⟧ ρ'σ' ↘ bx2)
    by (eapply eval_exp_let; [ exact Hb3' | exact Er3 | exact Hn3 | exact Hbx2 ]).
  assert (Hlet4 : ⟦ (ℓ A' ≔ M' in B')[σ'] ⟧ ρ' ↘ v4)
    by (simpl; eapply eval_exp_let; [ exact Hb4' | exact Er4 | exact Hn4 | exact Hv4 ]).
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
  pose proof Hσj as [env_relΓ HΓ env_relΔA HΔA _ _].
  pose proof (rel_type_inversion_simple (rel_type_of_prop 0 HA)) as [env_relΔ [HΔ HAs]].
  pose proof (per_ctx_env_extend HΔ HAs) as HΔAc.
  pose proof (per_ctx_env_of_def_prop (M := M) HΔ HA) as HΔd.
  eapply rel_sub_under_ctx_restrict;
    [ exact HΓ | exact HΓ | exact HΔAc | exact HΔd | intros; assumption | intros; assumption | cbn; lia | lia
    | intros ? ? _ [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption | exact Hσj ].
Qed.

(** A lifted substitution into a definition of a proposition: the source
    context PER is that of the lifted assumption, the head a proof. *)
Lemma rel_sub_under_ctx_q_def_prop : forall {Γ Δ σ σ' A M},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ A : Propₘ ->
    Γ ▸ A[σ] ≔ M[σ] ⊨ˢ q σ ≈ q σ' : Δ ▸ A ≔ M.
Proof.
  intros * Hσj HA.
  pose proof Hσj as [RΓ HΓ _ _ _ _].
  pose proof (rel_sub_under_ctx_q Hσj (rel_type_of_prop 0 HA)) as Hq.
  pose proof Hq as [_ _ S HS _ _].
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj (rel_type_of_prop 0 HA)) as HΓB.
  pose proof (per_ctx_env_of_def_prop_at (M := M[σ]) HΓ (rel_exp_of_prop_sub_simple HΓ Hσj HA)) as HΓBd.
  apply (rel_sub_under_ctx_into_def_prop HA).
  exact (rel_sub_under_ctx_restrict HΓBd HΓB HS HS (fun _ _ H => H) (fun _ _ H => H) (le_n _) (le_n _)
           (fun _ _ _ _ _ => iff_refl _) Hq).
Qed.

(** The [let] rules at a proposition.  Each side binds its definiens kept
    as a proof: [⋆ᵈ⟨M[σ], ρ⟩] and [⋆ᵈ⟨M, ρσ⟩] in the two instances,
    [⋆ᵈ⟨M', ρ'σ'⟩] and [⋆ᵈ⟨M'[σ'], ρ'⟩] in the two values of the [let].
    These read back, as their terms are scoped by the contexts, so any two
    are related at the head of the proposition.  No definiens is evaluated.
    The shape is that of [rel_exp_let_relevant], with the heads related by
    proof irrelevance instead of the definientia. *)
Lemma rel_exp_let_prop : forall {Γ A A'} {M M' B B' C},
    Γ ⊨ A : Propₘ ->
    Γ ⊨ A ≈ A' : Propₘ ->
    Γ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Γ) M ->
    exp_scoped (List.length Γ) M' ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HA HAA' HM HMs HMs' HB.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
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
    by (eapply rel_exp_under_ctx_restrict; [ exact HΓd' | exact HΓd | intros; assumption | cbn; lia
        | intros ? ? _ [| x] _; split; intros [T HT E HE a Ea Hp]; econstructor; eassumption | exact HBr ]).
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
  assert (Hρ'σ' : Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ) by solve_per.
  assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_rel') by solve_per.
  pose proof (rel_sub_under_ctx_refl_right Hσj) as Hσ'σ'.
  (** *** The Kept Proofs

      The definientia, substituted, are scoped by [Γ'], so the four proofs
      read back. *)
  pose proof Hσj as [? _ ? _ _ Hσs].
  assert (HMσ : exp_scoped (List.length Γ') M[σ])
    by (eapply exp_scoped_sub; [ exact HMs | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
  assert (HM'σ' : exp_scoped (List.length Γ') M'[σ'])
    by (eapply exp_scoped_sub; [ exact HMs' | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  destruct (per_ctx_env_kept_proof_readable _ _ _ M[σ] HΓ' (exp_scoped_free_bound _ _ HMσ) _ _ Hρ) as [Rp1 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ M'[σ'] HΓ' (exp_scoped_free_bound _ _ HM'σ') _ _ Hρ) as [_ Rp4].
  destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓ (exp_scoped_free_bound _ _ HMs) _ _ Hρσ) as [Rp2 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ M' HΓ (exp_scoped_free_bound _ _ HMs') _ _ Hρσ) as [_ Rp3].
  (** *** The Heads

      [A] is a proposition at the substituted environments, so every
      extension along a definition of it binds [⋆ᵈ]. *)
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HA _ _ Hρσ) as (a2 & a3 & Ha2 & Ha3 & [Hl2 Hr3 _]).
  assert (Hp : forall e, ctx_entry_type (e :: nil) 0 = Some A ->
                 head_propositional gc_deps gc_stack e Γ ρσ /\ head_propositional gc_deps gc_stack e Γ ρ'σ')
    by (intros e He; split;
        [ apply (proj2 (head_propositional_iff HΓ He HAs Hρσ Ha2)); exact Hl2
        | apply (proj2 (head_propositional_iff_right HΓ He HAs Hρσ Ha3)); exact Hr3 ]).
  destruct (Hp (ce_def A M) eq_refl) as [Hh2 Hh3].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  (** *** The Annotation

      [A'] at the two environments the [let] is evaluated at: a
      proposition, at whose values the kept proofs read back. *)
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HAA' _ _ Hρ'σ') as (b3 & b3' & Hb3 & Hb3' & Hb3p).
  assert (Hb3p' : Dom b3' ≈ b3' ∈ per_prop) by (etransitivity; [ symmetry |]; exact Hb3p).
  pose proof (rel_exp_of_prop_inversion HAA') as [env_relΓ6 [HΓ6 HAA'gen]].
  destruct (HAA'gen _ _ HΓ' _ _ Hσ'σ' _ _ _ _ Hρ'ρ' Hev' Hev') as [b1 b2 bb3 b4 Hb1 Hb2 Hbb3 Hb4 Hbchain].
  assert (Hb4p : Dom b4 ≈ b4 ∈ per_prop) by pairwise.
  assert (Hrd3 : entry_readable (de_term ⋆ᵈ⟨M', ρ'σ'⟩ (entry_type_value b3')))
    by exact (proj1 (entry_readable_of_elem (per_univ_elem_of_prop 0 _ _ Hb3p') (conj Rp3 Rp3))).
  assert (Hrd4 : entry_readable (de_term ⋆ᵈ⟨M'[σ'], ρ'⟩ (entry_type_value b4)))
    by exact (proj1 (entry_readable_of_elem (per_univ_elem_of_prop 0 _ _ Hb4p) (conj Rp4 Rp4))).
  (** *** The Instances

      [B] along [σ,,M[σ]] gives the outer values of the type and the first
      value of the term, and [B] along [Id,,M] at the substituted environments
      gives the inner values of the type and the second value of the term. *)
  pose proof (rel_sub_under_ctx_into_def_prop (M := M) HA (rel_sub_under_ctx_extend_sub Hσj HMl HMs HMs)) as Hτ.
  destruct (HBlgen _ _ HΓ' _ _ Hτ _ _ _ _ Hρ
              (eval_sub_extend_proof _ _ _ _ _ _ Hev Hh2) (eval_sub_extend_proof _ _ _ _ _ _ Hev' Hh3))
    as [R1 [HI1t HI1e]].
  pose proof HI1t as [c1 cA2 cA3 c4 Hc1 HcA2 HcA3 Hc4 Hc1chain].
  rewrite <- exp_sub_extend_sub in Hc1, Hc4.
  pose proof (rel_sub_under_ctx_into_def_prop (M := M) HA
                (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HMl HMs HMs)) as HidM.
  rewrite exp_sub_id in HidM.
  (** [Id,,M] evaluates to the extensions of the retagged environments;
      the instance is read at the extensions of [ρσ] and [ρ'σ'] themselves
      ([rel_exp_body_of_retagged]). *)
  pose proof (per_ctx_env_retag HΓ _ _ Hρσ) as Hρσr.
  destruct (rel_exp_of_prop_inversion_simple_at HΓ HA _ _ Hρσr) as (a2r & a3r & Ha2r & Ha3r & [Hl2r Hr3r _]).
  assert (Hh2r : head_propositional gc_deps gc_stack (ce_def A M) Γ (ctx_retag Γ ρσ))
    by (apply (proj2 (head_propositional_iff (e := ce_def A M) HΓ eq_refl HAs Hρσr Ha2r)); exact Hl2r).
  assert (Hh3r : head_propositional gc_deps gc_stack (ce_def A M) Γ (ctx_retag Γ ρ'σ'))
    by (apply (proj2 (head_propositional_iff_right (e := ce_def A M) HΓ eq_refl HAs Hρσr Ha3r)); exact Hr3r).
  destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓ (exp_scoped_free_bound _ _ HMs) _ _ Hρσ) as [_ Rp2'].
  assert (HId2 : Dom ρσ ↦ ⋆ᵈ⟨M, ρσ⟩ ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρ'σ' ↦ ⋆ᵈ⟨M, ρ'σ'⟩ ⦂ centry_tag (ce_def A M) Γ ρ'σ'
                   ∈ per_env_extend A A env_relΓ)
    by exact (per_env_extend_intro_tagged HΓA HΓ Hρσ (per_head_proof Ha2 Hl2 Rp2 Rp2')).
  destruct (rel_exp_body_of_retagged HΓd HBlgen _ _ HΓ _ _ HidM ρσ ρ'σ'
              (ρσ ↦ ⋆ᵈ⟨M, ρσ⟩ ⦂ centry_tag (ce_def A M) Γ ρσ) (ρ'σ' ↦ ⋆ᵈ⟨M, ρ'σ'⟩ ⦂ centry_tag (ce_def A M) Γ ρ'σ') Hρσ
              (eval_sub_extend_proof _ _ _ _ _ _ Hid2 Hh2r) (eval_sub_extend_proof _ _ _ _ _ _ Hid3 Hh3r) HId2)
    as [R2 [HI2t HI2e]].
  pose proof HI2t as [c2 cB2 cB3 c3 Hc2 HcB2 HcB3 Hc3 Hc2chain].
  (** *** The Bridges at the Substituted Environments

      [B] at the two kept proofs [⋆ᵈ⟨M[σ], ρ⟩] and [⋆ᵈ⟨M, ρσ⟩], and
      [B ≈ B'] at the substituted pair. *)
  assert (Hρσρσ : Dom ρσ ≈ ρσ ∈ env_relΓ) by solve_per.
  assert (HY1 : Dom ρσ ↦ ⋆ᵈ⟨M[σ], ρ⟩ ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρσ ↦ ⋆ᵈ⟨M, ρσ⟩ ⦂ centry_tag (ce_def A M) Γ ρσ
                  ∈ per_env_extend A A env_relΓ)
    by exact (per_env_extend_intro_tagged HΓA HΓ Hρσρσ (per_head_proof Ha2 Hl2 Rp1 Rp2)).
  assert (HX1 : Dom ρσ ↦ ⋆ᵈ⟨M, ρσ⟩ ⦂ centry_tag (ce_def A M) Γ ρσ ≈ ρ'σ' ↦ ⋆ᵈ⟨M', ρ'σ'⟩ ⦂ entry_type_value b3'
                  ∈ per_env_extend A A env_relΓ).
  { pose proof (per_head_proof (S' := A) (ρ' := ρ'σ') Ha2 Hl2 Rp2 Rp3) as Hh.
    exact (per_env_extend_intro' Hρσ Hh (proj1 (per_head_closure_readable HΓA HΓ Hρσ Hh)) Hrd3). }
  destruct (HY _ _ HY1) as [cy1 [cy2 [RY [Hcy1 [Hcy2 [HRY HYd]]]]]].
  destruct (HX _ _ HX1) as [cx1 [cx2 [RX [Hcx1 [Hcx2 [HRX HXd]]]]]].
  (** *** The Right Commutation

      [B'] along [q σ'] at [ρ' ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩], whose inner value
      [⟦B'⟧(s ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩)] is bridged to [⟦B'⟧(ρ'σ' ↦ ⋆ᵈ⟨M', ρ'σ'⟩)]
      by [B'] itself. *)
  pose proof (per_ctx_env_of_typ_sub HΓ' Hσ'σ' (rel_type_of_prop 0 HA)) as HΓ'a.
  pose proof (rel_sub_under_ctx_into_def_prop (M := M') HA (rel_sub_under_ctx_q Hσ'σ' (rel_type_of_prop 0 HA))) as Hq.
  pose proof (rel_exp_of_prop_inversion HA) as [env_relΓ5 [HΓ5 HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσ'σ' _ _ _ _ Hρ'ρ' Hev' Hev') as [a1' a2' a3' a4' Ha1' Ha2' Ha3' Ha4' Hachain'].
  assert (Ha4p : Dom a4' ≈ a4' ∈ per_prop) by pairwise.
  assert (Hpair : Dom ρ' ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩ ⦂ entry_type_value b4 ≈ ρ' ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩ ⦂ entry_type_value b4
                    ∈ per_env_extend A[σ'] A[σ'] env_rel')
    by (apply per_env_extend_intro';
        [ exact Hρ'ρ' | eapply per_head_proof; [ exact Ha4' | exact (per_prop_left _ _ Ha4p) | exact Rp4 | exact Rp4 ]
        | exact Hrd4 | exact Hrd4 ]).
  assert (Hts : args_readable_at ⋆ᵈ⟨M'[σ'], ρ'⟩ ⋆ᵈ⟨M'[σ'], ρ'⟩
                  ([entry_type_value b4; entry_type_value b4; entry_type_value b4; entry_type_value b4]))
    by (repeat constructor; exact Hrd4).
  destruct (rel_sub_under_ctx_q_at HΓ' HΓA Hσ'σ' (rel_type_of_prop 0 HA) _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev' Hev')
    as [s [s' [Hqs [Hqs' Hqchain]]]].
  apply (eval_sub_same_types (Htya M') eq_refl ltac:(intros [| x]; reflexivity)) in Hqs.
  destruct (HB'gen _ _ HΓ'a _ _ Hq _ _ _ _ Hpair Hqs Hqs) as [R3 [HI3t HI3e]].
  pose proof HI3t as [e1 e2 e3 e4 He1 He2 He3 He4 He1chain].
  assert (Hsq : Dom ρ'σ' ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩ ⦂ entry_type_value b4 ≈ s ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩ ⦂ centry_tag (ce_ass A) Γ s
                  ∈ per_env_extend A A env_relΓ) by pairwise.
  destruct Hsq as [Hts' _ _ _ _ _].
  change (Dom ρ'σ' ≈ s ∈ env_relΓ) in Hts'.
  assert (HZ1 : Dom ρ'σ' ↦ ⋆ᵈ⟨M', ρ'σ'⟩ ⦂ entry_type_value b3' ≈ s ↦ ⋆ᵈ⟨M'[σ'], ρ'⟩ ⦂ centry_tag (ce_ass A) Γ s
                  ∈ per_env_extend A A env_relΓ).
  { pose proof (per_head_proof (S' := A) (ρ' := s) Ha3 Hr3 Rp3 Rp4) as Hh.
    exact (per_env_extend_intro' Hts' Hh Hrd3 (proj2 (per_head_closure_readable HΓA HΓ Hts' Hh))). }
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
  (** The [let] on the right keeps its definiens as a proof, at the value
      of its annotation, which is a proposition. *)
  assert (Hlet3 : ⟦ ℓ A' ≔ M' in B' ⟧ ρ'σ' ↘ bx2)
    by (eapply eval_exp_let_proof; [ exact Hb3' | exact (per_prop_left _ _ Hb3p') | exact Hbx2 ]).
  assert (Hlet4 : ⟦ (ℓ A' ≔ M' in B')[σ'] ⟧ ρ' ↘ v4)
    by (simpl; eapply eval_exp_let_proof; [ exact Hb4 | exact (per_prop_left _ _ Hb4p) | exact Hv4 ]).
  apply (mk_rel_exp w1 w2 bx2 v4); try eassumption.
  apply rel_chain_4; solve_per.
Qed.

(** The two together: a definition of a type of any sort. *)
Corollary rel_exp_let_any_sort : forall {Γ A A' S} {M M' B B' C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ A ≈ A' : S ->
    Γ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Γ) M ->
    exp_scoped (List.length Γ) M' ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ B[Id,,M] ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * [i | |] HA HAA' HM HMs HMs' HB.
  - exact (rel_exp_let_relevant (rel_type_of_typ HA) (rel_type_of_typ HAA') (rel_type_relevant_of_typ HA)
             HM HMs HMs' HB).
  - exact (rel_exp_let_prop HA HAA' HM HMs HMs' HB).
  - exact (rel_exp_let_relevant (rel_type_of_level_sort 0 HA) (rel_type_of_level_sort 0 HAA')
             (rel_type_relevant_of_level_sort HA) HM HMs HMs' HB).
Qed.

(** [ζ]. *)
Corollary rel_exp_under_ctx_let_zeta : forall {Γ A S} {M B C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    exp_scoped (List.length Γ) M ->
    Γ ▸ A ≔ M ⊨ B : C ->
    Γ ⊨ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M].
Proof.
  intros * HS HA HM HMs HB.
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_any_sort HS HA HA HM HMs HMs HB).
Qed.

Hint Resolve rel_exp_under_ctx_let_zeta : mctt.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M] ).
Proof. intros * HA HS HM HB HMs; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_zeta HS HA HM HMs HB) ]. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Congruence: both sides are related to the instance [B[Id,,M]]. *)
Corollary rel_exp_under_ctx_let_cong : forall {Γ A A' S} {M M' B B' C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ A ≈ A' : S ->
    Γ ⊨ M ≈ M' : A ->
    exp_scoped (List.length Γ) M ->
    exp_scoped (List.length Γ) M' ->
    Γ ▸ A ≔ M ⊨ B ≈ B' : C ->
    Γ ⊨ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M].
Proof.
  intros * HS HA HAA' HM HMs HMs' HB.
  eapply rel_exp_under_ctx_trans; [| exact (rel_exp_let_any_sort HS HA HAA' HM HMs HMs' HB) ].
  apply rel_exp_under_ctx_sym.
  exact (rel_exp_let_any_sort HS HA HA (rel_exp_under_ctx_refl_left HM) HMs HMs (rel_exp_under_ctx_refl_left HB)).
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
     exp_scoped (List.length Γ) M ->
     exp_scoped (List.length Γ) M' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓ A ≔ M in B ≈ ℓ A' ≔ M' in B' : C[Id,,M] ).
Proof.
  intros * HA HS HAA' _ HM HB HMs HMs'; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_cong HS HA HAA' HM HMs HMs' HB) ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary valid_exp_under_ctx_let : forall {Γ A S} {M B C},
    type_sort S ->
    Γ ⊨ A : S ->
    Γ ⊨ M : A ->
    exp_scoped (List.length Γ) M ->
    Γ ▸ A ≔ M ⊨ B : C ->
    Γ ⊨ ℓ A ≔ M in B : C[Id,,M].
Proof.
  intros * HS HA HM HMs HB.
  exact (rel_exp_under_ctx_let_cong HS HA HA HM HMs HMs HB).
Qed.

Hint Resolve valid_exp_under_ctx_let : mctt.

End Fixed_GCtx.

Lemma sem_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓ A ≔ M in B : C[Id,,M] ).
Proof. intros * HA HS HM HB HMs; sem_intro; [ assumption | exact (valid_exp_under_ctx_let HS HA HM HMs HB) ]. Qed.

#[export]
Hint Resolve rel_exp_under_ctx_let_zeta rel_exp_under_ctx_let_cong valid_exp_under_ctx_let : mctt.
