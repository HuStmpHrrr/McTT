(** * Completeness of Normalization by Evaluation

    The fundamental theorem instantiated at the identity substitution and the
    initial environment, where only the inner two values of each chain of
    [rel_exp_under_ctx] are used. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.

(** A semantic equality read at the initial environment of its own context. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The values of two terms at the value [a] of their type, related by
    [elem_rel]: at a proposition nothing is asked of them, as proofs are
    never evaluated. *)
Inductive initial_env_term_values (ρ : env) (M M' : exp) (a : domain) (elem_rel : relation domain) : Prop :=
(** At a proposition: no values *)
| initial_env_term_values_proof :
    domain_relevance a = propositional ->
    initial_env_term_values ρ M M' a elem_rel
(** Otherwise: both terms evaluate, to related values *)
| initial_env_term_values_related : forall m m',
    ⟦ M ⟧ ρ ↘ m ->
    ⟦ M' ⟧ ρ ↘ m' ->
    Dom m ≈ m' ∈ elem_rel ->
    initial_env_term_values ρ M M' a elem_rel.

(** A semantic equality [Γ ⊨ M ≈ M' : A] read at the initial environment
    of [Γ]. *)
#[warnings="-cannot-define-projection"]
Record initial_env_values (Γ : ctx) (M M' A : exp) : Prop := mk_initial_env_values
  { (** The initial environment of [Γ] *)
    initial_env_values_env : env
    (** The universe level of the type *)
  ; initial_env_values_level : nat
    (** The relation of the type's elements *)
  ; initial_env_values_elem_rel : relation domain
    (** The value of the type *)
  ; initial_env_values_type : domain
    (** It is the initial environment *)
  ; initial_env_values_init : initial_env_f Γ initial_env_values_env
    (** The type evaluates there *)
  ; initial_env_values_eval_type : ⟦ A ⟧ initial_env_values_env ↘ initial_env_values_type
    (** Its value is a type of the universe, with that element relation *)
  ; initial_env_values_per : DF initial_env_values_type ≈ initial_env_values_type
      ∈ per_univ_elem initial_env_values_level ↘ initial_env_values_elem_rel
    (** The terms' values, if the type is relevant *)
  ; initial_env_values_terms : initial_env_term_values initial_env_values_env M M'
      initial_env_values_type initial_env_values_elem_rel }.

Lemma rel_exp_under_ctx_at_initial_env : forall {Γ A M M'},
    Γ ⊨ M ≈ M' : A ->
    initial_env_values Γ M M' A.
Proof.
  intros * H.
  destruct H as [env_relΓ HΓ i HMgen].
  pose proof (per_ctx_then_per_env_initial_env HΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  pose proof (proj1 (per_ctx_env_proofs _ _ _ HΓ _ _ Hrel)) as Hpf.
  destruct (HMgen _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hrel
                  (eval_sub_id _ _ Hpf) (eval_sub_id _ _ Hpf)) as [elem_rel [Htyp Hexp]].
  pose proof (rel_typ_elem_PER Htyp) as HPER.
  pose proof Htyp as Htyp0.
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  assert (a3 = a2) as -> by (eapply functional_eval_exp; eassumption).
  apply (mk_initial_env_values _ _ _ _ ρ i elem_rel a2); try eassumption; [ pairwise |].
  destruct Hexp as [Hp | Hexp].
  - apply initial_env_term_values_proof.
    destruct (rel_typ_prop_any Htyp0 (or_introl Hp)) as (_ & (c & Ec & Hc) & _).
    functional_eval_rewrite_clear; exact Hc.
  - destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
    apply (initial_env_term_values_related _ _ _ _ _ m2 m3); try eassumption; pairwise.
Qed.

(** The same at a type equality, where the element relation is [per_univ i]. *)
Lemma rel_typ_under_ctx_at_initial_env : forall {Γ A A'} {i : nat},
    Γ ⊨ A ≈ A' : Typeω@i ->
    exists ρ a a',
      initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * H%rel_exp_of_typ_inversion_simple.
  destruct H as [env_relΓ [HΓ HA]].
  pose proof (per_ctx_then_per_env_initial_env HΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HA _ _ Hrel) as [a [a' [Ha [Ha' Haa']]]].
  exists ρ, a, a'.
  repeat apply conj; eassumption.
Qed.

(** The same at a semantic type equality ([⊨ᵗ]), of either sort. *)
Lemma rel_type_under_ctx_at_initial_env : forall {Γ A A'} {i : nat},
    Γ ⊨ᵗ A ≈ A' at i ->
    exists ρ a a',
      initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * [env_relΓ HΓ Hgen].
  pose proof (per_ctx_then_per_env_initial_env HΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  pose proof (proj1 (per_ctx_env_proofs _ _ _ HΓ _ _ Hrel)) as Hpf.
  destruct (Hgen _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hrel
                 (eval_sub_id _ _ Hpf) (eval_sub_id _ _ Hpf)) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  exists ρ, a2, a3; repeat apply conj; try eassumption; pairwise.
Qed.

(** A type equality at a sort, read at the initial environment: the two
    values are related in a universe ([rel_type_of_sort]). *)
Lemma rel_typ_sort_at_initial_env : forall {Γ A A' Srt},
    type_sort Srt ->
    Γ ⊢ A ≈ A' : Srt ->
    exists ρ a a' (i : nat),
      initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HS H.
  destruct (rel_type_of_sort HS (completeness_fundamental_exp_eq _ _ _ _ H)) as [i Hi].
  destruct (rel_type_under_ctx_at_initial_env Hi) as (ρ & a & a' & ?).
  exists ρ, a, a', i; assumption.
Qed.

End Fixed_GCtx.

(** Equal terms have the same normal form: the semantic equality of
    [completeness_fundamental], read at the identity embedding and at the
    initial environment. *)
Theorem completeness : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    exists W, nbe Θ Ξ Γ M A W /\ nbe Θ Ξ Γ M' A W.
Proof.
  intros * H.
  pose proof (proj1 (proj2 (proj2 completeness_fundamental)) _ _ _ _ _ _ H) as HK.
  pose proof (sem_exp_eq_at_rel (HK _ _ (valid_gctx_embedding_refl _ _ (ctx_wf_gctx _ _ _ (presup_exp_eq_ctx H))))) as Hrel.
  destruct (@rel_exp_under_ctx_at_initial_env (gc_mk Θ Ξ) _ _ _ _ Hrel)
    as [ρ i elem_rel a Hρ Ha Htyp [Hp | m m' Hm Hm' Hrel']].
  (** A proof: [⋆ⁿ], neither term evaluated *)
  - exists ⋆ⁿ; split; econstructor; try eassumption; apply nbe_term_proof; exact Hp.
  (** Otherwise both values, read back at the type *)
  - destruct (domain_relevance a) eqn:Hr.
    + destruct (per_elem_then_per_top Htyp Hrel' (length Γ)) as [W [HW HW']].
      exists W; split; econstructor; try eassumption; eapply nbe_term_relevant; eassumption.
    + exists ⋆ⁿ; split; econstructor; try eassumption; apply nbe_term_proof; exact Hr.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary completeness_ty : forall {Γ} {i : nat} {A A'},
    Γ ⊢ A ≈ A' : Typeω@i ->
    exists W, nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.

End Fixed_GCtx.
