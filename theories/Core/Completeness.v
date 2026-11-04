(** * Completeness of Normalization by Evaluation

    The fundamental theorem instantiated at the identity substitution and the
    initial environment, where only the inner two values of each chain of
    [rel_exp_under_ctx] are used. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases LetCases.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations Fixed_Notations.

(** The context of a judgment is scoped ([wf_scoped]): what reading at its
    initial environment asks. *)
Lemma wf_ctx_scoped_exp : forall {Θ Ξ Γ A M}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> ctx_scoped 0 Γ.
Proof. intros * H; exact (proj1 (proj1 (proj1 (proj2 wf_scoped) _ _ _ _ _ H))). Qed.

Lemma wf_ctx_scoped_exp_eq : forall {Θ Ξ Γ A M M'}, Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ctx_scoped 0 Γ.
Proof. intros * H; exact (proj1 (proj1 (proj1 (proj2 (proj2 wf_scoped)) _ _ _ _ _ _ H))). Qed.

(** A semantic equality read at the initial environment of its own context. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** A semantic equality [Γ ⊨ M ≈ M' : A] read at the initial environment
    of [Γ]: both terms have normal forms there, equal up to their proofs
    ([nf_erase]).  At a proposition the terms are never evaluated: each is
    kept over the environment and read back as a proof term. *)
#[warnings="-cannot-define-projection"]
Record initial_env_normal_forms (Γ : ctx) (M M' A : exp) : Prop := mk_initial_env_normal_forms
  { (** The initial environment of [Γ] *)
    initial_env_normal_forms_env : env
    (** The value of the type *)
  ; initial_env_normal_forms_type : domain
    (** The left term's normal form *)
  ; initial_env_normal_forms_left : nf
    (** The right term's normal form *)
  ; initial_env_normal_forms_right : nf
    (** It is the initial environment *)
  ; initial_env_normal_forms_init : initial_env_f Γ initial_env_normal_forms_env
    (** The type evaluates there *)
  ; initial_env_normal_forms_eval_type : ⟦ A ⟧ initial_env_normal_forms_env ↘ initial_env_normal_forms_type
    (** The left term reads back as its normal form *)
  ; initial_env_normal_forms_nbe_left : nbe_term gc_deps gc_stack (List.length Γ)
      initial_env_normal_forms_env M initial_env_normal_forms_type initial_env_normal_forms_left
    (** The right term as its own *)
  ; initial_env_normal_forms_nbe_right : nbe_term gc_deps gc_stack (List.length Γ)
      initial_env_normal_forms_env M' initial_env_normal_forms_type initial_env_normal_forms_right
    (** The two are equal up to their proofs *)
  ; initial_env_normal_forms_erased : nf_erase initial_env_normal_forms_left = nf_erase initial_env_normal_forms_right }.

(** The context is scoped, for its initial environment to be related to
    itself ([per_ctx_then_per_env_initial_env]), and so are the terms, for
    a proof kept over it to read back ([per_ctx_env_kept_proof_readable]). *)
Lemma rel_exp_under_ctx_at_initial_env : forall {Γ A M M'},
    ctx_scoped 0 Γ -> exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
    Γ ⊨ M ≈ M' : A ->
    initial_env_normal_forms Γ M M' A.
Proof.
  intros * HsΓ HsM HsM' H.
  pose proof H as [env_relΓ HΓ _ _].
  destruct (rel_exp_under_ctx_simple_full_at HΓ H) as [i HM].
  pose proof (per_ctx_then_per_env_initial_env HΓ HsΓ HsΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HM _ _ Hrel) as (a & a' & elem_rel & Ha & Ha' & HR & Hexp).
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  destruct (domain_relevance a) eqn:Hr.
  (** A relevant type: both terms evaluate, to related values, which read
      back alike *)
  - destruct Hexp as [Hp | (m & m' & Hm & Hm' & Hmm')]; [ congruence |].
    destruct (per_elem_then_per_top HR Hmm' (List.length Γ)) as [W W' HW HW' HE].
    exact (mk_initial_env_normal_forms _ _ _ _ ρ a W W' Hρ Ha
             (nbe_term_relevant _ _ _ _ _ _ _ _ Hr Hm HW) (nbe_term_relevant _ _ _ _ _ _ _ _ Hr Hm' HW') HE).
  (** A proposition: both terms kept over the environment, read back as
      proof terms *)
  - destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓ (exp_scoped_free_bound _ _ HsM) _ _ Hrel) as [HP _].
    destruct (per_ctx_env_kept_proof_readable _ _ _ M' HΓ (exp_scoped_free_bound _ _ HsM') _ _ Hrel) as [HP' _].
    destruct (HP (List.length Γ)) as [P HPr], (HP' (List.length Γ)) as [P' HPr'].
    exact (mk_initial_env_normal_forms _ _ _ _ ρ a (nf_proof P) (nf_proof P') Hρ Ha
             (nbe_term_proof _ _ _ _ _ _ _ Hr (read_nf_proof _ _ _ _ _ _ Hr HPr))
             (nbe_term_proof _ _ _ _ _ _ _ Hr (read_nf_proof _ _ _ _ _ _ Hr HPr')) eq_refl).
Qed.

(** The same at a type equality, where the element relation is [per_univ i],
    the type values only. *)
Lemma rel_typ_under_ctx_at_initial_env : forall {Γ A A'} {i : nat},
    ctx_scoped 0 Γ ->
    Γ ⊨ A ≈ A' : Typeω@i ->
    exists ρ a a',
      initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HsΓ H%rel_exp_of_typ_inversion_simple.
  destruct H as [env_relΓ [HΓ HA]].
  pose proof (per_ctx_then_per_env_initial_env HΓ HsΓ HsΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HA _ _ Hrel) as [a [a' [Ha [Ha' Haa']]]].
  exists ρ, a, a'.
  repeat apply conj; eassumption.
Qed.

(** The same at a semantic type equality ([⊨ᵗ]), of either sort. *)
Lemma rel_type_under_ctx_at_initial_env : forall {Γ A A'} {i : nat},
    ctx_scoped 0 Γ ->
    Γ ⊨ᵗ A ≈ A' at i ->
    exists ρ a a',
      initial_env_f Γ ρ /\ ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HsΓ H.
  destruct (rel_type_inversion_simple H) as [env_relΓ [HΓ HA]].
  pose proof (per_ctx_then_per_env_initial_env HΓ HsΓ HsΓ) as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  destruct (HA _ _ Hrel) as [a [a' [Ha [Ha' Haa']]]].
  exists ρ, a, a'; repeat apply conj; eassumption.
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
  destruct (rel_type_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq H) Hi) as (ρ & a & a' & ?).
  exists ρ, a, a', i; assumption.
Qed.

End Fixed_GCtx.

(** Equal terms have normal forms equal up to their proofs: the semantic
    equality of [completeness_fundamental], read at the identity embedding
    and at the initial environment.  The proofs are compared erased
    ([nf_erase]): two equal proofs of a proposition are any two of its
    proofs. *)
Theorem completeness : forall {Θ Ξ Γ M M' A},
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    exists W W', nbe Θ Ξ Γ M A W /\ nbe Θ Ξ Γ M' A W' /\ nf_erase W = nf_erase W'.
Proof.
  intros * H.
  pose proof (proj1 (proj2 (proj2 completeness_fundamental)) _ _ _ _ _ _ H) as HK.
  pose proof (sem_exp_eq_at_rel (HK _ _ (valid_gctx_embedding_refl _ _ (ctx_wf_gctx _ _ _ (presup_exp_eq_ctx H))))) as Hrel.
  destruct (@rel_exp_under_ctx_at_initial_env (gc_mk Θ Ξ) _ _ _ _ (wf_ctx_scoped_exp_eq H)
              (wf_exp_eq_scoped_left _ _ _ _ _ _ H) (wf_exp_eq_scoped_right _ _ _ _ _ _ H) Hrel)
    as [ρ a W W' Hρ Ha HW HW' HE].
  exists W, W'; repeat split; [ econstructor; eassumption | econstructor; eassumption | exact HE ].
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** Equal types have normal forms equal up to their proofs: a type holds
    proofs at its indices. *)
Corollary completeness_ty : forall {Γ} {i : nat} {A A'},
    Γ ⊢ A ≈ A' : Typeω@i ->
    exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ A' W' /\ nf_erase W = nf_erase W'.
Proof.
  intros * (W & W' & HW%nbe_type_to_nbe_ty & HW'%nbe_type_to_nbe_ty & HE)%completeness.
  exists W, W'; repeat split; assumption.
Qed.

End Fixed_GCtx.
