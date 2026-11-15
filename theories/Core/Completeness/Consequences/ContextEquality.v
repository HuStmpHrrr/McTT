(** * Consequences of Completeness: normal forms respect context equality

    Context equality is not a judgment, so the hypothesis here is semantic.
    [per_ctx_of_exp_eq] is the instance needed: extending one context by two
    judgmentally equal types. *)

From Stdlib Require Import RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Completeness Require Import ContextCases LetCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Corollary per_ctx_of_exp_eq : forall {Γ κ A A'} {i : nat},
    Γ ⊢ A ≈ A' : Typeω@i ->
    ⊨ Γ ▹{κ} A ≈ Γ ▹{κ} A'.
Proof.
  intros * H.
  assert (⊢ Γ) by mauto 2.
  eapply per_ctx_extend; [ apply rel_ctx_wf_per_ctx | ]; mauto 2.
Qed.

Hint Resolve per_ctx_of_exp_eq : mctt.

(** A term has normal forms in two equal contexts, equal up to their
    proofs: a proof is kept over each context's initial environment, whose
    lets bind the entries at each context's types.  The right context is
    scoped, as the left one is by the typing ([wf_scoped]), for its
    initial environment to be related ([per_ctx_then_per_env_initial_env]). *)
Lemma ctxeq_nbe_eq : forall Γ Γ' M A,
    Γ ⊢ M : A ->
    ctx_scoped 0 Γ' ->
    ⊨ Γ ≈ Γ' ->
    exists W W', nbe_f Γ M A W /\ nbe_f Γ' M A W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HM0 HsΓ' HΓΓ'.
  pose proof (completeness_fundamental_exp _ _ _ HM0) as HM.
  pose proof (wf_ctx_scoped_exp HM0) as HsΓ.
  pose proof (exp_scoped_free_bound _ _ (wf_exp_scoped_term _ _ _ _ _ HM0)) as HsM.
  pose proof (per_ctx_respects_length HΓΓ') as Hlen.
  destruct HΓΓ' as [env_rel HΓΓ'].
  pose proof HM as [env_relΓ HΓ _ _].
  assert (Hirrel : env_rel <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [ exact HΓΓ' | exact HΓ ]).
  destruct (rel_exp_under_ctx_simple_full_at HΓ HM) as [i HMi].
  (** The two initial environments are related, so the judgment may be read with
      one on each side. *)
  pose proof (per_ctx_then_per_env_initial_env HΓΓ' HsΓ HsΓ') as [ρ [ρ' [Hρ [Hρ' Hrel]]]].
  destruct (HMi _ _ (proj1 (Hirrel _ _) Hrel)) as (a & a' & elem_rel & Ha & Ha' & HR & Hexp).
  pose proof (per_univ_elem_kind _ _ _ _ HR) as Hra.
  destruct (evaluated_kind_or_propositional (domain_kind a)) as [Hr | Hr].
  (** A type of an evaluated kind: both values read back alike *)
  - destruct Hexp as [Hp | (m & m' & Hm & Hm' & Hmm')]; [ rewrite Hp in Hr; inversion Hr |].
    destruct (per_elem_then_per_top HR Hmm' (length Γ)) as [W W' HW HW' HE].
    exists W, W'; repeat split; [ econstructor; [ exact Hρ | exact Ha | eapply nbe_term_evaluated; eassumption ] | | exact HE ].
    econstructor; [ exact Hρ' | exact Ha' | eapply nbe_term_evaluated; [ rewrite <- Hra; exact Hr | exact Hm' |] ].
    rewrite <- Hlen; exact HW'.
  (** A proposition: the term kept over each environment, read back as a
      proof term *)
  - destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓΓ' HsM _ _ Hrel)
      as [HP HP'].
    destruct (HP (length Γ)) as [P HPr], (HP' (length Γ')) as [P' HPr'].
    (** with the propositions, related types, which read back alike *)
    destruct (per_univ_then_per_top_typ HR (length Γ)) as [Q Q' HQ HQ' HE].
    rewrite Hlen in HQ'.
    exists (nf_proof Q P), (nf_proof Q' P'); refine (conj _ (conj _ _));
      [ econstructor; try eassumption; apply nbe_term_proof; first [ congruence | apply read_nf_proof; first [ congruence | eassumption ] ]
      | econstructor; try eassumption; apply nbe_term_proof; first [ congruence | apply read_nf_proof; first [ congruence | eassumption ] ]
      | unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; exact HE ].
Qed.

(** A normal form in the left context has one in the right context, equal up
    to its proofs. *)
Corollary ctxeq_nbe_eq' : forall Γ Γ' M A W,
    Γ ⊢ M : A ->
    ctx_scoped 0 Γ' ->
    ⊨ Γ ≈ Γ' ->
    nbe_f Γ M A W ->
    exists W', nbe_f Γ' M A W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HM HsΓ' HΓΓ' HW.
  destruct (ctxeq_nbe_eq _ _ _ _ HM HsΓ' HΓΓ') as (W0 & W' & HW0 & HW' & HE).
  functional_nbe_rewrite_clear.
  exists W'; split; assumption.
Qed.

Corollary ctxeq_nbe_ty_eq : forall Γ Γ' A i,
    Γ ⊢ A : Typeω@i ->
    ctx_scoped 0 Γ' ->
    ⊨ Γ ≈ Γ' ->
    exists W W', nbe_ty_f Γ A W /\ nbe_ty_f Γ' A W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HA HsΓ' HΓΓ'.
  destruct (ctxeq_nbe_eq _ _ _ _ HA HsΓ' HΓΓ') as (W & W' & HW%nbe_type_to_nbe_ty & HW'%nbe_type_to_nbe_ty & HE).
  exists W, W'; repeat split; assumption.
Qed.

Corollary ctxeq_nbe_ty_eq' : forall Γ Γ' A i W,
    Γ ⊢ A : Typeω@i ->
    ctx_scoped 0 Γ' ->
    ⊨ Γ ≈ Γ' ->
    nbe_ty_f Γ A W ->
    exists W', nbe_ty_f Γ' A W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HA HsΓ' HΓΓ' HW.
  destruct (ctxeq_nbe_ty_eq _ _ _ _ HA HsΓ' HΓΓ') as (W0 & W' & HW0 & HW' & HE).
  functional_nbe_rewrite_clear.
  exists W'; split; assumption.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_ctx_of_exp_eq : mctt.
