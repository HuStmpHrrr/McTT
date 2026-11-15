(** * The Rules of Universes

    The rules of the universes in the PER model: [Typeω@i], [Type⟨M⟩] and
    their congruences, and the tests for large and small universes.  The
    lemmas they rest on are in [LogicalRelation/Universes.v] and
    [LogicalRelation/Levels.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Universes Levels.
From Mctt.Core.Semantic Require Import Levels Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
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
  assert (Hu : per_universe_elements (per_univ (S i)) 𝕌ω@i 𝕌ω@i)
    by (constructor; [| reflexivity | reflexivity | discriminate | discriminate ];
        eexists; apply per_univ_elem_core_univ'; [ solve_universe_index | reflexivity ]).
  econstructor; try apply eval_exp_typ.
  apply rel_chain_4; assumption.
Qed.

Lemma sem_exp_eq_typ_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Typeω@i ≈ Typeω@i : Typeω@(S i) ).
Proof. intros; eapply sem_typ; eassumption. Qed.

Lemma sem_is_univ_large :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Typeω@i ).
Proof. intros * H; sem_intro; [ assumption | left; eexists; reflexivity ]. Qed.

Lemma sem_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵤ Type⟨L⟩ ).
Proof. intros * H; sem_intro; [ assumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ]. Qed.

Lemma sem_exp_eq_univ_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩ ).
Proof.
  intros * HM; sem_intro; [ assumption |].
  pose proof (rel_exp_under_ctx_refl_left HM) as HMM.
  apply (rel_exp_of_suniv_tm (n := n)); [ apply rel_exp_under_ctx_succl_cong; exact HMM |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev' t Ht.
  destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  inversion Ht; subst.
  functional_eval_rewrite_clear.
  assert (H12 : Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (H23 : Dom m2 ≈ m3 ∈ per_lvl) by lvl_pw.
  assert (H34 : Dom m3 ≈ m4 ∈ per_lvl) by lvl_pw.
  pose proof (per_lvl_real _ _ H12) as E12.
  pose proof (per_lvl_real _ _ H23) as E23.
  pose proof (per_lvl_real _ _ H34) as E34.
  rewrite domain_level_real_suc.
  apply (mk_rel_exp 𝕌@m1 𝕌@m2 𝕌@m3 𝕌@m4); try (apply eval_exp_univ; eassumption).
  apply rel_chain_4; (constructor; [| reflexivity | reflexivity | discriminate | discriminate ]);
    eexists; apply per_univ_elem_core_suniv';
    first [ eassumption | cbn; ordinal_solve | reflexivity ].
Qed.

Corollary sem_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Type⟨M⟩ : Type⟨succl M⟩ ).
Proof. intros; eapply sem_exp_eq_univ_cong; eassumption. Qed.
