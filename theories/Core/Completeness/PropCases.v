(** * The Rules of Propositions

    The rules of [Prop] and its formers in the PER model: [⊤], [tt], [⊥],
    [absurd], [Σₚ] and its pairs, the injections, the proof tag, their
    congruences, and proof irrelevance.  The lemmas they rest on are in
    [LogicalRelation/Props.v]. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Universes Props.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

Lemma sem_prop :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Propₘ : Type@0 ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_prop (u := us (0, 0)) HΓ).
Qed.

Lemma sem_exp_eq_prop_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Propₘ ≈ Propₘ : Type@0 ).
Proof. intros; eapply sem_prop; eassumption. Qed.

Lemma sem_True :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ : Propₘ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_prop_True HΓ).
Qed.

Lemma sem_exp_eq_True_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊤ ≈ ⊤ : Propₘ ).
Proof. intros; eapply sem_True; eassumption. Qed.

(** The introduction of [⊤] is related at [⊤], as every proof of it. *)
Lemma sem_tt :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_tt : ⊤ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_under_ctx_proof (rel_exp_of_prop_True HΓ)).
Qed.

Lemma sem_False :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ : Propₘ ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H; destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_prop_False HΓ).
Qed.

Lemma sem_exp_eq_False_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ⊥ ≈ ⊥ : Propₘ ).
Proof. intros; eapply sem_False; eassumption. Qed.

Lemma sem_exp_eq_absurd_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ C : Srt ->
     type_sort Srt ->
     level_closed_sort Propₘ Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ C ≈ C' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : ⊥ ->
     exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return C ≈ efq M' return C' : C ).
Proof.
  intros * HC HS Hcl HCC' _ _ HMs HMs'; sem_intro; [ assumption |].
  destruct (rel_type_pair_of_sort HS HC HCC') as [i [Hl Hr]].
  exact (rel_exp_under_ctx_absurd Hl Hr (rel_type_not_level_kind_of_closed Hcl HC) HMs HMs').
Qed.

Lemma sem_absurd :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ C : Srt ->
     type_sort Srt ->
     level_closed_sort Propₘ Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : ⊥ ->
     exp_scoped (List.length Γ) M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ efq M return C : C ).
Proof. intros; eapply sem_exp_eq_absurd_cong; eassumption. Qed.

Lemma sem_exp_eq_and_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P ≈ P' : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊨ Q ≈ Q' : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Σₚ P Q ≈ Σₚ P' Q' : Propₘ ).
Proof.
  intros * HP HPP' HQ; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_and HP HPP' HQ).
Qed.

Lemma sem_and :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Σₚ P Q : Propₘ ).
Proof. intros; eapply sem_exp_eq_and_cong; eassumption. Qed.

(** A proof of a conjunction, at its components' propositions. *)
Lemma sem_conj :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Q[Id,,M] ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_conj P Q M N : Σₚ P Q ).
Proof.
  intros * HP HQ _ _.
  assert (HT : Θ ⍮ Ξ ⍮ Γ ⊨ Σₚ P Q : Propₘ) by (eapply sem_and; eassumption).
  sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HT).
Qed.

Lemma sem_left :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_left M : P ).
Proof.
  intros * HP _ _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.

(** The premises begin with the conjunction's proof, which fixes [P]: the
    conclusion does not. *)
Lemma sem_right :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊨ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Q[Id,,a_left M] : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_right M : Q[Id,,a_left M] ).
Proof.
  intros * _ _ _ HQ; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HQ).
Qed.

(** A tagged proof, a proof of its tag. *)
Lemma sem_proof_tag :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_proof P M : P ).
Proof.
  intros * HP _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.

Lemma sem_exp_eq_irrelevant :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M' : P ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : P ).
Proof.
  intros * HP _ _; sem_intro; [ assumption |].
  exact (rel_exp_under_ctx_proof HP).
Qed.
