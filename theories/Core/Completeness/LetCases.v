(** * The Rules of Lets

    The rules of the three lets in the PER model: of a term, of a module
    and of a definition with a module part, their congruences and their
    [ζ]-rules.  The lemmas they rest on are in [LogicalRelation/Lets.v]
    and, for the module lets, [Modules/Slots.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import LookupSound.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Contexts Universes Variables Lets.
From Mctt.Core.Completeness.Modules Require Import Slots.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.
#[local] Generalizable All Variables.

Lemma sem_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓ A ≔ M in B ≈ B[Id,,M] : C[Id,,M] ).
Proof. intros * HA HS HM HB HMs; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_zeta HS HA HM HMs HB) ]. Qed.

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

Lemma sem_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓ A ≔ M in B : C[Id,,M] ).
Proof. intros * HA HS HM HB HMs; sem_intro; [ assumption | exact (valid_exp_under_ctx_let HS HA HM HMs HB) ]. Qed.

Lemma sem_let_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HM HU HB HMs HUs; sem_intro;
    [ assumption | exact (valid_exp_under_ctx_let_dm HA HM HU HMs HUs HB) ].
Qed.

Lemma sem_exp_eq_let_dm_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B ≈ B' : C ->
     exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
     gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ ℓᵈ A' ≔ M' ‖ U' in B' : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HAA' HM HU HB HMs HMs' HUs HUs'; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_dm_cong HA HAA' HM HU HMs HMs' HUs HUs' HB) ].
Qed.

Lemma sem_exp_eq_let_dm_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U ⊨ B : C ->
     exp_scoped (List.length Γ) M ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓᵈ A ≔ M ‖ U in B ≈ B[Id ,,ᵈ M ‖ me_lit U] : C[Id ,,ᵈ M ‖ me_lit U] ).
Proof.
  intros * HA HM HU HB HMs HUs; sem_intro;
    [ assumption | exact (rel_exp_under_ctx_let_dm_zeta HA HM HU HMs HUs HB) ].
Qed.

Lemma sem_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ _ HB HUs; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_zeta HU HB HUs) ]. Qed.

Lemma sem_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     gunit_scoped (List.length Γ) U -> gunit_scoped (List.length Γ) U' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU HB _ HUs HUs'; sem_intro; [ assumption | exact (rel_exp_under_ctx_let_mod_cong HU HB HUs HUs') ]. Qed.

Lemma sem_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ C : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊨ B : C ->
     gunit_scoped (List.length Γ) U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ ℓₘ U in B : C[Id ,,ₘ me_lit U] ).
Proof. intros * HU _ _ HB HUs; sem_intro; [ assumption | exact (valid_exp_under_ctx_let_mod HU HB HUs) ]. Qed.
