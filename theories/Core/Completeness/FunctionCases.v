(** * The Rules of Functions

    The rules of [Π] in the PER model: the type former, [λ], application,
    their congruences, [β] and [η].  The lemmas they rest on are in
    [LogicalRelation/Functions.v]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Contexts Levels Universes Variables Props
  Lets Instance Functions.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

(** A [Π] out of a domain of the kind [κd] into a codomain of the kind
    [κc] ([pi_kinds]), at a universe [U] ([wf_exp_eq_pi_cong]): at
    [ak_relevant] a type of [U], large or small at a level term; at
    [ak_propositional] the [∀], a proposition; at [ak_level] a [Π] between
    types of levels, a type of levels. *)
Lemma sem_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : abs_kind_sort κd U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : abs_kind_sort κd U ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B ≈ B' : (abs_kind_sort κc U)[↑]ʷ ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_pi κd κc A B ≈ a_pi κd κc A' B' : abs_kind_sort κc U ).
Proof.
  intros * HU HA0 HA HB Hk; sem_intro; [ assumption |].
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort exp_wk] in *.
  - destruct HU as [[? ->] | (? & ? & -> & ?)]; cbn [exp_wk] in *.
    + eapply rel_exp_under_ctx_pi_cong;
        [ exact (rel_type_of_abs_kind_sort HA0) | exact (rel_type_of_abs_kind_sort HA)
        | intros R HR ρ ρ' Hρ; exact (rel_exp_of_abs_kind_sort_at HR HA0 _ _ Hρ) | exact HB ].
    + eapply rel_exp_under_ctx_pi_cong_small; eassumption.
  - destruct HU as [[? ->] | (? & ? & -> & ?)].
    + eapply rel_exp_under_ctx_all; [ exact (rel_type_of_abs_kind_sort HA0) | exact (rel_type_of_abs_kind_sort HA) | exact HB ].
    + eapply rel_exp_under_ctx_all;
        [ exact (rel_type_of_domain_suniv HA0) | exact (rel_type_of_domain_suniv HA) | exact HB ].
  - exact (rel_exp_under_ctx_pi_level_cong HA0 HA HB).
Qed.

Lemma sem_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A : abs_kind_sort κd U ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : (abs_kind_sort κc U)[↑]ʷ ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ a_pi κd κc A B : abs_kind_sort κc U ).
Proof. intros * HU HA HB Hk; eapply sem_exp_eq_pi_cong; eassumption. Qed.

(** A λ over a domain of the kind [κd] into a codomain of the kind [κc]
    ([pi_kinds], [wf_exp_eq_fn_cong]): a function into a type of a
    universe, a function between types of levels, or a proof of a [∀]. *)
Lemma sem_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ⊨ A ≈ A' : Srt ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M ≈ λ A' M' : a_pi κd κc A B ).
Proof.
  intros * HA0 HS HA HB Hk HM; sem_intro; [ assumption |].
  pose proof (sort_kind_type_sort _ _ HS) as HSt.
  pose proof (rel_type_kind_of_sort_kind HS HA0) as HAk.
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort] in *.
  - destruct (rel_pi_parts HSt HA0 HA HB) as [k [Hl [Hr Hk]]].
    exact (rel_exp_under_ctx_fn_cong Hl Hr HAk Hk HM).
  - exact (rel_exp_under_ctx_proof (rel_all_of_parts HSt HA0 HA0 HB)).
  - inversion HS; subst.
    exact (rel_exp_under_ctx_fn_cong_evaluated (rel_type_of_level_sort 0 HA0) (rel_type_of_level_sort 0 HA) HAk
             (rel_type_of_level_sort 0 HB) (rel_type_kind_of_level_sort HB) pi_kinds_level evaluated_kind_level HM).
Qed.

Lemma sem_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ λ A M : a_pi κd κc A B ).
Proof. intros * HA HS HB Hk HM; eapply sem_exp_eq_fn_cong; eassumption. Qed.

(** Application of a function or of a proof of a [∀]. *)
Lemma sem_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : a_pi κd κc A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : A ->
     exp_scoped (List.length Γ) N ->
     exp_scoped (List.length Γ) N' ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N ≈ M' $ N' : B[Id,,N] ).
Proof.
  intros * HA HS HB Hk HM HN HNs HN's; sem_intro; [ assumption |].
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort] in *.
  - destruct HS.
    + exact (rel_exp_under_ctx_app_cong (rel_type_of_typ HA) (rel_type_kind_of_typ HA) evaluated_kind_relevant
               evaluated_kind_relevant (rel_type_of_typ HB) HM HN HNs).
    + exact (rel_exp_under_ctx_app_cong_prop HA HB HM HN HNs HN's).
    + exact (rel_exp_under_ctx_app_cong (rel_type_of_level_sort 0 HA) (rel_type_kind_of_level_sort HA) evaluated_kind_level
               evaluated_kind_relevant (rel_type_of_typ HB) HM HN HNs).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB (rel_exp_under_ctx_refl_left HN) HNs) end.
  - inversion HS; subst.
    exact (rel_exp_under_ctx_app_cong (rel_type_of_level_sort 0 HA) (rel_type_kind_of_level_sort HA) evaluated_kind_level
             evaluated_kind_level (rel_type_of_level_sort 0 HB) HM HN HNs).
Qed.

Lemma sem_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : a_pi κd κc A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     exp_scoped (List.length Γ) N ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M $ N : B[Id,,N] ).
Proof.
  intros * HA HS HB Hk HM HN HNs;
    eapply sem_exp_eq_app_cong; [ exact HA | exact HS | exact HB | exact Hk | exact HM | exact HN | exact HNs | exact HNs ].
Qed.

(** β for a function or for a proof of a [∀] ([wf_exp_eq_pi_beta]). *)
Lemma sem_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : A ->
     exp_scoped (List.length Γ) N ->
     Θ ⍮ Ξ ⍮ Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] ).
Proof.
  intros * HA HS HB Hk HM HN HNs; sem_intro; [ assumption |].
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort] in *.
  - destruct HS.
    + exact (rel_exp_under_ctx_pi_beta (rel_type_of_typ HA) (rel_type_kind_of_typ HA) evaluated_kind_relevant
               (rel_type_of_typ HB) (rel_type_evaluated_of_typ HB) HM HN HNs).
    + exact (rel_exp_under_ctx_pi_beta_prop HA HB HM HN HNs).
    + exact (rel_exp_under_ctx_pi_beta (rel_type_of_level_sort 0 HA) (rel_type_kind_of_level_sort HA) evaluated_kind_level
               (rel_type_of_typ HB) (rel_type_evaluated_of_typ HB) HM HN HNs).
  - apply rel_exp_under_ctx_proof.
    match goal with HΓ : ⊨ Γ |- _ =>
      exact (rel_exp_under_ctx_instance HΓ HS HA HB HN HNs) end.
  - inversion HS; subst.
    exact (rel_exp_under_ctx_pi_beta (rel_type_of_level_sort 0 HA) (rel_type_kind_of_level_sort HA) evaluated_kind_level
             (rel_type_of_level_sort 0 HB) (rel_type_evaluated_of_level_sort HB) HM HN HNs).
Qed.

(** η for a function or for a proof of a [∀] ([wf_exp_eq_fn_eta]). *)
Lemma sem_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ A : Srt ->
     sort_kind Srt κd ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊨ B : abs_kind_sort κc Typeω@i ->
     pi_kinds κd κc ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M : a_pi κd κc A B ->
     Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ λ A M[↑]ʷ $ #0 : a_pi κd κc A B ).
Proof.
  intros * HA HS HB Hk HM; sem_intro; [ assumption |].
  pose proof (sort_kind_type_sort _ _ HS) as HSt.
  pose proof (rel_type_kind_of_sort_kind HS HA) as HAk.
  destruct Hk as [κd | κd |]; cbn [abs_kind_sort] in *.
  - destruct (rel_pi_parts HSt HA HA HB) as [k [Hl [_ Hk]]].
    exact (rel_exp_under_ctx_fn_eta Hl HAk (rel_type_of_typ Hk) (rel_type_kind_of_typ Hk) (pi_kinds_relevant _)
             evaluated_kind_relevant HM).
  - exact (rel_exp_under_ctx_proof (rel_all_of_parts HSt HA HA HB)).
  - inversion HS; subst.
    exact (rel_exp_under_ctx_fn_eta (rel_type_of_level_sort 0 HA) HAk (rel_type_of_level_sort 0 HB)
             (rel_type_kind_of_level_sort HB) pi_kinds_level evaluated_kind_level HM).
Qed.
