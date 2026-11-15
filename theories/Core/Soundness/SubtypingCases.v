(** * The Rules of Subtyping

    The rules of [⊆] in the gluing model, with the subsumption rules of
    terms and equations and the symmetry and transitivity of equations.
    The lemmas they rest on are in [LogicalRelation/Subtyping.v] and
    [LogicalRelation/Levels.v]. *)

From Stdlib Require Import PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LogicalRelation.Levels.
From Mctt.Core.Completeness Require LogicalRelation.Universes.
From Mctt.Core.Semantic Require Import Levels Realizability.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Subtyping
  LogicalRelation.Variables LogicalRelation.Instance LogicalRelation.Universes LogicalRelation.Levels.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

Lemma glu_subtyp_suniv :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M' : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_small_large :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A' ).
Proof.
  glu_inst_intro.
  eapply (glu_rel_exp_subtyp (A := A[τ])); [ glu_inst_premise | glu_inst_premise | eassumption |].
  eapply sub_preserves_subtyp; [ apply Hwst; eassumption | apply Hτ ].
Qed.

Lemma glu_exp_eq_subtyp :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Srt ->
     type_sort Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_sym :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_refl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M' : Srt ->
     type_sort Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_trans :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_univ :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_level :
  `( m <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : abs_kind_sort κd Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : abs_kind_sort κd Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊩ B : abs_kind_sort κc Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ⊩ B' : abs_kind_sort κc Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κd} A' ->
     pi_kinds κd κc ->
     evaluated_kind κc ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
