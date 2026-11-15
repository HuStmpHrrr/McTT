(** * The Rules of Universes

    The rules of the universes in the gluing model: [Typeω@i], [Type⟨M⟩]
    and their congruences, and the tests for large and small universes.
    The lemmas they rest on are in [LogicalRelation/Universes.v] and
    [LogicalRelation/Levels.v]. *)

From Stdlib Require Import PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LogicalRelation.Universes LogicalRelation.Levels.
From Mctt.Core.Semantic Require Import Levels Realizability.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Subtyping
  LogicalRelation.Variables LogicalRelation.Instance LogicalRelation.Universes LogicalRelation.Levels.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

Lemma glu_typ :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Typeω@i : Typeω@(S i) ).
Proof. glu_inst_intro; cbn; apply glu_rel_exp_typ; apply Hτ. Qed.

Lemma glu_exp_eq_typ_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_is_univ_large :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Typeω@i ).
Proof. glu_intro; [ assumption | left; eexists; reflexivity ]. Qed.

Lemma glu_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ᵤ Type⟨L⟩ ).
Proof.
  glu_intro; [ eapply glu_rel_exp_under_sub_ctx; eassumption | right; do 2 eexists; split; [ reflexivity | eassumption ] ].
Qed.

Lemma glu_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Type⟨M⟩ : Type⟨succl M⟩ ).
Proof. glu_inst_intro; eapply glu_rel_exp_univ_lvl; glu_inst_premise. Qed.

Lemma glu_exp_eq_univ_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
