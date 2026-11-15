(** * The Rules of Levels

    The rules of the types of levels in the gluing model: [Level@n], the
    literals, [succl], [maxl], their congruences and the equations of
    levels.  The lemmas they rest on are in [LogicalRelation/Levels.v]. *)

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

Lemma glu_level :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Level@n : LevelSort ).
Proof. glu_inst_intro; apply glu_rel_exp_level; glu_inst_premise. Qed.

Lemma glu_llit :
  `( fst o <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ 𝕃ᵒ o : Level@n ).
Proof. glu_inst_intro; apply glu_rel_exp_llit; glu_inst_premise. Qed.

Lemma glu_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ succl M : Level@n ).
Proof. glu_inst_intro; eapply glu_rel_exp_succl; glu_inst_premise. Qed.

Lemma glu_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ maxl M N : Level@n ).
Proof. glu_inst_intro; eapply glu_rel_exp_maxl; glu_inst_premise. Qed.

Lemma glu_exp_eq_level_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_llit_cong :
  `( @fst nat nat o <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_succl_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_llit_succl :
  `( a <= n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_absorb :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_zero :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_assoc :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ P : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_comm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_idem :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_succl_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_maxl_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : Level@n ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
