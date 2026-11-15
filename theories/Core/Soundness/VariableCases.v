(** * The Rules of Variables

    The rules of variables in the gluing model: a context's lookup and the
    variable rules.  The lemmas they rest on are in
    [LogicalRelation/Variables.v] and [LogicalRelation/Instance.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import FundamentalTheorem LogicalRelation.Universes.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Variables LogicalRelation.Contexts
  Modules.ModuleValues LogicalRelation.Instance.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

(** A variable at an instance is the instance's component, glued at its
    type at every renaming, so at the identity. *)
Lemma glu_vlookup :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ #x : A ).
Proof.
  glu_intro; econstructor; [ eassumption |].
  intros Γ' τ Hτ.
  apply glu_rel_exp_of_under_renaming; [ apply Hτ | apply Hτ; eassumption ].
Qed.

Lemma glu_exp_eq_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_var_delta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
