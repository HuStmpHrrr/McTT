(** * The Rules of Propositions

    The rules of [Prop] and its formers in the gluing model: [⊤], [tt],
    [⊥], [absurd], [Σₚ] and its pairs, the injections, the proof tag,
    their congruences, and proof irrelevance.  The lemmas they rest on are
    in [LogicalRelation/Props.v]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem LogicalRelation.Props LogicalRelation.Universes.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation LogicalRelation.Contexts LogicalRelation.Functions
  LogicalRelation.Subtyping LogicalRelation.Universes LogicalRelation.Variables LogicalRelation.Instance
  LogicalRelation.Props.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Generalizable All Variables.

Lemma glu_prop :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Propₘ : Type@0 ).
Proof. glu_inst_intro; apply glu_rel_exp_prop_univ; glu_inst_premise. Qed.

Lemma glu_True :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊤ : Propₘ ).
Proof. glu_inst_intro; apply glu_rel_exp_True; glu_inst_premise. Qed.

Lemma glu_tt :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_tt : ⊤ ).
Proof. glu_inst_intro; apply glu_rel_exp_tt; glu_inst_premise. Qed.

Lemma glu_False :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ ⊥ : Propₘ ).
Proof. glu_inst_intro; apply glu_rel_exp_False; glu_inst_premise. Qed.

Lemma glu_absurd :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ C : Srt ->
     type_sort Srt ->
     level_closed_sort Propₘ Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ efq M return C : C ).
Proof. glu_inst_intro; eapply (glu_rel_exp_absurd (C := C[τ]) (Srt := Srt)); glu_inst_premise. Qed.

Lemma glu_and :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Σₚ P Q : Propₘ ).
Proof.
  glu_inst_intro.
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▹{ak_propositional} P[τ]) (q τ) (Γ ▹{ak_propositional} P))
    by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | constructor ]).
  eapply glu_rel_exp_and; glu_inst_premise.
Qed.

Lemma glu_conj :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊩ N : Q[Id,,M] ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_conj P Q M N : Σₚ P Q ).
Proof.
  glu_inst_intro.
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▹{ak_propositional} P[τ]) (q τ) (Γ ▹{ak_propositional} P))
    by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | constructor ]).
  eapply (glu_rel_exp_conj (P := P[τ]) (Q := Q[q τ])); glu_inst_premise.
Qed.

Lemma glu_left :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_left M : P ).
Proof.
  glu_inst_intro.
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▹{ak_propositional} P[τ]) (q τ) (Γ ▹{ak_propositional} P))
    by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | constructor ]).
  eapply (glu_rel_exp_left (P := P[τ]) (Q := Q[q τ])); glu_inst_premise.
Qed.

Lemma glu_right :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊩ Q : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : Σₚ P Q ->
     Θ ⍮ Ξ ⍮ Γ ⊩ Q[Id,,a_left M] : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_right M : Q[Id,,a_left M] ).
Proof.
  glu_inst_intro.
  assert (Hq : @glu_rel_sub_inst (gc_mk Θ2 Ξ2) (Γ' ▹{ak_propositional} P[τ]) (q τ) (Γ ▹{ak_propositional} P))
    by (eapply glu_rel_sub_inst_q; [ exact Hτ | eassumption | constructor ]).
  rewrite <- exp_sub_extend_comm.
  eapply (glu_rel_exp_right (P := P[τ]) (Q := Q[q τ]) (M := M[τ])); try glu_inst_premise.
  change (a_left M[τ]) with ((a_left M)[τ]); rewrite exp_sub_extend_comm; glu_inst.
Qed.

Lemma glu_proof_tag :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : P ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_proof P M : P ).
Proof.
  glu_inst_intro.
  eapply (glu_rel_exp_proof_tag (P := P[τ]) (M := M[τ])); glu_inst_premise.
Qed.

(** The equations glue their context. *)
Lemma glu_exp_eq_prop_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_True_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_False_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_absurd_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ C : Srt ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_and_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_irrelevant :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ P : Propₘ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
