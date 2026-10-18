(** * Subtyping and Conversion

    The gluing model has subsumption and conversion rules for terms only: there
    is no substitution judgment, and context subtyping is the syntactic
    relation [ctx_sub]. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma glu_rel_exp_subtyp : forall {Γ M A A'} {i : nat},
    Γ ⊩ M : A ->
    Γ ⊩ A' : Typeω@i ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊩ M : A'.
Proof.
  intros * [] HA' Hsub%completeness_fundamental_subtyp.
  destruct_conjs.
  pose proof (rel_subtyp_under_ctx_simple Hsub) as [env_relΓ [HΓ [k Hsubsimple]]].
  invert_glu_rel_exp HA'.
  eapply mk_glu_rel_exp with (gre_lvl := max i k); [eassumption |].
  intros Δ σ ρ HSb.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; mauto).
  destruct (Hsubsimple _ _ ltac:(eassumption)) as [a1 [a2 [? [? ?]]]].
  functional_eval_rewrite_clear.
  destruct_glu_records.
  destruct_conjs.
  eapply mk_glu_rel_exp_with_sub'; try eassumption.
  - eapply glu_univ_elem_cumu_max_left; eassumption.
  - intros P El HPEl.
    eapply glu_univ_elem_per_subtyp_trm_conv; try eassumption.
    eapply glu_univ_elem_typ_cumu_max_left; [| exact HPEl |]; eassumption.
Qed.

Hint Resolve glu_rel_exp_subtyp : mctt.

Lemma glu_rel_exp_conv : forall {Γ M A A'} {i : nat},
    Γ ⊩ M : A ->
    Γ ⊩ A' : Typeω@i ->
    Γ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊩ M : A'.
Proof.
  mauto 3.
Qed.

Hint Resolve glu_rel_exp_conv : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_subtyp : mctt.
#[export]
Hint Resolve glu_rel_exp_conv : mctt.

(** ** The Rules *)

#[local] Generalizable All Variables.

Lemma glu_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A' ).
Proof. glu_intro; glu_emb_wf; eapply glu_rel_exp_subtyp; [ eassumption | eassumption | apply Hwst; eassumption ]. Qed.

Lemma glu_exp_eq_subtyp :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Typeω@i ->
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
  `( Θ ⍮ Ξ ⍮ Γ ⊩ M' : Typeω@i ->
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
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ A' : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊩ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊩ B' : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ A' ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
