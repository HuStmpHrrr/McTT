(** * Subtyping and Conversion

    Only the term rules survive: with the [⊩s] judgment gone, so are
    [glu_rel_sub_subtyp] and [glu_rel_sub_conv], and context subtyping is now
    [ctx_sub] rather than a judgment the gluing model has a rule for. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_exp_subtyp : forall {Γ M A A' i},
    Γ ⊩ M : A ->
    Γ ⊩ A' : Type@i ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊩ M : A'.
Proof.
  intros * [] HA' Hsub%completeness_fundamental_subtyp.
  destruct_conjs.
  pose proof (subtyp_under_ctx_simple Hsub) as [env_relΓ [HΓ [k Hsubsimple]]].
  invert_glu_rel_exp HA'.
  econstructor; split; [eassumption |].
  exists (max i k); intros Δ σ ρ HSb.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  assert (Dom ρ ≈ ρ ∈ env_relΓ) by (eapply glu_ctx_env_per_env; mauto).
  destruct (Hsubsimple _ _ ltac:(eassumption)) as [a1 [a2 [? [? ?]]]].
  functional_eval_rewrite_clear.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  eapply mk_glu_rel_exp_with_sub'; try eassumption.
  - eapply glu_univ_elem_cumu_max_left; eassumption.
  - intros P El HPEl.
    eapply glu_univ_elem_per_subtyp_trm_conv; try eassumption.
    eapply glu_univ_elem_typ_cumu_max_left; [| exact HPEl |]; eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_subtyp : mctt.

Lemma glu_rel_exp_conv : forall {Γ M A A' i},
    Γ ⊩ M : A ->
    Γ ⊩ A' : Type@i ->
    Γ ⊢ A ≈ A' : Type@i ->
    Γ ⊩ M : A'.
Proof.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv : mctt.
