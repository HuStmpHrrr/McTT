(** * Soundness of Normalization by Evaluation

    The fundamental theorem of the gluing model, instantiated at the identity
    substitution.  [exp_sub_id] and [exp_wk_id] line the statement up with the
    gluing predicate by rewriting. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Export FundamentalTheorem.
From Mctt.Core.Soundness Require Import LevelCases.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Theorem soundness : forall {Γ M A},
    Γ ⊢ M : A ->
    exists W, nbe_f Γ M A W /\ Γ ⊢ M ≈ W : A.
Proof.
  intros * H.
  assert (⊢ Γ) by mauto 3.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ]
      by mauto 3 using completeness_fundamental_ctx, sem_ctx_per_ctx_env.
  destruct (soundness_fundamental_exp _ _ _ H) as [Sb [? [i]]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [ρ [? ?]].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢s Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  assert (Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top i a) as [? ? ? ? ? ? Hrb]
      by (eapply realize_glu_elem_top; mauto 3).
  match_by_head per_top ltac:(fun H => destruct (H (length Γ)) as [W []]).
  assert (Γ ⊢k wk_id : Γ) by mauto 3.
  assert (Γ ⊢ M[Id][wk_id]ʷ ≈ W : A[Id][wk_id]ʷ) as Heq by (eapply Hrb; eassumption).
  rewrite !exp_wk_id, !exp_sub_id in Heq.
  exists W; split; [econstructor |]; eassumption.
Qed.

Theorem soundness' : forall {Γ M A W},
    Γ ⊢ M : A ->
    nbe_f Γ M A W ->
    Γ ⊢ M ≈ W : A.
Proof.
  intros * [? []]%soundness ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Lemma soundness_ty : forall {Γ} {i : nat} {A},
    Γ ⊢ A : Typeω@i ->
    exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i.
Proof.
  intros.
  assert (exists W', nbe_f Γ A Typeω@i W' /\ Γ ⊢ A ≈ W' : Typeω@i) as [? [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
  firstorder.
Qed.

Lemma soundness_ty' : forall {Γ} {i : nat} {A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    Γ ⊢ A ≈ B : Typeω@i.
Proof.
  intros.
  assert (exists B', nbe_ty_f Γ A B' /\ Γ ⊢ A ≈ B' : Typeω@i) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

(** The normal form of a level of sort [n] is a canonical level of sort [n]:
    its constant is of a tier at most [n], and each atom is a level of its
    own sort ([nf_lvl_ws]).  It is read off the gluing of the level, whose
    atoms are glued at their types.  The algorithmic layer needs it to trust
    the sorts an atom of a normal form carries. *)
Theorem soundness_lvl_ws : forall {Γ M n W},
    Γ ⊢ M : Level@n ->
    nbe_f Γ M Level@n W ->
    nf_lvl_ws n Γ W.
Proof.
  intros * H Hn.
  assert (⊢ Γ) by mauto 3.
  assert (exists env_relΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ) as [env_relΓ]
      by mauto 3 using completeness_fundamental_ctx, sem_ctx_per_ctx_env.
  pose proof (soundness_fundamental_exp _ _ _ H) as HM.
  destruct HM as [Sb [HSb Hrest]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [ρ [? ?]].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (HId : Γ ⊢s Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct (glu_rel_exp_level_elim (n := n) HSb (soundness_fundamental_exp _ _ _ H) _ _ _ HId)
    as [m [Hev [_ Hglu]]].
  inversion Hn; subst.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  match goal with He : ⟦ Level@n ⟧ _ ↘ _ |- _ => inversion He; subst end.
  assert (Γ ⊢k wk_id : Γ) by mauto 3.
  match goal with Hr : Rnf ⇓ (Levelᵈ@n) m in _ ↘ W |- _ =>
    exact (proj2 (Hglu _ _ _ ltac:(eassumption) (read_nf_level_sort _ _ 0 _ _ Hr))) end.
Qed.

End Fixed_GCtx.


(** Soundness at a global context named explicitly. *)
Theorem soundness_gctx : forall Θ Ξ Γ M A,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    exists W, nbe Θ Ξ Γ M A W /\ Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof. intros * H; exact (@soundness (gc_mk Θ Ξ) _ _ _ H). Qed.

Theorem soundness_gctx' : forall Θ Ξ Γ M A W,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    nbe Θ Ξ Γ M A W ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ W : A.
Proof. intros * H; exact (@soundness' (gc_mk Θ Ξ) _ _ _ _ H). Qed.
