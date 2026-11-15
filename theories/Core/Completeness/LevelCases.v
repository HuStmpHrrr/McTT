(** * The Rules of Levels

    The rules of the types of levels in the PER model: [Level@n], the
    literals, [succl], [maxl], their congruences and the equations of
    levels.  The lemmas they rest on are in [LogicalRelation/Levels.v]. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Universes Levels.
From Mctt.Core.Semantic Require Import Levels Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Generalizable All Variables.

Corollary sem_level :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@n : LevelSort ).
Proof.
  intros * H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H.
  destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_level_sort_level HΓ).
Qed.

Lemma sem_exp_eq_level_cong :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ Level@n ≈ Level@n : LevelSort ).
Proof. intros; eapply sem_level; eassumption. Qed.

Corollary sem_llit :
  `( fst o <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ o : Level@n ).
Proof.
  intros * Ho H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_llit; eassumption.
Qed.

Lemma sem_exp_eq_llit_cong :
  `( fst o <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ o ≈ 𝕃ᵒ o : Level@n ).
Proof. intros; eapply sem_llit; eassumption. Qed.

Lemma sem_exp_eq_succl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl M ≈ succl M' : Level@n ).
Proof. intros * HM; sem_intro; [ assumption | exact (rel_exp_under_ctx_succl_cong HM) ]. Qed.

Lemma sem_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl M : Level@n ).
Proof. intros; eapply sem_exp_eq_succl_cong; eassumption. Qed.

Lemma sem_exp_eq_maxl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N ≈ N' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N ≈ maxl M' N' : Level@n ).
Proof.
  intros * HM HN; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (domain_level_max m1 n1) (domain_level_max m2 n2) (domain_level_max m3 n3) (domain_level_max m4 n4));
    try (apply eval_exp_maxl; eassumption).
  apply rel_chain_4; apply per_lvl_at_max; pairwise.
Qed.

Lemma sem_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N : Level@n ).
Proof. intros; eapply sem_exp_eq_maxl_cong; eassumption. Qed.

Corollary sem_exp_eq_llit_succl :
  `( a <= n ->
     ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊨ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n ).
Proof.
  intros * Ha H; sem_intro; [ assumption |].
  apply rel_ctx_wf_per_ctx_env in H.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_llit_succl; eassumption.
Qed.

Lemma sem_exp_eq_maxl_zero :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl (𝕃@0) M ≈ M : Level@n ).
Proof.
  intros * HM; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (domain_level_max (domain_level_lit ordinal_zero) m1) (domain_level_max (domain_level_lit ordinal_zero) m2) m3 m4);
    try (apply eval_exp_maxl; [ apply eval_exp_llit | eassumption ]);
    try eassumption.
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ apply per_lvl_at_lit; cbn; lia | pairwise ]
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_zero; lvl_pw | lvl_sort_bounded ]
    | pairwise ].
Qed.

Lemma sem_exp_eq_maxl_assoc :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ P : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl (maxl M N) P ≈ maxl M (maxl N P) : Level@n ).
Proof.
  intros * HM HN HP; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  pose proof (rel_exp_of_level_inversion HP) as [env_relΓ3 [HΓ3 HPgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  destruct (HPgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [p1 p2 p3 p4 Hp1 Hp2 Hp3 Hp4 Hpchain].
  apply (mk_rel_exp (domain_level_max (domain_level_max m1 n1) p1) (domain_level_max (domain_level_max m2 n2) p2)
                    (domain_level_max m3 (domain_level_max n3 p3)) (domain_level_max m4 (domain_level_max n4 p4)));
    try (apply eval_exp_maxl; [ apply eval_exp_maxl |]; eassumption);
    try (apply eval_exp_maxl; [| apply eval_exp_maxl ]; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ apply per_lvl_at_max |]; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_assoc; lvl_pw | lvl_sort_bounded ]
    | apply per_lvl_at_max; [| apply per_lvl_at_max ]; pairwise ].
Qed.

Lemma sem_exp_eq_maxl_comm :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M N ≈ maxl N M : Level@n ).
Proof.
  intros * HM HN; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (domain_level_max m1 n1) (domain_level_max m2 n2) (domain_level_max n3 m3) (domain_level_max n4 m4));
    try (apply eval_exp_maxl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_comm; lvl_pw | lvl_sort_bounded ]
    | apply per_lvl_at_max; pairwise ].
Qed.

Lemma sem_exp_eq_maxl_idem :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M M ≈ M : Level@n ).
Proof.
  intros * HM; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (domain_level_max m1 m1) (domain_level_max m2 m2) m3 m4);
    try (apply eval_exp_maxl; eassumption);
    try eassumption.
  apply rel_chain_4;
    [ apply per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_idem; lvl_pw | lvl_sort_bounded ]
    | pairwise ].
Qed.

Lemma sem_exp_eq_succl_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ succl (maxl M N) ≈ maxl (succl M) (succl N) : Level@n ).
Proof.
  intros * HM HN; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (domain_level_suc (domain_level_max m1 n1)) (domain_level_suc (domain_level_max m2 n2))
                    (domain_level_max (domain_level_suc m3) (domain_level_suc n3)) (domain_level_max (domain_level_suc m4) (domain_level_suc n4)));
    try (apply eval_exp_succl, eval_exp_maxl; eassumption);
    try (apply eval_exp_maxl; apply eval_exp_succl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_suc, per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_suc_max; lvl_pw | lvl_sort_bounded ]
    | apply per_lvl_at_max; apply per_lvl_at_suc; pairwise ].
Qed.

Lemma sem_exp_eq_maxl_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M (succl M) ≈ succl M : Level@n ).
Proof.
  intros * HM; sem_intro; [ assumption |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (domain_level_max m1 (domain_level_suc m1)) (domain_level_max m2 (domain_level_suc m2))
                    (domain_level_suc m3) (domain_level_suc m4));
    try (apply eval_exp_maxl; [ eassumption | apply eval_exp_succl; eassumption ]);
    try (apply eval_exp_succl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ pairwise | apply per_lvl_at_suc; pairwise ]
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_suc; lvl_pw | lvl_sort_bounded ]
    | apply per_lvl_at_suc; pairwise ].
Qed.

Corollary sem_exp_eq_maxl_absorb :
  `( Θ ⍮ Ξ ⍮ Γ ⊨ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊨ maxl M (𝕃ᵒ(S n, 0)) ≈ 𝕃ᵒ(S n, 0) : Level@(S n) ).
Proof. intros * HM; sem_intro; [ assumption | apply rel_exp_maxl_absorb; assumption ]. Qed.
