(** * Fundamental Theorem: Universe Levels

    Substitution pushes through every level form by computation of [exp_sub]:
    [Level@n[σ]] is [Level@n], [(𝕃ᵒ o)[σ]] is [𝕃ᵒ o], and [succl] and [maxl] commute
    with it.  So what is validated here is the typing of [Level@n] and of a level
    literal, the congruence rules of [succl] and [maxl], and the level
    equations.

    A judgment at type [Level@n] is exactly a four-value pattern in
    [per_lvl_at n]: related levels, all of sort [n].  Each equation is then
    the corresponding lemma of [Core.Semantic.Levels], where it is an
    identity between canonical forms, and the bound of each side. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation SubstitutionCases UniverseCases.
From Mctt.Core.Semantic Require Import Levels Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** A link of a chain of levels at a sort as a fact of [per_lvl], and the
    bounds of the values of a chain of four. *)
Ltac lvl_pw :=
  first [ pairwise
        | match goal with
          | H : rel_chain (per_lvl_at ?n) _ |- per_lvl _ _ => apply (per_lvl_at_lvl n); pairwise_from H (per_lvl_at n)
          end ].

Ltac lvl_bnd :=
  first [ pairwise
        | solve [ apply per_lvl_at_lit; cbn; lia ]
        | solve [ apply per_lvl_at_suc; lvl_bnd ]
        | solve [ apply per_lvl_at_max; lvl_bnd ] ].

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The sort of the levels is a parameter of this section. *)
  Context {n : nat}.

(** [Level@n]'s [per_univ_elem], at its element PER and at any index. *)
Lemma per_univ_elem_level : forall i,
    DF Levelᵈ@n ≈ Levelᵈ@n ∈ per_univ_elem i ↘ per_lvl_at n.
Proof.
  intros; per_univ_elem_econstructor; reflexivity.
Qed.

Hint Resolve per_univ_elem_level : mctt.

(** ** [Level@n] as a Type *)
Lemma rel_exp_of_typ_level : forall {Γ} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ Level@n ≈ Level@n : Typeω@i.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom Levelᵈ@n ≈ Levelᵈ@n ∈ per_univ i)
    by (eexists; apply per_univ_elem_level).
  econstructor; try apply eval_exp_level.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ_level : mctt.

Corollary valid_exp_level : forall {Γ} {i : nat},
    ⊨ Γ ->
    Γ ⊨ Level@n : Typeω@i.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_of_typ_level; eassumption.
Qed.

Hint Resolve valid_exp_level : mctt.

(** [Level@n] in a universe at any index, in particular in the small ones. *)
Lemma rel_exp_of_univ_level : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ Level@n ≈ Level@n : ulvl_tm u.
Proof.
  intros * HΓ.
  apply rel_exp_of_univ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom Levelᵈ@n ≈ Levelᵈ@n ∈ per_univ u)
    by (eexists; apply per_univ_elem_level).
  econstructor; try apply eval_exp_level.
  apply rel_chain_4; assumption.
Qed.

Corollary valid_exp_level_small : forall {Γ o},
    ⊨ Γ ->
    Γ ⊨ Level@n : Type⟨𝕃ᵒ o⟩.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_level (u := us o) HΓ).
Qed.

Hint Resolve valid_exp_level_small : mctt.

(** ** Levels as Terms

    As for [ℕ], a judgment at [Level@n] is exactly a four-value pattern in its
    element PER. *)
Lemma rel_exp_of_level_inversion : forall {Γ M M'},
    Γ ⊨ M ≈ M' : Level@n ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' (per_lvl_at n).
Proof.
  intros * [env_relΓ [HΓ [i HM]]].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HM _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [? ? ? ? ? ? ? ? Hchain].
  simpl in Hchain; destruct Hchain as [? [? ?]].
  invert_rel_typ_body.
  eassumption.
Qed.

Lemma rel_exp_of_level : forall {Γ M M'},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' (per_lvl_at n)) ->
    Γ ⊨ M ≈ M' : Level@n.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists (per_lvl_at n).
  split; [| eapply H; eassumption].
  pose proof (per_univ_elem_level 0) as Hn.
  econstructor; try apply eval_exp_level.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_level : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_level : mctt.
#[export]
Hint Resolve rel_exp_of_typ_level valid_exp_level valid_exp_level_small : mctt.
#[export]
Hint Resolve rel_exp_of_level : mctt.
Ltac eexists_rel_exp_of_level :=
  apply rel_exp_of_level;
  eexists;
  eexists; [eassumption |].

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The sort of the levels is a parameter of this section. *)
  Context {n : nat}.

(** ** The Level Forms

    [𝕃ᵒ o] is a value, and [succl] and [maxl] evaluate by flattening the values
    of their arguments, so each rule is a four-value pattern built from those of
    its arguments. *)
Lemma rel_exp_llit : forall {Γ env_relΓ o},
    fst o <= n ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ 𝕃ᵒ o ≈ 𝕃ᵒ o : Level@n.
Proof.
  intros * Ho HΓ.
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  econstructor; try apply eval_exp_llit.
  apply rel_chain_4; apply per_lvl_at_lit; exact Ho.
Qed.

Corollary valid_exp_llit : forall {Γ o},
    fst o <= n ->
    ⊨ Γ ->
    Γ ⊨ 𝕃ᵒ o : Level@n.
Proof.
  intros * Ho H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_llit; eassumption.
Qed.

Hint Resolve valid_exp_llit : mctt.

Lemma rel_exp_succl_cong : forall {Γ M M'},
    Γ ⊨ M ≈ M' : Level@n ->
    Γ ⊨ succl M ≈ succl M' : Level@n.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hchain].
  apply (mk_rel_exp (dlvl_suc m1) (dlvl_suc m2) (dlvl_suc m3) (dlvl_suc m4));
    try (apply eval_exp_succl; eassumption).
  apply rel_chain_4; apply per_lvl_at_suc; pairwise.
Qed.

Hint Resolve rel_exp_succl_cong : mctt.

Lemma rel_exp_maxl_cong : forall {Γ M M' N N'},
    Γ ⊨ M ≈ M' : Level@n ->
    Γ ⊨ N ≈ N' : Level@n ->
    Γ ⊨ maxl M N ≈ maxl M' N' : Level@n.
Proof.
  intros * HM HN.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (dlvl_max m1 n1) (dlvl_max m2 n2) (dlvl_max m3 n3) (dlvl_max m4 n4));
    try (apply eval_exp_maxl; eassumption).
  apply rel_chain_4; apply per_lvl_at_max; pairwise.
Qed.

Hint Resolve rel_exp_maxl_cong : mctt.

(** ** The Level Equations

    Each is a four-value pattern whose middle link is the corresponding lemma
    of [Core.Semantic.Levels], with the bound of both sides, and whose outer
    links are the reflexivity of both sides. *)
Lemma rel_exp_llit_succl : forall {Γ env_relΓ a b},
    a <= n ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n.
Proof.
  intros * Ha HΓ.
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  apply (mk_rel_exp (dlvl_lit (a, S b)) (dlvl_lit (a, S b)) (dlvl_suc (dlvl_lit (a, b))) (dlvl_suc (dlvl_lit (a, b))));
    try (apply eval_exp_llit);
    try (apply eval_exp_succl, eval_exp_llit).
  apply rel_chain_4;
    [ apply per_lvl_at_lit; exact Ha
    | apply per_lvl_at_of_lvl; [ apply per_lvl_llit_suc | lvl_bnd ]
    | apply per_lvl_at_suc, per_lvl_at_lit; exact Ha ].
Qed.

Corollary valid_exp_llit_succl : forall {Γ a b},
    a <= n ->
    ⊨ Γ ->
    Γ ⊨ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n.
Proof.
  intros * Ha H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_llit_succl; eassumption.
Qed.

Hint Resolve rel_exp_llit_succl valid_exp_llit_succl : mctt.

Lemma rel_exp_maxl_zero : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ maxl (𝕃@0) M ≈ M : Level@n.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (dlvl_max (dlvl_lit oz) m1) (dlvl_max (dlvl_lit oz) m2) m3 m4);
    try (apply eval_exp_maxl; [ apply eval_exp_llit | eassumption ]);
    try eassumption.
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ apply per_lvl_at_lit; cbn; lia | pairwise ]
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_zero; lvl_pw | lvl_bnd ]
    | pairwise ].
Qed.

Hint Resolve rel_exp_maxl_zero : mctt.

Lemma rel_exp_maxl_assoc : forall {Γ M N P},
    Γ ⊨ M : Level@n ->
    Γ ⊨ N : Level@n ->
    Γ ⊨ P : Level@n ->
    Γ ⊨ maxl (maxl M N) P ≈ maxl M (maxl N P) : Level@n.
Proof.
  intros * HM HN HP.
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
  apply (mk_rel_exp (dlvl_max (dlvl_max m1 n1) p1) (dlvl_max (dlvl_max m2 n2) p2)
                    (dlvl_max m3 (dlvl_max n3 p3)) (dlvl_max m4 (dlvl_max n4 p4)));
    try (apply eval_exp_maxl; [ apply eval_exp_maxl |]; eassumption);
    try (apply eval_exp_maxl; [| apply eval_exp_maxl ]; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ apply per_lvl_at_max |]; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_assoc; lvl_pw | lvl_bnd ]
    | apply per_lvl_at_max; [| apply per_lvl_at_max ]; pairwise ].
Qed.

Hint Resolve rel_exp_maxl_assoc : mctt.

Lemma rel_exp_maxl_comm : forall {Γ M N},
    Γ ⊨ M : Level@n ->
    Γ ⊨ N : Level@n ->
    Γ ⊨ maxl M N ≈ maxl N M : Level@n.
Proof.
  intros * HM HN.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (dlvl_max m1 n1) (dlvl_max m2 n2) (dlvl_max n3 m3) (dlvl_max n4 m4));
    try (apply eval_exp_maxl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_comm; lvl_pw | lvl_bnd ]
    | apply per_lvl_at_max; pairwise ].
Qed.

Hint Resolve rel_exp_maxl_comm : mctt.

Lemma rel_exp_maxl_idem : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ maxl M M ≈ M : Level@n.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (dlvl_max m1 m1) (dlvl_max m2 m2) m3 m4);
    try (apply eval_exp_maxl; eassumption);
    try eassumption.
  apply rel_chain_4;
    [ apply per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_idem; lvl_pw | lvl_bnd ]
    | pairwise ].
Qed.

Hint Resolve rel_exp_maxl_idem : mctt.

Lemma rel_exp_succl_maxl : forall {Γ M N},
    Γ ⊨ M : Level@n ->
    Γ ⊨ N : Level@n ->
    Γ ⊨ succl (maxl M N) ≈ maxl (succl M) (succl N) : Level@n.
Proof.
  intros * HM HN.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HN) as [env_relΓ2 [HΓ2 HNgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  apply (mk_rel_exp (dlvl_suc (dlvl_max m1 n1)) (dlvl_suc (dlvl_max m2 n2))
                    (dlvl_max (dlvl_suc m3) (dlvl_suc n3)) (dlvl_max (dlvl_suc m4) (dlvl_suc n4)));
    try (apply eval_exp_succl, eval_exp_maxl; eassumption);
    try (apply eval_exp_maxl; apply eval_exp_succl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_suc, per_lvl_at_max; pairwise
    | apply per_lvl_at_of_lvl; [ apply per_lvl_suc_max; lvl_pw | lvl_bnd ]
    | apply per_lvl_at_max; apply per_lvl_at_suc; pairwise ].
Qed.

Hint Resolve rel_exp_succl_maxl : mctt.

Lemma rel_exp_maxl_succl : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ maxl M (succl M) ≈ succl M : Level@n.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  apply (mk_rel_exp (dlvl_max m1 (dlvl_suc m1)) (dlvl_max m2 (dlvl_suc m2))
                    (dlvl_suc m3) (dlvl_suc m4));
    try (apply eval_exp_maxl; [ eassumption | apply eval_exp_succl; eassumption ]);
    try (apply eval_exp_succl; eassumption).
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ pairwise | apply per_lvl_at_suc; pairwise ]
    | apply per_lvl_at_of_lvl; [ apply per_lvl_max_suc; lvl_pw | lvl_bnd ]
    | apply per_lvl_at_suc; pairwise ].
Qed.

Hint Resolve rel_exp_maxl_succl : mctt.

(** Absorption: the limit [ω·(n+1)] is above every level of sort [n]
    ([per_lvl_absorb]).  The two sides are levels of sort [n+1]. *)
Lemma rel_exp_maxl_absorb : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ maxl M (𝕃ᵒ(S n, 0)) ≈ 𝕃ᵒ(S n, 0) : Level@(S n).
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_level.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (H12 : Dom m1 ≈ m2 ∈ per_lvl_at n) by pairwise.
  assert (H22 : Dom m2 ≈ m2 ∈ per_lvl_at n) by pairwise.
  apply (mk_rel_exp (dlvl_max m1 (dlvl_lit (S n, 0))) (dlvl_max m2 (dlvl_lit (S n, 0)))
                    (dlvl_lit (S n, 0)) (dlvl_lit (S n, 0)));
    try (apply eval_exp_maxl; [ eassumption | apply eval_exp_llit ]);
    try (apply eval_exp_llit).
  assert (H12' : Dom m1 ≈ m2 ∈ per_lvl_at (S n)) by (eapply per_lvl_at_mono; [| exact H12 ]; lia).
  assert (H22' : Dom m2 ≈ m2 ∈ per_lvl_at (S n)) by (eapply per_lvl_at_mono; [| exact H22 ]; lia).
  apply rel_chain_4;
    [ apply per_lvl_at_max; [ exact H12' | apply per_lvl_at_lit; cbn; lia ]
    | apply per_lvl_at_of_lvl;
      [ eapply per_lvl_absorb; exact H22
      | apply per_lvl_at_max; [ exact H22' | apply per_lvl_at_lit; cbn; lia ] ]
    | apply per_lvl_at_lit; cbn; lia ].
Qed.

Corollary valid_exp_maxl_absorb : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ maxl M (𝕃ᵒ(S n, 0)) ≈ 𝕃ᵒ(S n, 0) : Level@(S n).
Proof. intros; apply rel_exp_maxl_absorb; assumption. Qed.

Hint Resolve rel_exp_maxl_absorb valid_exp_maxl_absorb : mctt.

End Fixed_GCtx.

(** ** Universes at a Level@n Term

    A type of the small universe [Type⟨T⟩] is a four-value pattern in the
    small universe at the realiser of [T]'s value: that is the universe's
    element PER ([per_univ_elem_core_suniv]), and related levels have the same
    realiser ([per_lvl_real]), so it does not depend on which of [T]'s four
    values is taken. *)
Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The sort of the levels is a parameter of this section: the elements of
    [Level@n] are the level values, whatever the sort, so each case is proved
    once for every sort. *)
  Context {n : nat}.

Lemma rel_exp_of_suniv_tm : forall {Γ T A A'},
    Γ ⊨ T : Level@n ->
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          forall t, ⟦ T ⟧ ρσ ↘ t ->
          rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ (us (dlvl_real t)))) ->
    Γ ⊨ A ≈ A' : Type⟨T⟩.
Proof.
  intros * HT [env_relΓ [HΓ H]].
  pose proof (rel_exp_of_level_inversion HT) as [env_relΓT [HΓT HTgen]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HTgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htchain].
  assert (H12 : Dom t1 ≈ t2 ∈ per_lvl) by lvl_pw.
  assert (H23 : Dom t2 ≈ t3 ∈ per_lvl) by lvl_pw.
  assert (H34 : Dom t3 ≈ t4 ∈ per_lvl) by lvl_pw.
  pose proof (per_lvl_real _ _ H12) as E12.
  pose proof (per_lvl_real _ _ H23) as E23.
  pose proof (per_lvl_real _ _ H34) as E34.
  exists (per_univ (us (dlvl_real t2))).
  split; [| eapply H; eassumption ].
  apply (mk_rel_exp 𝕌@t1 𝕌@t2 𝕌@t3 𝕌@t4);
    try (apply eval_exp_univ; eassumption).
  apply rel_chain_4; apply per_univ_elem_core_suniv';
    solve [ assumption | rewrite ?E12, ?E23, ?E34; first [ exact I | reflexivity ]
          | rewrite <- ?E12; first [ exact I | reflexivity ] ].
Qed.

(** The converse: a judgment at [Type⟨T⟩] relates, at every pair of
    environments, its four values in the small universe at the realiser of
    [T]'s inner value. *)
Lemma rel_exp_of_suniv_tm_inversion : forall {Γ T A A'},
    Γ ⊨ A ≈ A' : Type⟨T⟩ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        exists t, ⟦ T ⟧ ρσ ↘ t /\ rel_exp A σ ρ ρσ A' σ' ρ' ρ'σ' (per_univ (us (dlvl_real t))).
Proof.
  intros * [env_relΓ [HΓ [i HA]]].
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [R [Htyp Hexp]].
  destruct Htyp as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Hchain].
  cbn [exp_sub] in *.
  inversion Hu1; inversion Hu2; inversion Hu3; inversion Hu4; subst.
  destruct Hchain as [Hl12 _].
  (** The first link names the element PER: the small universe at the
      realiser of the outer level, which is the inner one's. *)
  invert_per_univ_elem Hl12.
  match goal with HT : ⟦ T ⟧ ρσ ↘ ?t |- _ => exists t; split; [ exact HT |] end.
  destruct Hexp as [? ? ? ? ? ? ? ? Hc].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| exact Hc ].
  intros x y Hxy.
  match goal with
  | Hl : per_lvl ?a ?b, Heq : _ <~> _ |- per_univ (us (dlvl_real ?b)) _ _ =>
      rewrite <- (per_lvl_real _ _ Hl); apply Heq in Hxy; exact Hxy
  end.
Qed.

Corollary rel_exp_of_suniv_tm_inversion_simple : forall {Γ T A A'},
    Γ ⊨ A ≈ A' : Type⟨T⟩ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ env_rel ->
      exists a a' t,
        ⟦ A ⟧ ρ ↘ a /\ ⟦ A' ⟧ ρ' ↘ a' /\ ⟦ T ⟧ ρ ↘ t /\ Dom a ≈ a' ∈ per_univ (us (dlvl_real t)).
Proof.
  intros * H%rel_exp_of_suniv_tm_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists; eexists; [eassumption |].
  intros ρ ρ' Hρ.
  destruct (HA _ _ HΓ _ _ (rel_sub_id (ex_intro _ _ HΓ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [t [Ht [aσ a a' a'σ' HaσI ? ? Ha'σ'I Hchain]]].
  rewrite exp_sub_id in HaσI, Ha'σ'I.
  exists a, a', t.
  repeat split; try eassumption.
  pairwise.
Qed.

(** A type of a small universe is a type of every large one. *)
Corollary rel_exp_suniv_tm_large : forall {Γ T A A'} {i : nat},
    Γ ⊨ A ≈ A' : Type⟨T⟩ ->
    Γ ⊨ A ≈ A' : Typeω@i.
Proof.
  intros * H%rel_exp_of_suniv_tm_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  apply rel_exp_of_typ; eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [t [_ [? ? ? ? ? ? ? ? Hchain]]].
  econstructor; try eassumption.
  eapply rel_chain_mono; [| eassumption ].
  intros ? ? Hx; eapply (per_univ_cumu_uidx (u := us _)); [| exact Hx ]; exact I.
Qed.

(** [Type⟨M⟩] is a type of [Type⟨succl M⟩]: its four values are small
    universes at related levels, each a universe below the realiser of
    [succl M], which is one more than the realiser of [M]. *)
Lemma rel_exp_univ_cong_tm : forall {Γ M M'},
    Γ ⊨ M ≈ M' : Level@n ->
    Γ ⊨ Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩.
Proof.
  intros * HM.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMM.
  apply rel_exp_of_suniv_tm; [ apply rel_exp_succl_cong; exact HMM |].
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists; eexists; [ eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev' t Ht.
  destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  inversion Ht; subst.
  functional_eval_rewrite_clear.
  assert (H12 : Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (H23 : Dom m2 ≈ m3 ∈ per_lvl) by lvl_pw.
  assert (H34 : Dom m3 ≈ m4 ∈ per_lvl) by lvl_pw.
  pose proof (per_lvl_real _ _ H12) as E12.
  pose proof (per_lvl_real _ _ H23) as E23.
  pose proof (per_lvl_real _ _ H34) as E34.
  rewrite dlvl_real_suc.
  apply (mk_rel_exp 𝕌@m1 𝕌@m2 𝕌@m3 𝕌@m4); try (apply eval_exp_univ; eassumption).
  apply rel_chain_4; eexists; apply per_univ_elem_core_suniv';
    first [ eassumption | cbn; ord | reflexivity ].
Qed.

Corollary valid_exp_univ_tm : forall {Γ M},
    Γ ⊨ M : Level@n ->
    Γ ⊨ Type⟨M⟩ : Type⟨succl M⟩.
Proof. intros; apply rel_exp_univ_cong_tm; assumption. Qed.

(** ** Subtyping of Small Universes

    The premise [maxl M M' ≈ M'] is, in the model, the canonical order on the
    two levels at every length ([per_sublvl_of_max]), which is what
    [per_subtyp_suniv] asks.  A small universe below a large one needs only
    that its level is a level. *)
Lemma subtyp_suniv_tm : forall {Γ M M'},
    Γ ⊨ M : Level@n ->
    Γ ⊨ M' : Level@n ->
    Γ ⊨ maxl M M' ≈ M' : Level@n ->
    Γ ⊨ Type⟨M⟩ ⊆ Type⟨M'⟩.
Proof.
  intros * HM HM' Hmax.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (rel_exp_of_level_inversion HM') as [env_relΓ' [HΓ' HM'gen]].
  pose proof (rel_exp_of_level_inversion Hmax) as [env_relΓ'' [HΓ'' Hmaxgen]].
  eexists_subtyp_with 0.
  intros Γ' env_rel' HΓ0 σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (HM'gen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  destruct (Hmaxgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [j1 j2 j3 j4 Hj1 Hj2 Hj3 Hj4 Hjchain].
  inversion Hj2; subst.
  functional_eval_rewrite_clear.
  assert (Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom m2 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom n4 ≈ n3 ∈ per_lvl) by lvl_pw.
  assert (Dom n2 ≈ n3 ∈ per_lvl) by lvl_pw.
  assert (Dom dlvl_max m2 n2 ≈ n3 ∈ per_lvl) by lvl_pw.
  functional_eval_rewrite_clear.
  exists 𝕌@m1, 𝕌@m2, 𝕌@n4, 𝕌@n3.
  repeat apply conj; try (apply eval_exp_univ; eassumption).
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - apply per_subtyp_suniv; [| exact I ].
    apply (per_sublvl_of_max m2 n2 n3); assumption.
Qed.

Lemma subtyp_small_large_tm : forall {Γ M} {i : nat},
    Γ ⊨ M : Level@n ->
    Γ ⊨ Type⟨M⟩ ⊆ Typeω@i.
Proof.
  intros * HM.
  pose proof (rel_exp_of_level_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_subtyp_with (S i).
  intros Γ' env_rel' HΓ0 σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ0 _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Dom m1 ≈ m2 ∈ per_lvl) by lvl_pw.
  assert (Dom m2 ≈ m2 ∈ per_lvl) by lvl_pw.
  exists 𝕌@m1, 𝕌@m2, 𝕌ω@i, 𝕌ω@i.
  repeat apply conj; try (apply eval_exp_univ; eassumption); try apply eval_exp_typ.
  - eexists; apply per_univ_elem_core_suniv';
      [ eassumption | exact I | reflexivity ].
  - eexists; apply per_univ_elem_core_univ'; [ solve_uidx | reflexivity ].
  - apply per_subtyp_small_large; [ assumption | solve_uidx ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve rel_exp_univ_cong_tm valid_exp_univ_tm subtyp_suniv_tm subtyp_small_large_tm : mctt.

#[export]
Hint Resolve valid_exp_llit rel_exp_succl_cong rel_exp_maxl_cong : mctt.
#[export]
Hint Resolve rel_exp_llit_succl valid_exp_llit_succl rel_exp_maxl_zero rel_exp_maxl_assoc rel_exp_maxl_comm
  rel_exp_maxl_idem rel_exp_succl_maxl rel_exp_maxl_succl valid_exp_maxl_absorb : mctt.
