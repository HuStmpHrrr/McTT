(** * Fundamental Theorem: the Unit and Empty Types

    Substitution pushes through [⊤], [⋆], [⊥] and the eliminator of [⊥] by
    computation of [exp_sub]: the first three are closed, and
<<
(efq M return A)[σ] ≡ efq M[σ] return A[q σ]
>>
    So what is validated here is the typing of the three constants, η for [⊤],
    and the congruence rule of the eliminator.

    Every pair of values is related at [⊤], so η holds in the model without a
    computation.  [⊥] has the element PER of a neutral type, so the eliminator
    only ever meets a neutral, and the proof of its congruence rule is the
    neutral case of the [ℕ]-eliminator's, without the branches. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation SubstitutionCases UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [⊤]'s and [⊥]'s [per_univ_elem], at their canonical element PERs and at
    any level. *)
Lemma per_univ_elem_True : forall i,
    DF ⊤ᵈ ≈ ⊤ᵈ ∈ per_univ_elem i ↘ per_True.
Proof.
  intros; per_univ_elem_econstructor; reflexivity.
Qed.

Hint Resolve per_univ_elem_True : mctt.

Lemma per_univ_elem_False : forall i,
    DF ⊥ᵈ ≈ ⊥ᵈ ∈ per_univ_elem i ↘ per_ne.
Proof.
  intros; per_univ_elem_econstructor; reflexivity.
Qed.

Hint Resolve per_univ_elem_False : mctt.

(** ** [⊤] and [⊥] as Types

    Stated from the context PER, as [rel_exp_of_typ_nat] is. *)
Lemma rel_exp_of_typ_True : forall {Γ} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊤ ≈ ⊤ : Type@i.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ⊤ᵈ ≈ ⊤ᵈ ∈ per_univ i)
    by (eexists; apply per_univ_elem_True).
  econstructor; try apply eval_exp_True.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ_True : mctt.

Corollary valid_exp_True : forall {Γ} {i : nat},
    ⊨ Γ ->
    Γ ⊨ ⊤ : Type@i.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_of_typ_True; eassumption.
Qed.

Hint Resolve valid_exp_True : mctt.

Lemma rel_exp_of_typ_False : forall {Γ} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊥ ≈ ⊥ : Type@i.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ⊥ᵈ ≈ ⊥ᵈ ∈ per_univ i)
    by (eexists; apply per_univ_elem_False).
  econstructor; try apply eval_exp_False.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ_False : mctt.

Corollary valid_exp_False : forall {Γ} {i : nat},
    ⊨ Γ ->
    Γ ⊨ ⊥ : Type@i.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_of_typ_False; eassumption.
Qed.

Hint Resolve valid_exp_False : mctt.

(** [⊤] in a universe at any index, in particular in the small ones. *)
Lemma rel_exp_of_univ_True : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊤ ≈ ⊤ : univ_tm u.
Proof.
  intros * HΓ.
  apply rel_exp_of_univ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ⊤ᵈ ≈ ⊤ᵈ ∈ per_univ u)
    by (eexists; per_univ_elem_econstructor; reflexivity).
  econstructor; try apply eval_exp_True.
  apply rel_chain_4; assumption.
Qed.

Corollary valid_exp_True_small : forall {Γ n},
    ⊨ Γ ->
    Γ ⊨ ⊤ : Typeˢ@n.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_True (u := us n) HΓ).
Qed.

Hint Resolve valid_exp_True_small : mctt.

(** [⊥] in a universe at any index, in particular in the small ones. *)
Lemma rel_exp_of_univ_False : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⊥ ≈ ⊥ : univ_tm u.
Proof.
  intros * HΓ.
  apply rel_exp_of_univ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ⊥ᵈ ≈ ⊥ᵈ ∈ per_univ u)
    by (eexists; per_univ_elem_econstructor; reflexivity).
  econstructor; try apply eval_exp_False.
  apply rel_chain_4; assumption.
Qed.

Corollary valid_exp_False_small : forall {Γ n},
    ⊨ Γ ->
    Γ ⊨ ⊥ : Typeˢ@n.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_False (u := us n) HΓ).
Qed.

Hint Resolve valid_exp_False_small : mctt.

(** ** [⊤] and [⊥] as the Types of Terms

    As for [ℕ], a judgment at either type is exactly a four-value pattern in its
    element PER. *)
Lemma rel_exp_of_True_inversion : forall {Γ M M'},
    Γ ⊨ M ≈ M' : ⊤ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' per_True.
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

Lemma rel_exp_of_True : forall {Γ M M'},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' per_True) ->
    Γ ⊨ M ≈ M' : ⊤.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists per_True.
  split; [| eapply H; eassumption].
  pose proof (per_univ_elem_True 0) as Hn.
  econstructor; try apply eval_exp_True.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_True : mctt.

Lemma rel_exp_of_False_inversion : forall {Γ M M'},
    Γ ⊨ M ≈ M' : ⊥ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' per_ne.
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

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_True per_univ_elem_False : mctt.
#[export]
Hint Resolve rel_exp_of_typ_True valid_exp_True valid_exp_True_small : mctt.
#[export]
Hint Resolve rel_exp_of_typ_False valid_exp_False valid_exp_False_small : mctt.
#[export]
Hint Resolve rel_exp_of_True : mctt.
Ltac eexists_rel_exp_of_True :=
  apply rel_exp_of_True;
  eexists;
  eexists; [eassumption |].

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** [⋆] and η

    [⋆[σ]] is [⋆], and every pair of values is related at [⊤]. *)
Lemma rel_exp_true : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ⋆ ≈ ⋆ : ⊤.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_True.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  econstructor; try apply eval_exp_true.
  apply rel_chain_4; exact I.
Qed.

Corollary valid_exp_true : forall {Γ},
    ⊨ Γ ->
    Γ ⊨ ⋆ : ⊤.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_true; eassumption.
Qed.

Hint Resolve valid_exp_true : mctt.

Lemma rel_exp_true_eta : forall {Γ M},
    Γ ⊨ M : ⊤ ->
    Γ ⊨ M ≈ ⋆ : ⊤.
Proof.
  intros * HM.
  pose proof (rel_exp_of_True_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_True.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hchain].
  apply (mk_rel_exp m1 m2 ⋆ᵈ ⋆ᵈ);
    solve [ eassumption | apply eval_exp_true | apply rel_chain_4; exact I ].
Qed.

Hint Resolve rel_exp_true_eta : mctt.

(** ** Extension by [⊥]

    The head PER of [⊥] is [per_ne], in both directions, and the context PER of
    [Γ ▹ ⊥] has the corresponding rule. *)
Lemma per_head_of_False : forall {ρ ρ' m m'},
    Dom m ≈ m' ∈ per_ne ->
    Dom m ≈ m' ∈ per_head ⊥ ⊥ ρ ρ'.
Proof.
  intros * H.
  eapply per_head_of;
    [ apply eval_exp_False | apply eval_exp_False | apply (per_univ_elem_False 0) | eassumption ].
Qed.

Lemma per_ne_of_head_False : forall {ρ ρ' m m'},
    Dom m ≈ m' ∈ per_head ⊥ ⊥ ρ ρ' ->
    Dom m ≈ m' ∈ per_ne.
Proof.
  intros * H.
  eapply (H 0 per_ne);
    [ apply eval_exp_False | apply eval_exp_False | apply per_univ_elem_False ].
Qed.

Corollary per_ctx_env_False : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹ ⊥ ≈ Γ ▹ ⊥ ∈ per_ctx_env ↘ (per_env_extend ⊥ ⊥ env_relΓ).
Proof.
  intros * HΓ.
  eapply per_ctx_env_of_typ; [ eassumption |].
  eapply (@rel_exp_of_typ_False _ _ 0); eassumption.
Qed.

Corollary per_env_extend_False_intro : forall {env_relΓ ρ ρ' m m'},
    Dom ρ ≈ ρ' ∈ env_relΓ ->
    Dom m ≈ m' ∈ per_ne ->
    Dom ρ ↦ m ≈ ρ' ↦ m' ∈ per_env_extend ⊥ ⊥ env_relΓ.
Proof.
  intros * Hρ Hm.
  apply per_env_extend_intro'; [ eassumption | apply per_head_of_False; eassumption ].
Qed.

(** ** The Semantic Eliminator

    The only obligation is the motive at an arbitrary pair of related
    arguments, as a [per_univ_elem] at a family [Rel] of element PERs indexed by
    the pair, as in [per_nat_natrec].  The readback of the neutral eliminator
    uses it at a fresh variable. *)
Lemma per_bot_exfalso : forall {i : nat} {Aa Ab ρa ρb m m'}
                               {Rel : domain -> domain -> relation domain},
    (forall w z,
        Dom w ≈ z ∈ per_ne ->
        exists a a',
          ⟦ Aa ⟧ ρa ↦ w ↘ a /\ ⟦ Ab ⟧ ρb ↦ z ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem i ↘ (Rel w z)) ->
    Dom m ≈ m' ∈ per_bot ->
    Dom efqᵈ m under ρa return Aa ≈ efqᵈ m' under ρb return Ab ∈ per_bot.
Proof.
  intros * Hmot Hm s.
  assert (Hvar : Dom ⇑! ⊥ᵈ s ≈ ⇑! ⊥ᵈ s ∈ per_ne)
    by (econstructor; apply var_per_bot).
  destruct (Hmot _ _ Hvar) as [b [b' [Hb [Hb' Hbb']]]].
  destruct (per_univ_then_per_top_typ Hbb' (S s)) as [B' [HB'l HB'r]].
  destruct (Hm s) as [M [HMl HMr]].
  eexists; split; econstructor; eassumption.
Qed.

Lemma per_ne_exfalso : forall {i : nat} {Aa Ab ρa ρb}
                              {Rel : domain -> domain -> relation domain},
    (forall w z,
        Dom w ≈ z ∈ per_ne ->
        exists a a',
          ⟦ Aa ⟧ ρa ↦ w ↘ a /\ ⟦ Ab ⟧ ρb ↦ z ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem i ↘ (Rel w z)) ->
    forall M M' m m',
      ⟦ M ⟧ ρa ↘ m ->
      ⟦ M' ⟧ ρb ↘ m' ->
      Dom m ≈ m' ∈ per_ne ->
      exists r r',
        ⟦ efq M return Aa ⟧ ρa ↘ r /\
          ⟦ efq M' return Ab ⟧ ρb ↘ r' /\
          Dom r ≈ r' ∈ Rel m m'.
Proof.
  intros * Hmot * HM HM' Hmm'.
  destruct (Hmot _ _ Hmm') as [c [c' [Hc [Hc' Hcc']]]].
  inversion Hmm'; subst.
  do 2 eexists.
  split; [ eapply eval_exp_exfalso; eassumption |].
  split; [ eapply eval_exp_exfalso; eassumption |].
  eapply per_bot_then_per_elem; [ exact Hcc' |].
  eapply per_bot_exfalso; eassumption.
Qed.

(** ** The Motive at an Arbitrary Argument Pair

    The obligation of [per_ne_exfalso] for all three links, in the one family
    [Rel w z := per_head A A (⟦σ⟧ρ ↦ w) (⟦σ'⟧ρ' ↦ z)].  The proof is that of
    [rel_typ_of_nat_motive] with [⊥] for [ℕ]. *)
Lemma rel_typ_of_False_motive : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ⊥ ⊨ A ≈ A' : Type@i ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        forall w z,
          Dom w ≈ z ∈ per_ne ->
          (exists b b',
              ⟦ A[q σ] ⟧ ρ ↦ w ↘ b /\ ⟦ A ⟧ ρσ ↦ z ↘ b' /\
                DF b ≈ b' ∈ per_univ_elem i
                     ↘ (per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))) /\
          (exists b b',
              ⟦ A ⟧ ρσ ↦ w ↘ b /\ ⟦ A' ⟧ ρ'σ' ↦ z ↘ b' /\
                DF b ≈ b' ∈ per_univ_elem i
                     ↘ (per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))) /\
          (exists b b',
              ⟦ A' ⟧ ρ'σ' ↦ w ↘ b /\ ⟦ A'[q σ'] ⟧ ρ' ↦ z ↘ b' /\
                DF b ≈ b' ∈ per_univ_elem i
                     ↘ (per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))).
Proof.
  intros * HΓ HA * HΓ' * Hσj Hρ Hev Hev' * Hwz.
  pose proof (@rel_exp_of_typ_False _ _ 0 _ HΓ) as HF.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  assert (Hww : Dom w ≈ w ∈ per_ne) by (transitivity z; [| symmetry]; exact Hwz).
  assert (Hzz : Dom z ≈ z ∈ per_ne) by (transitivity w; [symmetry |]; exact Hwz).
  pose proof (per_env_extend_False_intro Hρ Hwz) as Hp_wz.
  pose proof (per_env_extend_False_intro Hρ Hww) as Hp_ww.
  pose proof (per_env_extend_False_intro Hρ Hzz) as Hp_zz.
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HF HAl _ _ _ _ _ _ Hp_wz Hev Hev')
    as [[b1 [c1 [Hb1 [Hc1 Hbc1]]]] [[a1 [g1 [Ha1 [Hg1 Hag1]]]] _]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HF HAl _ _ _ _ _ _ Hp_zz Hev Hev')
    as [_ [[c2 [g2 [Hc2 [Hg2 Hcg2]]]] _]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HF HA _ _ _ _ _ _ Hp_wz Hev Hev')
    as [_ [[a2 [d1 [Ha2 [Hd1 Had1]]]] [e1 [f1 [He1 [Hf1 Hef1]]]]]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HF HA _ _ _ _ _ _ Hp_ww Hev Hev')
    as [_ [[a3 [e2 [Ha3 [He2 Hae2]]]] _]].
  assert (c2 = c1) as -> by (eapply functional_eval_exp; eassumption).
  assert (g2 = g1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (e2 = e1) as -> by (eapply functional_eval_exp; eassumption).
  assert (C1 : rel_chain (per_univ i) ([b1; c1; g1; a1; d1])).
  { apply rel_chain_cons; [ exact Hbc1 |].
    apply rel_chain_cons; [ exact Hcg2 |].
    apply rel_chain_cons; [ symmetry; exact Hag1 |].
    apply rel_chain_of_pair; exact Had1. }
  assert (C2 : rel_chain (per_univ i) ([a1; e1; f1]))
    by (apply rel_chain_cons; [ exact Hae2 | apply rel_chain_of_pair; exact Hef1 ]).
  assert (Cbig : rel_chain (per_univ i) ([b1; c1; g1; a1; d1; e1; f1]))
    by (merge_rel_chain C1 C2 a1).
  assert (HAnchor : DF a1 ≈ g1 ∈ per_univ_elem i
                         ↘ (per_head A A (ρσ ↦ w) (ρ'σ' ↦ z)))
    by (eapply per_univ_elem_at_head; [ exact Ha1 | exact Hg1 | exact Hag1 ]).
  assert (CbigR : rel_chain
                    (per_univ_elem i (per_head A A (ρσ ↦ w) (ρ'σ' ↦ z)))
                    ([b1; c1; g1; a1; d1; e1; f1]))
    by (eapply per_univ_chain_at_in; [ exact Cbig | | | exact HAnchor ]; solve_in).
  repeat split.
  - exists b1, c1; repeat split; try eassumption.
    pairwise.
  - exists a1, d1; repeat split; try eassumption.
    pairwise.
  - exists e1, f1; repeat split; try eassumption.
    pairwise.
Qed.

(** ** The Diagonal, for the Gluing Model

    [per_bot_exfalso] at one environment and no substitution. *)
Lemma per_bot_exfalso_diag : forall {Γ A} {i : nat} {env_relΓ ρ m},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ⊥ ⊨ A ≈ A : Type@i ->
    Dom ρ ≈ ρ ∈ env_relΓ ->
    Dom m ≈ m ∈ per_bot ->
    Dom efqᵈ m under ρ return A ≈ efqᵈ m under ρ return A ∈ per_bot.
Proof.
  intros * HΓ HA Hρ Hm.
  pose proof (rel_sub_id (ex_intro _ _ HΓ)) as Hid.
  pose proof (rel_typ_of_False_motive HΓ HA _ _ HΓ _ _ _ _ _ _ Hid Hρ
                (eval_sub_id ρ) (eval_sub_id ρ)) as Hmot.
  eapply (per_bot_exfalso (Rel := fun x y => per_head A A (ρ ↦ x) (ρ ↦ y)));
    [ intros w z Hwz; exact (proj1 (proj2 (Hmot w z Hwz))) | exact Hm ].
Qed.

(** ** The Eliminator's Congruence Rule

    Three instantiations of [per_ne_exfalso], at the three links of the
    scrutinee's chain, in the family of head PERs of the motive that
    [rel_typ_of_instance] reports; [per_head_of_args] then moves each link to
    the argument pair the type names, as in [rel_exp_natrec_cong]. *)
Lemma rel_exp_exfalso_cong : forall {Γ A A'} {i : nat} {M M'},
    Γ ▹ ⊥ ⊨ A ≈ A' : Type@i ->
    Γ ⊨ M ≈ M' : ⊥ ->
    Γ ⊨ efq M return A ≈ efq M' return A' : A[Id ,, M].
Proof.
  intros * HA HM.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_of_False_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (@rel_exp_of_typ_False _ _ i _ HΓ) as HF.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** *** The Type *)
  destruct (rel_typ_of_instance HF HAl HMl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  assert (a2 = ⊥ᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha2 | apply eval_exp_False ]).
  assert (a3 = ⊥ᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha3 | apply eval_exp_False ]).
  assert (HRN : RN <~> per_ne)
    by (eapply per_univ_elem_right_irrel; [ exact Hmid | apply (per_univ_elem_False 0) ]).
  rewrite HRN in Hpchain.
  assert (Hcodn : forall w z,
             Dom w ≈ z ∈ per_ne ->
             exists b b',
               ⟦ A ⟧ ρσ ↦ w ↘ b /\ ⟦ A ⟧ ρ'σ' ↦ z ↘ b' /\
                 Dom b ≈ b' ∈ per_univ i)
    by (intros w z Hwz; apply (Hcod w z); rewrite HRN; exact Hwz).
  exists (per_head A A (ρσ ↦ p2) (ρ'σ' ↦ p3)).
  split; [ exact Htyp |].
  (** *** The Scrutinee *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Hp1m1 : p1 = m1) by (eapply functional_eval_exp; [ exact Hp1 | exact Hm1 ]).
  assert (Hp2m2 : p2 = m2) by (eapply functional_eval_exp; [ exact Hp2 | exact Hm2 ]).
  subst p1 p2.
  assert (Hall : rel_chain per_ne ([m1; m2; m3; m4; p3; p4]))
    by (merge_rel_chain Hmchain Hpchain m1).
  assert (Hm12 : Dom m1 ≈ m2 ∈ per_ne) by pairwise.
  assert (Hm23 : Dom m2 ≈ m3 ∈ per_ne) by pairwise.
  assert (Hm34 : Dom m3 ≈ m4 ∈ per_ne) by pairwise.
  assert (Hm2p3 : Dom m2 ≈ p3 ∈ per_ne) by pairwise.
  assert (Hm22 : Dom m2 ≈ m2 ∈ per_ne) by pairwise.
  assert (Hm24 : Dom m2 ≈ m4 ∈ per_ne) by pairwise.
  (** *** The Three Eliminations *)
  pose proof (rel_typ_of_False_motive HΓ HA _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as Hmotgen.
  destruct (per_ne_exfalso
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj1 (Hmotgen w z H)) _ _ _ _ Hm1 Hm2 Hm12)
    as [r1 [r2 [Hr1 [Hr2 Hr12]]]].
  destruct (per_ne_exfalso
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj1 (proj2 (Hmotgen w z H))) _ _ _ _ Hm2 Hm3 Hm23)
    as [s1 [s2 [Hs1 [Hs2 Hs23]]]].
  destruct (per_ne_exfalso
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj2 (proj2 (Hmotgen w z H))) _ _ _ _ Hm3 Hm4 Hm34)
    as [u1 [u2 [Hu1 [Hu2 Hu34]]]].
  assert (Hs1e : s1 = r2) by (eapply functional_eval_exp; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_exp; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  apply (mk_rel_exp r1 r2 s2 u2); try eassumption.
  apply rel_chain_4;
    [ apply (per_head_of_args Hcodn m1 m2 m2 p3 Hm12 Hm2p3 Hm22); exact Hr12
    | apply (per_head_of_args Hcodn m2 m3 m2 p3 Hm23 Hm2p3 Hm23); exact Hs23
    | apply (per_head_of_args Hcodn m3 m4 m2 p3 Hm34 Hm2p3 Hm24); exact Hu34 ].
Qed.

Hint Resolve rel_exp_exfalso_cong : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve valid_exp_true rel_exp_true_eta rel_exp_exfalso_cong : mctt.
