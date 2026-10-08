(** * Fundamental Theorem: Natural Numbers

    Substitution pushes through [ℕ], [zero], [succ] and the eliminator by
    computation of [exp_sub]: [ℕ[σ]] is [ℕ], [zero[σ]] is [zero], and
<<
(rec M return A | zero -> MZ | succ -> MS end)[σ]
  ≡ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end
>>
    So what is validated here is the eliminator's congruence rule and its two
    β-rules, together with the semantic recursion they share.

    That recursion, [per_nat_natrec], is stated once over a family of element PERs
    [Rel : domain -> domain -> relation domain] indexed by the pair of arguments.
    It is a family because the zero branch lives in the PER of the motive at
    [zero], the successor branch in the PER of the motive at [succ w], and the goal
    in the PER of the motive at the scrutinee; dependent elimination means these
    differ.

    Abstracting over the family also lets one lemma cover the one-sided
    substituted recursion, with [A[q σ]], [MZ[σ]], [MS[q (q σ)]] at [ρ] on the left
    and the unsubstituted eliminator at [⟦σ'⟧ρ'] on the right.  This is
    [per_nat_natrec] at [(Aa, ρa) := (A[q σ], ρ)], with the head PER of that pair
    as the family, since the proof never inspects the shape of [Aa].  So there are
    three instantiations of [per_nat_natrec], one per link of the four-value
    pattern, and only one induction. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation SubstitutionCases UniverseCases SubtypingCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** [ℕ]'s [per_univ_elem], at the canonical element PER and at any level.
    Every [ℕ] obligation below uses this lemma; naming it keeps the level from
    becoming an unresolved existential, as [per_univ_elem_econstructor] under
    [eapply] would leave it. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_elem_nat : forall i,
    DF ℕᵈ ≈ ℕᵈ ∈ per_univ_elem i ↘ per_nat.
Proof.
  intros; per_univ_elem_econstructor; reflexivity.
Qed.

Hint Resolve per_univ_elem_nat : mctt.

(** ** [ℕ] as a Type

    Stated from the context PER rather than from [⊨ Γ], because inside the
    eliminator's congruence rule the only thing known about [Γ] is the PER its
    hypotheses' inversions produce, and [⊨ Γ] does not follow from it.  The level
    is arbitrary because [rel_typ_of_instance] reads the domain and codomain of a
    dependent elimination at one level, the motive's. *)
Lemma rel_exp_of_typ_nat : forall {Γ} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ℕ ≈ ℕ : Typeω@i.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ℕᵈ ≈ ℕᵈ ∈ per_univ i)
    by (eexists; apply per_univ_elem_nat).
  (** [ℕ[σ]] is [ℕ], so all four values come from the same rule. *)
  econstructor; try apply eval_exp_nat.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_typ_nat : mctt.

Corollary valid_exp_nat : forall {Γ} {i : nat},
    ⊨ Γ ->
    Γ ⊨ ℕ : Typeω@i.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_of_typ_nat; eassumption.
Qed.

Hint Resolve valid_exp_nat : mctt.

(** [ℕ] in a universe at any index, in particular in the small ones. *)
Lemma rel_exp_of_univ_nat : forall {Γ u env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ℕ ≈ ℕ : ulvl_tm u.
Proof.
  intros * HΓ.
  apply rel_exp_of_univ.
  eexists; eexists; [eassumption |].
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ℕᵈ ≈ ℕᵈ ∈ per_univ u)
    by (eexists; per_univ_elem_econstructor; reflexivity).
  econstructor; try apply eval_exp_nat.
  apply rel_chain_4; assumption.
Qed.

Corollary valid_exp_nat_small : forall {Γ n},
    ⊨ Γ ->
    Γ ⊨ ℕ : Type⟨𝕃ᵒ n⟩.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  exact (rel_exp_of_univ_nat (u := us n) HΓ).
Qed.

Hint Resolve valid_exp_nat_small : mctt.

(** ** [ℕ] as the Type of a Term

    The [ℕ] analogue of [rel_exp_of_typ_inversion]: a judgment at type [ℕ] is
    exactly a four-value pattern in [per_nat], because the four values of the type
    are all [ℕ] and the [ℕ] case of [per_univ_elem] fixes the element PER. *)
Lemma rel_exp_of_nat_inversion : forall {Γ M M' },
    Γ ⊨ M ≈ M' : ℕ ->
    exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
    forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
      Γ' ⊨s σ ≈ σ' : Γ ->
      forall ρ ρ' ρσ ρ'σ',
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' per_nat.
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

Lemma rel_exp_of_nat : forall {Γ M M'},
    (exists env_rel (_ : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel),
      forall Γ' env_rel' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel') σ σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        forall ρ ρ' ρσ ρ'σ',
          Dom ρ ≈ ρ' ∈ env_rel' ->
          ⟦ σ ⟧s ρ ↘ ρσ ->
          ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
          rel_exp M σ ρ ρσ M' σ' ρ' ρ'σ' per_nat) ->
    Γ ⊨ M ≈ M' : ℕ.
Proof.
  intros * [env_relΓ [HΓ H]].
  eexists_rel_exp_with 0.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists per_nat.
  split; [| eapply H; eassumption].
  pose proof (per_univ_elem_nat 0) as Hn.
  econstructor; try apply eval_exp_nat.
  apply rel_chain_4; assumption.
Qed.

Hint Resolve rel_exp_of_nat : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_elem_nat : mctt.
#[export]
Hint Resolve rel_exp_of_typ_nat : mctt.
#[export]
Hint Resolve valid_exp_nat valid_exp_nat_small : mctt.
#[export]
Hint Resolve rel_exp_of_nat : mctt.
Ltac eexists_rel_exp_of_nat :=
  apply rel_exp_of_nat;
  eexists;
  eexists; [eassumption |].

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** The head PER of [ℕ] is [per_nat], in both directions.  Every context
    extension by [ℕ] uses this, as does every argument obligation of the
    eliminator: callers have [per_nat], while the context PER of [Γ ▹ ℕ] speaks of
    [per_head ℕ ℕ]. *)
Lemma per_head_of_nat : forall {ρ ρ' m m'},
    Dom m ≈ m' ∈ per_nat ->
    Dom m ≈ m' ∈ per_head ℕ ℕ ρ ρ'.
Proof.
  intros * H.
  eapply per_head_of;
    [ apply eval_exp_nat | apply eval_exp_nat | apply (per_univ_elem_nat 0) | eassumption ].
Qed.

Lemma per_nat_of_head : forall {ρ ρ' m m'},
    Dom m ≈ m' ∈ per_head ℕ ℕ ρ ρ' ->
    Dom m ≈ m' ∈ per_nat.
Proof.
  intros * H.
  eapply (H 0 per_nat);
    [ apply eval_exp_nat | apply eval_exp_nat | apply per_univ_elem_nat ].
Qed.

(** The context PER of [Γ ▹ ℕ] and its two rules.  Since [ℕ[σ]] is [ℕ], this
    is also the substituted form [per_ctx_env_of_typ_sub] would produce. *)
Corollary per_ctx_env_nat : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹ ℕ ≈ Γ ▹ ℕ ∈ per_ctx_env ↘ (per_env_extend ℕ ℕ env_relΓ).
Proof.
  intros * HΓ.
  eapply per_ctx_env_of_typ; [ eassumption |].
  eapply (@rel_exp_of_typ_nat _ _ 0); eassumption.
Qed.

Corollary per_env_extend_nat_intro : forall {env_relΓ ρ ρ' m m'},
    Dom ρ ≈ ρ' ∈ env_relΓ ->
    Dom m ≈ m' ∈ per_nat ->
    Dom ρ ↦ m ≈ ρ' ↦ m' ∈ per_env_extend ℕ ℕ env_relΓ.
Proof.
  intros * Hρ Hm.
  apply per_env_extend_intro'; [ eassumption | apply per_head_of_nat; eassumption ].
Qed.

Corollary per_env_extend_nat_elim : forall {env_relΓ ρ ρ'},
    Dom ρ ≈ ρ' ∈ per_env_extend ℕ ℕ env_relΓ ->
    Dom ρ↯ ≈ ρ'↯ ∈ env_relΓ /\ Dom (ρ 0) ≈ (ρ' 0) ∈ per_nat.
Proof.
  intros * [Htail Hhead].
  split; [ eassumption | eapply per_nat_of_head; eassumption ].
Qed.

(** ** The Semantic Recursor

    The three obligations are the semantic content of the eliminator's three
    premises, each stated at the argument pair the recursion needs:

    - [Hmot]: the motive at an arbitrary pair of related arguments, as a
      [per_univ_elem] at the family, which pins down [Rel];
    - [Hz]: the zero branch, in the family at [(zero, zero)];
    - [Hsucc]: the successor branch, at an arbitrary argument pair and a pair of
      recursive results related in the family there, landing in the family at
      the successors.

    Nothing else about [Aa], [Ab], [MZa], … is used, which is why the same lemma
    serves the substituted links.

    [per_bot_natrec] is the neutral case.  It uses the obligations at three fixed
    argument pairs (a fresh variable, [zero], and the successor of that variable),
    which are where [read_ne_natrec] reads the motive.  The recursive call's
    argument is [⇑! b (S s)], the variable at the motive's value, so [Hsucc] is
    instantiated at [var_per_elem]. *)
Lemma per_bot_natrec : forall {i : nat} {Aa Ab MZa MZb MSa MSb ρa ρb za zb m m'}
                              {Rel : domain -> domain -> relation domain},
    (forall w z,
        Dom w ≈ z ∈ per_nat ->
        exists a a',
          ⟦ Aa ⟧ ρa ↦ w ↘ a /\ ⟦ Ab ⟧ ρb ↦ z ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem i ↘ (Rel w z)) ->
    ⟦ MZa ⟧ ρa ↘ za ->
    ⟦ MZb ⟧ ρb ↘ zb ->
    Dom za ≈ zb ∈ Rel zeroᵈ zeroᵈ ->
    (forall w z r r',
        Dom w ≈ z ∈ per_nat ->
        Dom r ≈ r' ∈ Rel w z ->
        exists s s',
          ⟦ MSa ⟧ ρa ↦ w ↦ r ↘ s /\ ⟦ MSb ⟧ ρb ↦ z ↦ r' ↘ s' /\
            Dom s ≈ s' ∈ Rel succᵈ w succᵈ z) ->
    Dom m ≈ m' ∈ per_bot ->
    Dom recᵈ m under ρa return Aa | zero -> za | succ -> MSa end
         ≈ recᵈ m' under ρb return Ab | zero -> zb | succ -> MSb end ∈ per_bot.
Proof.
  intros * Hmot Hza Hzb Hz Hsucc Hm s.
  assert (Hvar : Dom ⇑! ℕᵈ s ≈ ⇑! ℕᵈ s ∈ per_nat) by mauto.
  assert (Hzz : Dom zeroᵈ ≈ zeroᵈ ∈ per_nat) by econstructor.
  destruct (Hmot _ _ Hvar) as [b [b' [Hb [Hb' Hbb']]]].
  destruct (Hmot _ _ Hzz) as [bz [bz' [Hbz [Hbz' Hbzz']]]].
  destruct (Hmot _ _ (per_nat_succ Hvar)) as [bs [bs' [Hbs [Hbs' Hbss']]]].
  destruct (Hsucc _ _ _ _ Hvar (var_per_elem (S s) Hbb'))
    as [ms [ms' [Hms [Hms' Hmss']]]].
  (** The four common readbacks, one per premise of [read_ne_natrec]. *)
  destruct (per_univ_then_per_top_typ Hbb' (S s)) as [B' [HB'l HB'r]].
  destruct (per_elem_then_per_top Hbzz' Hz s) as [MZ' [HMZ'l HMZ'r]].
  destruct (per_elem_then_per_top Hbss' Hmss' (S (S s))) as [MS' [HMS'l HMS'r]].
  destruct (Hm s) as [M [HMl HMr]].
  eexists; split; econstructor; eassumption.
Qed.

Lemma per_nat_natrec : forall {i : nat} {Aa Ab MZa MZb MSa MSb ρa ρb za zb}
                              {Rel : domain -> domain -> relation domain},
    (forall w z,
        Dom w ≈ z ∈ per_nat ->
        exists a a',
          ⟦ Aa ⟧ ρa ↦ w ↘ a /\ ⟦ Ab ⟧ ρb ↦ z ↘ a' /\
            DF a ≈ a' ∈ per_univ_elem i ↘ (Rel w z)) ->
    ⟦ MZa ⟧ ρa ↘ za ->
    ⟦ MZb ⟧ ρb ↘ zb ->
    Dom za ≈ zb ∈ Rel zeroᵈ zeroᵈ ->
    (forall w z r r',
        Dom w ≈ z ∈ per_nat ->
        Dom r ≈ r' ∈ Rel w z ->
        exists s s',
          ⟦ MSa ⟧ ρa ↦ w ↦ r ↘ s /\ ⟦ MSb ⟧ ρb ↦ z ↦ r' ↘ s' /\
            Dom s ≈ s' ∈ Rel succᵈ w succᵈ z) ->
    forall m m',
      Dom m ≈ m' ∈ per_nat ->
      exists r r',
        ⟦rec m return Aa | zero -> MZa | succ -> MSa end ⟧ ρa ↘ r /\
          ⟦rec m' return Ab | zero -> MZb | succ -> MSb end ⟧ ρb ↘ r' /\
          Dom r ≈ r' ∈ Rel m m'.
Proof.
  intros * Hmot Hza Hzb Hz Hsucc * Hmm'.
  induction Hmm' as [| w z Hwz IH | m n a b Hbot].
  - exists za, zb.
    split; [ apply eval_natrec_zero; eassumption |].
    split; [ apply eval_natrec_zero; eassumption | eassumption ].
  - destruct IH as [r [r' [Hr [Hr' Hrr']]]].
    destruct (Hsucc _ _ _ _ Hwz Hrr') as [t [t' [Ht [Ht' Htt']]]].
    exists t, t'.
    split; [ eapply eval_natrec_succ; eassumption |].
    split; [ eapply eval_natrec_succ; eassumption | eassumption ].
  - assert (Hne : Dom ⇑ a m ≈ ⇑ b n ∈ per_nat) by (econstructor; eassumption).
    destruct (Hmot _ _ Hne) as [c [c' [Hc [Hc' Hcc']]]].
    do 2 eexists.
    split; [ eapply eval_natrec_neut; eassumption |].
    split; [ eapply eval_natrec_neut; eassumption |].
    eapply per_bot_then_per_elem; [ exact Hcc' |].
    eapply per_bot_natrec; eassumption.
Qed.

(** ** [zero] and [succ]

    Both rules are one-line four-value patterns.  [zero[σ]] is [zero] and
    [(succ M)[σ]] is [succ (M[σ])], so the two commutation links add nothing to the
    links they are built from. *)
Lemma rel_exp_zero : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ zero ≈ zero : ℕ.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_nat.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  econstructor; try apply eval_exp_zero.
  apply rel_chain_4; econstructor.
Qed.

Corollary valid_exp_zero : forall {Γ},
    ⊨ Γ ->
    Γ ⊨ zero : ℕ.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_zero; eassumption.
Qed.

Hint Resolve valid_exp_zero : mctt.

Lemma rel_exp_succ_cong : forall {Γ M M'},
    Γ ⊨ M ≈ M' : ℕ ->
    Γ ⊨ succ M ≈ succ M' : ℕ.
Proof.
  intros * HM.
  pose proof (rel_exp_of_nat_inversion HM) as [env_relΓ [HΓ HMgen]].
  eexists_rel_exp_of_nat.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hchain].
  apply (mk_rel_exp succᵈ m1 succᵈ m2 succᵈ m3 succᵈ m4);
    try (apply eval_exp_succ; eassumption).
  apply rel_chain_4; apply per_nat_succ; pairwise.
Qed.

Hint Resolve rel_exp_succ_cong : mctt.

(** ** The Successor Branch's Substitution

    The successor branch has type [A[Wk ⨟ Wk ,, succ #1]], the motive at the
    successor of the number, in [Γ ▹ ℕ ▹ A] where [#1] is that number.  Validating
    the substitution needs [#1 : ℕ] there, but not via [valid_exp_var], whose
    premise [⊨ Γ ▹ ℕ ▹ A] is stronger than the context PER available inside the
    eliminator's rules. *)
Lemma rel_exp_var1_nat : forall {Γ A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ ℕ ▹ A ⊨ #1 ≈ #1 : ℕ.
Proof.
  intros * HΓ HA.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  eexists_rel_exp_of_nat.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσj HΓ' HΓNA _ _ _ _ Hρ Hev Hev') as [Htail _].
  apply per_env_extend_nat_elim in Htail as [_ Hhead].
  (** [#1[σ]] is [σ 1] and [(ρσ ↯) 0] is [ρσ 1], so both commutation links
    relate a value to itself and the pattern collapses onto its middle. *)
  apply (mk_rel_exp (ρσ 1) (ρσ 1) (ρ'σ' 1) (ρ'σ' 1));
    try apply eval_exp_var; try (apply eval_sub_var; eassumption).
  apply rel_chain_4_of_2; first [ solve_chain_PER | eassumption ].
Qed.

(** The same one context shorter, which is the scrutinee of the generic
    recursor.  [#0[σ]] is [σ 0] and [ρσ 0] is the head of [ρσ], so again the
    pattern collapses onto its middle. *)
Lemma rel_exp_var0_nat : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ #0 ≈ #0 : ℕ.
Proof.
  intros * HΓ.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  eexists_rel_exp_of_nat.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσj HΓ' HΓN _ _ _ _ Hρ Hev Hev') as Hpair.
  apply per_env_extend_nat_elim in Hpair as [_ Hhead].
  apply (mk_rel_exp (ρσ 0) (ρσ 0) (ρ'σ' 0) (ρ'σ' 0));
    try apply eval_exp_var; try (apply eval_sub_var; eassumption).
  apply rel_chain_4_of_2; first [ solve_chain_PER | eassumption ].
Qed.

Lemma rel_sub_nat_step : forall {Γ A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ ℕ ▹ A ⊨s Wk ⨟ Wk,,succ #1 : Γ ▹ ℕ.
Proof.
  intros * HΓ HA.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_intro HΓNA HΓN (rel_wk_shift HΓN HΓNA)))
    as HWk.
  eapply rel_sub_under_ctx_extend;
    [ eapply rel_sub_under_ctx_shift; exact HWk
    | eapply (@rel_exp_of_typ_nat _ _ 0); exact HΓ
    | apply rel_exp_succ_cong; eapply rel_exp_var1_nat; eassumption ].
Qed.

(** ** The Motive at an Arbitrary Argument Pair

    The first obligation of [per_nat_natrec], for all three links, in one family of
    element PERs, the head PER of the motive at the environments the goal names:
<<
Rel w z := per_head A A (⟦σ⟧ρ ↦ w) (⟦σ'⟧ρ' ↦ z)
>>
    It must be one family because a recursion cannot mix relations, while the
    three links compare the motive at three different pairs of expressions and
    environments ([A[q σ]] at [ρ] against [A] at [⟦σ⟧ρ], and so on).

    The proof is one anchor and one chain.  The anchor is the motive's relatedness
    link at [(w, z)], read as a [per_univ_elem] at [Rel w z] by
    [per_univ_elem_at_head].  The chain collects every value the three obligations
    mention together with the anchor's two, so refining it along the anchor
    ([per_univ_chain_at_in]) puts them all in [Rel w z].  Four instantiations of
    [rel_exp_of_typ_under_ctx_q] produce its links: the motive at [(w, z)] both
    reflexively and as [A ≈ A'], and reflexively at [(w, w)] and [(z, z)], which
    bridge the two argument values. *)
Lemma rel_typ_of_nat_motive : forall {Γ A A'} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A' : Typeω@i ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        forall w z,
          Dom w ≈ z ∈ per_nat ->
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
  pose proof (@rel_exp_of_typ_nat _ _ 0 _ HΓ) as Hnat.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  (** The three argument pairs the four instantiations run at.  [ℕ[σ]] is [ℕ],
    so the extended context PER is the unsubstituted one, with introduction rule
    [per_env_extend_nat_intro]. *)
  assert (Hρρ : Dom ρ ≈ ρ ∈ env_rel') by (transitivity ρ'; [| symmetry]; exact Hρ).
  assert (Hww : Dom w ≈ w ∈ per_nat) by (transitivity z; [| symmetry]; exact Hwz).
  assert (Hzz : Dom z ≈ z ∈ per_nat) by (transitivity w; [symmetry |]; exact Hwz).
  pose proof (per_env_extend_nat_intro Hρ Hwz) as Hp_wz.
  pose proof (per_env_extend_nat_intro Hρ Hww) as Hp_ww.
  pose proof (per_env_extend_nat_intro Hρ Hzz) as Hp_zz.
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj Hnat HAl _ _ _ _ _ _ Hp_wz Hev Hev')
    as [[b1 [c1 [Hb1 [Hc1 Hbc1]]]] [[a1 [g1 [Ha1 [Hg1 Hag1]]]] _]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj Hnat HAl _ _ _ _ _ _ Hp_zz Hev Hev')
    as [_ [[c2 [g2 [Hc2 [Hg2 Hcg2]]]] _]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj Hnat HA _ _ _ _ _ _ Hp_wz Hev Hev')
    as [_ [[a2 [d1 [Ha2 [Hd1 Had1]]]] [e1 [f1 [He1 [Hf1 Hef1]]]]]].
  destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj Hnat HA _ _ _ _ _ _ Hp_ww Hev Hev')
    as [_ [[a3 [e2 [Ha3 [He2 Hae2]]]] _]].
  (** The shared values are named explicitly, because the merge below depends on
    which of two names [functional_eval_rewrite_clear] keeps. *)
  assert (c2 = c1) as -> by (eapply functional_eval_exp; eassumption).
  assert (g2 = g1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (a3 = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (e2 = e1) as -> by (eapply functional_eval_exp; eassumption).
  (** [b1 — c1 — g1 — a1 — d1] and [a1 — e1 — f1], merged along [a1]: the seven
      values of the three obligations and the anchor, in one chain. *)
  assert (C1 : rel_chain (per_univ i) ([b1; c1; g1; a1; d1])).
  { apply rel_chain_cons; [ exact Hbc1 |].
    apply rel_chain_cons; [ exact Hcg2 |].
    apply rel_chain_cons; [ symmetry; exact Hag1 |].
    apply rel_chain_of_pair; exact Had1. }
  assert (C2 : rel_chain (per_univ i) ([a1; e1; f1]))
    by (apply rel_chain_cons; [ exact Hae2 | apply rel_chain_of_pair; exact Hef1 ]).
  assert (Cbig : rel_chain (per_univ i) ([b1; c1; g1; a1; d1; e1; f1]))
    by (merge_rel_chain C1 C2 a1).
  (** The anchor, and the whole chain refined along it. *)
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

(** ** The Type of the Successor Branch

    [MS] has type [A[Wk ⨟ Wk ,, succ #1]], so the values the successor obligation
    of [per_nat_natrec] produces are related in that type's head PER, while the
    obligation's goal is in the head PER of [A] at [succ] of the number.  These are
    the two ends of one instantiation of [A]'s judgment along
    [Wk ⨟ Wk ,, succ #1], and this lemma is that instantiation: its outer values
    are those of the premises, its inner values those of the goal, and
    [per_head_bridge] consumes its chain to move between them.

    The substitution's evaluation can be named exactly, as [ρ1 ↦ succ x1], because
    neither component hides a closure: the tail is a precomposition by a weakening,
    which computes ([eval_sub_shift_pre]), and the head is a variable under
    [succ]. *)
Lemma rel_typ_of_nat_step_gen : forall {Γ A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    forall ρ1 ρ2,
      Dom ρ1 ≈ ρ2 ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ) ->
      exists p1 p2 p3 p4,
        ⟦ A[Wk ⨟ Wk,,succ #1] ⟧ ρ1 ↘ p1 /\
        ⟦ A ⟧ (drop_env (drop_env ρ1)) ↦ succᵈ (drop_env ρ1 0) ↘ p2 /\
        ⟦ A ⟧ (drop_env (drop_env ρ2)) ↦ succᵈ (drop_env ρ2 0) ↘ p3 /\
        ⟦ A[Wk ⨟ Wk,,succ #1] ⟧ ρ2 ↘ p4 /\
        rel_chain (per_univ i) ([p1; p2; p3; p4]).
Proof.
  intros * HΓ HA * Hpair.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  pose proof (rel_sub_nat_step HΓ HA) as Hstep.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓN [HΓN2 HAgen]].
  handle_per_ctx_env_irrel.
  assert (Hτ : forall ρ, ⟦ Wk ⨟ Wk,,succ #1 ⟧s ρ
                              ↘ (drop_env (drop_env ρ)) ↦ succᵈ (drop_env ρ 0)).
  {
    intros ρ.
    apply eval_sub_intro; intros [| n]; simpl;
      [ eexists; split; [ reflexivity | apply eval_exp_succ; apply eval_exp_var_eq; reflexivity ]
      | reflexivity ].
  }
  destruct (HAgen _ _ HΓNA _ _ Hstep _ _ _ _ Hpair (Hτ _) (Hτ _))
    as [p1 p2 p3 p4 Hp1 Hp2 Hp3 Hp4 Hpchain].
  exists p1, p2, p3, p4.
  do 4 (split; [ eassumption |]).
  exact Hpchain.
Qed.

Corollary rel_typ_of_nat_step : forall {Γ A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    forall ρ1 ρ2 x1 x2 y1 y2,
      Dom ρ1 ↦ x1 ↦ y1 ≈ ρ2 ↦ x2 ↦ y2
           ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ) ->
      exists p1 p2 p3 p4,
        ⟦ A[Wk ⨟ Wk,,succ #1] ⟧ ρ1 ↦ x1 ↦ y1 ↘ p1 /\
        ⟦ A ⟧ ρ1 ↦ succᵈ x1 ↘ p2 /\
        ⟦ A ⟧ ρ2 ↦ succᵈ x2 ↘ p3 /\
        ⟦ A[Wk ⨟ Wk,,succ #1] ⟧ ρ2 ↦ x2 ↦ y2 ↘ p4 /\
        rel_chain (per_univ i) ([p1; p2; p3; p4]).
Proof.
  intros * HΓ HA *.
  exact (rel_typ_of_nat_step_gen HΓ HA (ρ1 ↦ x1 ↦ y1) (ρ2 ↦ x2 ↦ y2)).
Qed.

(** ** The Successor Branch at an Arbitrary Argument Pair

    The term counterpart of [rel_typ_of_nat_motive]: the successor premises of the
    three [per_nat_natrec] instantiations, in the one family [Rel] of the motive's
    head PERs, here at [(succ w, succ z)].

    Each needs two moves.  The values of [MS] are related in the head PER of its
    type [A[Wk ⨟ Wk ,, succ #1]] at the environments where they were read, while
    the goal asks for the head PER of [A] at [ρσ ↦ succ w] and [ρ'σ' ↦ succ z].  So
    each premise is moved along the environments ([per_head_of_typ_resp], through
    the chain below) and then along the substitution ([per_head_bridge], through
    [rel_typ_of_nat_step]); [Hmv] does this once for all six.

    The chain is over eight environments of [Γ ▹ ℕ ▹ A].  [rel_exp_under_ctx_q]
    reports its inner values at the environments [q σ] reaches, and in a doubly
    extended context those are two levels of [s ↦ w] away from the ones the goal
    names.  Every value the six premises mention is an extension of one of the four
    tails of [rel_sub_under_ctx_q] by one of the two heads [r], [r'], and the chain
    relates them all. *)
Lemma rel_exp_of_nat_step : forall {Γ A} {i : nat} {MS MS' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS' : A[Wk ⨟ Wk ,, succ #1] ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        forall w z r r',
          Dom w ≈ z ∈ per_nat ->
          Dom r ≈ r' ∈ per_head A A (ρσ ↦ w) (ρ'σ' ↦ z) ->
          (exists m m',
              ⟦ MS[q (q σ)] ⟧ ρ ↦ w ↦ r ↘ m /\ ⟦ MS ⟧ ρσ ↦ z ↦ r' ↘ m' /\
                Dom m ≈ m' ∈ per_head A A (ρσ ↦ succᵈ w) (ρ'σ' ↦ succᵈ z)) /\
          (exists m m',
              ⟦ MS ⟧ ρσ ↦ w ↦ r ↘ m /\ ⟦ MS' ⟧ ρ'σ' ↦ z ↦ r' ↘ m' /\
                Dom m ≈ m' ∈ per_head A A (ρσ ↦ succᵈ w) (ρ'σ' ↦ succᵈ z)) /\
          (exists m m',
              ⟦ MS' ⟧ ρ'σ' ↦ w ↦ r ↘ m /\ ⟦ MS'[q (q σ')] ⟧ ρ' ↦ z ↦ r' ↘ m' /\
                Dom m ≈ m' ∈ per_head A A (ρσ ↦ succᵈ w) (ρ'σ' ↦ succᵈ z)).
Proof.
  intros * HΓ HA HMS * HΓ' * Hσj Hρ Hev Hev' * Hwz Hrr'.
  pose proof (@rel_exp_of_typ_nat _ _ 0 _ HΓ) as Hnat.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_nat HΓ') as HΓ'N.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  pose proof (presup_rel_exp_under_ctx HMS) as [i0 HAτ].
  pose proof (rel_exp_of_typ_extend_simple HΓ Hnat HA) as HAsimple.
  (** [ℕ[σ]] is [ℕ], so the context [q σ] maps into is the unsubstituted
    [Γ' ▹ ℕ], but only up to the reduction of [exp_sub], which the applications
    below would have to see through. *)
  pose proof (rel_sub_under_ctx_q Hσj Hnat) as Hqσj.
  cbn [exp_sub] in Hqσj.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  pose proof (per_env_extend_nat_intro Hρ Hwz) as Hnp.
  (** The four tails, and the eight extensions of them [rel_sub_under_ctx_q]
      relates. *)
  destruct (rel_sub_under_ctx_q_at HΓ' HΓN Hσj Hnat _ _ _ _ _ _ Hnp Hev Hev')
    as [s [s' [Hq [Hq' Ch1]]]].
  (** The head PER the caller's pair [r ≈ r'] lives in, anchored so that it is a
      PER and the other three orderings of the pair are available. *)
  assert (Pwz : Dom ρσ ↦ w ≈ ρ'σ' ↦ z ∈ per_env_extend ℕ ℕ env_relΓ)
    by (apply per_env_extend_nat_intro; eassumption).
  destruct (HAsimple _ _ Pwz) as [aw [gz [Haw [Hgz Hawgz]]]].
  pose proof (per_univ_elem_at_head Haw Hgz Hawgz) as HAnc.
  assert (Hrr : Dom r ≈ r ∈ per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))
    by (transitivity r'; [| symmetry]; exact Hrr').
  assert (Hr'r' : Dom r' ≈ r' ∈ per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))
    by (transitivity r; [symmetry |]; exact Hrr').
  assert (Hr'r : Dom r' ≈ r ∈ per_head A A (ρσ ↦ w) (ρ'σ' ↦ z))
    by (symmetry; exact Hrr').
  (** One link of the chain: a pair of tails from [Ch1] extended by a pair of
      heads read at the anchor's tails, which is [per_env_extend_move]. *)
  assert (Hlink : forall ρ1 ρ2 c c',
             rel_chain (per_env_extend ℕ ℕ env_relΓ)
               ([ρσ ↦ w; ρ'σ' ↦ z; ρ1; ρ2]) ->
             Dom c ≈ c' ∈ per_head A A (ρσ ↦ w) (ρ'σ' ↦ z) ->
             Dom ρ1 ↦ c ≈ ρ2 ↦ c'
                  ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (intros; eapply (per_env_extend_move HΓN HA); eassumption).
  assert (HE12 : Dom ρσ ↦ w ↦ r ≈ ρ'σ' ↦ z ↦ r'
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hrr' ]).
  assert (HE23 : Dom ρ'σ' ↦ z ↦ r' ≈ s ↦ w ↦ r
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hr'r ]).
  assert (HE34 : Dom s ↦ w ↦ r ≈ s' ↦ z ↦ r'
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hrr' ]).
  assert (HE45 : Dom s' ↦ z ↦ r' ≈ s ↦ w ↦ r'
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hr'r' ]).
  assert (HE56 : Dom s ↦ w ↦ r' ≈ ρσ ↦ z ↦ r'
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hr'r' ]).
  assert (HE67 : Dom ρσ ↦ z ↦ r' ≈ ρ'σ' ↦ w ↦ r
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hr'r ]).
  assert (HE78 : Dom ρ'σ' ↦ w ↦ r ≈ s' ↦ z ↦ r
                      ∈ per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
    by (apply Hlink; [ apply rel_chain_4; pairwise | exact Hrr ]).
  assert (ChE : rel_chain (per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
                  ([ρσ ↦ w ↦ r; ρ'σ' ↦ z ↦ r'; s ↦ w ↦ r;
                   s' ↦ z ↦ r'; s ↦ w ↦ r'; ρσ ↦ z ↦ r';
                   ρ'σ' ↦ w ↦ r; s' ↦ z ↦ r])).
  { apply rel_chain_cons; [ exact HE12 |].
    apply rel_chain_cons; [ exact HE23 |].
    apply rel_chain_cons; [ exact HE34 |].
    apply rel_chain_cons; [ exact HE45 |].
    apply rel_chain_cons; [ exact HE56 |].
    apply rel_chain_cons; [ exact HE67 |].
    apply rel_chain_of_pair; exact HE78. }
  (** The instantiation of the motive along the successor branch's substitution,
      whose chain is what carries a value of [MS] from its own type's head PER to
      the motive's at [succ]. *)
  destruct (rel_typ_of_nat_step HΓ HA _ _ _ _ _ _ HE12)
    as [p1 [p2 [p3 [p4 [Hp1 [Hp2 [Hp3 [Hp4 Hpchain]]]]]]]].
  functionalize_per_univ_chain Hpchain RT.
  (** The goal's own PER, anchored: this is what makes it a PER, hence what lets
      the two halves of each of the outer links be composed. *)
  pose proof (per_univ_elem_at_head Hp2 Hp3 ltac:(pairwise_univ)) as HAncT.
  assert (Hmv : forall ρ1 ρ2 m m',
             rel_chain (per_env_extend A A (per_env_extend ℕ ℕ env_relΓ))
               ([ρ1; ρ2; ρσ ↦ w ↦ r; ρ'σ' ↦ z ↦ r']) ->
             Dom m ≈ m' ∈ per_head A[Wk ⨟ Wk,,succ #1]
                                      A[Wk ⨟ Wk,,succ #1] ρ1 ρ2 ->
             Dom m ≈ m' ∈ per_head A A (ρσ ↦ succᵈ w) (ρ'σ' ↦ succᵈ z)).
  { intros ρ1 ρ2 m m' Hch Hm.
    assert (HmT : Dom m ≈ m' ∈ per_head A[Wk ⨟ Wk,,succ #1]
                                           A[Wk ⨟ Wk,,succ #1]
                                           (ρσ ↦ w ↦ r) (ρ'σ' ↦ z ↦ r'))
      by (apply (per_head_of_typ_resp HΓNA HAτ _ _ _ _ Hch); exact Hm).
    eapply per_head_bridge;
      [ exact HmT | exact Hp1 | exact Hp4 | pairwise | exact Hp2 | exact Hp3 | pairwise_univ ]. }
  (** The two substituted values, from the judgment along [q (q σ)].  Only the
    outer value of each outer obligation is used: the inner ones are read at
    [s ↦ w] and [s' ↦ z], which the chain relates to the goal's environments but
    does not equal. *)
  destruct (rel_typ_of_nat_motive HΓ HA _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev' _ _ Hwz)
    as [[b1 [c1 [Hb1 [Hc1 Hbc1]]]] _].
  pose proof (per_env_extend_sub_intro HΓ'N Hqσj HA _ _ _ _ _ _ _ _ Hnp Hb1 Hbc1 Hrr')
    as Hpair2.
  destruct (rel_exp_under_ctx_q HΓ'N Hqσj HA HMS _ _ _ _ _ _ Hpair2 Hq Hq')
    as [[m1 [m2 [Hm1 [Hm2 Hm12]]]] [_ [m3 [m4 [Hm3 [Hm4 Hm34]]]]]].
  (** The three unsubstituted instances, at the three pairs of environments the
      goal's links name. *)
  destruct (rel_exp_under_ctx_extend_simple HΓN HA (rel_exp_under_ctx_refl_left HMS) _ _ HE56)
    as [t1 [t2 [Ht1 [Ht2 Ht12]]]].
  destruct (rel_exp_under_ctx_extend_simple HΓN HA HMS _ _ HE12)
    as [u1 [u2 [Hu1 [Hu2 Hu12]]]].
  destruct (rel_exp_under_ctx_extend_simple HΓN HA (rel_exp_under_ctx_refl_right HMS) _ _ HE78)
    as [v1 [v2 [Hv1 [Hv2 Hv12]]]].
  assert (t1 = m2) as -> by (eapply functional_eval_exp; eassumption).
  assert (v2 = m3) as -> by (eapply functional_eval_exp; eassumption).
  repeat split.
  - exists m1, t2.
    do 2 (split; [ eassumption |]).
    transitivity m2.
    + apply (Hmv (s ↦ w ↦ r) (s' ↦ z ↦ r')); [ solve_rel_chain | exact Hm12 ].
    + apply (Hmv (s ↦ w ↦ r') (ρσ ↦ z ↦ r')); [ solve_rel_chain | exact Ht12 ].
  - exists u1, u2.
    do 2 (split; [ eassumption |]).
    apply (Hmv (ρσ ↦ w ↦ r) (ρ'σ' ↦ z ↦ r')); [ solve_rel_chain | exact Hu12 ].
  - exists v1, m4.
    do 2 (split; [ eassumption |]).
    transitivity m3.
    + apply (Hmv (ρ'σ' ↦ w ↦ r) (s' ↦ z ↦ r)); [ solve_rel_chain | exact Hv12 ].
    + apply (Hmv (s ↦ w ↦ r) (s' ↦ z ↦ r')); [ solve_rel_chain | exact Hm34 ].
Qed.

(** ** The Diagonal, for the Gluing Model

    The gluing model needs [per_bot_natrec] at one environment and no
    substitution, with the zero branch's value coming from a gluing predicate
    rather than a semantic judgment.  Instantiating the two obligations above at
    [Id], where [⟦Id⟧s ρ] is [ρ], gives exactly the two it asks for as their middle
    components. *)
Lemma per_bot_natrec_diag : forall {Γ A} {i : nat} {MZ MS env_relΓ ρ mz m},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS : A[Wk ⨟ Wk ,, succ #1] ->
    Dom ρ ≈ ρ ∈ env_relΓ ->
    ⟦ MZ ⟧ ρ ↘ mz ->
    Dom mz ≈ mz ∈ per_head A A (ρ ↦ zeroᵈ) (ρ ↦ zeroᵈ) ->
    Dom m ≈ m ∈ per_bot ->
    Dom recᵈ m under ρ return A | zero -> mz | succ -> MS end
         ≈ recᵈ m under ρ return A | zero -> mz | succ -> MS end ∈ per_bot.
Proof.
  intros * HΓ HA HMS Hρ Hmz Hz Hm.
  pose proof (rel_sub_id (ex_intro _ _ HΓ)) as Hid.
  pose proof (rel_typ_of_nat_motive HΓ HA _ _ HΓ _ _ _ _ _ _ Hid Hρ
                (eval_sub_id ρ) (eval_sub_id ρ)) as Hmot.
  pose proof (rel_exp_of_nat_step HΓ HA HMS _ _ HΓ _ _ _ _ _ _ Hid Hρ
                (eval_sub_id ρ) (eval_sub_id ρ)) as Hstep.
  eapply (per_bot_natrec (Rel := fun x y => per_head A A (ρ ↦ x) (ρ ↦ y)));
    [ intros w z Hwz; exact (proj1 (proj2 (Hmot w z Hwz)))
    | exact Hmz | exact Hmz | exact Hz
    | intros w z r r' Hwz Hr; exact (proj1 (proj2 (Hstep w z r r' Hwz Hr)))
    | exact Hm ].
Qed.

(** ** The Eliminator's Congruence Rule

    Three instantiations of [per_nat_natrec], at the three links of the number's
    chain, in one family of element PERs: the head PER of the motive at the
    arguments the type names, which [rel_typ_of_instance] reports.  For each, the
    motive obligation is one of the three [rel_typ_of_nat_motive] produces, the
    successor obligation one of the three [rel_exp_of_nat_step] produces, and the
    zero obligation one link of [MZ]'s chain, whose element PER is identified with
    the family at [(zero, zero)] by reading the type [A[Id ,, zero]] through
    [rel_typ_of_instance] a second time.

    Each link then lands in the family at its own argument pair, and
    [per_head_of_args] moves it to the pair the type names, as in
    [rel_exp_app_cong]. *)
Lemma rel_exp_natrec_cong : forall {Γ A A'} {i : nat} {MZ MZ' MS MS' M M'},
    Γ ▹ ℕ ⊨ A ≈ A' : Typeω@i ->
    Γ ⊨ MZ ≈ MZ' : A[Id ,, zero] ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS' : A[Wk ⨟ Wk ,, succ #1] ->
    Γ ⊨ M ≈ M' : ℕ ->
    Γ ⊨ rec M return A | zero -> MZ | succ -> MS end
         ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id ,, M].
Proof.
  intros * HA HMZ HMS HM.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_of_nat_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (@rel_exp_of_typ_nat _ _ i _ HΓ) as Hnat.
  destruct HMZ as [? [? [k HMZgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** *** The Type

    [A[Id ,, M]] is an instance of the motive, so the type, the number's four
    values, and the motive at an arbitrary related pair (needed by the moves below)
    all come from [rel_typ_of_instance]. *)
  destruct (rel_typ_of_instance Hnat HAl HMl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  (** The domain is [ℕ], so its values live in [per_nat], from which the
    recursor's argument pairs are drawn and at which every obligation below is
    stated. *)
  assert (a2 = ℕᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha2 | apply eval_exp_nat ]).
  assert (a3 = ℕᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha3 | apply eval_exp_nat ]).
  assert (HRN : RN <~> per_nat)
    by (eapply per_univ_elem_right_irrel; [ exact Hmid | apply (per_univ_elem_nat 0) ]).
  rewrite HRN in Hpchain.
  assert (Hcodn : forall w z,
             Dom w ≈ z ∈ per_nat ->
             exists b b',
               ⟦ A ⟧ ρσ ↦ w ↘ b /\ ⟦ A ⟧ ρ'σ' ↦ z ↘ b' /\
                 Dom b ≈ b' ∈ per_univ i)
    by (intros w z Hwz; apply (Hcod w z); rewrite HRN; exact Hwz).
  pose proof Htyp as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htchain].
  assert (HAncT : DF t2 ≈ t3 ∈ per_univ_elem i
                       ↘ (per_head A A (ρσ ↦ p2) (ρ'σ' ↦ p3))) by pairwise.
  exists (per_head A A (ρσ ↦ p2) (ρ'σ' ↦ p3)).
  split; [ exact Htyp |].
  (** *** The Number

    Its other judgment, [M ≈ M'], whose two outer values are the type's first two.
    The two chains merge, and the six values of the merge are all the argument
    pairs the three instantiations run at. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Hp1m1 : p1 = m1) by (eapply functional_eval_exp; [ exact Hp1 | exact Hm1 ]).
  assert (Hp2m2 : p2 = m2) by (eapply functional_eval_exp; [ exact Hp2 | exact Hm2 ]).
  subst p1 p2.
  assert (Hall : rel_chain per_nat ([m1; m2; m3; m4; p3; p4]))
    by (merge_rel_chain Hmchain Hpchain m1).
  assert (Hm12 : Dom m1 ≈ m2 ∈ per_nat) by pairwise.
  assert (Hm23 : Dom m2 ≈ m3 ∈ per_nat) by pairwise.
  assert (Hm34 : Dom m3 ≈ m4 ∈ per_nat) by pairwise.
  assert (Hm2p3 : Dom m2 ≈ p3 ∈ per_nat) by pairwise.
  assert (Hm22 : Dom m2 ≈ m2 ∈ per_nat) by pairwise.
  assert (Hm24 : Dom m2 ≈ m4 ∈ per_nat) by pairwise.
  (** *** The Zero Branch

    Its type is the motive at [zero], so reading that type through
    [rel_typ_of_instance] again identifies the element PER of [MZ]'s judgment with
    the family at [(zero, zero)]; the two agree on the type's inner values, which is
    all irrelevance needs. *)
  destruct (rel_typ_of_instance Hnat HAl (rel_exp_zero HΓ) _ _ HΓ' _ _ _ _ _ _
              Hσj Hρ Hev Hev')
    as [lz [RNz [b1 [b2 [b3 [b4 [q1 [q2 [q3 [q4 [Hb1 [Hb2 [Hb3 [Hb4 [Houterz
       [Hmidz [Hq1 [Hq2 [Hq3 [Hq4 [Hqchain [Hcodz Htypz]]]]]]]]]]]]]]]]]]]]]].
  assert (q2 = zeroᵈ) as ->
    by (eapply functional_eval_exp; [ exact Hq2 | apply eval_exp_zero ]).
  assert (q3 = zeroᵈ) as ->
    by (eapply functional_eval_exp; [ exact Hq3 | apply eval_exp_zero ]).
  destruct Htypz as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hwchain].
  assert (HAncZ : DF w2 ≈ w3 ∈ per_univ_elem i
                       ↘ (per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ)))
    by pairwise.
  destruct (HMZgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RMZ [HMZtyp HMZexp]].
  destruct HMZtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMZexp as [z1 z2 z3 z4 Hz1 Hz2 Hz3 Hz4 Hzchain].
  assert (c2 = w2) as -> by (eapply functional_eval_exp; [ exact Hc2 | exact Hw2 ]).
  assert (c3 = w3) as -> by (eapply functional_eval_exp; [ exact Hc3 | exact Hw3 ]).
  retype_rel_chain Hcchain HAncZ Hzchain.
  assert (Hz12 : Dom z1 ≈ z2 ∈ per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ))
    by pairwise.
  assert (Hz23 : Dom z2 ≈ z3 ∈ per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ))
    by pairwise.
  assert (Hz34 : Dom z3 ≈ z4 ∈ per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ))
    by pairwise.
  (** *** The Three Recursions

    The motive and the successor branch at an arbitrary argument pair, both already
    in the one family.  The family is given explicitly, since [per_nat_natrec]
    cannot infer a relation under two binders from an obligation. *)
  pose proof (rel_typ_of_nat_motive HΓ HA _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as Hmotgen.
  pose proof (rel_exp_of_nat_step HΓ HAl HMS _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as Hstepgen.
  destruct (per_nat_natrec
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj1 (Hmotgen w z H)) Hz1 Hz2 Hz12
              (fun w z r r' Hwz Hr => proj1 (Hstepgen w z r r' Hwz Hr))
              _ _ Hm12)
    as [r1 [r2 [Hr1 [Hr2 Hr12]]]].
  destruct (per_nat_natrec
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj1 (proj2 (Hmotgen w z H))) Hz2 Hz3 Hz23
              (fun w z r r' Hwz Hr => proj1 (proj2 (Hstepgen w z r r' Hwz Hr)))
              _ _ Hm23)
    as [s1 [s2 [Hs1 [Hs2 Hs23]]]].
  destruct (per_nat_natrec
              (Rel := fun x y => per_head A A (ρσ ↦ x) (ρ'σ' ↦ y))
              (fun w z H => proj2 (proj2 (Hmotgen w z H))) Hz3 Hz4 Hz34
              (fun w z r r' Hwz Hr => proj2 (proj2 (Hstepgen w z r r' Hwz Hr)))
              _ _ Hm34)
    as [u1 [u2 [Hu1 [Hu2 Hu34]]]].
  (** The middle value of each link is the first of the next, so the three are one
      chain — once each is moved to the argument pair the type names. *)
  assert (Hs1e : s1 = r2) by (eapply functional_eval_natrec; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_natrec; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  apply (mk_rel_exp r1 r2 s2 u2);
    [ simplify_subs; eapply eval_exp_natrec; [ exact Hm1 | exact Hr1 ]
    | eapply eval_exp_natrec; [ exact Hm2 | exact Hr2 ]
    | eapply eval_exp_natrec; [ exact Hm3 | exact Hs2 ]
    | simplify_subs; eapply eval_exp_natrec; [ exact Hm4 | exact Hu2 ]
    |].
  apply rel_chain_4;
    [ apply (per_head_of_args Hcodn m1 m2 m2 p3 Hm12 Hm2p3 Hm22); exact Hr12
    | apply (per_head_of_args Hcodn m2 m3 m2 p3 Hm23 Hm2p3 Hm23); exact Hs23
    | apply (per_head_of_args Hcodn m3 m4 m2 p3 Hm34 Hm2p3 Hm24); exact Hu34 ].
Qed.

Hint Resolve rel_exp_natrec_cong : mctt.

(** ** [β] at [zero]

    The recursion at [zero] is the evaluation of the zero branch ([eval_natrec_zero]
    read right to left), so both sides of the rule have the same two inner values
    and [MZ]'s chain is the goal's.  What remains is to name the element PER fixed
    by the goal's type, the head PER of the motive at [(zero, zero)], and to
    identify it with the one from [MZ]'s judgment.  Reading [A[Id ,, zero]] through
    [rel_typ_of_instance] does both, as in the zero-branch step of
    [rel_exp_natrec_cong].

    The successor branch plays no part, so unlike the syntactic rule this one has no
    premise about it. *)
Lemma rel_exp_nat_beta_zero : forall {Γ A} {i : nat} {MZ MS},
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ⊨ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id ,, zero].
Proof.
  intros * HA HMZ.
  destruct HMZ as [env_relΓ [HΓ [k HMZgen]]].
  pose proof (@rel_exp_of_typ_nat _ _ i _ HΓ) as Hnat.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance Hnat HA (rel_exp_zero HΓ) _ _ HΓ' _ _ _ _ _ _
              Hσj Hρ Hev Hev')
    as [l [RN [b1 [b2 [b3 [b4 [q1 [q2 [q3 [q4 [Hb1 [Hb2 [Hb3 [Hb4 [Houter
       [Hmid [Hq1 [Hq2 [Hq3 [Hq4 [Hqchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  assert (q2 = zeroᵈ) as ->
    by (eapply functional_eval_exp; [ exact Hq2 | apply eval_exp_zero ]).
  assert (q3 = zeroᵈ) as ->
    by (eapply functional_eval_exp; [ exact Hq3 | apply eval_exp_zero ]).
  pose proof Htyp as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hwchain].
  assert (HAncZ : DF w2 ≈ w3 ∈ per_univ_elem i
                       ↘ (per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ)))
    by pairwise.
  exists (per_head A A (ρσ ↦ zeroᵈ) (ρ'σ' ↦ zeroᵈ)).
  split; [ exact Htyp |].
  destruct (HMZgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RMZ [HMZtyp HMZexp]].
  destruct HMZtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMZexp as [z1 z2 z3 z4 Hz1 Hz2 Hz3 Hz4 Hzchain].
  assert (c2 = w2) as -> by (eapply functional_eval_exp; [ exact Hc2 | exact Hw2 ]).
  assert (c3 = w3) as -> by (eapply functional_eval_exp; [ exact Hc3 | exact Hw3 ]).
  retype_rel_chain Hcchain HAncZ Hzchain.
  (** The left two values are the zero branch's, reached through the recursion;
      the right two are the zero branch's own. *)
  apply (mk_rel_exp z1 z2 z3 z4);
    [ simplify_subs; eapply eval_exp_natrec;
      [ apply eval_exp_zero | apply eval_natrec_zero; exact Hz1 ]
    | eapply eval_exp_natrec;
      [ apply eval_exp_zero | apply eval_natrec_zero; exact Hz2 ]
    | exact Hz3
    | exact Hz4
    | exact Hzchain ].
Qed.

Hint Resolve rel_exp_nat_beta_zero : mctt.

(** ** The Generic Recursor

    The eliminator of [exp_sub_natrec_generic], validated semantically.  The [ℕ]-β
    rule for [succ] mentions the recursive call [E] inside the substitution
    [Id ,, M ,, E], and a substitution extension can only be validated by
    [rel_sub_under_ctx_extend_sub_double], whose last premise is a term of the
    context being extended.  [E] is a term of [Γ], but a term of [Γ ▹ ℕ] is
    needed.  The generic form (scrutinee [#0], everything else weakened past that
    binder) is such a term, and [exp_sub_natrec_generic_self] turns it back into
    [E] under any extension whose head is [M].

    The proof is [rel_exp_natrec_cong] at the weakened premises, which
    [rel_exp_under_ctx_wk] provides; the two type rewrites are the syntactic lemmas
    saying weakening commutes with the two instantiated motives. *)
(** ** The Head Variable as a Term

    [B[wk_q ↑]ʷ[Id ,, #0]] is [B] up to the sort of the entry at index [0]:
    [Id ,, #0] substitutes the term [#0] where [Id] has the variable [0].  On a
    context whose head is a term the two denote the same, because the
    environment relation reads only the head's term value and the tail. *)

Definition sb_head_term (σ : sub) : sub := sb_extend (Wk ⨟ σ) (se_exp (sentry_exp (σ 0))).

Definition env_head_term (ρ : env) : env := de_term (ρ 0) :: ρ↯.

Lemma exp_sub_wk_q_var0 : forall B σ, B[wk_q ↑]ʷ[Id ,, #0][σ] = B[sb_head_term σ].
Proof.
  intros; rewrite exp_sub_sub, <- exp_sub_of_wk, exp_sub_sub.
  apply exp_sub_sb_eq; intros [| x]; reflexivity.
Qed.

Lemma exp_wk_q_var0 : forall B, B[wk_q ↑]ʷ[Id ,, #0] = B[sb_head_term Id].
Proof. intros; rewrite <- exp_sub_wk_q_var0, exp_sub_id; reflexivity. Qed.

Lemma sb_wk_head_term : forall σ φ, sb_eq (sb_wk (sb_head_term σ) φ) (sb_head_term (sb_wk σ φ)).
Proof.
  intros σ φ [| x]; cbn; [ rewrite sentry_exp_wk; reflexivity | reflexivity ].
Qed.

Lemma eval_sub_head_term : forall σ ρ ρσ,
    ⟦ σ ⟧s ρ ↘ ρσ -> ⟦ sb_head_term σ ⟧s ρ ↘ env_head_term ρσ.
Proof.
  intros * H [| x]; [| exact (H (S x)) ].
  exists (ρσ 0); split; [ reflexivity | apply (eval_sub_var σ ρ ρσ 0 H) ].
Qed.

(** An environment relation of a context with a term at its head reads only the
    head's value and the tail. *)
Lemma per_ctx_env_head_term : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' <-> R (env_head_term ρ) (env_head_term ρ').
Proof.
  intros * H; inversion H; subst.
  intros ρ ρ'; apply_relation_equivalence; reflexivity.
Qed.

Lemma per_ctx_env_head_term_l : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> R (env_head_term ρ) ρ'.
Proof.
  intros * H ρ ρ' Hρ; apply (per_ctx_env_head_term H); exact (proj1 (per_ctx_env_head_term H ρ ρ') Hρ).
Qed.

Lemma per_ctx_env_head_term_r : forall {Γ A Γ' A' R},
    EF Γ ▹ A ≈ Γ' ▹ A' ∈ per_ctx_env ↘ R ->
    forall ρ ρ', R ρ ρ' -> R ρ (env_head_term ρ').
Proof.
  intros * H ρ ρ' Hρ; apply (per_ctx_env_head_term H); exact (proj1 (per_ctx_env_head_term H ρ ρ') Hρ).
Qed.

Lemma rel_chain_head_term4 : forall {Γ A R a b c d},
    EF Γ ▹ A ≈ Γ ▹ A ∈ per_ctx_env ↘ R ->
    rel_chain R ([a; b; c; d]) ->
    rel_chain R ([env_head_term a; env_head_term b; c; d]).
Proof.
  intros * HΓ (Hab & Hbc & Hcd).
  repeat split; [ | | exact Hcd ].
  - apply (per_ctx_env_head_term_l HΓ), (per_ctx_env_head_term_r HΓ), Hab.
  - apply (per_ctx_env_head_term_l HΓ), Hbc.
Qed.

Lemma rel_sub_under_ctx_head_term : forall {Γ' Γ A σ σ'},
    Γ' ⊨s σ ≈ σ' : Γ ▹ A ->
    Γ' ⊨s sb_head_term σ ≈ σ' : Γ ▹ A.
Proof.
  intros * [env_rel [HΓ' [env_relo [HΓA Hσ]]]].
  exists env_rel, HΓ', env_relo, HΓA.
  intros Γ'' env_rel' HΓ'' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [a b c d Ha Hb Hc Hd Hchain].
  apply (mk_rel_sub (env_head_term a) (env_head_term b) c d);
    [ rewrite sb_wk_head_term; apply eval_sub_head_term; exact Ha
    | apply eval_sub_head_term; exact Hb | exact Hc | exact Hd |].
  exact (rel_chain_head_term4 HΓA Hchain).
Qed.

Lemma rel_exp_typ_var0 : forall {Γ A B} {i : nat},
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ▹ A ⊨ B[wk_q ↑]ʷ[Id ,, #0] ≈ B : Typeω@i.
Proof.
  intros * HB.
  pose proof (rel_exp_of_typ_inversion HB) as [env_rel [HΓA HBgen]].
  apply rel_exp_of_typ; exists env_rel, HΓA.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_head_term Hσ) _ _ _ _ Hρ
              (eval_sub_head_term _ _ _ Hev) Hev') as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hc].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_rel) by (eapply rel_sub_under_ctx_at'; eassumption).
  assert (Hρσ' : Dom ρσ ≈ ρσ ∈ env_rel) by solve_per.
  destruct (HBgen _ _ HΓA _ _ (rel_sub_under_ctx_head_term (rel_sub_id (ex_intro _ _ HΓA))) _ _ _ _ Hρσ'
              (eval_sub_head_term _ _ _ (eval_sub_id ρσ)) (eval_sub_id ρσ)) as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hd].
  apply (mk_rel_exp c1 d1 c3 c4);
    [ rewrite exp_sub_wk_q_var0; exact Hc1 | rewrite exp_wk_q_var0; exact Hd1 | exact Hc3 | exact Hc4 |].
  functional_eval_rewrite_clear.
  merge_rel_chain Hc Hd c2.
Qed.

Lemma rel_exp_natrec_generic : forall {Γ A} {i : nat} {MZ MS env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS : A[Wk ⨟ Wk ,, succ #1] ->
    Γ ▹ ℕ ⊨ rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end
            ≈ rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end : A.
Proof.
  intros * HΓ HA HMZ HMS.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (@rel_exp_of_typ_nat _ _ 0 _ HΓ) as Hnat0.
  pose proof (rel_wk_under_ctx_intro HΓN HΓ (rel_wk_shift HΓ HΓN)) as Hup.
  pose proof (rel_wk_under_ctx_q Hup Hnat0) as Hupq.
  pose proof (rel_wk_under_ctx_q Hupq HA) as Hupqq.
  pose proof (rel_exp_under_ctx_wk Hup HMZ) as HMZw.
  pose proof (rel_exp_under_ctx_wk Hupqq HMS) as HMSw.
  rewrite exp_wk_sub_extend in HMZw.
  rewrite exp_wk_sub_natrec in HMSw.
  (** The conclusion type is produced as [A[wk_q ↑]ʷ[Id ,, #0]] and then
    converted to [A] ([rel_exp_typ_var0]). *)
  assert (HEg : Γ ▹ ℕ ⊨ rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end
                        ≈ rec #0 return A[wk_q ↑]ʷ | zero -> MZ[↑]ʷ | succ -> MS[wk_q (wk_q ↑)]ʷ end
                        : A[wk_q ↑]ʷ[Id ,, #0])
    by (eapply rel_exp_natrec_cong;
        [ exact (rel_exp_under_ctx_wk Hupq HA) | exact HMZw | exact HMSw
        | apply (rel_exp_var0_nat HΓ) ]).
  eapply rel_exp_eq_subtyp; [ exact HEg | exact HA |].
  eapply subtyp_refl; exact (rel_exp_typ_var0 HA).
Qed.

(** ** [β] at [succ]

    Both sides run the successor branch, so the two inner values are shared and the
    work is in the outer ones.  The left side reaches [MS] through
    [eval_natrec_succ] under [σ]; the right side through the doubly extended
    substitution [σ ,, M[σ] ,, E[σ]].  Nothing computes
    [MS[Id ,, M ,, E][σ] = MS[σ ,, M[σ] ,, E[σ]]] semantically, since evaluated
    substitutions have no composition law (see the closing comment of
    [Core/Semantic/Evaluation/Definitions.v]).

    Instead, two more instances of [MS]'s judgment are used, each a four-value
    pattern:

    - chain A, at [Γ ⊨s Id ,, M ,, E], whose outer environments are [ρσ] and
      [ρ'σ'] and whose inner ones are the two the recursion produces.  Its fourth
      value is the goal's third.
    - chain B, at [Γ' ⊨s σ ,, M[σ] ,, E[σ]], whose outer environments are [ρ] and
      [ρ'].  Its fourth value is the goal's fourth, modulo
      [exp_sub_extend_sub2].

    Both come from [rel_sub_under_ctx_extend_sub_double] applied to the generic
    recursor, at [Id] and at [σ] respectively.  Their element PERs are identified
    with the goal's by irrelevance, because [exp_sub_natrec_step] makes the outer
    values of their types the same evaluations as the goal type's; this is the one
    use of that lemma at an arbitrary [σ] rather than at [Id].

    The three links of the goal are then:

    - [v1 ≈ v2], from the first obligation of [rel_exp_of_nat_step] at
      [(m1, m2, c1, c2)];
    - [v2 ≈ v3], by [pairwise] on chain A;
    - [v3 ≈ v4], by [pairwise] on chain A, the second step obligation at
      [(m1, m3, c1, c3)] read backwards, and [pairwise] on chain B.

    Each obligation lands in the motive's head PER at its own argument pair, and
    [per_head_of_args] moves it to the pair the goal type names. *)
Lemma rel_exp_nat_beta_succ : forall {Γ A} {i : nat} {MZ MS M},
    Γ ▹ ℕ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS : A[Wk ⨟ Wk ,, succ #1] ->
    Γ ⊨ M ≈ M : ℕ ->
    Γ ⊨ rec succ M return A | zero -> MZ | succ -> MS end
         ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end]
         : A[Id ,, succ M].
Proof.
  intros * HA HMZ HMS HM.
  pose proof (rel_exp_of_nat_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (@rel_exp_of_typ_nat _ _ i _ HΓ) as Hnat.
  pose proof (rel_exp_natrec_generic HΓ HA HMZ HMS) as HEg.
  pose proof (rel_exp_natrec_cong HA HMZ HMS HM) as HE.
  destruct HE as [envE [HΓE [k HEgen]]].
  pose proof HMS as [envS [HΓS [j HMSgen]]].
  clear HΓE HΓS.
  (** The inner substitution, [Id ,, M ,, E] out of [Γ] itself. *)
  pose proof (rel_sub_under_ctx_extend_sub_double (rel_sub_id (ex_intro _ _ HΓ)) HM HEg)
    as HsubI.
  rewrite exp_sub_natrec_generic_self in HsubI.
  do 2 rewrite exp_sub_id in HsubI.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** and the outer one, [σ ,, M[σ] ,, E[σ]] out of [Γ']. *)
  pose proof (rel_sub_under_ctx_extend_sub_double Hσj HM HEg) as HsubS.
  do 2 rewrite exp_sub_natrec_generic_self in HsubS.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** *** The Number *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (Hm12 : Dom m1 ≈ m2 ∈ per_nat) by pairwise.
  assert (Hm13 : Dom m1 ≈ m3 ∈ per_nat) by pairwise.
  assert (Hm22 : Dom m2 ≈ m2 ∈ per_nat) by pairwise.
  assert (Hm23 : Dom m2 ≈ m3 ∈ per_nat) by pairwise.
  (** *** The Type

      [A[Id ,, succ M]] is the motive at [(succ m2, succ m3)]. *)
  destruct (rel_typ_of_instance Hnat HA (rel_exp_succ_cong HM) _ _ HΓ' _ _ _ _ _ _
              Hσj Hρ Hev Hev')
    as [l [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  assert (a2 = ℕᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha2 | apply eval_exp_nat ]).
  assert (a3 = ℕᵈ) as ->
    by (eapply functional_eval_exp; [ exact Ha3 | apply eval_exp_nat ]).
  assert (HRN : RN <~> per_nat)
    by (eapply per_univ_elem_right_irrel; [ exact Hmid | apply (per_univ_elem_nat 0) ]).
  assert (Hcodn : forall w z,
             Dom w ≈ z ∈ per_nat ->
             exists b b',
               ⟦ A ⟧ ρσ ↦ w ↘ b /\ ⟦ A ⟧ ρ'σ' ↦ z ↘ b' /\
                 Dom b ≈ b' ∈ per_univ i)
    by (intros w z Hwz; apply (Hcod w z); rewrite HRN; exact Hwz).
  assert (p2 = succᵈ m2) as ->
    by (eapply functional_eval_exp; [ exact Hp2 | apply eval_exp_succ; exact Hm2 ]).
  assert (p3 = succᵈ m3) as ->
    by (eapply functional_eval_exp; [ exact Hp3 | apply eval_exp_succ; exact Hm3 ]).
  exists (per_head A A (ρσ ↦ succᵈ m2) (ρ'σ' ↦ succᵈ m3)).
  split; [ exact Htyp |].
  pose proof Htyp as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htchain].
  assert (HAncMid : DF t2 ≈ t3 ∈ per_univ_elem i
                         ↘ (per_head A A (ρσ ↦ succᵈ m2) (ρ'σ' ↦ succᵈ m3)))
    by pairwise.
  assert (HAncOut : DF t1 ≈ t4 ∈ per_univ_elem i
                         ↘ (per_head A A (ρσ ↦ succᵈ m2) (ρ'σ' ↦ succᵈ m3)))
    by pairwise.
  rewrite exp_sub_extend_sub in Ht1, Ht4.
  cbn [exp_sub] in Ht1, Ht4.
  (** *** The Recursive Call

      Its element PER is the motive's head PER at [(m2, m3)] — the pair its own
      type [A[Id ,, M]] names — which a second reading of that type identifies. *)
  destruct (rel_typ_of_instance Hnat HA HM _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [lM [RNM [d1 [d2 [d3 [d4 [q1 [q2 [q3 [q4 [Hd1 [Hd2 [Hd3 [Hd4 [HouterM
       [HmidM [Hq1 [Hq2 [Hq3 [Hq4 [HqchainM [HcodM HtypM]]]]]]]]]]]]]]]]]]]]]].
  assert (q2 = m2) as -> by (eapply functional_eval_exp; [ exact Hq2 | exact Hm2 ]).
  assert (q3 = m3) as -> by (eapply functional_eval_exp; [ exact Hq3 | exact Hm3 ]).
  pose proof HtypM as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hfchain].
  assert (HAncE : DF f2 ≈ f3 ∈ per_univ_elem i
                       ↘ (per_head A A (ρσ ↦ m2) (ρ'σ' ↦ m3))) by pairwise.
  destruct (HEgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RE [HEtyp HEexp]].
  destruct HEtyp as [e1 e2 e3 e4 He1 He2 He3 He4 Hechain].
  destruct HEexp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  assert (e2 = f2) as -> by (eapply functional_eval_exp; [ exact He2 | exact Hf2 ]).
  assert (e3 = f3) as -> by (eapply functional_eval_exp; [ exact He3 | exact Hf3 ]).
  retype_rel_chain Hechain HAncE Hcchain.
  (** The two recursions the left side runs inside its [eval_natrec_succ] are the
    ones [E] already evaluates.  Inverting [E]'s two evaluations avoids running
    [simplify_evals] on a context of eight evaluations at six environments. *)
  pose proof Hc1 as Hc1'.
  cbn [exp_sub] in Hc1'.
  destruct (eval_exp_natrec_inversion _ _ _ _ _ _ Hc1') as [n1 [Hn1 Hrec1]].
  assert (n1 = m1) as -> by (eapply functional_eval_exp; [ exact Hn1 | exact Hm1 ]).
  destruct (eval_exp_natrec_inversion _ _ _ _ _ _ Hc2) as [n2 [Hn2 Hrec2]].
  assert (n2 = m2) as -> by (eapply functional_eval_exp; [ exact Hn2 | exact Hm2 ]).
  (** *** The Successor Branch

    [E]'s chain lives at [(m2, m3)], while each obligation of the step runs at the
    argument pair it is about, so the relevant link is moved there first. *)
  pose proof (rel_exp_of_nat_step HΓ HA HMS _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as Hstepgen.
  assert (Hc12 : Dom c1 ≈ c2 ∈ per_head A A (ρσ ↦ m1) (ρ'σ' ↦ m2))
    by (apply (per_head_of_args Hcodn m2 m3 m1 m2 Hm23 Hm12 Hm13); pairwise).
  assert (Hc13 : Dom c1 ≈ c3 ∈ per_head A A (ρσ ↦ m1) (ρ'σ' ↦ m3))
    by (apply (per_head_of_args Hcodn m2 m3 m1 m3 Hm23 Hm13 Hm13); pairwise).
  destruct (proj1 (Hstepgen m1 m2 c1 c2 Hm12 Hc12)) as [b1 [b2 [Hb1 [Hb2 Hb12]]]].
  destruct (proj1 (proj2 (Hstepgen m1 m3 c1 c3 Hm13 Hc13)))
    as [g1 [g2 [Hg1 [Hg2 Hg12]]]].
  assert (H12 : Dom b1 ≈ b2
                     ∈ per_head A A (ρσ ↦ succᵈ m2) (ρ'σ' ↦ succᵈ m3))
    by (apply (per_head_of_args Hcodn succᵈ m1 succᵈ m2
                 succᵈ m2 succᵈ m3
                 (per_nat_succ Hm12) (per_nat_succ Hm23) (per_nat_succ Hm22));
        exact Hb12).
  assert (Hg : Dom g1 ≈ g2
                    ∈ per_head A A (ρσ ↦ succᵈ m2) (ρ'σ' ↦ succᵈ m3))
    by (apply (per_head_of_args Hcodn succᵈ m1 succᵈ m3
                 succᵈ m2 succᵈ m3
                 (per_nat_succ Hm13) (per_nat_succ Hm23) (per_nat_succ Hm23));
        exact Hg12).
  (** *** Chain A, at the inner substitution *)
  destruct (HMSgen _ _ HΓ _ _ HsubI _ _ _ _ Hρσ
              (eval_sub_extend _ _ _ _ _ (eval_sub_extend _ _ _ _ _ (eval_sub_id ρσ) Hm2) Hc2)
              (eval_sub_extend _ _ _ _ _ (eval_sub_extend _ _ _ _ _ (eval_sub_id ρ'σ') Hm3) Hc3))
    as [RA [HAtyp HAexp]].
  destruct HAtyp as [T1 T2 T3 T4 HT1 HT2 HT3 HT4 HTchain].
  destruct HAexp as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hxchain].
  rewrite exp_sub_natrec_step in HT1, HT4.
  assert (T1 = t2) as -> by (eapply functional_eval_exp; [ exact HT1 | exact Ht2 ]).
  assert (T4 = t3) as -> by (eapply functional_eval_exp; [ exact HT4 | exact Ht3 ]).
  retype_rel_chain HTchain HAncMid Hxchain.
  (** *** Chain B, at the outer substitution *)
  destruct (HMSgen _ _ HΓ' _ _ HsubS _ _ _ _ Hρ
              (eval_sub_extend _ _ _ _ _ (eval_sub_extend _ _ _ _ _ Hev Hm1) Hc1)
              (eval_sub_extend _ _ _ _ _ (eval_sub_extend _ _ _ _ _ Hev' Hm4) Hc4))
    as [RB [HBtyp HBexp]].
  destruct HBtyp as [U1 U2 U3 U4 HU1 HU2 HU3 HU4 HUchain].
  destruct HBexp as [z1 z2 z3 z4 Hz1 Hz2 Hz3 Hz4 Hzchain].
  rewrite exp_sub_natrec_step in HU1, HU4.
  assert (U1 = t1) as -> by (eapply functional_eval_exp; [ exact HU1 | exact Ht1 ]).
  assert (U4 = t4) as -> by (eapply functional_eval_exp; [ exact HU4 | exact Ht4 ]).
  retype_rel_chain HUchain HAncOut Hzchain.
  (** The two chains share their second values with the step's outputs. *)
  assert (x2 = b2) as -> by (eapply functional_eval_exp; [ exact Hx2 | exact Hb2 ]).
  assert (x3 = g2) as -> by (eapply functional_eval_exp; [ exact Hx3 | exact Hg2 ]).
  assert (z2 = g1) as -> by (eapply functional_eval_exp; [ exact Hz2 | exact Hg1 ]).
  apply (mk_rel_exp b1 b2 x4 z4);
    [ cbn [exp_sub]; eapply eval_exp_natrec;
      [ apply eval_exp_succ; exact Hm1
      | eapply eval_natrec_succ; [ exact Hrec1 | exact Hb1 ] ]
    | eapply eval_exp_natrec;
      [ apply eval_exp_succ; exact Hm2
      | eapply eval_natrec_succ; [ exact Hrec2 | exact Hb2 ] ]
    | exact Hx4
    | rewrite exp_sub_extend_sub2; exact Hz4
    |].
  apply rel_chain_4;
    [ exact H12
    | pairwise
    | transitivity g2;
      [ pairwise | transitivity g1; [ symmetry; exact Hg | pairwise ] ] ].
Qed.

Hint Resolve rel_exp_nat_beta_succ : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve valid_exp_zero : mctt.
#[export]
Hint Resolve rel_exp_succ_cong : mctt.
#[export]
Hint Resolve rel_exp_natrec_cong : mctt.
#[export]
Hint Resolve rel_exp_nat_beta_zero : mctt.
#[export]
Hint Resolve rel_exp_nat_beta_succ : mctt.
