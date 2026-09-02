(** * Fundamental Theorem: Natural Numbers

    Four of the old file's lemmas are gone.  [rel_exp_nat_sub],
    [rel_exp_zero_sub], [rel_exp_succ_sub] and [rel_exp_natrec_sub] validated the
    rules that pushed a substitution through [ℕ], [zero], [succ] and the
    eliminator; all four are now *equations* of [exp_sub] — indeed
    [exp_sub] matches on the expression, so [ℕ[σ]] literally *is* [ℕ],
    [zero[σ]] *is* [zero], and

      [(rec M return A | zero -> MZ | succ -> MS end)[σ]]

    *is* [rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end].

    What is left is the eliminator's congruence rule and its two β-rules, and the
    semantic recursion the three of them share.  That recursion is
    [per_nat_natrec], and it is stated here once, over an abstract *family* of
    element PERs

      [Rel : domain -> domain -> relation domain]

    indexed by the pair of arguments.  A family and not a single relation: the
    zero branch lives in the PER of the motive at [zero], the successor branch in
    the PER of the motive at [succ w], and the goal in the PER of the motive at
    the argument the eliminator was applied to.  Dependent elimination is exactly
    the statement that those are different relations, so no single [R] can serve.

    Abstracting over the family is also what makes *one* helper do the work of two.
    The "one-sided substituted" recursion — the eliminator with [A[q σ]], [MZ[σ]],
    [MS[q (q σ)]] at [ρ] on the left and the unsubstituted one at [⟦σ'⟧ρ'] on the
    right — has [per_nat_natrec]'s premises with [(Aa, ρa) := (A[q σ], ρ)] and its
    family the head PER of that pair; nothing in the proof looks at the *shape* of
    [Aa], so it is the same lemma at a different instance.  Hence three
    instantiations of [per_nat_natrec] — one per link of the four-value pattern —
    and no second induction. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation SubstitutionCases UniverseCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations.
Import Wk_Notations.

(** [ℕ]'s own [per_univ_elem], at the canonical element PER and at any level.
    Every [ℕ]-obligation below is this lemma; naming it is what keeps the level
    from being left as an unresolved existential, which is what
    [per_univ_elem_econstructor] under an [eapply] would do. *)
Lemma per_univ_elem_nat : forall i,
    DF ℕᵈ ≈ ℕᵈ ∈ per_univ_elem i ↘ per_nat.
Proof.
  intros; per_univ_elem_econstructor; reflexivity.
Qed.

#[export]
Hint Resolve per_univ_elem_nat : mctt.

(** ** [ℕ] as a Type

    Stated from the context PER and not from [⊨ Γ], because that is all the callers
    have: inside the eliminator's congruence rule the only thing known about [Γ] is
    the PER its hypotheses' inversions produce, and [⊨ Γ] does not follow from it.
    The level is arbitrary — [rel_typ_of_instance] reads the domain and the codomain
    of a dependent elimination at *one* level, and the codomain's is the motive's,
    so [ℕ]'s judgment has to be available there. *)
Lemma rel_exp_of_typ_nat : forall {Γ i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ ℕ ≈ ℕ : Type@i.
Proof.
  intros * HΓ.
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hn : Dom ℕᵈ ≈ ℕᵈ ∈ per_univ i)
    by (eexists; apply per_univ_elem_nat).
  (** [ℕ[σ]] *is* [ℕ], so all four values are handed over by the same rule. *)
  econstructor; try apply eval_exp_nat.
  apply rel_chain_4; assumption.
Qed.

#[export]
Hint Resolve rel_exp_of_typ_nat : mctt.

Corollary valid_exp_nat : forall {Γ i},
    ⊨ Γ ->
    Γ ⊨ ℕ : Type@i.
Proof.
  intros * H%sem_ctx_per_ctx_env.
  destruct H as [env_relΓ HΓ].
  eapply rel_exp_of_typ_nat; eassumption.
Qed.

#[export]
Hint Resolve valid_exp_nat : mctt.

(** ** [ℕ] as the Type of a Term

    The [ℕ] analogue of [rel_exp_of_typ_inversion]: a judgment at type [ℕ] is a
    four-value pattern in [per_nat] and nothing else, because the four values of
    the type are all [ℕ] and [per_univ_elem]'s [ℕ] case pins the element PER. *)
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

#[export]
Hint Resolve rel_exp_of_nat : mctt.

Ltac eexists_rel_exp_of_nat :=
  apply rel_exp_of_nat;
  eexists;
  eexists; [eassumption |].

(** The head PER of [ℕ] *is* [per_nat], in both directions.  Every context
    extension by [ℕ] goes through this, and so does every argument obligation of
    the eliminator, since the argument PER a caller has is [per_nat] while the
    context PER of [Γ ▹ ℕ] speaks of [per_head ℕ ℕ]. *)
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

(** The context PER of [Γ ▹ ℕ] and its two rules.  [ℕ[σ]] is [ℕ], so the
    substituted form [per_ctx_env_of_typ_sub] would produce is this one. *)
Corollary per_ctx_env_nat : forall {Γ env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Γ ▹ ℕ ≈ Γ ▹ ℕ ∈ per_ctx_env ↘ (per_env_extend ℕ ℕ env_relΓ).
Proof.
  intros * HΓ.
  eapply per_ctx_env_of_typ; [ eassumption |].
  eapply (@rel_exp_of_typ_nat _ 0); eassumption.
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

    The three obligations are the semantic contents of the eliminator's three
    premises, each stated at the pair of arguments the *recursion* needs it at
    rather than at the pair some judgment happened to be read at:

    - [Hmot] — the motive at an arbitrary pair of related arguments, reported as a
      [per_univ_elem] *at the family*, which is what pins [Rel] down;
    - [Hz] — the zero branch, in the family at [(zero, zero)];
    - [Hsucc] — the successor branch, at an arbitrary argument pair and an
      arbitrary pair of recursive results related in the family *there*, landing
      in the family at the successors.

    Nothing else about [Aa], [Ab], [MZa], … is used, which is why the same lemma
    serves the substituted links.

    [per_bot_natrec] is the neutral case, split off because it is where the
    obligations are consumed at *three* fixed argument pairs — a fresh variable,
    [zero], and the successor of that variable — the three [read_ne_natrec] reads
    the motive at.  The recursive call's argument is [⇑! b (S s)], the variable at
    the motive's own value, so [Hsucc] is instantiated at [var_per_elem]. *)
Lemma per_bot_natrec : forall {i Aa Ab MZa MZb MSa MSb ρa ρb za zb m m'}
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

Lemma per_nat_natrec : forall {i Aa Ab MZa MZb MSa MSb ρa ρb za zb}
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

    Both rules are one-line four-value patterns.  [zero[σ]] *is* [zero] and
    [(succ M)[σ]] *is* [succ (M[σ])], so the two commutation links of the pattern
    carry no content beyond the links they are built from, and every value is
    handed over by the same evaluation rule on both sides of the substitution. *)
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

#[export]
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

#[export]
Hint Resolve rel_exp_succ_cong : mctt.

(** ** The Successor Branch's Substitution

    The type of the successor branch is [A[Wk ⨟ Wk ,, succ #1]] — the motive at the
    successor of the number, in the context [Γ ▹ ℕ ▹ A] where [#1] is that number.
    Validating that substitution needs [#1 : ℕ] there, and *not* via
    [valid_exp_var], whose premise [⊨ Γ ▹ ℕ ▹ A] is strictly stronger than the
    context PER a caller inside the eliminator's rules has. *)
Lemma rel_exp_var1_nat : forall {Γ A i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
    Γ ▹ ℕ ▹ A ⊨ #1 ≈ #1 : ℕ.
Proof.
  intros * HΓ HA.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  eexists_rel_exp_of_nat.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  pose proof (rel_sub_under_ctx_at' Hσj HΓ' HΓNA _ _ _ _ Hρ Hev Hev') as [Htail _].
  apply per_env_extend_nat_elim in Htail as [_ Hhead].
  (** [#1[σ]] *is* [σ 1] and [(ρσ ↯) 0] *is* [ρσ 1], so both commutation links are
      the same value on both sides and the pattern collapses onto its middle. *)
  apply (mk_rel_exp (ρσ 1) (ρσ 1) (ρ'σ' 1) (ρ'σ' 1));
    try apply eval_exp_var; try (apply eval_sub_index; eassumption).
  apply rel_chain_4_of_2; first [ solve_chain_PER | eassumption ].
Qed.

(** Its companion one context shorter, which is what the *scrutinee* of the
    generic recursor is.  Same proof: [#0[σ]] is [σ 0] and [ρσ 0] is the head of
    [ρσ], so the four-value pattern collapses onto its middle. *)
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
    try apply eval_exp_var; try (apply eval_sub_index; eassumption).
  apply rel_chain_4_of_2; first [ solve_chain_PER | eassumption ].
Qed.

Lemma rel_sub_nat_step : forall {Γ A i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
    Γ ▹ ℕ ▹ A ⊨s Wk ⨟ Wk,,succ #1 : Γ ▹ ℕ.
Proof.
  intros * HΓ HA.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_intro HΓNA HΓN (rel_wk_shift HΓN HΓNA)))
    as HWk.
  eapply rel_sub_under_ctx_extend;
    [ eapply rel_sub_under_ctx_shift; exact HWk
    | eapply (@rel_exp_of_typ_nat _ 0); exact HΓ
    | apply rel_exp_succ_cong; eapply rel_exp_var1_nat; eassumption ].
Qed.

(** ** The Motive at an Arbitrary Argument Pair

    [per_nat_natrec]'s first obligation, delivered for all three links at *one*
    family of element PERs,

      [Rel w z := per_head A A (⟦σ⟧ρ ↦ w) (⟦σ'⟧ρ' ↦ z)],

    the head PER of the motive at the environments the *goal* names.  That it can
    be one family is the point: the three links compare values of the motive at
    three different pairs of expressions and environments ([A[q σ]] at [ρ] against
    [A] at [⟦σ⟧ρ], and so on), and a recursion cannot mix relations, so every one
    of them has to be reported in this single [Rel].

    Doing so is one anchoring plus one chain.  The anchor is the motive's own
    relatedness link at [(w, z)], read as a [per_univ_elem] *at* [Rel w z] by
    [per_univ_elem_at_head]; the chain collects every value the three obligations
    mention together with the anchor's two, so that refining it along the anchor
    ([per_univ_chain_at_in]) puts all of them in [Rel w z] at once.  Four
    instantiations of [rel_exp_of_typ_under_ctx_q] produce its links — the motive
    at [(w, z)] both reflexively and as [A ≈ A'], and reflexively at [(w, w)] and
    [(z, z)], which are what bridge the two argument values. *)
Lemma rel_typ_of_nat_motive : forall {Γ A A' i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A' : Type@i ->
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
  pose proof (@rel_exp_of_typ_nat _ 0 _ HΓ) as Hnat.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAl.
  (** The three pairs of arguments the four instantiations run at.  [ℕ[σ]] is [ℕ],
      so the extended context PER is the unsubstituted one and its introduction
      rule is [per_env_extend_nat_intro]. *)
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
  (** Naming the values the instantiations share, explicitly: which of two names
      [functional_eval_rewrite_clear] keeps is what the merge below selects on. *)
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

    [MS]'s type is [A[Wk ⨟ Wk ,, succ #1]], so every value the successor
    obligation of [per_nat_natrec] produces is related in *that* type's head PER,
    while the obligation's goal is stated in the head PER of the motive [A] at
    [succ] of the number.  The two are the two ends of a single instantiation of
    [A]'s judgment along [Wk ⨟ Wk ,, succ #1], and this lemma is that
    instantiation: its outer values are the ones the premises come with, its inner
    ones the ones the goal asks for, and its chain is what [per_head_bridge]
    consumes to move between them.

    That the substitution's evaluation can be *named* at all — [ρ1 ↦ succ x1] on
    the nose, rather than something merely related to it — is because neither of
    its components hides a closure: the tail is a *pre*composition by a weakening,
    which does compute ([eval_sub_shift_pre]), and the head is a variable under a
    [succ]. *)
Lemma rel_typ_of_nat_step_gen : forall {Γ A i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
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
      [ apply eval_exp_succ |]; apply eval_exp_var_eq; reflexivity.
  }
  destruct (HAgen _ _ HΓNA _ _ Hstep _ _ _ _ Hpair (Hτ _) (Hτ _))
    as [p1 p2 p3 p4 Hp1 Hp2 Hp3 Hp4 Hpchain].
  exists p1, p2, p3, p4.
  do 4 (split; [ eassumption |]).
  exact Hpchain.
Qed.

Corollary rel_typ_of_nat_step : forall {Γ A i env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
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

    The companion of [rel_typ_of_nat_motive] for the *term* obligation: the three
    successor premises of the three [per_nat_natrec] instantiations, delivered —
    as they must be — in the one family [Rel] of the motive's head PERs, here at
    [(succ w, succ z)].

    Two moves are needed for each of them, and both are forced by the operational
    reading of substitution.  The values [MS] takes are related in the head PER of
    its *type*, [A[Wk ⨟ Wk ,, succ #1]], at whichever pair of environments they
    were read at; the goal asks for the head PER of [A] at [ρσ ↦ succ w] and
    [ρ'σ' ↦ succ z].  So each premise is moved along the environments
    ([per_head_of_typ_resp], through the chain below) and then along the
    substitution ([per_head_bridge], through [rel_typ_of_nat_step]) — which is
    what [Hmv] does once for all six.

    The chain is over eight environments of [Γ ▹ ℕ ▹ A], and again not because any
    one consumer wants eight: [rel_exp_under_ctx_q] reports its inner values at
    the environments [q σ] *reaches*, and at a doubly extended context those are
    two levels of [s ↦ w] away from the ones the goal names.  Every value the six
    premises mention is an extension of one of the four tails of
    [rel_sub_under_ctx_q] by one
    of the two heads [r], [r'], and the chain says they are all related. *)
Lemma rel_exp_of_nat_step : forall {Γ A i MS MS' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
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
  pose proof (@rel_exp_of_typ_nat _ 0 _ HΓ) as Hnat.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (per_ctx_env_nat HΓ') as HΓ'N.
  pose proof (per_ctx_env_of_typ HΓN HA) as HΓNA.
  pose proof (presup_rel_exp_under_ctx HMS) as [i0 HAτ].
  pose proof (rel_exp_of_typ_extend_simple HΓ Hnat HA) as HAsimple.
  (** [ℕ[σ]] is [ℕ], so the context [q σ] is a substitution *into* is the
      unsubstituted [Γ' ▹ ℕ] — but only up to the reduction of [exp_sub], which the
      applications below would have to see through. *)
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
      outer value of each outer obligation is wanted: their inner ones are read at
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
    substitution, with the
    zero branch's value coming from a gluing predicate rather than from a semantic
    judgment.  Instantiating the two obligations above at [Id] — where [⟦Id⟧s ρ]
    *is* [ρ] — makes their middle components exactly the two it asks for. *)
Lemma per_bot_natrec_diag : forall {Γ A i MZ MS env_relΓ ρ mz m},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
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
    chain and at *one* family of element PERs — the head PER of the motive at the
    arguments the *type* names, which is what [rel_typ_of_instance] reports and so
    what the goal's type component fixes.  The motive obligation of each is one of
    the three [rel_typ_of_nat_motive] produces, its successor obligation one of the
    three [rel_exp_of_nat_step] produces, and its zero obligation one link of
    [MZ]'s own chain, whose element PER is identified with the family at
    [(zero, zero)] by reading the type [A[Id ,, zero]] a second time through
    [rel_typ_of_instance].

    Each link then arrives in the family at its own pair of arguments, and
    [per_head_of_args] moves it to the pair the type names — the same final step as
    in [rel_exp_app_cong], for the same reason. *)
Lemma rel_exp_natrec_cong : forall {Γ A A' i MZ MZ' MS MS' M M'},
    Γ ▹ ℕ ⊨ A ≈ A' : Type@i ->
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
  pose proof (@rel_exp_of_typ_nat _ i _ HΓ) as Hnat.
  destruct HMZ as [? [? [k HMZgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** *** The Type

      [A[Id ,, M]] is an instance of the motive, so all of it — and the number's
      four values, and the motive at an arbitrary related pair, which the moves
      below need — comes from [rel_typ_of_instance]. *)
  destruct (rel_typ_of_instance Hnat HAl HMl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  (** The domain is [ℕ], so the PER its values live in is [per_nat] — which every
      obligation below is stated at, [per_nat] being what an argument pair of the
      recursor is drawn from. *)
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

      Its other judgment, [M ≈ M'], whose two outer values are the type's two
      first ones; the two chains therefore merge, and the six values of the merge
      are every argument pair the three instantiations run at. *)
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
      [rel_typ_of_instance] a second time identifies the element PER [MZ]'s
      judgment hands over with the family at [(zero, zero)] — the two agree on the
      type's inner values, which is all irrelevance needs. *)
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

      The motive and the successor branch at an arbitrary argument pair, both
      already in the one family; the family is supplied explicitly, since
      [per_nat_natrec] cannot read it off an obligation without solving for a
      relation under two binders. *)
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

#[export]
Hint Resolve rel_exp_natrec_cong : mctt.

(** ** [β] at [zero]

    The recursion at [zero] *is* the evaluation of the zero branch — that is
    [eval_natrec_zero], read from right to left — so the two sides of the rule have
    literally the same two inner values and [MZ]'s own chain is the goal's.  All
    that has to be done is to name the element PER the goal's type component fixes,
    which is the head PER of the motive at [(zero, zero)], and to identify it with
    the one [MZ]'s judgment hands over.  Reading the type [A[Id ,, zero]] through
    [rel_typ_of_instance] does both, exactly as in the zero-branch step of
    [rel_exp_natrec_cong].

    The successor branch plays no part, so — unlike the syntactic rule, which
    needs it to have a type at all — the premise about it can be dropped. *)
Lemma rel_exp_nat_beta_zero : forall {Γ A i MZ MS},
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ⊨ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id ,, zero].
Proof.
  intros * HA HMZ.
  destruct HMZ as [env_relΓ [HΓ [k HMZgen]]].
  pose proof (@rel_exp_of_typ_nat _ i _ HΓ) as Hnat.
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

#[export]
Hint Resolve rel_exp_nat_beta_zero : mctt.

(** ** The Generic Recursor

    The eliminator of [exp_sub_natrec_generic], validated semantically.  It is
    needed because the [ℕ]-[β] rule for [succ] mentions the recursive call [E]
    inside a *substitution* — [Id ,, M ,, E] — and the only way to
    validate a substitution extension is [rel_sub_under_ctx_extend_sub_double],
    whose last premise is a term of the context being extended.  [E] is a term of
    [Γ]; what is asked for is a term of [Γ ▹ ℕ].  Its generic form — scrutinee
    [#0], everything else weakened past that binder — is that term, and
    [exp_sub_natrec_generic_self] turns it back into [E] under any extension whose
    head is [M].

    The proof is [rel_exp_natrec_cong] at the weakened premises, which is what
    [rel_exp_under_ctx_wk] delivers; the two type rewrites are the syntactic
    lemmas that say weakening commutes with the two instantiated motives. *)
Lemma rel_exp_natrec_generic : forall {Γ A i MZ MS env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS : A[Wk ⨟ Wk ,, succ #1] ->
    Γ ▹ ℕ ⊨ rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end
            ≈ rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end : A.
Proof.
  intros * HΓ HA HMZ HMS.
  pose proof (per_ctx_env_nat HΓ) as HΓN.
  pose proof (@rel_exp_of_typ_nat _ 0 _ HΓ) as Hnat0.
  pose proof (rel_wk_under_ctx_intro HΓN HΓ (rel_wk_shift HΓ HΓN)) as Hup.
  pose proof (rel_wk_under_ctx_q Hup Hnat0) as Hupq.
  pose proof (rel_wk_under_ctx_q Hupq HA) as Hupqq.
  pose proof (rel_exp_under_ctx_wk Hup HMZ) as HMZw.
  pose proof (rel_exp_under_ctx_wk Hupqq HMS) as HMSw.
  rewrite exp_wk_sub_extend in HMZw.
  rewrite exp_wk_sub_natrec in HMSw.
  (** The conclusion type has to be produced as [A⟨wk_q ↑⟩[Id ,, #0]] and only
      then collapsed: rewriting the *goal* by [exp_wk_q_shift_single] backwards
      would match the [A⟨wk_q ↑⟩] inside the motive instead. *)
  assert (HEg : Γ ▹ ℕ ⊨ rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end
                        ≈ rec #0 return A⟨wk_q ↑⟩ | zero -> MZ⟨↑⟩ | succ -> MS⟨wk_q (wk_q ↑)⟩ end
                        : A⟨wk_q ↑⟩[Id ,, #0])
    by (eapply rel_exp_natrec_cong;
        [ exact (rel_exp_under_ctx_wk Hupq HA) | exact HMZw | exact HMSw
        | apply (rel_exp_var0_nat HΓ) ]).
  rewrite exp_wk_q_shift_single in HEg.
  exact HEg.
Qed.

(** ** [β] at [succ]

    The rule the whole [ℕ] section has been building towards.  Both sides run the
    successor branch, so the two inner values are shared and the work is entirely
    in the *outer* ones: the left side reaches [MS] through
    [eval_natrec_succ] under [σ], the right side reaches it through the
    doubly-extended substitution [σ ,, M[σ] ,, E[σ]], and nothing computes
    [MS[Id ,, M ,, E][σ] = MS[σ ,, M[σ] ,, E[σ]]] semantically — no composition
    law for evaluated substitutions exists (see the closing comment of
    [Core/Semantic/Evaluation/Definitions.v]).

    What replaces it is two more instances of [MS]'s own judgment, each a
    four-value pattern of its own:

      - chain A at [Γ ⊨s Id ,, M ,, E], whose *outer* environments are [ρσ] and
        [ρ'σ'] and whose inner ones are the two the recursion produces.  Its
        fourth value is the goal's third.
      - chain B at [Γ' ⊨s σ ,, M[σ] ,, E[σ]], whose outer environments are [ρ] and
        [ρ'].  Its fourth value is the goal's fourth, modulo
        [exp_sub_extend_sub2].

    Both are supplied by [rel_sub_under_ctx_extend_sub_double] applied to the
    generic recursor, at [Id] and at [σ] respectively.  Their element PERs are
    both identified with the goal's by irrelevance, because
    [exp_sub_natrec_step] makes their type components' outer values the *same*
    evaluations as the goal type's — this is the one place the generalisation of
    that lemma from [Id] to an arbitrary [σ] is used.

    The three links of the goal are then:

      - [v1 ≈ v2] from the first obligation of [rel_exp_of_nat_step] at
        [(m1, m2, c1, c2)];
      - [v2 ≈ v3] by [pairwise] on chain A;
      - [v3 ≈ v4] by [pairwise] on chain A, the *second* step obligation at
        [(m1, m3, c1, c3)] read backwards, and [pairwise] on chain B.

    Each obligation lands in the motive's head PER at its own argument pair, and
    [per_head_of_args] moves it to the pair the goal type names — as everywhere
    else in this file. *)
Lemma rel_exp_nat_beta_succ : forall {Γ A i MZ MS M},
    Γ ▹ ℕ ⊨ A ≈ A : Type@i ->
    Γ ⊨ MZ ≈ MZ : A[Id ,, zero] ->
    Γ ▹ ℕ ▹ A ⊨ MS ≈ MS : A[Wk ⨟ Wk ,, succ #1] ->
    Γ ⊨ M ≈ M : ℕ ->
    Γ ⊨ rec succ M return A | zero -> MZ | succ -> MS end
         ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end]
         : A[Id ,, succ M].
Proof.
  intros * HA HMZ HMS HM.
  pose proof (rel_exp_of_nat_inversion HM) as [env_relΓ [HΓ HMgen]].
  pose proof (@rel_exp_of_typ_nat _ i _ HΓ) as Hnat.
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
  (** The two recursions the goal's left-hand side runs *inside* its own
      [eval_natrec_succ] are the ones [E] already evaluates: invert [E]'s two
      evaluations rather than letting [simplify_evals] loose on a context of eight
      evaluations at six different environments. *)
  pose proof Hc1 as Hc1'.
  cbn [exp_sub] in Hc1'.
  destruct (eval_exp_natrec_inversion _ _ _ _ _ _ Hc1') as [n1 [Hn1 Hrec1]].
  assert (n1 = m1) as -> by (eapply functional_eval_exp; [ exact Hn1 | exact Hm1 ]).
  destruct (eval_exp_natrec_inversion _ _ _ _ _ _ Hc2) as [n2 [Hn2 Hrec2]].
  assert (n2 = m2) as -> by (eapply functional_eval_exp; [ exact Hn2 | exact Hm2 ]).
  (** *** The Successor Branch

      [E]'s chain lives at [(m2, m3)]; each obligation of the step runs at the
      pair of arguments *it* is about, so move the relevant link there first. *)
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

#[export]
Hint Resolve rel_exp_nat_beta_succ : mctt.
