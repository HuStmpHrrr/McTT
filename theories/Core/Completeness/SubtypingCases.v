(** * Subtyping

    The four rules of [wf_subtyp] and the subsumption rule of [wf_exp_subtyp],
    validated semantically.

    [subtyp_under_ctx] spells a subtyping judgment out as *three* facts at each
    instantiation — the two commutation links [⟦A[σ]⟧ρ ≈ ⟦A⟧ρσ] and
    [⟦A'[σ']⟧ρ' ≈ ⟦A'⟧ρ'σ'], and [Sub ⟦A⟧ρσ <: ⟦A'⟧ρ'σ' at i] between the two
    middles.  So it is a four-value pattern with its middle link replaced by a
    subtyping: the two ends still have to be reconciled with the values the caller
    names, and only the *comparison* in the middle is asymmetric.  Every proof
    below has the same three-part shape as a result, and the interesting work is
    always in the middle part.

    Two consequences of that shape are worth recording, because both look like
    omissions and are not:

    - the judgment never relates [A'] at two *different* environments (both of its
      links stay within one column), so [rel_exp_eq_subtyp] cannot reconstruct
      [A']'s own type chain and must be given it.  That is exactly why
      [wf_exp_subtyp] and [wf_exp_eq_subtyp] carry the extra premise
      [{{ Γ ⊢ A' : Type@i }}];

    - [subtyp_refl] needs only [Γ ⊨ A ≈ A' : Type@i] and not the companion
      premise [Γ ⊨ A' ≈ A' : Type@i], since the second link is the first
      judgment's own third-to-fourth link read backwards.
 *)

From Stdlib Require Import Lia List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases SubstitutionCases FunctionCases.
Import Domain_Notations.
Import Wk_Notations.

(** ** [Sub-Eq]

    A type equality is a subtyping, because [per_subtyp_refl1] turns any related
    pair of type values into a subtyping between them.  The four-value pattern of
    the equality supplies all three parts at once: its outer two links *are* the
    two commutation obligations, and its middle link is what
    [per_subtyp_refl1] consumes. *)
Lemma subtyp_refl : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ⊆ A' }}.
Proof.
  intros * H%rel_exp_of_typ_inversion.
  destruct H as [env_relΓ [HΓ HA]].
  eexists_subtyp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  exists a1, a2, a4, a3.
  repeat apply conj; try eassumption.
  - pairwise.
  - (** The second obligation runs the other way round: what the chain has is
        [a3 ≈ a4] and what [subtyp_under_ctx] asks for is [a4 ≈ a3].  A chain in a PER
        relates every pair in either direction, so [pairwise] serves both. *)
    pairwise.
  - assert (Hmid : {{ Dom a2 ≈ a3 ∈ per_univ i }}) by pairwise.
    destruct Hmid as [R HR].
    eapply per_subtyp_refl1; eassumption.
Qed.

#[export]
Hint Resolve subtyp_refl : mctt.

(** ** [Sub-Trans]

    Transitivity is where the asymmetry of [subtyp_under_ctx] costs something.  The two
    hypotheses instantiated at the *same* data do not chain: the first reports
    [Sub ⟦A⟧ρσ <: ⟦A'⟧ρ'σ'] and the second [Sub ⟦A'⟧ρσ <: ⟦A''⟧ρ'σ'], whose
    middles are the values of [A'] at *different* environments.  What does chain is
    the second hypothesis taken a second time, at [Id] and at the pair
    [(ρ'σ', ρ'σ')] — legitimate because [ρσ ≈ ρ'σ'] makes [ρ'σ'] self-related —
    which reports [Sub ⟦A'⟧ρ'σ' <: ⟦A''⟧ρ'σ'] and so meets the first hypothesis on
    the nose.  [subtyp_under_ctx_simple] is that instance packaged. *)
Lemma subtyp_trans : forall {Γ A A' A''},
    {{ Γ ⊨ A ⊆ A' }} ->
    {{ Γ ⊨ A' ⊆ A'' }} ->
    {{ Γ ⊨ A ⊆ A'' }}.
Proof.
  intros * H1 H2.
  destruct H1 as [env_relΓ [HΓ [i H1gen]]].
  pose proof H2 as [env_relΓ2 [HΓ2 [j H2gen]]].
  pose proof (subtyp_under_ctx_simple H2) as [env_relΓ3 [HΓ3 [j' H2simple]]].
  assert (Hiff3 : env_relΓ3 <~> env_relΓ)
    by (eapply per_ctx_env_right_irrel; [ exact HΓ3 | exact HΓ ]).
  eexists_subtyp_with (max i (max j j')).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (H1gen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Hl1 [Hr1 Hsub1]]]]]]]]]].
  destruct (H2gen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [b1 [b2 [b3 [b4 [Hb1 [Hb2 [Hb3 [Hb4 [Hl2 [Hr2 Hsub2]]]]]]]]]].
  (** [ρ'σ'] is self-related, so the second hypothesis may be read at it. *)
  assert (Hρσ : {{ Dom ρσ ≈ ρ'σ' ∈ env_relΓ }})
    by (eapply (rel_sub_under_ctx_at' Hσ HΓ' HΓ); eassumption).
  assert (Hρ'σ' : {{ Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ3 }})
    by (rewrite Hiff3; etransitivity; [ symmetry; exact Hρσ | exact Hρσ ]).
  destruct (H2simple _ _ Hρ'σ') as [c [c' [Hc [Hc' Hsub3]]]].
  (** The three values of [A'] and the one of [A''] that the two readings share. *)
  assert (c = a4) as -> by (eapply functional_eval_exp; [ exact Hc | exact Ha4 ]).
  assert (c' = b4) as -> by (eapply functional_eval_exp; [ exact Hc' | exact Hb4 ]).
  exists a1, a2, b3, b4.
  repeat apply conj; try eassumption.
  - destruct Hl1 as [R HR]; exists R.
    eapply per_univ_elem_cumu_max_left; eassumption.
  - destruct Hr2 as [R HR]; exists R.
    eapply per_univ_elem_cumu_ge; [| eassumption]. lia.
  - eapply per_subtyp_trans;
      (eapply per_subtyp_cumu; [ eassumption | lia ]).
Qed.

#[export]
Hint Resolve subtyp_trans : mctt.

#[export]
Instance subtyp_Transitive Γ : Transitive (subtyp_under_ctx Γ).
Proof.
  intros A A' A''; apply subtyp_trans.
Qed.

(** ** [Sub-Univ]

    [Type@i[σ]] *is* [Type@i], so all four values of both columns are already
    equal and the two commutation obligations are reflexivity.  Only the middle is
    real, and it is [per_subtyp_univ].  The ambient level has to be strictly above
    [j], hence [S j]. *)
Lemma subtyp_univ : forall {Γ i j},
    {{ ⊨ Γ }} ->
    i <= j ->
    {{ Γ ⊨ Type@i ⊆ Type@j }}.
Proof.
  intros * HΓsem Hij.
  pose proof (sem_ctx_per_ctx_env HΓsem) as [env_relΓ HΓ].
  eexists_subtyp_with (S j).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  exists d{{{ 𝕌@i }}}, d{{{ 𝕌@i }}}, d{{{ 𝕌@j }}}, d{{{ 𝕌@j }}}.
  repeat apply conj; try apply eval_exp_typ.
  - eexists; apply per_univ_elem_core_univ'; [ lia | reflexivity ].
  - eexists; apply per_univ_elem_core_univ'; [ lia | reflexivity ].
  - apply per_subtyp_univ; lia.
Qed.

#[export]
Hint Resolve subtyp_univ : mctt.

(** ** [Sub-Pi]

    [per_subtyp_pi] wants four things: the two Π-values self-related, a domain PER
    relating them, and a codomain subtyping valid at every argument pair of that
    PER.  The first three are [rel_typ_of_pi] read at the three type equalities
    among the premises — the two self-equalities give the Π-values and the
    heterogeneous one gives the domain PER — and the fourth is the codomain
    premise, whose extended-context PER is [per_env_extend A' A' env_relΓ] because
    the repo checks both codomains in [Γ, A'] (see [System/Definitions.v]).

    Moving the quantified argument pair from the domain PER into that extended
    context PER is the one step with content: the two PERs share their *right*
    value [⟦A'⟧ρ'σ'], so [per_univ_elem_left_irrel] identifies them.

    Levels: the premises fix [i], the codomain subtyping arrives at whatever level
    [subtyp_under_ctx_simple] reports, and [per_subtyp_pi] insists that all of its
    premises and its conclusion agree.  So everything is raised to [max i i0]. *)
Lemma subtyp_pi : forall {Γ A A' i B B'},
    {{ Γ ⊨ A ≈ A : Type@i }} ->
    {{ Γ ⊨ A' ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊨ B ≈ B : Type@i }} ->
    {{ Γ, A' ⊨ B' ≈ B' : Type@i }} ->
    {{ Γ, A' ⊨ B ⊆ B' }} ->
    {{ Γ ⊨ Π A B ⊆ Π A' B' }}.
Proof.
  intros * HAself HA'self HAA' HB HB' Hsub.
  pose proof (rel_exp_of_typ_inversion HAA') as [env_relΓ [HΓ HAA'gen]].
  pose proof (subtyp_under_ctx_simple Hsub) as [env_relΓA' [HΓA' [i0 Hsubgen]]].
  pose proof (per_ctx_env_of_typ HΓ HA'self) as HΓA'can.
  assert (HiffA' : env_relΓA' <~> per_env_extend A' A' env_relΓ)
    by (eapply per_ctx_env_right_irrel; [ exact HΓA' | exact HΓA'can ]).
  eexists_subtyp_with (max i i0).
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρσ : {{ Dom ρσ ≈ ρ'σ' ∈ env_relΓ }})
    by (eapply (rel_sub_under_ctx_at' Hσ HΓ' HΓ); eassumption).
  (** The two Π-values, each from its own self-equality. *)
  destruct (rel_typ_of_pi HAself HB _ _ HΓ' _ _ _ _ _ _ Hσ Hρ Hev Hev')
    as [in1 [p1 [p2 [p3 [p4 [Hp1 [Hp2 [Hp3 [Hp4 [_ [_ Htyp1]]]]]]]]]]].
  destruct (rel_typ_of_pi HA'self HB' _ _ HΓ' _ _ _ _ _ _ Hσ Hρ Hev Hev')
    as [in2 [q1 [q2 [q3 [q4 [Hq1 [Hq2 [Hq3 [Hq4 [_ [Hmid2 Htyp2]]]]]]]]]]].
  pose proof Htyp1 as [P1 P2 P3 P4 HP1 HP2 HP3 HP4 HPchain].
  pose proof Htyp2 as [Q1 Q2 Q3 Q4 HQ1 HQ2 HQ3 HQ4 HQchain].
  assert (P2 = d{{{ Π p2 ρσ B }}}) as ->
    by (eapply functional_eval_exp; [ exact HP2 | apply eval_exp_pi; exact Hp2 ]).
  assert (Q3 = d{{{ Π q3 ρ'σ' B' }}}) as ->
    by (eapply functional_eval_exp; [ exact HQ3 | apply eval_exp_pi; exact Hq3 ]).
  (** The domain PER, from the heterogeneous equality's middle link. *)
  destruct (HAA'gen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  assert (d2 = p2) as -> by (eapply functional_eval_exp; [ exact Hd2 | exact Hp2 ]).
  assert (d3 = q3) as -> by (eapply functional_eval_exp; [ exact Hd3 | exact Hq3 ]).
  assert (Hmid : {{ Dom p2 ≈ q3 ∈ per_univ i }}) by pairwise.
  destruct Hmid as [in_rel Hin_rel].
  exists P1, d{{{ Π p2 ρσ B }}}, Q4, d{{{ Π q3 ρ'σ' B' }}}.
  (** The two element PERs are named rather than left to [eexists]: [pairwise]
      matches its [rel_chain] hypothesis syntactically, so a metavariable in the
      relation position of the goal finds nothing. *)
  repeat apply conj; try eassumption.
  - exists (per_pi in1 B ρσ B ρ'σ').
    eapply per_univ_elem_cumu_max_left; pairwise.
  - (** [Q4 ≈ Q3], i.e. the second chain's last link read backwards. *)
    exists (per_pi in2 B' ρσ B' ρ'σ').
    eapply per_univ_elem_cumu_max_left; pairwise.
  - eapply per_subtyp_pi with (in_rel := in_rel)
                              (elem_rel := per_pi in1 B ρσ B ρ'σ')
                              (elem_rel' := per_pi in2 B' ρσ B' ρ'σ').
    + eapply per_univ_elem_cumu_max_left; exact Hin_rel.
    + intros c c' b b' Hc Hb Hb'.
      (** [in_rel] and [in2] share the value [q3] on the right. *)
      assert (Hii : in_rel <~> in2)
        by (eapply per_univ_elem_left_irrel; [ exact Hin_rel | exact Hmid2 ]).
      rewrite Hii in Hc.
      assert (Hext : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΓA' }})
        by (rewrite HiffA'; apply per_env_extend_intro'; [ exact Hρσ |];
            eapply per_head_of; [ exact Hq2 | exact Hq3 | exact Hmid2 | exact Hc ]).
      destruct (Hsubgen _ _ Hext) as [b0 [b0' [Hb0 [Hb0' Hsubb]]]].
      assert (b0 = b) as -> by (eapply functional_eval_exp; [ exact Hb0 | exact Hb ]).
      assert (b0' = b') as -> by (eapply functional_eval_exp; [ exact Hb0' | exact Hb' ]).
      apply per_subtyp_cumu_right; exact Hsubb.
    + eapply per_univ_elem_cumu_max_left; pairwise.
    + eapply per_univ_elem_cumu_max_left; pairwise.
Qed.

#[export]
Hint Resolve subtyp_pi : mctt.

(** ** [Subsump]

    The term chain is already there; all that changes is the PER it is read in.
    [per_elem_subtyping] moves a single pair up a subtyping, and [rel_chain_mono]
    lifts that to the whole chain — the chain's *shape* is untouched, which is the
    point of stating the four-value pattern over a [rel_chain] in the first place.

    Two choices make the bookkeeping small.  The target PER is [A']'s canonical
    head PER rather than an anonymous witness, so that
    [per_univ_elem_at_head]/[per_univ_chain_at_in] can pin [A']'s chain to it
    instead of leaving an existential for [per_elem_subtyping] to guess.  And the
    common level is [max (max i j) k], the three levels the three hypotheses
    report, since [per_elem_subtyping] needs its subtyping and both of its type
    values at one level. *)
Lemma rel_exp_eq_subtyp : forall {Γ A A' i M M'},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A' ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ⊆ A' }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof.
  intros * HM HA' Hsub.
  pose proof (rel_exp_of_typ_inversion HA') as [env_relΓ [HΓ HA'gen]].
  destruct HM as [? [? [j HMgen]]].
  destruct Hsub as [? [? [k Hsubgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (HA'gen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htchain].
  assert (Hanchor : {{ DF t2 ≈ t3 ∈ per_univ_elem i ↘ (per_head A' A' ρσ ρ'σ') }})
    by (eapply per_univ_elem_at_head; [ exact Ht2 | exact Ht3 | pairwise ]).
  assert (Htchain' : rel_chain (per_univ_elem i (per_head A' A' ρσ ρ'σ')) [t1; t2; t3; t4])
    by (eapply per_univ_chain_at_in; [ exact Htchain | | | exact Hanchor ]; solve_in).
  destruct (HMgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev') as [RA [HAtyp HAexp]].
  destruct HAtyp as [s1 s2 s3 s4 Hs1 Hs2 Hs3 Hs4 Hschain].
  destruct HAexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct (Hsubgen _ _ HΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev')
    as [u1 [u2 [u3 [u4 [Hu1 [Hu2 [Hu3 [Hu4 [_ [_ Hsubst]]]]]]]]]].
  assert (u2 = s2) as -> by (eapply functional_eval_exp; [ exact Hu2 | exact Hs2 ]).
  assert (u4 = t3) as -> by (eapply functional_eval_exp; [ exact Hu4 | exact Ht3 ]).
  assert (HsubL : {{ Sub s2 <: t3 at (max (max i j) k) }})
    by (eapply per_subtyp_cumu; [ exact Hsubst | lia ]).
  (** Both self-relations have to be read off their own chain *before* the level
      is raised: [pairwise] cannot match a goal whose level is still a
      metavariable. *)
  assert (HRA0 : {{ DF s2 ≈ s2 ∈ per_univ_elem j ↘ RA }}) by pairwise.
  assert (HH0 : {{ DF t3 ≈ t3 ∈ per_univ_elem i ↘ (per_head A' A' ρσ ρ'σ') }})
    by pairwise.
  assert (HRAL : {{ DF s2 ≈ s2 ∈ per_univ_elem (max (max i j) k) ↘ RA }})
    by (eapply per_univ_elem_cumu_ge; [| exact HRA0 ]; lia).
  assert (HHL : {{ DF t3 ≈ t3 ∈ per_univ_elem (max (max i j) k)
                     ↘ (per_head A' A' ρσ ρ'σ') }})
    by (eapply per_univ_elem_cumu_ge; [| exact HH0 ]; lia).
  exists (per_head A' A' ρσ ρ'σ').
  split.
  - apply (mk_rel_exp t1 t2 t3 t4); eassumption.
  - apply (mk_rel_exp m1 m2 m3 m4); try eassumption.
    eapply rel_chain_mono; [| exact Hmchain ].
    intros w z Hwz.
    eapply per_elem_subtyping; [ exact HsubL | exact HRAL | exact HHL | exact Hwz ].
Qed.

#[export]
Hint Resolve rel_exp_eq_subtyp : mctt.
