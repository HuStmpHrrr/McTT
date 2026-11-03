(** * Building Semantic Substitutions

    These lemmas validate no typing rule, since substitution is an operation and
    has no rules of its own.  They are the tools the case files need: every rule
    with a premise in an extended context (Π, λ, ℕ-elim, …) is proved by
    instantiating that premise at a substitution built here.

    The target context is always an extension, whose context PER is
    [per_env_extend], so each proof has two halves:

    - Tails: the underlying substitution, from one instantiation of the
      hypothesis, or from two merged along a shared value.
    - Heads: the extension term, whose four values must land in the head PER of
      the target.  That PER is the one [A] denotes at the substituted
      environments, while the hypothesis about the term speaks of [A[σ]] at the
      outer ones, so the two must be bridged.  [per_head] is impredicative for
      this reason: bridging is then saturation of the [per_univ_elem]
      irrelevance biconditionals by [handle_per_univ_elem_irrel].

    The type of an extended context is written [A] and the extension term [M],
    also because [S] is [nat]'s constructor, so [S[ψ]ʷ] in a tactic argument
    would be read as a name and rejected. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation UniverseCases.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** The extended context PER of [Δ ▹ A], read off a semantic type judgment:
    [per_ctx_env_extend] fed by the [Id] instance of [rel_exp_under_ctx_simple].
    This is the first step of every proof below. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The arguments [c] and [c'] read back at each of the stored types [ts]:
    the entry types the extensions of the four environments of a
    Π-pattern carry, one per environment.  For example, at [Π A B] the
    four types are the values of [A[σ]] at [ρ], of [A] at [⟦σ⟧ρ] and at
    [⟦σ'⟧ρ'], and of [A[σ']] at [ρ'], and [c ≈ c'] in the domain PER reads
    back at each ([entry_readable_of_elem]). *)
Definition args_readable_at (c c' : domain) (ts : list entry_type) : Prop :=
  List.Forall (fun t => entry_readable (de_term c t) /\ entry_readable (de_term c' t)) ts.

Lemma per_ctx_env_of_typ : forall {Δ A} {i : nat} {env_relΔ},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    Δ ⊨ᵗ A ≈ A at i ->
    EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ (per_env_extend A A env_relΔ).
Proof.
  intros * HΔ H.
  pose proof (rel_type_inversion_simple H) as [env_relΔ' [HΔ' HA]].
  handle_per_ctx_env_irrel.
  eapply per_ctx_env_extend; eassumption.
Qed.

(** The same for a substituted type.  Every rule with a premise in an extended
    context needs this: [q σ] goes from [Γ ▹ A[σ]] to [Δ ▹ A], and a Π-, λ- or
    ℕ-elim rule instantiates its premise there.

    It is not an instance of the lemma above, because [Γ ⊨ A[σ] ≈ A[σ] : Typeω@i]
    would need a semantic substitution lemma for types, which the development
    neither has nor needs.  Instead, [A]'s own judgment is instantiated along
    [σ ≈ σ]; its outer values are the values of [A[σ]] at the outer environments,
    which is what the head obligation asks for.  Hence the
    [rel_sub_under_ctx_simple] form of the substitution: only two evaluations of
    [σ] at a related pair are needed, not the four of a full four-value
    pattern. *)
Lemma per_ctx_env_of_typ_sub : forall {Γ Δ σ σ' A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    EF Γ ▹ A[σ] ≈ Γ ▹ A[σ] ∈ per_ctx_env ↘ (per_env_extend A[σ] A[σ] env_relΓ).
Proof.
  intros * HΓ Hσj HA.
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  pose proof (rel_sub_under_ctx_simple (rel_sub_under_ctx_refl_left Hσj))
    as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 Hσrefl]]]].
  handle_per_ctx_env_irrel.
  eapply (per_ctx_env_extend (i := i)); [ eassumption |].
  intros ρ ρ' Hρ.
  destruct (Hσrefl _ _ Hρ) as [ρσ [ρ'σ' [Hev [Hev' Hrel]]]].
  destruct (HAgen _ _ HΓ2 _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  exists a1, a4.
  repeat split; try eassumption.
  pairwise.
Qed.

(** A member of that PER, from an element of any PER inhabited by the values
    of [A[σ]].  Rules with a premise in an extended context need this form: they
    start from a pair [c ≈ c'] drawn from the domain PER of a Π-value or from
    [per_nat], at whatever level and relation the other hypothesis produced, never
    the [i] of [A]'s judgment.  Only [a] is named, since irrelevance needs one
    shared value and the caller has the left one. *)
Lemma per_env_extend_sub_intro : forall {Γ Δ σ σ' A} {i : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    forall ρ ρ' j a b R c c' t t',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ A[σ] ⟧ ρ ↘ a ->
      DF a ≈ b ∈ per_univ_elem j ↘ R ->
      Dom c ≈ c' ∈ R ->
      entry_readable (de_term c t) -> entry_readable (de_term c' t') ->
      Dom ρ ↦ c ⦂ t ≈ ρ' ↦ c' ⦂ t' ∈ per_env_extend A[σ] A[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA * Hρ Ha HR Hc Hrd Hrd'.
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  pose proof (rel_sub_under_ctx_simple (rel_sub_under_ctx_refl_left Hσj))
    as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 Hσrefl]]]].
  handle_per_ctx_env_irrel.
  (** [A]'s judgment along [σ ≈ σ]: its outer values are the values of [A[σ]] at
      [ρ] and at [ρ'], which is what the head PER is stated at. *)
  destruct (Hσrefl _ _ Hρ) as [ρσ [ρ'σ' [Hev [Hev' Hrel]]]].
  destruct (HAgen _ _ HΓ2 _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
  assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
  functionalize_per_univ_chain Hchain R0.
  apply per_env_extend_intro'; [ eassumption | | exact Hrd | exact Hrd' ].
  eapply per_head_of; [ exact Ha | exact Ha4 | pairwise |].
  (** [Hc] retyped: the chain and [HR] both relate [a] on the left, and
    [per_univ_elem] irrelevance is cross-level, so the caller's level [j] need
    not match [i]. *)
  retype_rel_chain Hchain HR Hc; exact Hc.
Qed.

(** A type judgment in [Δ ▹ A] read at an arbitrary member of the canonical
    extended context PER, rather than at one built from a [q] by
    [per_env_extend_sub_intro].  An instantiated codomain needs this: it is
    evaluated at [ρ ↦ m] for some [m] coming from the term being applied, which no
    [q]-shaped lemma produces.

    It is a separate lemma so that [handle_per_ctx_env_irrel] runs on a goal where
    the extended PER occurs on both sides, in the hypothesis [HBl] and in the
    argument [Hρ]; whichever name the tactic keeps, the application still
    typechecks. *)
Lemma rel_exp_of_typ_extend_simple : forall {Γ A} {i : nat} {B B' j env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A ⊨ B ≈ B' : Typeω@j ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ per_env_extend A A env_relΓ ->
      exists b b',
        ⟦ B ⟧ ρ ↘ b /\ ⟦ B' ⟧ ρ' ↘ b' /\ Dom b ≈ b' ∈ per_univ j.
Proof.
  intros * HΓ HA HB * Hρ.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_exp_of_typ_inversion_simple HB) as [env_relΓA [HΓA2 HBl]].
  handle_per_ctx_env_irrel.
  exact (HBl _ _ Hρ).
Qed.

(** The same for a term of [Δ, A], with its element PER replaced by the
    canonical [per_head] of its type ([per_head_of]).  Reporting the canonical PER
    rather than the judgment's own [R] makes results composable: consumers put
    several such instances into one chain, and [per_head_of_args] moves between
    head PERs at different arguments, which a bare [R] does not allow. *)
Lemma rel_exp_under_ctx_extend_simple : forall {Γ A} {i : nat} {B M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A ⊨ M ≈ M' : B ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ per_env_extend A A env_relΓ ->
      rel_typ_propositional B ρ \/
      exists m m',
        ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\
          Dom m ≈ m' ∈ per_head B B ρ ρ'.
Proof.
  intros * HΓ HA HM * Hρ.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  exact (rel_exp_under_ctx_simple_at HΓA HM _ _ Hρ).
Qed.

(** The [Wk] instance of the same, which is the only way a weakened term
    acquires a value.  The equation [⟦M[φ]ʷ⟧ρ = ⟦M⟧(⟪φ⟫ ρ)] fails: in the λ case
    the two sides are the closures [λ ρ (N[q φ]ʷ)] and [λ (⟪φ⟫ ρ) N], which are
    different and not even related.  So semantic weakening exists only as the
    instance of a judgment along [Wk], and [⟦M[↑]ʷ⟧(ρ ↦ c)] is reachable no other
    way.  [rel_exp_under_ctx_extend_simple] is the [Id] instance of the same idea.

    Unlike there, the element PER is not replaced by a canonical [per_head].
    Instead [B]'s four values are reported, with the PER at its outer pair (which
    [per_head_iff] turns into the head PER of [B[↑]ʷ] at the two extended
    environments) and at its inner pair (which [per_pi_iff] turns into the
    function PER of [B] at the two tails, when [B] is a Π).  Which one a caller
    wants depends on the shape of [B]. *)
Lemma rel_exp_under_ctx_shift_at : forall {Γ A} {i : nat} {B M M' env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ M ≈ M' : B ->
    (forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΓ -> rel_typ_sort B ρ relevant) ->
    forall ρ ρ' c c' t t',
      Dom ρ ↦ c ⦂ t ≈ ρ' ↦ c' ⦂ t' ∈ per_env_extend A A env_relΓ ->
      exists j R b1 b2 b3 b4 w1 w2 w3 w4,
        ⟦ B[↑]ʷ ⟧ ρ ↦ c ⦂ t ↘ b1 /\
        ⟦ B ⟧ ρ ↘ b2 /\
        ⟦ B ⟧ ρ' ↘ b3 /\
        ⟦ B[↑]ʷ ⟧ ρ' ↦ c' ⦂ t' ↘ b4 /\
        DF b1 ≈ b4 ∈ per_univ_elem j ↘ R /\
        DF b2 ≈ b3 ∈ per_univ_elem j ↘ R /\
        ⟦ M[↑]ʷ ⟧ ρ ↦ c ⦂ t ↘ w1 /\
        ⟦ M ⟧ ρ ↘ w2 /\
        ⟦ M' ⟧ ρ' ↘ w3 /\
        ⟦ M'[↑]ʷ ⟧ ρ' ↦ c' ⦂ t' ↘ w4 /\
        rel_chain R ([w1; w2; w3; w4]).
Proof.
  intros * HΓ HA HM HBr * Hρ.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_sub_of_wk_rel HΓA HΓ (rel_wk_shift HΓ HΓA) (fun x Hx => ltac:(cbn; lia))) as HWk.
  destruct HM as [env_relΓ2 HΓ2 j HMgen].
  assert (Hρt : Dom ρ ≈ ρ' ∈ env_relΓ) by (destruct Hρ as [Ht _ _ _ _ _]; exact Ht).
  (** The two substituted environments of [Wk] at [ρ ↦ c] and [ρ' ↦ c'] are
    the retagged tails ([eval_sub_shift]).  The [Id] instance at the
    tails has the same inner environments, and its outer values are the
    values at the tails themselves: the two chains merge there. *)
  destruct (eval_sub_shift_rel HΓA Hρ) as [Hs Hs'].
  destruct (HMgen _ _ HΓA _ _ HWk _ _ _ _ Hρ Hs Hs') as [R [Htyp Hexp]].
  pose proof (HBr _ _ (per_ctx_env_retag_left HΓ _ _ Hρt)) as HBrr.
  apply (rel_exp_or_prop_relevant Htyp HBrr) in Hexp.
  destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct Hexp as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hwchain].
  rewrite exp_sub_of_shift in Hb1, Hb4, Hw1, Hw4.
  assert (HΓk : EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ2) by exact HΓ2.
  assert (E2 : env_relΓ <~> env_relΓ2) by (eapply per_ctx_env_right_irrel; [ exact HΓ | exact HΓ2 ]).
  destruct (eval_sub_id_rel HΓk (proj1 (E2 _ _) Hρt)) as [Hid Hid'].
  destruct (HMgen _ _ HΓk _ _ (rel_sub_id (ex_intro _ _ HΓk)) _ _ _ _ (proj1 (E2 _ _) Hρt) Hid Hid')
    as [R' [Htyp' Hexp']].
  apply (rel_exp_or_prop_relevant Htyp' HBrr) in Hexp'.
  destruct Htyp' as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct Hexp' as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Huchain].
  rewrite exp_sub_id in Hc1, Hc4, Hu1, Hu4.
  cbn [drop_env List.tl] in *.
  functional_eval_rewrite_clear.
  assert (Hm1 : DF b2 ≈ b3 ∈ per_univ_elem j ↘ R) by pairwise.
  assert (Hm2 : DF b2 ≈ b3 ∈ per_univ_elem j ↘ R') by pairwise.
  assert (ER : R' <~> R) by exact (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hm2 Hm1).
  assert (PER R) by (eapply per_elem_PER; exact Hm1).
  apply (rel_chain_mono _ _ (fun a b Hab => proj1 (ER a b) Hab)) in Huchain.
  apply (fun Hx => per_univ_elem_resp_iff Hx ER) in Hm2.
  assert (Hcc : rel_chain (per_univ_elem j R) ([c1; b2; b3; c4])).
  { eapply rel_chain_mono; [| exact Hcchain ]; intros a b Hab; eapply per_univ_elem_resp_iff; [ exact Hab | exact ER ]. }
  exists j, R, b1, c1, c4, b4, w1, u1, u4, w4.
  do 4 (split; [ eassumption |]).
  split; [ pairwise |].
  split; [ pairwise |].
  do 4 (split; [ eassumption |]).
  merge_rel_chain Hwchain Huchain w2.
Qed.

(** ** [q] Preserves Semantic Weakening

    The only lemma here about weakenings, and a cheap one: both halves of the
    extended context PER hold by conversion for [q ψ] ([eval_wk_q_tail],
    [eval_wk_q_zero]), so the tail obligation is the hypothesis and the head
    obligation is one bridging step. *)

Lemma rel_wk_under_ctx_q : forall {Γ ψ Δ A} {i : nat},
    Γ ⊨ʷ ψ : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A[ψ]ʷ ⊨ʷ (wk_q ψ) : Δ ▹ A.
Proof.
  intros * Hψj HA.
  pose proof Hψj as [env_relΓ HΓ env_relΔ HΔ Hψ Hψl Hψp].
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  handle_per_ctx_env_irrel.
  pose proof (rel_wk_mono _ _ _ Hψ) as Hψm.
  (** The commutation obligation of [A] along [ι ψ].  It is used three times,
    to build the context PER of [Γ ▹ A[ψ]ʷ], to bridge the head PERs and to
    carry a propositional head across, so it is named, at an environment
    pair the caller supplies.  Its inner values are at [⟪ψ⟫ ρ] and
    [⟪ψ⟫ ρ'] themselves, read off [rel_type_inversion_wk] at three pairs
    (the instance along [ι ψ] has them at the retaggings). *)
  assert (Hcom : forall ρ ρ',
             Dom ρ ≈ ρ' ∈ env_relΓ ->
             rel_exp A (ι ψ) ρ ⟪ψ⟫ ρ
                     A (ι ψ) ρ' ⟪ψ⟫ ρ' (per_univ i)).
  { intros ρ ρ' Hρ.
    destruct (rel_type_inversion_wk Hψj HA) as [R0 [HR0 Hw]].
    assert (E0 : env_relΓ <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (PER env_relΓ) by (eapply per_env_PER; eassumption).
    assert (Hρρ : Dom ρ ≈ ρ ∈ env_relΓ) by solve_per.
    assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ env_relΓ) by solve_per.
    destruct (Hw _ _ (proj1 (E0 _ _) Hρ)) as (a1 & a3 & Ha1 & Ha3 & H13).
    destruct (Hw _ _ (proj1 (E0 _ _) Hρρ)) as (a1' & a2 & Ha1' & Ha2 & H12).
    destruct (Hw _ _ (proj1 (E0 _ _) Hρ'ρ')) as (a4 & a3' & Ha4 & Ha3' & H43).
    assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
    assert (a3' = a3) as -> by (eapply functional_eval_exp; eassumption).
    rewrite <- exp_sub_of_wk in Ha1, Ha4.
    apply (mk_rel_exp a1 a2 a3 a4); try eassumption.
    apply rel_chain_4;
      [ exact H12 | etransitivity; [ symmetry; exact H12 | exact H13 ] | symmetry; exact H43 ]. }
  pose proof (per_ctx_env_of_typ HΔ' HA) as HΔA.
  assert (HΓA : EF Γ ▹ A[ψ]ʷ ≈ Γ ▹ A[ψ]ʷ ∈ per_ctx_env
                     ↘ (per_env_extend A[ψ]ʷ A[ψ]ʷ env_relΓ)).
  { eapply (per_ctx_env_extend (i := i)); [ eassumption |].
    intros ρ ρ' Hρ.
    destruct (Hcom _ _ Hρ) as [a1 ? ? a4 Ha1 ? ? Ha4 Hchain].
    rewrite exp_sub_of_wk in Ha1, Ha4.
    exists a1, a4.
    repeat split; try eassumption.
    pairwise. }
  eexists_rel_wk.
  - (** Both projections of [⟪q ψ⟫ ρ] are conversions, so nothing is rewritten
      below: [exact] sees through [⟪q ψ⟫ ρ] to [⟪ψ⟫ (ρ ↯)] and to [ρ 0]. *)
    split; [ typeclasses eauto |].
    intros ρ ρ' [Htail Hhead Hl Hr Hrl Hrr].
    apply per_env_extend_intro; rewrite ?eval_wk_q_zero; rewrite ?eval_wk_q_tail by typeclasses eauto;
      [ | | | | rewrite eval_wk_q_zero_entry; exact Hrl | rewrite eval_wk_q_zero_entry; exact Hrr ].
    + exact (Hψ _ _ Htail).
    + destruct (Hcom _ _ Htail) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
      rewrite exp_sub_of_wk in Ha1, Ha4.
      functionalize_per_univ_chain Hchain R.
      eapply per_head_bridge;
        [ exact Hhead | exact Ha1 | exact Ha4 | pairwise | exact Ha2 | exact Ha3
        | pairwise_univ ].
    + (** [A] at the image of the tail is a proposition exactly when
          [A[ψ]ʷ] is at the tail. *)
      rewrite eval_wk_q_zero_entry; intros (a & Ea & Hp); apply Hl.
      rewrite ?eval_wk_q_tail in Ea by typeclasses eauto.
      destruct (Hcom _ _ Htail) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
      rewrite exp_sub_of_wk in Ha1.
      assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (H12 : Dom a1 ≈ a ∈ per_univ i) by pairwise.
      destruct H12 as [R12 H12]; pose proof (per_univ_elem_relevance _ _ _ _ H12).
      exists a1; split; [ exact Ha1 | congruence ].
    + rewrite eval_wk_q_zero_entry; intros (a & Ea & Hp); apply Hr.
      rewrite ?eval_wk_q_tail in Ea by typeclasses eauto.
      destruct (Hcom _ _ Htail) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
      rewrite exp_sub_of_wk in Ha4.
      assert (a3 = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (H34 : Dom a ≈ a4 ∈ per_univ i) by pairwise.
      destruct H34 as [R34 H34]; pose proof (per_univ_elem_relevance _ _ _ _ H34).
      exists a4; split; [ exact Ha4 | congruence ].
  - (** The target's entries: the head to the head, the others as [ψ]
      takes them. *)
    intros [| x] Hx; cbn [wk_q]; [ cbn; lia |].
    pose proof (Hψl x ltac:(cbn in Hx; lia)); cbn; lia.
  - (** The head: [A[ψ]ʷ] at a tail is a proposition exactly when [A] is at
      its image, by the commutation obligation, at a tail agreeing with the
      given one. *)
    intros ρ ρ' [Htail _ _ _ _ _] [| x] Hlt; split.
    + intros Hx; destruct Hx as [T HT E HE v Ev Hv]; cbn in HT; injection HT as <-.
      rewrite skipn_one_drop in HE.
      assert (HE' : Dom E ≈ ρ'↯ ∈ env_relΓ)
        by (eapply per_ctx_env_resp_agree; [ exact HΓ | symmetry; exact HE | reflexivity | exact Htail ]).
      destruct (Hcom _ _ HE') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
      rewrite exp_sub_of_wk in Ha1.
      functional_eval_rewrite_clear.
      assert (H12 : Dom v ≈ a2 ∈ per_univ i) by pairwise.
      destruct H12 as [R12 H12].
      pose proof (per_univ_elem_relevance _ _ _ _ H12) as Hr12.
      econstructor; [ reflexivity | | exact Ha2 | congruence ].
      intros y Hy; rewrite skipn_one_drop, eval_wk_q_tail by typeclasses eauto.
      rewrite !eval_wk_entry by assumption; apply HE, Hψl; exact Hy.
    + (** Conversely: [A] at a tail agreeing with the image of the tail
          is related to [A[ψ]ʷ] at the tail itself. *)
      intros Hx; destruct Hx as [T HT E HE v Ev Hv]; cbn in HT; injection HT as <-.
      rewrite skipn_one_drop, eval_wk_q_tail in HE by typeclasses eauto.
      pose proof (Hψ _ _ Htail) as Hψρ.
      match type of Hψρ with
      | ?RΔ _ _ =>
          assert (HE' : RΔ E (⟪ψ⟫ (ρ'↯)))
            by (eapply per_ctx_env_resp_agree; [ eassumption | symmetry; exact HE | reflexivity | exact Hψρ ])
      end.
      destruct (Hcom _ _ Htail) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
      rewrite exp_sub_of_wk in Ha1.
      destruct (rel_type_inversion_simple_at (Γ := Δ) ltac:(eassumption) HA _ _ HE') as (b & b' & Eb & Eb' & [Rb Hb]).
      functional_eval_rewrite_clear.
      assert (H13 : Dom a1 ≈ a3 ∈ per_univ i) by pairwise.
      destruct H13 as [R13 H13].
      pose proof (per_univ_elem_relevance _ _ _ _ H13) as Hr13.
      pose proof (per_univ_elem_relevance _ _ _ _ Hb) as Hrb.
      econstructor; [ reflexivity | intros y _; rewrite skipn_one_drop; reflexivity | exact Ha1 | congruence ].
    + intros Hx; apply (proj1 (entry_propositional_succ _ _ _ _)) in Hx.
      apply (proj2 (entry_propositional_succ _ _ _ _)).
      rewrite eval_wk_q_tail by typeclasses eauto.
      exact (proj1 (Hψp _ _ Htail x ltac:(cbn in Hlt; lia)) Hx).
    + intros Hx; apply (proj1 (entry_propositional_succ _ _ _ _)) in Hx.
      rewrite eval_wk_q_tail in Hx by typeclasses eauto.
      apply (proj2 (entry_propositional_succ _ _ _ _)).
      exact (proj2 (Hψp _ _ Htail x ltac:(cbn in Hlt; lia)) Hx).
Qed.

(** ** Extension is Semantic

    The first of three extension lemmas, and the template for the other two.  At
    every Kripke stage [Γ' ⊨ʷ φ : Γ] it produces four environments and the chain
    relating them in the extended context PER of [Δ ▹ A].

    The four environments come from the two judgments about [σ ,, M]: the tails
    from the substitution judgment, the heads from the term judgment.
    [sb_wk_extend] says the two halves recombine into the substitution in the goal
    ([eval_sub_wk_extend] packages this).

    The chain then splits link by link into tails and heads.  The tails are already
    related by the substitution judgment's chain.  The heads are related in the PER
    the term judgment produced, and the work is to identify that PER with the head
    PER of [Δ, A].  This needs [A]'s values at all four environments linked, which
    takes two more instantiations of the type judgment: along [sb_wk σ φ]
    ([rel_sub_under_ctx_wk]) for the outer pair, and along [σ] for the inner pair.
    The type judgment's own chain links these to each other and to the term
    judgment's type chain, and [handle_per_univ_elem_irrel] then closes everything
    ([solve_per_env_extend_chain]). *)

Lemma rel_sub_under_ctx_extend : forall {Γ Δ σ σ' A} {i : nat} {M M'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Γ ⊨ M ≈ M' : A[σ] ->
    exp_scoped (List.length Γ) M -> exp_scoped (List.length Γ) M' ->
    Γ ⊨ˢ σ,,M ≈ σ',,M' : Δ ▹ A.
Proof.
  intros * Hσj HA HM HMs HMs'.
  pose proof Hσj as [env_relΓ HΓ env_relΔ HΔ Hσ Hσs].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  pose proof (rel_type_inversion_simple HA) as [env_relΔ'' [HΔ'' HAs]].
  destruct HM as [env_relΓ2 HΓ2 j HMgen].
  handle_per_ctx_env_irrel.
  assert (HΔk : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ) by eassumption.
  eexists_rel_sub; [| intros [| x] Hx; cbn; [ split; assumption | apply Hσs; cbn in Hx; lia ] ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  (** Tails. *)
  destruct (Hσ _ _ HΓ' _ Hφ Hφb _ _ Hρ) as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htails].
  (** The two instantiations of [HA] that link [A]'s four values.  The term
    judgment's type chain links them to its element PER. *)
  pose proof (HAgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk_rel Hσj HΓ' HΓ Hφ Hφb) _ _ _ _ Hρ Ht1 Ht4) as Houter.
  pose proof (HAgen _ _ HΓ _ _ Hσj _ _ _ _ (Hφ _ _ Hρ) Ht2 Ht3) as Hinner.
  destruct Houter as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct Hinner as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  (** Whether the head is a proposition is decided by [A]'s value at an
    inner tail, and the four tails agree on it. *)
  assert (Ht12 : Dom t1 ≈ t2 ∈ env_relΔ) by pairwise.
  assert (Ht23 : Dom t2 ≈ t3 ∈ env_relΔ) by pairwise.
  assert (Ht34 : Dom t3 ≈ t4 ∈ env_relΔ) by pairwise.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAs Ht12) as I12.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAs Ht23) as I23.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAs Ht34) as I34.
  pose proof (head_propositional_iff (e := ce_ass A) HΔk eq_refl HAs Ht23 Hd2) as I2.
  assert (Hd12 : Dom d1 ≈ d2 ∈ per_univ i) by pairwise.
  destruct Hd12 as [R12 Hd12]; pose proof (per_univ_elem_relevance _ _ _ _ Hd12) as Er12.
  destruct (eval_sub_of_wk_pair Hφ HΓ Hρ) as [Hw Hw'].
  destruct (rel_exp_body_of_retagged HΓ HMgen _ _ HΓ' _ _ (rel_sub_of_wk_rel HΓ' HΓ Hφ Hφb) _ _ _ _ Hρ Hw Hw' (Hφ _ _ Hρ))
    as [Rt [Htyp Hexp]].
  destruct (domain_relevance d2) eqn:Er2.
  - (** A relevant head: the heads are the term's four values, related in
      the head PER of [A] through the chains. *)
    assert (Hn2 : ~ head_propositional gc_deps gc_stack (ce_ass A) Δ t2) by (rewrite I2; discriminate).
    assert (Hn1 : ~ head_propositional gc_deps gc_stack (ce_ass A) Δ t1) by (rewrite I12; exact Hn2).
    assert (Hn3 : ~ head_propositional gc_deps gc_stack (ce_ass A) Δ t3) by (rewrite <- I23; exact Hn2).
    assert (Hn4 : ~ head_propositional gc_deps gc_stack (ce_ass A) Δ t4) by (rewrite <- I34; exact Hn3).
    apply (rel_exp_or_prop_relevant Htyp (ex_intro _ d1 (conj Hd1 Er12))) in Hexp.
    destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hheads].
    rewrite exp_sub_of_wk in Hm1, Hm4.
    apply (mk_rel_sub (t1 ↦ m1 ⦂ centry_tag (ce_ass A) Δ t1) (t2 ↦ m2 ⦂ centry_tag (ce_ass A) Δ t2)
             (t3 ↦ m3 ⦂ centry_tag (ce_ass A) Δ t3) (t4 ↦ m4 ⦂ centry_tag (ce_ass A) Δ t4));
      [ apply eval_sub_wk_extend; eassumption
      | apply eval_sub_extend; eassumption
      | apply eval_sub_extend; eassumption
      | apply eval_sub_wk_extend; eassumption
      | ].
    (** Rewriting the outer types with [A[σ][ι φ] = A[sb_wk σ φ]] makes the
      type chain's values the same values, not merely equal ones. *)
    destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
    rewrite exp_sub_of_wk, exp_wk_sub in Hb1, Hb4.
    functional_eval_rewrite_clear.
    destruct Hbchain as [? [? ?]].
    destruct_per_univ_chain Hcchain.
    destruct_per_univ_chain Hdchain.
    solve_per_env_extend_chain_tagged.
  - (** A propositional head: the heads are proofs, which the head PER of
      [A] relates at every link. *)
    assert (Hp2 : head_propositional gc_deps gc_stack (ce_ass A) Δ t2) by (rewrite I2; reflexivity).
    assert (Hp1 : head_propositional gc_deps gc_stack (ce_ass A) Δ t1) by (rewrite I12; exact Hp2).
    assert (Hp3 : head_propositional gc_deps gc_stack (ce_ass A) Δ t3) by (rewrite <- I23; exact Hp2).
    assert (Hp4 : head_propositional gc_deps gc_stack (ce_ass A) Δ t4) by (rewrite <- I34; exact Hp3).
    apply (mk_rel_sub (t1 ↦ ⋆ᵈ⟨M[φ]ʷ, ρ⟩ ⦂ centry_tag (ce_ass A) Δ t1) (t2 ↦ ⋆ᵈ⟨M, ⟪φ⟫ ρ⟩ ⦂ centry_tag (ce_ass A) Δ t2)
             (t3 ↦ ⋆ᵈ⟨M', ⟪φ⟫ ρ'⟩ ⦂ centry_tag (ce_ass A) Δ t3) (t4 ↦ ⋆ᵈ⟨M'[φ]ʷ, ρ'⟩ ⦂ centry_tag (ce_ass A) Δ t4));
      [ apply eval_sub_wk_extend_proof; eassumption
      | apply eval_sub_extend_proof; eassumption
      | apply eval_sub_extend_proof; eassumption
      | apply eval_sub_wk_extend_proof; eassumption
      | ].
    pose proof (proj1 (head_propositional_iff (e := ce_ass A) HΔk eq_refl HAs Ht12 Hc2) Hp1) as Ec2.
    pose proof (proj1 (head_propositional_iff (e := ce_ass A) HΔk eq_refl HAs Ht34 Hd3) Hp3) as Ed3.
    (** The kept proofs read back: their free bounds are inside the
        contexts the environments are related at. *)
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M[φ]ʷ HΓ'
                  (exp_scoped_free_bound _ _ (exp_scoped_wk _ _ _ _ HMs Hφb)) _ _ Hρ) as [Rd1 _].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M'[φ]ʷ HΓ'
                  (exp_scoped_free_bound _ _ (exp_scoped_wk _ _ _ _ HMs' Hφb)) _ _ Hρ) as [_ Rd4].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M HΓ (exp_scoped_free_bound _ _ HMs) _ _ (Hφ _ _ Hρ)) as [Rd2 _].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M' HΓ (exp_scoped_free_bound _ _ HMs') _ _ (Hφ _ _ Hρ)) as [_ Rd3].
    repeat
      match goal with
      | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
      | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
      end;
      (eapply per_env_extend_intro_tagged; [ exact HΔA | exact HΔk | | ]);
      first [ pairwise | eapply per_head_proof; eassumption ].
Qed.

(** ** Extension by a Precomposed Term

    The same shape as [rel_sub_under_ctx_extend], but the term judgment lives in
    [Δ] rather than [Γ], so it is the one instantiated more than once; the type
    judgment is only needed to build the context PER of [Δ ▹ T] (via
    [presup_rel_exp_under_ctx]).

    The two obvious instantiations, along [sb_wk σ φ] for the outer environments
    and along [σ] for the inner ones, are not enough: their chains live in
    different PERs and share no value ([⟦M⟧t1] against [⟦M⟧t2]).  A third
    instantiation bridges them: the reflexive-left hypothesis [Δ ⊨ M : T] at
    [Id ≈ Id] and at the environment pair [t1 ≈ t2] the tails provide.  After
    [exp_sub_id] its chain is [⟦M⟧t1] twice and [⟦M⟧t2] twice, which links the
    first instantiation to the second.  No extra instantiation of the type
    judgment is needed: each of the three term instantiations carries its own type
    chain, and those overlap the same way.

    So three chains are combined into the four-value chain of the goal, by two
    applications of [rel_chain_merge], which joins two chains along a shared
    value. *)

Lemma rel_sub_under_ctx_extend_sub : forall {Γ Δ σ σ' T M M'},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ M ≈ M' : T ->
    exp_scoped (List.length Δ) M -> exp_scoped (List.length Δ) M' ->
    Γ ⊨ˢ σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▹ T.
Proof.
  intros * Hσj HM HMs HMs'.
  pose proof Hσj as [env_relΓ HΓ env_relΔ HΔ Hσ Hσs].
  assert (HMσs : exp_scoped (List.length Γ) M[σ])
    by (eapply exp_scoped_sub; [ exact HMs | intros x Hx; exact (proj1 (Hσs x Hx)) ]).
  assert (HMσs' : exp_scoped (List.length Γ) M'[σ'])
    by (eapply exp_scoped_sub; [ exact HMs' | intros x Hx; exact (proj2 (Hσs x Hx)) ]).
  pose proof (presup_rel_exp_under_ctx HM) as [i HT].
  pose proof (per_ctx_env_of_typ HΔ HT) as HΔT.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMrefl.
  pose proof (rel_type_inversion_simple HT) as [env_relΔ4 [HΔ4 HTs]].
  destruct HM as [env_relΔ2 HΔ2 j HMgen].
  destruct HMrefl as [env_relΔ3 HΔ3 j' HMrgen].
  handle_per_ctx_env_irrel.
  assert (HΔk : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ) by eassumption.
  eexists_rel_sub; [| intros [| x] Hx; cbn; [ split; assumption | apply Hσs; cbn in Hx; lia ] ].
  intros Γ' env_rel' HΓ' φ Hφ Hφb ρ ρ' Hρ.
  (** Tails, and the inner pair among them, which is the environment pair the
      bridging instantiation runs at. *)
  destruct (Hσ _ _ HΓ' _ Hφ Hφb _ _ Hρ) as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htails].
  assert (Ht12 : Dom t1 ≈ t2 ∈ env_relΔ) by pairwise.
  assert (Ht23 : Dom t2 ≈ t3 ∈ env_relΔ) by pairwise.
  assert (Ht34 : Dom t3 ≈ t4 ∈ env_relΔ) by pairwise.
  (** The three instantiations: outer, inner, and the bridge. *)
  destruct (eval_sub_id_rel HΔk Ht12) as [Hid1 Hid2].
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk_rel Hσj HΓ' HΓ Hφ Hφb) _ _ _ _ Hρ Ht1 Ht4) as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓ _ _ Hσj _ _ _ _ (Hφ _ _ Hρ) Ht2 Ht3) as [R2 [Htyp2 Hexp2]].
  destruct (rel_exp_body_of_retagged HΔk HMrgen _ _ HΔk _ _ (rel_sub_id (ex_intro _ _ HΔk)) _ _ _ _ Ht12 Hid1 Hid2 Ht12)
    as [R3 [Htyp3 Hexp3]].
  (** Whether the head is a proposition is decided by [T]'s value at an
    inner tail, and the four tails agree on it. *)
  pose proof (head_propositional_pair (e := ce_ass T) HΔk eq_refl HTs Ht12) as I12.
  pose proof (head_propositional_pair (e := ce_ass T) HΔk eq_refl HTs Ht23) as I23.
  pose proof (head_propositional_pair (e := ce_ass T) HΔk eq_refl HTs Ht34) as I34.
  destruct (HTs _ _ Ht12) as (e1 & e2 & Ee1 & Ee2 & [R12 He12]).
  pose proof (per_univ_elem_relevance _ _ _ _ He12) as Er12.
  pose proof (head_propositional_iff (e := ce_ass T) HΔk eq_refl HTs Ht12 Ee1) as I1.
  destruct (domain_relevance e1) eqn:Er1.
  2:{
    (** A propositional head: the heads are proofs, which the head PER of
      [T] relates at every link. *)
    assert (Hp1 : head_propositional gc_deps gc_stack (ce_ass T) Δ t1) by (rewrite I1; reflexivity).
    assert (Hp2 : head_propositional gc_deps gc_stack (ce_ass T) Δ t2) by (rewrite <- I12; exact Hp1).
    assert (Hp3 : head_propositional gc_deps gc_stack (ce_ass T) Δ t3) by (rewrite <- I23; exact Hp2).
    assert (Hp4 : head_propositional gc_deps gc_stack (ce_ass T) Δ t4) by (rewrite <- I34; exact Hp3).
    apply (mk_rel_sub (t1 ↦ ⋆ᵈ⟨M[σ][φ]ʷ, ρ⟩ ⦂ centry_tag (ce_ass T) Δ t1) (t2 ↦ ⋆ᵈ⟨M[σ], ⟪φ⟫ ρ⟩ ⦂ centry_tag (ce_ass T) Δ t2)
             (t3 ↦ ⋆ᵈ⟨M'[σ'], ⟪φ⟫ ρ'⟩ ⦂ centry_tag (ce_ass T) Δ t3) (t4 ↦ ⋆ᵈ⟨M'[σ'][φ]ʷ, ρ'⟩ ⦂ centry_tag (ce_ass T) Δ t4));
      [ apply eval_sub_wk_extend_proof; eassumption
      | apply eval_sub_extend_proof; eassumption
      | apply eval_sub_extend_proof; eassumption
      | apply eval_sub_wk_extend_proof; eassumption
      | ].
    destruct (HTs _ _ Ht34) as (e3 & e4 & Ee3 & Ee4 & _).
    pose proof (proj1 (head_propositional_iff (e := ce_ass T) HΔk eq_refl HTs Ht23 Ee2) Hp2) as Ee2p.
    pose proof (proj1 (head_propositional_iff (e := ce_ass T) HΔk eq_refl HTs Ht34 Ee3) Hp3) as Ee3p.
    (** The kept proofs read back: their free bounds are inside the
        contexts the environments are related at. *)
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M[σ][φ]ʷ HΓ'
                  (exp_scoped_free_bound _ _ (exp_scoped_wk _ _ _ _ HMσs Hφb)) _ _ Hρ) as [Rd1 _].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M'[σ'][φ]ʷ HΓ'
                  (exp_scoped_free_bound _ _ (exp_scoped_wk _ _ _ _ HMσs' Hφb)) _ _ Hρ) as [_ Rd4].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M[σ] HΓ (exp_scoped_free_bound _ _ HMσs) _ _ (Hφ _ _ Hρ)) as [Rd2 _].
    pose proof (per_ctx_env_kept_proof_readable _ _ _ M'[σ'] HΓ (exp_scoped_free_bound _ _ HMσs') _ _ (Hφ _ _ Hρ)) as [_ Rd3].
    repeat
      match goal with
      | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
      | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
      end;
      (eapply per_env_extend_intro_tagged; [ exact HΔT | exact HΔk | | ]);
      first [ pairwise | eapply per_head_proof; eassumption ].
  }
  (** A relevant head: the three term instantiations give values. *)
  assert (Hn1 : ~ head_propositional gc_deps gc_stack (ce_ass T) Δ t1) by (rewrite I1; discriminate).
  assert (Hn2 : ~ head_propositional gc_deps gc_stack (ce_ass T) Δ t2) by (rewrite <- I12; exact Hn1).
  assert (Hn3 : ~ head_propositional gc_deps gc_stack (ce_ass T) Δ t3) by (rewrite <- I23; exact Hn2).
  assert (Hn4 : ~ head_propositional gc_deps gc_stack (ce_ass T) Δ t4) by (rewrite <- I34; exact Hn3).
  assert (Hrel1 : rel_typ_sort T t1 relevant) by (exists e1; split; assumption).
  assert (Hrel2 : rel_typ_sort T t2 relevant) by (exists e2; split; congruence).
  apply (rel_exp_or_prop_relevant Htyp1 Hrel1) in Hexp1.
  apply (rel_exp_or_prop_relevant Htyp2 Hrel2) in Hexp2.
  apply (rel_exp_or_prop_relevant Htyp3 Hrel1) in Hexp3.
  destruct Hexp1 as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hfchain].
  destruct Hexp2 as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  destruct Hexp3 as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  (** [M[σ][ι φ] = M[σ][φ]ʷ] on the outer pair and [M[Id] = M] on the bridge:
    both rewrites make the values the same, so that
    [functional_eval_rewrite_clear] can identify them below. *)
  rewrite <- exp_wk_sub in Hf1, Hf4.
  rewrite exp_sub_id in Hh1, Hh4.
  destruct Htyp1 as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct Htyp2 as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct Htyp3 as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  rewrite exp_sub_id in Hc1, Hc4.
  functional_eval_rewrite_clear.
  apply (mk_rel_sub (t1 ↦ f1 ⦂ centry_tag (ce_ass T) Δ t1) (t2 ↦ g1 ⦂ centry_tag (ce_ass T) Δ t2)
           (t3 ↦ g4 ⦂ centry_tag (ce_ass T) Δ t3) (t4 ↦ f4 ⦂ centry_tag (ce_ass T) Δ t4));
    [ apply eval_sub_wk_extend; eassumption
    | apply eval_sub_extend; eassumption
    | apply eval_sub_extend; eassumption
    | apply eval_sub_wk_extend; eassumption
    | ].
  (** The three type chains identify [R1], [R2] and [R3] with each other. *)
  destruct Hachain as [? [? ?]].
  destruct Hbchain as [? [? ?]].
  destruct Hcchain as [? [? ?]].
  handle_per_univ_elem_irrel.
  (** Then the three term chains become one.  Neither merge can be inferred: the
    shared value is [⟦M⟧t1] for the first and [⟦M⟧t2] for the second, and the
    intermediate list must mention both. *)
  assert (Hm1 : rel_chain R1 ([f1; f4; f2; g2])) by (merge_rel_chain Hfchain Hhchain f2).
  assert (Hm2 : rel_chain R1 ([f1; g1; g4; f4])) by (merge_rel_chain Hm1 Hgchain g2).
  clear Hfchain Hgchain Hhchain Hm1.
  solve_per_env_extend_chain_tagged.
Qed.

(** ** Double Extension by Precomposed Terms

    Two applications of [rel_sub_under_ctx_extend_sub]: the first builds
    [Γ ⊨ˢ σ,,M[σ] : Δ ▹ T], and the second uses it as its substitution.  The outer
    extension term is [N] precomposed with the substitution the first application
    produced, which is why the statement repeats [σ ,, M[σ]]. *)

(** ** Lifting is Semantic

    The lemma the case files use most.  [sb_wk_q] makes it a four-value pattern:
    it says [(q σ)[ψ]ʷ] is again an extension, by [σ] postcomposed with [↑ ⊙ ψ]
    and by the variable [ψ 0].

    Tails: [q σ] extends [σ[↑]ʷ], so all four tails are values of [σ[↑]ʷ], which is
    a semantic substitution [Γ ▹ A[σ] ⊨ˢ σ[↑]ʷ : Δ] by [rel_sub_under_ctx_wk]
    applied to the weakening [Γ ▹ A[σ] ⊨ʷ ↑ : Γ].  One instantiation of it
    produces all four tails and their chain; the merge this would otherwise need
    is done once, in the proof of [rel_sub_under_ctx_wk].

    Heads: all four heads are the same two values, [(⟪ψ⟫ ρ) 0] and [(⟪ψ⟫ ρ') 0],
    because [(#0)[ψ]ʷ] is [#(ψ 0)] and [#0] reads index [0].  The Ctx-Ext
    biconditional for [Γ ▹ A[σ]] gives them related in the head PER of [A[σ]] at
    the dropped environments, and this must be bridged to the head PER of [A] at
    the tails.  Three instantiations of the type judgment are needed:

    - along [σ ≈ σ] at the dropped pair, whose outer values are [A[σ]]'s: the
      source of the bridge, and also what the context PER of [Γ ▹ A[σ]] is built
      from;
    - along [σ[↑]ʷ] at [⟪ψ⟫ ρ ≈ ⟪ψ⟫ ρ'], whose inner values are [A]'s at the two
      inner tails: the target;
    - along [Id], linking the two.  [σ[↑]ʷ] and [σ] evaluate at different
      environments (postcomposition by a weakening does not commute with
      evaluation), so only a fresh instantiation at a related pair of
      environments connects them, as in [rel_sub_under_ctx_extend_sub]. *)

Lemma rel_sub_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat},
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Γ ▹ A[σ] ⊨ˢ q σ ≈ q σ' : Δ ▹ A.
Proof.
  intros * Hσj HA.
  pose proof Hσj as [env_relΓ HΓ env_relΔ HΔ Hσ Hσs].
  pose proof (rel_type_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  (** The simple form of the hypothesis, at [σ ≈ σ].  The first of the three type
    instantiations below runs at a pair of [σ]-evaluated environments, which this
    form supplies: two evaluations of [σ] at a related pair, rather than the four
    of a full four-value pattern. *)
  pose proof (rel_sub_under_ctx_simple (rel_sub_under_ctx_refl_left Hσj))
    as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 Hσrefl]]]].
  handle_per_ctx_env_irrel.
  rename HΓ2 into HΓ; rename HΔ2 into HΔ.
  (** The simple form of [A]'s judgment, at [Δ]'s PER. *)
  assert (HAs : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔ ->
                  exists a a', ⟦ A ⟧ ρ ↘ a /\ ⟦ A ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i).
  { pose proof (rel_type_inversion_simple HA) as [env_relΔ5 [HΔ5 HAs]].
    assert (E5 : env_relΔ <~> env_relΔ5) by (eapply per_ctx_env_right_irrel; eassumption).
    intros ρ ρ' Hρ%E5; exact (HAs _ _ Hρ). }
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  (** [Γ ▹ A[σ] ⊨ˢ σ[↑]ʷ : Δ] — the substitution [q σ] extends.  All four tails
      come from this one judgment. *)
  pose proof (rel_wk_shift HΓ HΓA) as Hshift.
  assert (Hshiftb : forall x, x < List.length Γ -> ↑ x < List.length (Γ ▹ A[σ])) by (intros x Hx; cbn; lia).
  pose proof (rel_sub_under_ctx_wk_rel Hσj HΓA HΓ Hshift Hshiftb) as Hσwkj.
  pose proof Hσwkj as [env_relΓA HΓA' env_relΔ3 HΔ3 Hσwk _].
  handle_per_ctx_env_irrel.
  eexists_rel_sub;
    [| intros x Hx; split; eapply sb_q_bound; first [ exact Hx | intros y Hy; exact (proj1 (Hσs y Hy))
                                                   | intros y Hy; exact (proj2 (Hσs y Hy)) ] ].
  intros Γ' env_rel' HΓ' ψ Hψ Hψb ρ ρ' Hρ.
  (** The Kripke stage lands in [Γ ▹ A[σ]], so the pair [ρ ≈ ρ'] splits into a
      tail pair and a head pair — the [per_env_extend] the context PER just
      built. *)
  destruct (Hψ _ _ Hρ) as [Htail Hhead Hle Hre Hrdl Hrdr].
  rewrite (eval_wk_app_entry ψ), (eval_wk_app ψ) in Hle, Hre.
  rewrite (eval_wk_app_entry ψ) in Hrdl, Hrdr.
  destruct (Hσwk _ _ HΓ' _ Hψ Hψb _ _ Hρ) as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  (** [σ] itself along [↑], which puts [⟦σ⟧((⟪ψ⟫ ρ)↯)] in the same PER as the
    tails: its leftmost value is again [⟦σ[↑]ʷ⟧(⟪ψ⟫ ρ)], so determinism of
    substitution evaluation (up to [env_eq], not [eq]) links the two chains. *)
  destruct (Hσ _ _ HΓA' _ Hshift Hshiftb _ _ (Hψ _ _ Hρ)) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  rewrite ?eval_wk_shift in *.
  assert (Hy12 : Dom y1 ≈ y2 ∈ env_relΔ).
  { assert (Hz : Dom z1 ≈ y2 ∈ env_relΔ) by pairwise.
    exact (per_ctx_env_resp_agree HΔ3 _ _ _ _ (functional_eval_sub _ _ _ _ _ Hz1 Hy1) (reflexivity _) Hz). }
  (** The three instantiations of the type judgment.  The first is the one the
    head hypothesis speaks about (its outer values are [A[σ]]'s at the dropped
    environments); it is taken at [Hy2] and at the [σ]-evaluation from the simple
    form, because those are the environments the other two instantiations
    reach. *)
  destruct (Hσrefl _ _ Htail) as [u [u' [Hu [Hu' Huu']]]].
  destruct (HAgen _ _ HΓ _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Htail Hy2 Hu')
    as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct (HAgen _ _ HΓA' _ _ Hσwkj _ _ _ _ (Hψ _ _ Hρ) Hy1 Hy4)
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct (eval_sub_id_rel HΔ3 Hy12) as [Hid1 Hid2].
  destruct (rel_type_body_of_retagged HΔ3 HAgen _ _ HΔ3 _ _ (rel_sub_id (ex_intro _ _ HΔ3)) _ _ _ _ Hy12 Hid1 Hid2 Hy12)
    as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  rewrite exp_sub_id in Hd1, Hd4.
  (** The heads are proofs when [A] is a proposition at the tails, which
    the [c]-chain carries to [A[σ]] at the dropped environments, where
    the environments of [Γ ▹ A[σ]] hold their proofs. *)
  assert (HPERΔ : PER env_relΔ) by (eapply per_env_PER; eassumption).
  assert (Hc12 : Dom c1 ≈ c2 ∈ per_univ i) by pairwise.
  assert (Hc14 : Dom c1 ≈ c4 ∈ per_univ i) by pairwise.
  destruct Hc12 as [? Hc12]; destruct Hc14 as [? Hc14].
  pose proof (per_univ_elem_relevance _ _ _ _ Hc12) as Ec12.
  pose proof (per_univ_elem_relevance _ _ _ _ Hc14) as Ec14.
  pose proof (head_propositional_iff_right (e := ce_ass A) HΔ3 eq_refl HAs Hy12 Hc2) as Iy2.
  (** Weak functionality names [A[σ]]'s element PER, so the [per_head] hypothesis
      is instantiated at it directly with no transport.  Both heads are the same
      two values on all four sides, so [rel_chain_4_of_2] is the whole head
      chain. *)
  functionalize_per_univ_chain Hcchain R.
  assert (Hh : Dom (⟪ψ⟫ ρ 0) ≈ (⟪ψ⟫ ρ' 0) ∈ R)
    by (apply (Hhead i R c1 c4); first [ eassumption | pairwise ]).
  assert (Hheads : rel_chain R ([ρ (ψ 0); ρ (ψ 0); ρ' (ψ 0); ρ' (ψ 0)]))
    by (apply rel_chain_4_of_2; [ solve_chain_PER | rewrite <- !(eval_wk_app ψ); exact Hh ]).
  (** The heads are retagged at [A] over the tails ([eval_sub_q]). *)
  apply (mk_rel_sub (retag_entry (centry_tag (ce_ass A) Δ x1) (centry_slot_unit (ce_ass A)) (env_entry ρ (ψ 0)) :: x1)
                    (retag_entry (centry_tag (ce_ass A) Δ y1) (centry_slot_unit (ce_ass A)) (env_entry ρ (ψ 0)) :: y1)
                    (retag_entry (centry_tag (ce_ass A) Δ y4) (centry_slot_unit (ce_ass A)) (env_entry ρ' (ψ 0)) :: y4)
                    (retag_entry (centry_tag (ce_ass A) Δ x4) (centry_slot_unit (ce_ass A)) (env_entry ρ' (ψ 0)) :: x4));
    [ apply eval_sub_wk_q; exact Hx1
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; exact Hy1
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; exact Hy4
    | apply eval_sub_wk_q; exact Hx4
    | ].
  (** [Hdchain] is the bridge: after [functional_eval_rewrite_clear] its values
      are [⟦A⟧y1] and [⟦A⟧y2], which are [b2] and [c2], so the [b]- and
      [c]-chains meet.  [Hcchain] is already at one PER; saturating irrelevance
      once here rather than inside [solve_per_head] keeps the last step cheap. *)
  (** At a tail where [A] is a proposition, the heads are term entries:
      [A[σ]] is one at the dropped environments, which the [c]-chain links
      to the tails. *)
  assert (Hlit_l : forall t, Dom t ≈ y2 ∈ env_relΔ -> rel_typ_propositional A t ->
                     exists ty, env_entry ρ (ψ 0) = de_term (ρ (ψ 0)) ty).
  { intros t Ht (a & Ea & Hp); apply Hle; exists c1; split; [ exact Hc1 |].
    destruct (HAs _ _ Ht) as (a1 & a2 & Ea1 & Ea2 & [R' HR']).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = c2) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_elem_relevance _ _ _ _ HR'); congruence. }
  assert (Hlit_r : forall t, Dom t ≈ y2 ∈ env_relΔ -> rel_typ_propositional A t ->
                     exists ty, env_entry ρ' (ψ 0) = de_term (ρ' (ψ 0)) ty).
  { intros t Ht (a & Ea & Hp); apply Hre; exists c4; split; [ exact Hc4 |].
    destruct (HAs _ _ Ht) as (a1 & a2 & Ea1 & Ea2 & [R' HR']).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = c2) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_elem_relevance _ _ _ _ HR'); congruence. }
  functional_eval_rewrite_clear.
  destruct Hcchain as [? [? ?]].
  destruct_per_univ_chain Hbchain.
  destruct_per_univ_chain Hdchain.
  handle_per_univ_elem_irrel.
  repeat
    match goal with
    | |- rel_chain _ ([_; _]) => apply rel_chain_of_pair
    | |- rel_chain _ (_ :: _ :: _) => apply rel_chain_cons
    end;
    (eapply per_env_extend_intro_retagged; [ exact HΔA | exact HΔ3 | | | | ]);
    first
      [ pairwise
      | rewrite !env_var_head_entry; solve_per_head
      | intros Hq;
        match goal with
        | Hq : rel_typ_propositional A ?t |- _ =>
            assert (Ht : Dom t ≈ y2 ∈ env_relΔ) by (first [ exact Hy12 | etransitivity; [| exact Hy12 ]; pairwise ])
        end;
        first
          [ destruct (Hlit_l _ Ht Hq) as [ty Hty]; exists (ρ (ψ 0)), ty; exact Hty
          | destruct (Hlit_r _ Ht Hq) as [ty Hty]; exists (ρ' (ψ 0)), ty; exact Hty ] ].
Qed.

(** ** Instantiating a Premise in an Extended Context

    [rel_sub_under_ctx_q] says [q σ] is a semantic substitution.  Rules with a
    premise in an extended context need something more concrete: the two
    environments [q σ] and [q σ'] evaluate to at a given pair, and how they relate
    to the pair the goal speaks of.

    A rule like Π-congruence compares [B[q σ]] at [ρ ↦ c] with [B] at
    [(⟦σ⟧ρ) ↦ c'], and [⟦q σ⟧(ρ ↦ c)] is not [(⟦σ⟧ρ) ↦ c]: its tail is
    [⟦σ[↑]ʷ⟧(ρ ↦ c)], and postcomposition by a weakening does not commute with
    evaluation (a closure captures an environment).  So the two are only related
    in the PER, and this lemma packages that.

    The returned chain covers all eight extensions of the four tails by either
    head.  A [rel_chain] states that its members are pairwise related, and callers
    need different pairs from it, including mixed ones such as [s ↦ c] against
    [ρσ ↦ c'], because the codomain obligation of [per_pi] is stated at a related
    pair of arguments. *)
Lemma rel_sub_under_ctx_q_at : forall {Γ Δ σ σ' A} {i : nat} {env_relΓ env_relΔA},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ env_relΔA ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      exists s s',
        ⟦ q σ : Δ ▹ A ⟧s ρ ↦ c ⦂ t1 ↘ s ↦ c ⦂ centry_tag (ce_ass A) Δ s /\
        ⟦ q σ' : Δ ▹ A ⟧s ρ' ↦ c' ⦂ t4 ↘ s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s' /\
        rel_chain env_relΔA
          ([s ↦ c ⦂ centry_tag (ce_ass A) Δ s; s ↦ c' ⦂ centry_tag (ce_ass A) Δ s; ρσ ↦ c ⦂ t2; ρσ ↦ c' ⦂ t2;
           ρ'σ' ↦ c ⦂ t3; ρ'σ' ↦ c' ⦂ t3; s' ↦ c ⦂ centry_tag (ce_ass A) Δ s'; s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s']).
Proof.
  intros * HΓ HΔA Hσj HA * Hpair Hts Hev Hev'.
  pose proof Hpair as [Hρ Hhead _ _ _ _].
  inversion Hts as [| ? ? [R1 R1'] Hts2]; subst; inversion Hts2 as [| ? ? [R2 R2'] Hts3]; subst;
    inversion Hts3 as [| ? ? [R3 R3'] Hts4]; subst; inversion Hts4 as [| ? ? [R4 R4'] _]; subst.
  pose proof Hσj as [env_relΓ2 HΓ2 env_relΔ HΔ Hσ _].
  pose proof (rel_type_inversion HA) as [env_relΔ2 [HΔ2 HAgen]].
  pose proof (rel_type_inversion_simple HA) as [env_relΔ3 [HΔ3 HAsimple]].
  pose proof (rel_sub_under_ctx_simple (rel_sub_under_ctx_refl_left Hσj))
    as [env_relΓ3 [HΓ3 [env_relΔ4 [HΔ4 Hσrefl]]]].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA'.
  handle_per_ctx_env_irrel.
  (** [handle_per_ctx_env_irrel] clears the hypotheses it identifies, so the
    judgment of [Γ] that remains is [HΓ3], the one the substitution's inversion
    left. *)
  pose proof (per_ctx_env_of_typ_sub HΓ3 Hσj HA) as HΓA.
  (** Tails: [σ] at the Kripke stage [↑] and at the given pair.  Its two inner
    values are the caller's [⟦σ⟧ρ] and [⟦σ'⟧ρ'] (up to [env_eq], which is all
    determinism of substitution evaluation gives), and its two outer ones are the
    tails of [⟦q σ⟧(ρ ↦ c)] and [⟦q σ'⟧(ρ' ↦ c')]. *)
  pose proof (rel_wk_shift HΓ3 HΓA) as Hshift.
  destruct (Hσ _ _ HΓA _ Hshift (fun x Hx => ltac:(cbn; lia)) _ _ Hpair) as [s u2 u3 s' Hs Hu2 Hu3 Hs' Hstails].
  rewrite ?eval_wk_shift in *.
  assert (Hag2 : env_agree_upto (List.length Δ) u2 ρσ) by (eapply functional_eval_sub; [ exact Hu2 | exact Hev ]).
  assert (Hag3 : env_agree_upto (List.length Δ) u3 ρ'σ') by (eapply functional_eval_sub; [ exact Hu3 | exact Hev' ]).
  assert (Htails : rel_chain env_relΔ ([s; ρσ; ρ'σ'; s'])).
  { match goal with HD : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ |- _ =>
      apply rel_chain_4;
        [ eapply (per_ctx_env_resp_agree HD); [ reflexivity | exact Hag2 | pairwise ]
        | eapply (per_ctx_env_resp_agree HD); [ exact Hag2 | exact Hag3 | pairwise ]
        | eapply (per_ctx_env_resp_agree HD); [ exact Hag3 | reflexivity | pairwise ] ] end. }
  (** Heads: the values of [A] at all four tails, so that irrelevance identifies
    every PER a head obligation quantifies over with the one the two heads are
    related in; and the values of [A[σ]] at [ρ] and [ρ'], which the head
    hypothesis speaks of and which link it to them. *)
  assert (H1 : Dom s ≈ ρσ ∈ env_relΔ) by pairwise.
  assert (H2 : Dom ρσ ≈ ρ'σ' ∈ env_relΔ) by pairwise.
  assert (H3 : Dom ρ'σ' ≈ s' ∈ env_relΔ) by pairwise.
  destruct (HAsimple _ _ H1) as [? [? [? [? [? ?]]]]].
  destruct (HAsimple _ _ H2) as [? [? [? [? [? ?]]]]].
  destruct (HAsimple _ _ H3) as [? [? [? [? [? ?]]]]].
  destruct (Hσrefl _ _ Hρ) as [w [w' [Hw [Hw' Hww']]]].
  destruct (HAgen _ _ HΓ3 _ _ (rel_sub_under_ctx_refl_left Hσj) _ _ _ _ Hρ Hev Hw')
    as [e1 e2 e3 e4 He1 He2 He3 He4 Hechain].
  (** The heads are proofs when [A] is a proposition at the tails, which
    the [e]-chain carries to [A[σ]] at [ρ] and [ρ'], where the
    environments of [Γ ▹ A[σ]] hold their proofs. *)
  assert (HΔk : EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ) by eassumption.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAsimple H1) as I1.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAsimple H2) as I2.
  pose proof (head_propositional_pair (e := ce_ass A) HΔk eq_refl HAsimple H3) as I3.
  pose proof (head_propositional_iff (e := ce_ass A) HΔk eq_refl HAsimple H2 He2) as Ie2.
  assert (Hr12 : Dom e1 ≈ e2 ∈ per_univ i) by pairwise.
  assert (Hr24 : Dom e2 ≈ e4 ∈ per_univ i) by pairwise.
  destruct Hr12 as [? Hr12]; destruct Hr24 as [? Hr24].
  pose proof (per_univ_elem_relevance _ _ _ _ Hr12) as Er12.
  pose proof (per_univ_elem_relevance _ _ _ _ Hr24) as Er24.
  functionalize_per_univ_chain Hechain R.
  assert (HPER : PER R) by solve_chain_PER.
  (** [per_head] is a [Definition], so [eapply] on it does not see a product; its
      four arguments are given explicitly instead. *)
  assert (Hcc' : Dom c ≈ c' ∈ R)
    by (apply (Hhead i R e1 e4); first [ eassumption | pairwise ]).
  (** Both heads on both sides, in either order: the eight extensions use every
      combination, so what the head obligations are read off is this. *)
  assert (Hheads : rel_chain R ([c; c'; c; c']))
    by (apply rel_chain_4; first [ eassumption | symmetry; eassumption ]).
  exists s, s'.
  (** Not [repeat split]: the third conjunct is itself a chain of conjunctions. *)
  split; [ exact (eval_sub_q (ce_ass A) _ _ _ _ Hs) | split; [ exact (eval_sub_q (ce_ass A) _ _ _ _ Hs') |]].
  functional_eval_rewrite_clear.
  destruct Hechain as [? [? ?]].
  handle_per_univ_elem_irrel.
  (** The heads [q σ] stores at [A] over the outer tails read back
      ([per_head_closure_readable]). *)
  assert (Hrd : forall t t' m m', Dom t ≈ t' ∈ env_relΔ -> Dom m ≈ m' ∈ per_head A A t t' ->
                  entry_readable (de_term m (centry_tag (ce_ass A) Δ t)))
    by (intros * Ht Hm; exact (proj1 (per_head_closure_readable HΔA' HΔk Ht Hm))).
  assert (Hr1 : entry_readable (de_term c (centry_tag (ce_ass A) Δ s))) by (apply (Hrd s ρσ c c'); [ pairwise | solve_per_head ]).
  assert (Hr2 : entry_readable (de_term c' (centry_tag (ce_ass A) Δ s))) by (apply (Hrd s ρσ c' c); [ pairwise | solve_per_head ]).
  assert (Hr3 : entry_readable (de_term c (centry_tag (ce_ass A) Δ s'))) by (apply (Hrd s' ρ'σ' c c'); [ pairwise | solve_per_head ]).
  assert (Hr4 : entry_readable (de_term c' (centry_tag (ce_ass A) Δ s'))) by (apply (Hrd s' ρ'σ' c' c); [ pairwise | solve_per_head ]).
  solve_per_env_extend_chain.
Qed.

(** The same for a type in an extended context, in the three-obligation form
    [per_univ_elem_pi_canonical] consumes: the two commutations of a Π-type's
    four-value pattern and the relatedness between them, each at a related pair of
    arguments.

    The proof instantiates the hypothesis once along [q σ ≈ q σ'], which reaches
    the values of [B[q σ]] and [B'[q σ']] the outer links need but at the wrong
    inner environments, and four times reflexively to bridge those to the right
    ones.  All five chains live in [per_univ j], so merging is [merge_rel_chain]
    and selecting is [pairwise]. *)
Lemma rel_exp_of_univ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B' j env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : universe_index_term j ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ⦂ t1 ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ⦂ t2 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ⦂ t2 ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ⦂ t3 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ⦂ t3 ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ t4 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j).
Proof.
  intros * HΓ Hσj HA HB * Hpair Hts Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_univ_inversion HB) as [env_relΔA [HΔA HBgen]].
  pose proof (rel_exp_of_univ_inversion_simple (rel_exp_under_ctx_refl_left HB))
    as [env_relΔA2 [HΔA2 HBl]].
  pose proof (rel_exp_of_univ_inversion_simple (rel_exp_under_ctx_refl_right HB))
    as [env_relΔA3 [HΔA3 HBr]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA3 Hσj HA _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  apply rel_chain_relevant_univ in Hbchain.
  (** The four bridges, at four pairs the chain above relates. *)
  assert (P1 : Dom s ↦ c ⦂ centry_tag (ce_ass A) Δ s ≈ ρσ ↦ c' ⦂ t2 ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ⦂ t2 ≈ s ↦ c ⦂ centry_tag (ce_ass A) Δ s ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s' ≈ ρ'σ' ↦ c' ⦂ t3 ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ⦂ t3 ≈ s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s' ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [Hx1 [Hx2 Hx]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [Hy1 [Hy2 Hy]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
  destruct (HBr _ _ P4) as [u1 [u2 [Hu1 [Hu2 Hu]]]].
  (** Each bridge shares one endpoint with the main chain.  It is named
    explicitly rather than by [functional_eval_rewrite_clear], because the merges
    below depend on which of two names that tactic keeps. *)
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (u2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Hu.
  (** Merging the five chains into one, along the two values the main
      instantiation contributes. *)
  assert (M1 : rel_chain (per_univ j) ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain (per_univ j) ([u1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Hu b3).
  repeat split.
  - exists b1, x2; repeat split; try eassumption.
    pairwise.
  - exists y1, z2; repeat split; try eassumption.
    pairwise.
  - exists u1, b4; repeat split; try eassumption.
    pairwise.
Qed.

Corollary rel_exp_of_typ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B'} {j : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ B ≈ B' : Typeω@j ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ⦂ t1 ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ⦂ t2 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ⦂ t2 ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ⦂ t3 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ⦂ t3 ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ⦂ t4 ↘ b' /\
          Dom b ≈ b' ∈ per_univ j).
Proof.
  intros * HΓ Hσj HA HB.
  exact (rel_exp_of_univ_under_ctx_q (j := ul j) HΓ Hσj HA HB).
Qed.

(** The same for a term in an extended context, which is the codomain
    obligation of [per_pi]: three applications, at three argument pairs, all in
    the one [per_head] the Π-value carries.

    This is harder than the type version in two ways.  The three obligations must
    hold in one relation, since [per_head] quantifies over the PER of a single pair
    of type values, [⟦B⟧(⟦σ⟧ρ ↦ c)] and [⟦B⟧(⟦σ'⟧ρ' ↦ c')]; at the universe the
    element PER is [per_univ j] itself, so nothing needs identifying.  And these
    two type values occur in none of the main instantiation's chains: it runs along
    [q σ ≈ q σ'], so its inner environments are [s ↦ c] and [s' ↦ c'].

    So the bridges carry types as well as terms, which is why they use the
    [rel_exp_under_ctx_simple] form, the [Id] instance that reports both.  The
    relations are identified along the type values they share, explicitly rather
    than by [handle_per_univ_elem_irrel], whose choice of representative is
    unpredictable.  Four bridges suffice, closing the graph
<<
mid —⟦B⟧(⟦σ⟧ρ ↦ c)— L1 —⟦B⟧(s ↦ c)— main —⟦B⟧(s' ↦ c')— R
                    |
                    L2
>>
    [L2] and [R] contribute the terms of the two commutation obligations, [mid]
    the relatedness obligation, and [L1] only the link that brings everything into
    the PER [mid] is stated at. *)
Lemma rel_exp_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {M M' B env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ˢ σ ≈ σ' : Δ ->
    Δ ⊨ᵗ A ≈ A at i ->
    Δ ▹ A ⊨ M ≈ M' : B ->
    (forall ρ ρ' R, EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R -> rel_typ_sort B ρ relevant) ->
    forall ρ ρ' ρσ ρ'σ' c c' t1 t2 t3 t4,
      Dom ρ ↦ c ⦂ t1 ≈ ρ' ↦ c' ⦂ t4 ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      args_readable_at c c' ([t1; t2; t3; t4]) ->
      ⟦ σ : Δ ⟧s ρ ↘ ρσ ->
      ⟦ σ' : Δ ⟧s ρ' ↘ ρ'σ' ->
      (exists m m',
          ⟦ M[q σ] ⟧ ρ ↦ c ⦂ t1 ↘ m /\ ⟦ M ⟧ ρσ ↦ c' ⦂ t2 ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c ⦂ t2) (ρ'σ' ↦ c' ⦂ t3)) /\
      (exists m m',
          ⟦ M ⟧ ρσ ↦ c ⦂ t2 ↘ m /\ ⟦ M' ⟧ ρ'σ' ↦ c' ⦂ t3 ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c ⦂ t2) (ρ'σ' ↦ c' ⦂ t3)) /\
      (exists m m',
          ⟦ M' ⟧ ρ'σ' ↦ c ⦂ t3 ↘ m /\ ⟦ M'[q σ'] ⟧ ρ' ↦ c' ⦂ t4 ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c ⦂ t2) (ρ'σ' ↦ c' ⦂ t3)).
Proof.
  intros * HΓ Hσj HA HM HBrel * Hpair Hts Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof HM as [env_relΔA HΔA k HMgen].
  pose proof (rel_exp_under_ctx_simple HM) as [env_relΔA2 [HΔA2 [k1 HMmid]]].
  pose proof (rel_exp_under_ctx_simple (rel_exp_under_ctx_refl_left HM))
    as [env_relΔA3 [HΔA3 [k2 HMl]]].
  pose proof (rel_exp_under_ctx_simple (rel_exp_under_ctx_refl_right HM))
    as [env_relΔA4 [HΔA4 [k3 HMr]]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA4 Hσj HA _ _ _ _ _ _ _ _ _ _ Hpair Hts Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  (** The main instantiation, along [q σ ≈ q σ']: its two outer values are the
      goal's, on both the type and the term side. *)
  destruct (HMgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq') as [Rm [Htyp Hexp]].
  (** The four pairs the bridges are taken at, all related by the eight-value
      chain of [rel_sub_under_ctx_q], and the main one. *)
  assert (Pq : Dom s ↦ c ⦂ centry_tag (ce_ass A) Δ s ≈ s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s' ∈ env_relΔA) by pairwise.
  assert (Pm : Dom ρσ ↦ c ⦂ t2 ≈ ρ'σ' ↦ c' ⦂ t3 ∈ env_relΔA) by pairwise.
  assert (P1 : Dom s ↦ c ⦂ centry_tag (ce_ass A) Δ s ≈ ρσ ↦ c ⦂ t2 ∈ env_relΔA) by pairwise.
  assert (P2 : Dom s ↦ c ⦂ centry_tag (ce_ass A) Δ s ≈ ρσ ↦ c' ⦂ t2 ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ⦂ centry_tag (ce_ass A) Δ s' ≈ ρ'σ' ↦ c ⦂ t3 ∈ env_relΔA) by pairwise.
  (** [B] is relevant at all of them, so every judgment reports values. *)
  assert (HΔAk : EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ env_relΔA) by eassumption.
  apply (rel_exp_or_prop_relevant Htyp (HBrel _ _ _ HΔAk Pq)) in Hexp.
  destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct Hexp as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hfchain].
  destruct (HMmid _ _ Pm) as [dL [dR [Rmid [HdL [HdR [Emid [Hpm | [g1 [g2 [Hg1 [Hg2 Hgrel]]]]]]]]]]];
    [ exfalso; destruct (HBrel _ _ _ HΔAk Pm) as (? & ? & ?); functional_eval_rewrite_clear; congruence |].
  destruct (HMl _ _ P1) as [x1 [x2 [Rx [Hx1 [Hx2 [Ex [Hpx | [u1 [u2 [Hu1 [Hu2 Hurel]]]]]]]]]]];
    [ exfalso; destruct (HBrel _ _ _ HΔAk P1) as (? & ? & ?); functional_eval_rewrite_clear; congruence |].
  destruct (HMl _ _ P2) as [y1 [y2 [Ry [Hy1 [Hy2 [Ey [Hpy | [v1 [v2 [Hv1 [Hv2 Hvrel]]]]]]]]]]];
    [ exfalso; destruct (HBrel _ _ _ HΔAk P2) as (? & ? & ?); functional_eval_rewrite_clear; congruence |].
  destruct (HMr _ _ P3) as [z1 [z2 [Rz [Hz1 [Hz2 [Ez [Hpz | [w1 [w2 [Hw1 [Hw2 Hwrel]]]]]]]]]]];
    [ exfalso; destruct (HBrel _ _ _ HΔAk P3) as (? & ? & ?); functional_eval_rewrite_clear; congruence |].
  (** The values each bridge shares with the main chain or with the next bridge,
    named explicitly, since the merges depend on which of two names
    [functional_eval_rewrite_clear] keeps. *)
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (x2 = dL) by (eapply functional_eval_exp; eassumption).
  assert (y1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (u1 = f2) by (eapply functional_eval_exp; eassumption).
  assert (u2 = g1) by (eapply functional_eval_exp; eassumption).
  assert (v1 = f2) by (eapply functional_eval_exp; eassumption).
  assert (w1 = f3) by (eapply functional_eval_exp; eassumption).
  subst.
  (** One irrelevance per edge of the graph above, each at the type value the two
      endpoints share. *)
  assert (Hb23 : DF b2 ≈ b3 ∈ per_univ_elem k ↘ Rm) by pairwise.
  assert (HRx : Rm <~> Rx) by (eapply per_univ_elem_right_irrel; [ exact Hb23 | exact Ex ]).
  assert (HRm : Rm <~> Rmid)
    by (etransitivity;
        [ exact HRx
        | eapply per_univ_elem_right_irrel; [ apply per_univ_sym; exact Ex | exact Emid ]]).
  (** The PER the three obligations must be met in, transported to [Rm]. *)
  assert (Ehead : DF dL ≈ dR ∈ per_univ_elem k1 ↘ Rm)
    by (eapply per_univ_elem_resp_iff; [ exact Emid | symmetry; exact HRm ]).
  (** The four bridging term pairs, transported likewise and merged into the main
      term chain. *)
  apply rel_chain_of_pair in Hurel, Hvrel, Hwrel, Hgrel.
  rewrite <- HRx in Hurel.
  retype_rel_chain Hbchain Ey Hvrel.
  retype_rel_chain Hbchain Ez Hwrel.
  rewrite <- HRm in Hgrel.
  assert (C1 : rel_chain Rm ([f1; f2; f3; f4; g1])) by (merge_rel_chain Hfchain Hurel f2).
  assert (C2 : rel_chain Rm ([f1; f2; f3; f4; g1; v2])) by (merge_rel_chain C1 Hvrel f2).
  assert (C3 : rel_chain Rm ([f1; f2; f3; f4; g1; v2; g2])) by (merge_rel_chain C2 Hgrel g1).
  assert (C4 : rel_chain Rm ([f1; f2; f3; f4; g1; v2; g2; w2])) by (merge_rel_chain C3 Hwrel f3).
  repeat split.
  - exists f1, v2; repeat split; try eassumption.
    eapply per_head_of; [ exact HdL | exact HdR | exact Ehead |].
    pairwise.
  - exists g1, g2; repeat split; try eassumption.
    eapply per_head_of; [ exact HdL | exact HdR | exact Ehead |].
    pairwise.
  - exists w2, f4; repeat split; try eassumption.
    eapply per_head_of; [ exact HdL | exact HdR | exact Ehead |].
    pairwise.
Qed.

(** ** The Type Judgment of an Instantiation

    The counterpart of [rel_typ_of_pi] for the other shape a type takes in an
    elimination rule: [B[Id ,, N]], the codomain of a Π at the applied argument, or
    the motive of a [ℕ]-eliminator at the scrutinee.  Every such rule needs the
    same four values and element PER, so they are computed once here.

    The value of [B[Id ,, N]] at [ρ] is not [⟦B⟧(ρ ↦ ⟦N⟧ρ)]: the two differ as
    soon as [B] builds a closure, which captures the environment it is evaluated
    in, and [B = λ C #1] already separates them.  So the four values are reached
    through two instantiations of the codomain judgment:

    - along [σ ,, N[σ] ≈ σ' ,, N[σ']], whose outer values are the goal's outer
      ones, since [B[Id ,, N][σ] = B[σ ,, N[σ]]] ([exp_sub_extend_sub]);
    - along [Id ,, N ≈ Id ,, N] at the substituted pair of environments, whose
      outer values are the goal's inner ones.

    The two share no value, so a third instance bridges them: the codomain at the
    pair of arguments crossing from one to the other.  Two merges give the chain
    from which the goal's four values are selected; this is the three-chain shape
    of [rel_sub_under_ctx_extend_sub], for the same reason.

    The element PER is the head PER of [B] at the arguments the type names,
    [⟦N⟧(⟦σ⟧ρ)] and [⟦N⟧(⟦σ'⟧ρ')].  A consumer's chains arrive in the head PER of
    the arguments they were read at, and [per_head_of_args] moves them.  For that
    it needs the codomain at an arbitrary related pair, which is therefore
    reported too, as are [N]'s four values and their domain PER, from which every
    consumer draws its argument pairs. *)
Lemma rel_typ_of_instance : forall {Γ A} {i k : nat} {B N},
    Γ ⊨ᵗ A ≈ A at k ->
    rel_type_relevant Γ A ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    exp_scoped (List.length Γ) N ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨ˢ σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
        ⟦ σ' : Γ ⟧s ρ' ↘ ρ'σ' ->
        exists j RN a1 a2 a3 a4 n1 n2 n3 n4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A ⟧ ρ'σ' ↘ a3 /\
          ⟦ A[σ'] ⟧ ρ' ↘ a4 /\
          DF a1 ≈ a4 ∈ per_univ_elem j ↘ RN /\
          DF a2 ≈ a3 ∈ per_univ_elem j ↘ RN /\
          ⟦ N[σ] ⟧ ρ ↘ n1 /\
          ⟦ N ⟧ ρσ ↘ n2 /\
          ⟦ N ⟧ ρ'σ' ↘ n3 /\
          ⟦ N[σ'] ⟧ ρ' ↘ n4 /\
          rel_chain RN ([n1; n2; n3; n4]) /\
          (forall w z,
              Dom w ≈ z ∈ RN ->
              exists b b',
                ⟦ B ⟧ ρσ ↦ w ⦂ centry_tag (ce_ass A) Γ ρσ ↘ b /\ ⟦ B ⟧ ρ'σ' ↦ z ⦂ centry_tag (ce_ass A) Γ ρ'σ' ↘ b' /\
                  Dom b ≈ b' ∈ per_univ i) /\
          rel_typ i B[Id,,N] σ ρ ρσ B[Id,,N] σ' ρ' ρ'σ'
            (per_head B B (ρσ ↦ n2 ⦂ centry_tag (ce_ass A) Γ ρσ) (ρ'σ' ↦ n3 ⦂ centry_tag (ce_ass A) Γ ρ'σ')).
Proof.
  intros * HA HArel' HB HN HNs * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_type_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The argument, and the two pairs of values of its type: the outer one is what
      an extended context PER is built at, the inner one what the codomain is read
      at. *)
  pose proof HN as [? ? j HNgen].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  (** [A] is a relevant type, so the argument has values and the
    extended environments are literal extensions by them. *)
  pose proof (HArel' _ HΓ) as HArel.
  apply (rel_exp_or_prop_relevant HNtyp (HArel _ _ Hρσ)) in HNexp.
  destruct (head_not_propositional_of_relevant (e := ce_ass A) HΓ eq_refl HA HArel' _ _ Hρσ) as [Hnp2 Hnp3].
  destruct (eval_sub_id_rel HΓ Hρσ) as [Hid2 Hid3].
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  assert (Houter : DF a1 ≈ a4 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Hmid : DF a2 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA0.
  (** The codomain at an arbitrary related pair of arguments. *)
  assert (Hcod : forall w z,
             Dom w ≈ z ∈ RN ->
             exists b b',
               ⟦ B ⟧ ρσ ↦ w ⦂ centry_tag (ce_ass A) Γ ρσ ↘ b /\ ⟦ B ⟧ ρ'σ' ↦ z ⦂ centry_tag (ce_ass A) Γ ρ'σ' ↘ b' /\
                 Dom b ≈ b' ∈ per_univ i).
  { intros w z Hwz.
    eapply (rel_exp_of_typ_extend_simple HΓ HA HB).
    apply (per_env_extend_intro_tagged HΓA0 HΓ Hρσ).
    eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Hmid | exact Hwz ]. }
  (** The two instantiations, their outer values rewritten into the goal's
      spelling. *)
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN HNs HNs) _ _ _ _ Hρ
                  ltac:(apply eval_sub_extend; eassumption)
                  ltac:(apply eval_sub_extend; eassumption))
    as [t1 tA2 tA3 t4 Ht1 HtA2 HtA3 Ht4 HtAchain].
  apply rel_chain_relevant_univ in HtAchain.
  rewrite <- exp_sub_extend_sub in Ht1, Ht4.
  (** The second along [Id,,N], whose results are the extensions of the
      retagged environments; read at the extensions of the environments
      themselves ([rel_type_body_of_retagged]). *)
  destruct (head_not_propositional_of_relevant (e := ce_ass A) HΓ eq_refl HA HArel' _ _ (per_ctx_env_retag HΓ _ _ Hρσ))
    as [Hnp2r Hnp3r].
  assert (EA : env_relΓA <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hext : Dom ρσ ↦ n2 ⦂ centry_tag (ce_ass A) Γ ρσ ≈ ρ'σ' ↦ n3 ⦂ centry_tag (ce_ass A) Γ ρ'σ' ∈ env_relΓA).
  { apply EA; apply (per_env_extend_intro_tagged HΓA0 HΓ Hρσ).
    eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Hmid | pairwise ]. }
  destruct (rel_type_body_of_retagged HΓA HBgen _ _ HΓ _ _ HidN ρσ ρ'σ'
              (ρσ ↦ n2 ⦂ centry_tag (ce_ass A) Γ ρσ) (ρ'σ' ↦ n3 ⦂ centry_tag (ce_ass A) Γ ρ'σ') Hρσ
              (eval_sub_extend _ _ _ _ _ _ _ Hid2 Hnp2r Hn2) (eval_sub_extend _ _ _ _ _ _ _ Hid3 Hnp3r Hn3) Hext)
    as [t2 tB2 tB3 t3 Ht2 HtB2 HtB3 Ht3 HtBchain].
  apply rel_chain_relevant_univ in HtBchain.
  (** The bridge, at the pair of arguments that crosses from the one
      instantiation to the other. *)
  assert (Hn1n3 : Dom n1 ≈ n3 ∈ RN) by pairwise.
  destruct (Hcod _ _ Hn1n3) as [d1 [d2 [Hd1 [Hd2 Hd]]]].
  assert (Hd1e : d1 = tA2) by (eapply functional_eval_exp; [ exact Hd1 | exact HtA2 ]).
  assert (Hd2e : d2 = tB3) by (eapply functional_eval_exp; [ exact Hd2 | exact HtB3 ]).
  subst d1 d2.
  assert (Hbridge : rel_chain (per_univ i) ([tA2; tB3]))
    by (apply rel_chain_of_pair; exact Hd).
  assert (Hchain1 : rel_chain (per_univ i) ([t1; tA2; tB3; t4]))
    by (merge_rel_chain HtAchain Hbridge tA2).
  assert (Hall : rel_chain (per_univ i) ([t1; t2; tB2; tB3; t3; t4]))
    by (merge_rel_chain Hchain1 HtBchain tB3).
  (** Anchored at the canonical head PER, which is the element PER of the
      judgment. *)
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  destruct (per_head_anchor Hcod n2 n3 n2 n3 Hn23 Hn23 Hn23)
    as [e1 [e2 [He1 [He2 Hanchor]]]].
  assert (He1e : e1 = tB2) by (eapply functional_eval_exp; [ exact He1 | exact HtB2 ]).
  assert (He2e : e2 = tB3) by (eapply functional_eval_exp; [ exact He2 | exact HtB3 ]).
  subst e1 e2.
  assert (HallR : rel_chain (per_univ_elem i
                               (per_head B B (ρσ ↦ n2 ⦂ centry_tag (ce_ass A) Γ ρσ) (ρ'σ' ↦ n3 ⦂ centry_tag (ce_ass A) Γ ρ'σ')))
                    ([t1; t2; tB2; tB3; t3; t4]))
    by (eapply per_univ_chain_at_in; [ exact Hall | | | exact Hanchor ]; solve_in).
  exists j, RN, a1, a2, a3, a4, n1, n2, n3, n4.
  do 12 (split; [ eassumption |]).
  apply (mk_rel_exp t1 t2 t3 t4); try eassumption.
  solve_rel_chain.
Qed.

(** ** The Diagonal of the Above

    What the gluing model needs of an instantiated type.  There is only one
    environment there, so the four values collapse to two, [⟦B[Id ,, N]⟧ρ] and
    [⟦B⟧(ρ ↦ ⟦N⟧ρ)], which are not equal but are related: they form the first
    link of the chain above.  Relatedness suffices because
    [glu_univ_elem_resp_per_univ] transports a gluing predicate along
    [per_univ]. *)
Lemma per_univ_of_instance : forall {Γ A} {i j : nat} {B N env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨ A ≈ A : Typeω@j ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    exp_scoped (List.length Γ) N ->
    forall ρ n,
      Dom ρ ≈ ρ ∈ env_relΓ ->
      ⟦ N ⟧ ρ ↘ n ->
      exists a b,
        ⟦ B[Id,,N] ⟧ ρ ↘ a /\ ⟦ B ⟧ ρ ↦ n ⦂ centry_tag (ce_ass A) Γ ρ ↘ b /\
          Dom a ≈ a ∈ per_univ i /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HΓ HA HB HN HNs * Hρ Hn.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN HNs HNs) as HidN.
  rewrite exp_sub_id in HidN.
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  (** [Id,,N] evaluates to the extension of the retagged environment; the
      instance is read at the extension of [ρ] itself
      ([rel_type_body_of_retagged]). *)
  destruct (head_not_propositional_of_typ (e := ce_ass A) HΓ eq_refl HA _ _ (per_ctx_env_retag HΓ _ _ Hρ)) as [Hnp _].
  destruct (eval_sub_id_rel HΓ Hρ) as [Hid _].
  destruct (rel_exp_under_ctx_simple_at_rel HΓ HA HN _ _ Hρ) as (m & m' & Hm & Hm' & Hmm).
  assert (m = n) as -> by (eapply functional_eval_exp; eassumption).
  assert (m' = n) as -> by (eapply functional_eval_exp; eassumption).
  pose proof (per_ctx_env_of_typ HΓ (rel_type_of_typ HA)) as HΓA0.
  assert (EA : env_relΓA <~> per_env_extend A A env_relΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hext : Dom ρ ↦ n ⦂ centry_tag (ce_ass A) Γ ρ ≈ ρ ↦ n ⦂ centry_tag (ce_ass A) Γ ρ ∈ env_relΓA)
    by (apply EA; exact (per_env_extend_intro_tagged HΓA0 HΓ Hρ Hmm)).
  destruct (rel_type_body_of_retagged HΓA HBgen _ _ HΓ _ _ HidN ρ ρ
              (ρ ↦ n ⦂ centry_tag (ce_ass A) Γ ρ) (ρ ↦ n ⦂ centry_tag (ce_ass A) Γ ρ) Hρ
              (eval_sub_extend _ _ _ _ _ _ _ Hid Hnp Hn) (eval_sub_extend _ _ _ _ _ _ _ Hid Hnp Hn) Hext)
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  apply rel_chain_relevant_univ in Hchain.
  destruct Hchain as [Ht12 _].
  exists t1, t2.
  do 2 (split; [ eassumption |]).
  split; [| eassumption ].
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

End Fixed_GCtx.

