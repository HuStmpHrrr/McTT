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

Lemma per_ctx_env_of_typ : forall {Δ A} {i : nat} {env_relΔ},
    EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    EF Δ ▹ A ≈ Δ ▹ A ∈ per_ctx_env ↘ (per_env_extend A A env_relΔ).
Proof.
  intros * HΔ H.
  pose proof (rel_exp_of_typ_inversion_simple H) as [env_relΔ' [HΔ' HA]].
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    EF Γ ▹ A[σ] ≈ Γ ▹ A[σ] ∈ per_ctx_env ↘ (per_env_extend A[σ] A[σ] env_relΓ).
Proof.
  intros * HΓ Hσj HA.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    forall ρ ρ' j a b R c c',
      Dom ρ ≈ ρ' ∈ env_relΓ ->
      ⟦ A[σ] ⟧ ρ ↘ a ->
      DF a ≈ b ∈ per_univ_elem j ↘ R ->
      Dom c ≈ c' ∈ R ->
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ.
Proof.
  intros * HΓ Hσj HA * Hρ Ha HR Hc.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
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
  apply per_env_extend_intro'; [ eassumption |].
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
    Γ ⊨ A ≈ A : Typeω@i ->
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
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A ⊨ M ≈ M' : B ->
    forall ρ ρ',
      Dom ρ ≈ ρ' ∈ per_env_extend A A env_relΓ ->
      exists m m',
        ⟦ M ⟧ ρ ↘ m /\ ⟦ M' ⟧ ρ' ↘ m' /\
          Dom m ≈ m' ∈ per_head B B ρ ρ'.
Proof.
  intros * HΓ HA HM * Hρ.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_exp_under_ctx_simple HM) as [env_relΓA [HΓA2 [j HMl]]].
  handle_per_ctx_env_irrel.
  destruct (HMl _ _ Hρ) as [b [b' [R [Hb [Hb' [HR [m [m' [Hm [Hm' Hmm']]]]]]]]]].
  exists m, m'.
  do 2 (split; [ eassumption |]).
  eapply per_head_of; eassumption.
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
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ M ≈ M' : B ->
    forall ρ ρ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A A env_relΓ ->
      exists j R b1 b2 b3 b4 w1 w2 w3 w4,
        ⟦ B[↑]ʷ ⟧ ρ ↦ c ↘ b1 /\
        ⟦ B ⟧ ρ ↘ b2 /\
        ⟦ B ⟧ ρ' ↘ b3 /\
        ⟦ B[↑]ʷ ⟧ ρ' ↦ c' ↘ b4 /\
        DF b1 ≈ b4 ∈ per_univ_elem j ↘ R /\
        DF b2 ≈ b3 ∈ per_univ_elem j ↘ R /\
        ⟦ M[↑]ʷ ⟧ ρ ↦ c ↘ w1 /\
        ⟦ M ⟧ ρ ↘ w2 /\
        ⟦ M' ⟧ ρ' ↘ w3 /\
        ⟦ M'[↑]ʷ ⟧ ρ' ↦ c' ↘ w4 /\
        rel_chain R ([w1; w2; w3; w4]).
Proof.
  intros * HΓ HA HM * Hρ.
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_intro HΓA HΓ (rel_wk_shift HΓ HΓA)))
    as HWk.
  destruct HM as [env_relΓ2 [HΓ2 [j HMgen]]].
  (** [(ρ ↦ c)↯] is [ρ] up to conversion, so the two substituted environments
    that [rel_exp_under_ctx] asks to be named are the tails themselves.  This makes
    the inner pair of both chains a statement about [ρ] and [ρ'] rather than about
    environments reached through [σ]. *)
  destruct (HMgen _ _ HΓA _ _ HWk _ _ _ _ Hρ
                  (eval_sub_shift (ρ ↦ c)) (eval_sub_shift (ρ' ↦ c')))
    as [R [Htyp Hexp]].
  destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct Hexp as [w1 w2 w3 w4 Hw1 Hw2 Hw3 Hw4 Hwchain].
  rewrite exp_sub_of_shift in Hb1, Hb4, Hw1, Hw4.
  exists j, R, b1, b2, b3, b4, w1, w2, w3, w4.
  do 4 (split; [ eassumption |]).
  split; [ pairwise |].
  split; [ pairwise |].
  do 4 (split; [ eassumption |]).
  eassumption.
Qed.

(** ** [q] Preserves Semantic Weakening

    The only lemma here about weakenings, and a cheap one: both halves of the
    extended context PER hold by conversion for [q ψ] ([eval_wk_q_tail],
    [eval_wk_q_zero]), so the tail obligation is the hypothesis and the head
    obligation is one bridging step. *)

Lemma rel_wk_under_ctx_q : forall {Γ ψ Δ A} {i : nat},
    Γ ⊨w ψ : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A[ψ]ʷ ⊨w (wk_q ψ) : Δ ▹ A.
Proof.
  intros * Hψj HA.
  pose proof Hψj as [env_relΓ [HΓ [env_relΔ [HΔ Hψ]]]].
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  handle_per_ctx_env_irrel.
  (** The commutation obligation of [A] along [ι ψ].  It is used twice, to build
    the context PER of [Γ ▹ A[ψ]ʷ] and to bridge the head PERs, so it is named, at
    an environment pair the caller supplies. *)
  assert (Hcom : forall ρ ρ',
             Dom ρ ≈ ρ' ∈ env_relΓ ->
             rel_exp A (ι ψ) ρ ⟪ψ⟫ ρ
                     A (ι ψ) ρ' ⟪ψ⟫ ρ' (per_univ i))
    by (intros ρ ρ' Hρ;
        exact (HAgen _ _ HΓ _ _ (rel_sub_of_wk Hψj) _ _ _ _ Hρ
                     (eval_sub_of_wk _ _) (eval_sub_of_wk _ _))).
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
  (** Both projections of [⟪q ψ⟫ ρ] are conversions, so nothing is rewritten
    below: [exact] sees through [⟪q ψ⟫ ρ] to [⟪ψ⟫ (ρ ↯)] and to [ρ 0]. *)
  split; [ typeclasses eauto |].
  intros ρ ρ' [Htail Hhead].
  apply per_env_extend_intro; rewrite ?eval_wk_q_zero; rewrite ?eval_wk_q_tail by typeclasses eauto.
  - exact (Hψ _ _ Htail).
  - destruct (Hcom _ _ Htail) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hchain].
    rewrite exp_sub_of_wk in Ha1, Ha4.
    functionalize_per_univ_chain Hchain R.
    eapply per_head_bridge;
      [ exact Hhead | exact Ha1 | exact Ha4 | pairwise | exact Ha2 | exact Ha3
      | pairwise_univ ].
Qed.

(** ** Extension is Semantic

    The first of three extension lemmas, and the template for the other two.  At
    every Kripke stage [Γ' ⊨w φ : Γ] it produces four environments and the chain
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Γ ⊨ M ≈ M' : A[σ] ->
    Γ ⊨s σ,,M ≈ σ',,M' : Δ ▹ A.
Proof.
  intros * Hσj HA HM.
  pose proof Hσj as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  destruct HM as [env_relΓ2 [HΓ2 [j HMgen]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  pose proof (rel_wk_under_ctx_intro HΓ' HΓ Hφ) as Hφj.
  (** Tails, and the heads that go with them. *)
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htails].
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_of_wk Hφj) _ _ _ _ Hρ
                  (eval_sub_of_wk _ _) (eval_sub_of_wk _ _)) as [Rt [Htyp Hexp]].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hheads].
  rewrite exp_sub_of_wk in Hm1, Hm4.
  apply (mk_rel_sub (t1 ↦ m1) (t2 ↦ m2) (t3 ↦ m3) (t4 ↦ m4));
    [ apply eval_sub_wk_extend; eassumption
    | apply eval_sub_extend; eassumption
    | apply eval_sub_extend; eassumption
    | apply eval_sub_wk_extend; eassumption
    | ].
  (** The two instantiations of [HA] that link [A]'s four values, and the term
    judgment's type chain, which links them to [Rt].  Rewriting the outer types
    with [A[σ][ι φ] = A[sb_wk σ φ]] makes the first instantiation's values the
    same values, not merely equal ones. *)
  pose proof (HAgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk Hσj Hφj) _ _ _ _ Hρ Ht1 Ht4) as Houter.
  pose proof (HAgen _ _ HΓ _ _ Hσj _ _ _ _ (Hφ _ _ Hρ) Ht2 Ht3) as Hinner.
  destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  rewrite exp_sub_of_wk, exp_wk_sub in Hb1, Hb4.
  destruct Houter as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct Hinner as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  functional_eval_rewrite_clear.
  destruct Hbchain as [? [? ?]].
  destruct_per_univ_chain Hcchain.
  destruct_per_univ_chain Hdchain.
  solve_per_env_extend_chain.
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ M ≈ M' : T ->
    Γ ⊨s σ,,M[σ] ≈ σ',,M'[σ'] : Δ ▹ T.
Proof.
  intros * Hσj HM.
  pose proof Hσj as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  pose proof (presup_rel_exp_under_ctx HM) as [i HT].
  pose proof (per_ctx_env_of_typ HΔ HT) as HΔT.
  pose proof (rel_exp_under_ctx_refl_left HM) as HMrefl.
  destruct HM as [env_relΔ2 [HΔ2 [j HMgen]]].
  destruct HMrefl as [env_relΔ3 [HΔ3 [j' HMrgen]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  pose proof (rel_wk_under_ctx_intro HΓ' HΓ Hφ) as Hφj.
  (** Tails, and the inner pair among them, which is the environment pair the
      bridging instantiation runs at. *)
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Htails].
  assert (Ht12 : Dom t1 ≈ t2 ∈ env_relΔ) by pairwise.
  (** The three instantiations: outer, inner, and the bridge. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_wk Hσj Hφj) _ _ _ _ Hρ Ht1 Ht4) as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓ _ _ Hσj _ _ _ _ (Hφ _ _ Hρ) Ht2 Ht3) as [R2 [Htyp2 Hexp2]].
  destruct (HMrgen _ _ HΔ3 _ _ (rel_sub_id (ex_intro _ _ HΔ3)) _ _ _ _ Ht12
                   (eval_sub_id _) (eval_sub_id _)) as [R3 [Htyp3 Hexp3]].
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
  apply (mk_rel_sub (t1 ↦ f1) (t2 ↦ g1) (t3 ↦ g4) (t4 ↦ f4));
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
  solve_per_env_extend_chain.
Qed.

(** ** Double Extension by Precomposed Terms

    Two applications of [rel_sub_under_ctx_extend_sub]: the first builds
    [Γ ⊨s σ,,M[σ] : Δ ▹ T], and the second uses it as its substitution.  The outer
    extension term is [N] precomposed with the substitution the first application
    produced, which is why the statement repeats [σ ,, M[σ]]. *)

Corollary rel_sub_under_ctx_extend_sub_double : forall {Γ Δ σ σ' T M M' A N N'},
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ M ≈ M' : T ->
    Δ ▹ T ⊨ N ≈ N' : A ->
    Γ ⊨s σ,,M[σ],,N[σ,,M[σ]] ≈ σ',,M'[σ'],,N'[σ',,M'[σ']] : Δ ▹ T ▹ A.
Proof.
  intros * Hσj HM HN.
  apply rel_sub_under_ctx_extend_sub; [| eassumption ].
  apply rel_sub_under_ctx_extend_sub; eassumption.
Qed.

(** ** Lifting is Semantic

    The lemma the case files use most.  [sb_wk_q] makes it a four-value pattern:
    it says [(q σ)[ψ]ʷ] is again an extension, by [σ] postcomposed with [↑ ⊙ ψ]
    and by the variable [ψ 0].

    Tails: [q σ] extends [σ[↑]ʷ], so all four tails are values of [σ[↑]ʷ], which is
    a semantic substitution [Γ ▹ A[σ] ⊨s σ[↑]ʷ : Δ] by [rel_sub_under_ctx_wk]
    applied to the weakening [Γ ▹ A[σ] ⊨w ↑ : Γ].  One instantiation of it
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A[σ] ⊨s q σ ≈ q σ' : Δ ▹ A.
Proof.
  intros * Hσj HA.
  pose proof Hσj as [env_relΓ [HΓ [env_relΔ [HΔ Hσ]]]].
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ' [HΔ' HAgen]].
  (** The simple form of the hypothesis, at [σ ≈ σ].  The first of the three type
    instantiations below runs at a pair of [σ]-evaluated environments, which this
    form supplies: two evaluations of [σ] at a related pair, rather than the four
    of a full four-value pattern. *)
  pose proof (rel_sub_under_ctx_simple (rel_sub_under_ctx_refl_left Hσj))
    as [env_relΓ2 [HΓ2 [env_relΔ2 [HΔ2 Hσrefl]]]].
  handle_per_ctx_env_irrel.
  rename HΓ2 into HΓ; rename HΔ2 into HΔ.
  pose proof (per_ctx_env_of_typ HΔ HA) as HΔA.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  (** [Γ ▹ A[σ] ⊨s σ[↑]ʷ : Δ] — the substitution [q σ] extends.  All four tails
      come from this one judgment. *)
  pose proof (rel_wk_shift HΓ HΓA) as Hshift.
  pose proof (rel_wk_under_ctx_intro HΓA HΓ Hshift) as Hshiftj.
  pose proof (rel_sub_under_ctx_wk Hσj Hshiftj) as Hσwkj.
  pose proof Hσwkj as [env_relΓA [HΓA' [env_relΔ3 [HΔ3 Hσwk]]]].
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' ψ Hψ ρ ρ' Hρ.
  (** The Kripke stage lands in [Γ ▹ A[σ]], so the pair [ρ ≈ ρ'] splits into a
      tail pair and a head pair — the [per_env_extend] the context PER just
      built. *)
  destruct (Hψ _ _ Hρ) as [Htail Hhead].
  destruct (Hσwk _ _ HΓ' _ Hψ _ _ Hρ) as [x1 y1 y4 x4 Hx1 Hy1 Hy4 Hx4 Htails].
  (** [σ] itself along [↑], which puts [⟦σ⟧((⟪ψ⟫ ρ)↯)] in the same PER as the
    tails: its leftmost value is again [⟦σ[↑]ʷ⟧(⟪ψ⟫ ρ)], so determinism of
    substitution evaluation (up to [env_eq], not [eq]) links the two chains. *)
  destruct (Hσ _ _ HΓA' _ Hshift _ _ (Hψ _ _ Hρ)) as [z1 y2 y3 z4 Hz1 Hy2 Hy3 Hz4 Hbtails].
  rewrite ?eval_wk_shift in *.
  assert (Heq : env_eq y1 z1) by (eapply functional_eval_sub; eassumption).
  assert (Hy12 : Dom y1 ≈ y2 ∈ env_relΔ) by (rewrite Heq; pairwise).
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
  destruct (HAgen _ _ HΔ3 _ _ (rel_sub_id (ex_intro _ _ HΔ3)) _ _ _ _ Hy12
                  (eval_sub_id _) (eval_sub_id _)) as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  rewrite exp_sub_id in Hd1, Hd4.
  (** Weak functionality names [A[σ]]'s element PER, so the [per_head] hypothesis
      is instantiated at it directly with no transport.  Both heads are the same
      two values on all four sides, so [rel_chain_4_of_2] is the whole head
      chain. *)
  functionalize_per_univ_chain Hcchain R.
  assert (Hh : Dom (⟪ψ⟫ ρ 0) ≈ (⟪ψ⟫ ρ' 0) ∈ R)
    by (apply (Hhead i R c1 c4); first [ eassumption | pairwise ]).
  assert (Hheads : rel_chain R ([ρ (ψ 0); ρ (ψ 0); ρ' (ψ 0); ρ' (ψ 0)]))
    by (apply rel_chain_4_of_2; [ solve_chain_PER | rewrite <- !(eval_wk_app ψ); exact Hh ]).
  apply (mk_rel_sub (env_entry ρ (ψ 0) :: x1) (env_entry ρ (ψ 0) :: y1)
                    (env_entry ρ' (ψ 0) :: y4) (env_entry ρ' (ψ 0) :: x4));
    [ apply eval_sub_wk_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | rewrite <- (eval_wk_app_entry ψ); apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].
  (** [Hdchain] is the bridge: after [functional_eval_rewrite_clear] its values
      are [⟦A⟧y1] and [⟦A⟧y2], which are [b2] and [c2], so the [b]- and
      [c]-chains meet.  [Hcchain] is already at one PER; saturating irrelevance
      once here rather than inside [solve_per_head] keeps the last step cheap. *)
  functional_eval_rewrite_clear.
  destruct Hcchain as [? [? ?]].
  destruct_per_univ_chain Hbchain.
  destruct_per_univ_chain Hdchain.
  handle_per_univ_elem_irrel.
  solve_per_env_extend_chain.
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      exists s s',
        ⟦ q σ ⟧s ρ ↦ c ↘ s ↦ c /\
        ⟦ q σ' ⟧s ρ' ↦ c' ↘ s' ↦ c' /\
        rel_chain env_relΔA
          ([s ↦ c; s ↦ c'; ρσ ↦ c; ρσ ↦ c';
           ρ'σ' ↦ c; ρ'σ' ↦ c'; s' ↦ c; s' ↦ c']).
Proof.
  intros * HΓ HΔA Hσj HA * Hpair Hev Hev'.
  pose proof Hpair as [Hρ Hhead].
  pose proof Hσj as [env_relΓ2 [HΓ2 [env_relΔ [HΔ Hσ]]]].
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΔ2 [HΔ2 HAgen]].
  pose proof (rel_exp_of_typ_inversion_simple HA) as [env_relΔ3 [HΔ3 HAsimple]].
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
  destruct (Hσ _ _ HΓA _ Hshift _ _ Hpair) as [s u2 u3 s' Hs Hu2 Hu3 Hs' Hstails].
  rewrite ?eval_wk_shift in *.
  assert (Heq2 : env_eq ρσ u2) by (eapply functional_eval_sub; eassumption).
  assert (Heq3 : env_eq ρ'σ' u3) by (eapply functional_eval_sub; eassumption).
  assert (Htails : rel_chain env_relΔ ([s; ρσ; ρ'σ'; s']))
    by (apply rel_chain_4; [ rewrite Heq2 | rewrite Heq2, Heq3 | rewrite Heq3 ]; pairwise).
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
  split; [ apply eval_sub_q; eassumption | split; [ apply eval_sub_q; eassumption |]].
  functional_eval_rewrite_clear.
  destruct Hechain as [? [? ?]].
  handle_per_univ_elem_irrel.
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Δ ▹ A ⊨ B ≈ B' : ulvl_tm j ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ j).
Proof.
  intros * HΓ Hσj HA HB * Hpair Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof (rel_exp_of_univ_inversion HB) as [env_relΔA [HΔA HBgen]].
  pose proof (rel_exp_of_univ_inversion_simple (rel_exp_under_ctx_refl_left HB))
    as [env_relΔA2 [HΔA2 HBl]].
  pose proof (rel_exp_of_univ_inversion_simple (rel_exp_under_ctx_refl_right HB))
    as [env_relΔA3 [HΔA3 HBr]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA3 Hσj HA _ _ _ _ _ _ Hpair Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  destruct (HBgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq')
    as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  (** The four bridges, at four pairs the chain above relates. *)
  assert (P1 : Dom s ↦ c ≈ ρσ ↦ c' ∈ env_relΔA) by pairwise.
  assert (P2 : Dom ρσ ↦ c ≈ s ↦ c ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ≈ ρ'σ' ↦ c' ∈ env_relΔA) by pairwise.
  assert (P4 : Dom ρ'σ' ↦ c ≈ s' ↦ c' ∈ env_relΔA) by pairwise.
  destruct (HBl _ _ P1) as [x1 [x2 [Hx1 [Hx2 Hx]]]].
  destruct (HBl _ _ P2) as [y1 [y2 [Hy1 [Hy2 Hy]]]].
  destruct (HBr _ _ P3) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
  destruct (HBr _ _ P4) as [t1 [t2 [Ht1 [Ht2 Ht]]]].
  (** Each bridge shares one endpoint with the main chain.  It is named
    explicitly rather than by [functional_eval_rewrite_clear], because the merges
    below depend on which of two names that tactic keeps. *)
  assert (x1 = b2) by (eapply functional_eval_exp; eassumption).
  assert (y2 = b2) by (eapply functional_eval_exp; eassumption).
  assert (z1 = b3) by (eapply functional_eval_exp; eassumption).
  assert (t2 = b3) by (eapply functional_eval_exp; eassumption).
  subst.
  apply rel_chain_of_pair in Hx, Hy, Hz, Ht.
  (** Merging the five chains into one, along the two values the main
      instantiation contributes. *)
  assert (M1 : rel_chain (per_univ j) ([b1; b2; b3; b4; x2]))
    by (merge_rel_chain Hbchain Hx b2).
  assert (M2 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2]))
    by (merge_rel_chain M1 Hy b2).
  assert (M3 : rel_chain (per_univ j) ([y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M2 Hz b3).
  assert (M4 : rel_chain (per_univ j) ([t1; y1; b1; b2; b3; b4; x2; z2]))
    by (merge_rel_chain M3 Ht b3).
  repeat split.
  - exists b1, x2; repeat split; try eassumption.
    pairwise.
  - exists y1, z2; repeat split; try eassumption.
    pairwise.
  - exists t1, b4; repeat split; try eassumption.
    pairwise.
Qed.

Corollary rel_exp_of_typ_under_ctx_q : forall {Γ Δ σ σ' A} {i : nat} {B B'} {j : nat} {env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Δ ▹ A ⊨ B ≈ B' : Typeω@j ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      (exists b b',
          ⟦ B[q σ] ⟧ ρ ↦ c ↘ b /\ ⟦ B ⟧ ρσ ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B ⟧ ρσ ↦ c ↘ b /\ ⟦ B' ⟧ ρ'σ' ↦ c' ↘ b' /\
          Dom b ≈ b' ∈ per_univ j) /\
      (exists b b',
          ⟦ B' ⟧ ρ'σ' ↦ c ↘ b /\ ⟦ B'[q σ'] ⟧ ρ' ↦ c' ↘ b' /\
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
    Γ ⊨s σ ≈ σ' : Δ ->
    Δ ⊨ A ≈ A : Typeω@i ->
    Δ ▹ A ⊨ M ≈ M' : B ->
    forall ρ ρ' ρσ ρ'σ' c c',
      Dom ρ ↦ c ≈ ρ' ↦ c' ∈ per_env_extend A[σ] A[σ] env_relΓ ->
      ⟦ σ ⟧s ρ ↘ ρσ ->
      ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
      (exists m m',
          ⟦ M[q σ] ⟧ ρ ↦ c ↘ m /\ ⟦ M ⟧ ρσ ↦ c' ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c) (ρ'σ' ↦ c')) /\
      (exists m m',
          ⟦ M ⟧ ρσ ↦ c ↘ m /\ ⟦ M' ⟧ ρ'σ' ↦ c' ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c) (ρ'σ' ↦ c')) /\
      (exists m m',
          ⟦ M' ⟧ ρ'σ' ↦ c ↘ m /\ ⟦ M'[q σ'] ⟧ ρ' ↦ c' ↘ m' /\
          Dom m ≈ m' ∈ per_head B B (ρσ ↦ c) (ρ'σ' ↦ c')).
Proof.
  intros * HΓ Hσj HA HM * Hpair Hev Hev'.
  pose proof (per_ctx_env_of_typ_sub HΓ Hσj HA) as HΓA.
  pose proof (rel_sub_under_ctx_q Hσj HA) as Hqj.
  pose proof HM as [env_relΔA [HΔA [k HMgen]]].
  pose proof (rel_exp_under_ctx_simple HM) as [env_relΔA2 [HΔA2 [k1 HMmid]]].
  pose proof (rel_exp_under_ctx_simple (rel_exp_under_ctx_refl_left HM))
    as [env_relΔA3 [HΔA3 [k2 HMl]]].
  pose proof (rel_exp_under_ctx_simple (rel_exp_under_ctx_refl_right HM))
    as [env_relΔA4 [HΔA4 [k3 HMr]]].
  handle_per_ctx_env_irrel.
  destruct (rel_sub_under_ctx_q_at HΓ HΔA4 Hσj HA _ _ _ _ _ _ Hpair Hev Hev')
    as [s [s' [Hq [Hq' Hchain]]]].
  (** The main instantiation, along [q σ ≈ q σ']: its two outer values are the
      goal's, on both the type and the term side. *)
  destruct (HMgen _ _ HΓA _ _ Hqj _ _ _ _ Hpair Hq Hq') as [Rm [Htyp Hexp]].
  destruct Htyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct Hexp as [f1 f2 f3 f4 Hf1 Hf2 Hf3 Hf4 Hfchain].
  (** The four pairs the bridges are taken at, all related by the eight-value
      chain of [rel_sub_under_ctx_q]. *)
  assert (Pm : Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΔA) by pairwise.
  assert (P1 : Dom s ↦ c ≈ ρσ ↦ c ∈ env_relΔA) by pairwise.
  assert (P2 : Dom s ↦ c ≈ ρσ ↦ c' ∈ env_relΔA) by pairwise.
  assert (P3 : Dom s' ↦ c' ≈ ρ'σ' ↦ c ∈ env_relΔA) by pairwise.
  destruct (HMmid _ _ Pm) as [dL [dR [Rmid [HdL [HdR [Emid [g1 [g2 [Hg1 [Hg2 Hgrel]]]]]]]]]].
  destruct (HMl _ _ P1) as [x1 [x2 [Rx [Hx1 [Hx2 [Ex [u1 [u2 [Hu1 [Hu2 Hurel]]]]]]]]]].
  destruct (HMl _ _ P2) as [y1 [y2 [Ry [Hy1 [Hy2 [Ey [v1 [v2 [Hv1 [Hv2 Hvrel]]]]]]]]]].
  destruct (HMr _ _ P3) as [z1 [z2 [Rz [Hz1 [Hz2 [Ez [w1 [w2 [Hw1 [Hw2 Hwrel]]]]]]]]]].
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
Lemma rel_typ_of_instance : forall {Γ A} {i : nat} {B N},
    Γ ⊨ A ≈ A : Typeω@i ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
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
                ⟦ B ⟧ ρσ ↦ w ↘ b /\ ⟦ B ⟧ ρ'σ' ↦ z ↘ b' /\
                  Dom b ≈ b' ∈ per_univ i) /\
          rel_typ i B[Id,,N] σ ρ ρσ B[Id,,N] σ' ρ' ρ'σ'
            (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)).
Proof.
  intros * HA HB HN * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The argument, and the two pairs of values of its type: the outer one is what
      an extended context PER is built at, the inner one what the codomain is read
      at. *)
  pose proof HN as [? [? [j HNgen]]].
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN [HNtyp HNexp]].
  destruct HNtyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  assert (Houter : DF a1 ≈ a4 ∈ per_univ_elem j ↘ RN) by pairwise.
  assert (Hmid : DF a2 ≈ a3 ∈ per_univ_elem j ↘ RN) by pairwise.
  (** The codomain at an arbitrary related pair of arguments. *)
  assert (Hcod : forall w z,
             Dom w ≈ z ∈ RN ->
             exists b b',
               ⟦ B ⟧ ρσ ↦ w ↘ b /\ ⟦ B ⟧ ρ'σ' ↦ z ↘ b' /\
                 Dom b ≈ b' ∈ per_univ i).
  { intros w z Hwz.
    eapply (rel_exp_of_typ_extend_simple HΓ HA HB).
    apply per_env_extend_intro'; [ exact Hρσ |].
    eapply per_head_of; [ exact Ha2 | exact Ha3 | exact Hmid | exact Hwz ]. }
  (** The two instantiations, their outer values rewritten into the goal's
      spelling. *)
  destruct (HBgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ Hev Hn1)
                  (eval_sub_extend _ _ _ _ _ Hev' Hn4))
    as [t1 tA2 tA3 t4 Ht1 HtA2 HtA3 Ht4 HtAchain].
  rewrite <- exp_sub_extend_sub in Ht1, Ht4.
  destruct (HBgen _ _ HΓ _ _ HidN _ _ _ _ Hρσ
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn2)
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn3))
    as [t2 tB2 tB3 t3 Ht2 HtB2 HtB3 Ht3 HtBchain].
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
                               (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)))
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
Lemma per_univ_of_instance : forall {Γ A} {i : nat} {B N env_relΓ},
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ ->
    Γ ▹ A ⊨ B ≈ B : Typeω@i ->
    Γ ⊨ N ≈ N : A ->
    forall ρ n,
      Dom ρ ≈ ρ ∈ env_relΓ ->
      ⟦ N ⟧ ρ ↘ n ->
      exists a b,
        ⟦ B[Id,,N] ⟧ ρ ↘ a /\ ⟦ B ⟧ ρ ↦ n ↘ b /\
          Dom a ≈ a ∈ per_univ i /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HΓ HB HN * Hρ Hn.
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  pose proof (rel_exp_of_typ_inversion HB) as [env_relΓA [HΓA HBgen]].
  destruct (HBgen _ _ HΓ _ _ HidN _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn)
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn))
    as [t1 t2 t3 t4 Ht1 Ht2 Ht3 Ht4 Hchain].
  destruct Hchain as [Ht12 _].
  exists t1, t2.
  do 2 (split; [ eassumption |]).
  split; [| eassumption ].
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

End Fixed_GCtx.

