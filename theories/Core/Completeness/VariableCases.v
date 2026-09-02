(** * Fundamental Theorem: Variables

    Three of the old file's four lemmas are gone.  [rel_exp_var_0_sub],
    [rel_exp_var_S_sub] and [rel_exp_var_weaken] validated the rules that
    computed [#0[σ ,, M]], [#(S x)[σ ,, M]] and [#x⟨↑⟩[σ ,, M]]; all three are now
    *equations* of [exp_sub] ([sb_extend]'s two clauses and
    [exp_sub_shift_extend]), so there is no longer anything to validate.

    What is left is the variable case of the fundamental theorem, and the
    semantic weakening lemma its induction step is an instance of — since a
    lookup one context deeper is literally a weakened lookup:
    [#(S x)] is [(#x)⟨↑⟩] and the type it reports is [A⟨↑⟩].

    Both rest on a pair of instantiations.  A judgment about [Γ] is used twice:
    once along [Wk ⨟ σ] at [Γ'], whose *outer* values are the goal's outer values
    ([exp_sub_shift]), and once along [Wk] at the
    substituted environments, whose outer values are the goal's *inner* values
    ([exp_sub_of_shift]).  The two share their inner values — both evaluate the
    unweakened expression in [ρσ ↯] and [ρ'σ' ↯] — and since evaluation is
    functional that shared pair is what merges the two chains into the one the
    goal asks for.  Postcomposition would not do: [⟦σ⟨↑⟩⟧ρ] and [⟦σ⟧(ρ↯)] are
    different environments, which is exactly why the bridge is a *merge* and not a
    rewrite. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution SystemOpt.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases.
Import Domain_Notations.
Import Wk_Notations.

(** ** Semantic Weakening

    The judgment of a context survives being read in an extension of it, with
    everything weakened.  This is the form the induction step of [valid_exp_var]
    needs, and it is where the two instantiations live.

    The premise is the context PER of [Γ ▹ C] and not [⊨ Γ ▹ C]: what the extension
    is needed for is the [Wk]-instantiation, and [rel_sub_shift] factors through
    [rel_wk_shift], which asks only for the two PERs — the tail's coming from [M]'s
    own judgment.  Stating it this way is what lets the η-rule use it, since no
    premise of that rule mentions [Γ] and so [⊨ Γ] is not available there. *)
Lemma rel_exp_under_ctx_shift : forall {Γ C A M M' env_relΓC},
    EF Γ ▹ C ≈ Γ ▹ C ∈ per_ctx_env ↘ env_relΓC ->
    Γ ⊨ M ≈ M' : A ->
    Γ ▹ C ⊨ M⟨↑⟩ ≈ M'⟨↑⟩ : A⟨↑⟩.
Proof.
  intros * HΓCper HM.
  destruct HM as [env_relΓ [HΓ [i HMgen]]].
  pose proof (rel_sub_of_wk (rel_wk_under_ctx_intro HΓCper HΓ (rel_wk_shift HΓ HΓCper)))
    as HWk.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** The substituted environments are related in [Γ ▹ C] — needed to instantiate
      along [Wk] at them. *)
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓC)
    by (eapply rel_sub_under_ctx_at'; eassumption).
  (** The two instantiations. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_shift Hσj) _ _ _ _ Hρ
                  (eval_sub_shift_pre _ _ _ Hev) (eval_sub_shift_pre _ _ _ Hev'))
    as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓCper _ _ HWk _ _ _ _ Hρσ
                  (eval_sub_shift ρσ) (eval_sub_shift ρ'σ'))
    as [R2 [Htyp2 Hexp2]].
  destruct Htyp1 as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hvchain].
  destruct Htyp2 as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Huchain].
  destruct Hexp1 as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  destruct Hexp2 as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  (** Naming the values as the goal names them: the first instantiation's outer
      values are the goal's outer ones, the second's are the goal's inner ones. *)
  rewrite <- exp_sub_shift in Hv1, Hv4, Hm1, Hm4.
  rewrite exp_sub_of_shift in Hu1, Hu4, Hn1, Hn4.
  (** [v2 = u2] and [v3 = u3] by functionality: the two chains meet at the values
      of the *unweakened* type in the tails, and reading that shared link off both
      identifies the two element PERs. *)
  handle_per_univ_elem_irrel.
  assert (Hmid1 : DF v2 ≈ v3 ∈ per_univ_elem i ↘ R1) by pairwise.
  assert (Hmid2 : DF v2 ≈ v3 ∈ per_univ_elem i ↘ R2) by pairwise.
  handle_per_univ_elem_irrel.
  exists R1.
  split.
  - apply (mk_rel_exp v1 u1 u4 v4); try eassumption.
    merge_rel_chain Hvchain Huchain v2.
  - apply (mk_rel_exp m1 n1 n4 m4); try eassumption.
    merge_rel_chain Hmchain Hnchain m2.
Qed.

#[export]
Hint Resolve rel_exp_under_ctx_shift : mctt.

(** ** The Variable Case

    Fixing the instantiation before inducting, so that the induction hypothesis
    may be used twice, would split this into two lemmas; with the weakening lemma above doing that work, the induction
    is on the lookup derivation alone and its step case is a single [apply]. *)
Lemma valid_exp_var : forall {Γ x A},
    Γ ∋ #x : A ->
    ⊨ Γ ->
    Γ ⊨ #x : A.
Proof.
  induction 1 as [A Γ | x A Γ B Hx IH]; intros HΓ.
  - (** [Γ ▹ A ∋ #0 : A⟨↑⟩].  The type is weakened, so its four values come from
        the weakening lemma applied to [A]'s own judgment; the term's four values
        are all [ρσ 0] and [ρ'σ' 0], handed over by the head clause of the context
        PER of [Γ ▹ A].  That clause speaks of the values of [A] in the *tails*, so
        the instance of [A]'s judgment at [Wk] is needed a second time — as a
        bridge from those values to the values of [A⟨↑⟩]. *)
    pose proof HΓ as HΓA.
    inversion HΓ as [| ? ? i ? HΓ0 HΓAper HA]; subst.
    pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓper HAgen]].
    pose proof (rel_exp_of_typ_inversion (rel_exp_under_ctx_shift HΓAper HA))
      as [env_relΓA [HΓAper' HAwkgen]].
    (** [eexists_rel_exp_with] picks the context PER by [eassumption]; the one the
        inversion of [⊨ Γ ▹ A] left behind is redundant and must not be picked. *)
    clear HΓAper env_rel.
    eexists_rel_exp_with i.
    (** The head clause of the context PER of [Γ ▹ A]: it relates the heads of two
        related environments at the values of [A] in their *tails*. *)
    pose proof HΓAper' as HΓAcons.
    invert_per_ctx_env HΓAcons.
    rename x into j; rename x0 into head_rel; rename H into Hheadtyp; rename H0 into Hequiv.
    intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓA)
      by (eapply rel_sub_under_ctx_at'; eassumption).
    (** The type's four values, and the [Wk]-instantiation that bridges them to the
        values [head_rel] is stated at. *)
    destruct (HAwkgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
      as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hvchain].
    destruct (HAgen _ _ HΓAper' _ _ (rel_sub_shift HΓA) _ _ _ _ Hρσ
                    (eval_sub_shift ρσ) (eval_sub_shift ρ'σ'))
      as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Huchain].
    rewrite exp_sub_of_shift in Hu1, Hu4.
    (** Reading the head clause off [Hρσ], together with the values of [A] it
        speaks of. *)
    apply_relation_equivalence.
    destruct Hρσ as [Hteq Hhead].
    pose proof (Hheadtyp _ _ Hteq) as Hatyp.
    destruct_by_head PER.Definitions.rel_typ.
    (** Weak functionality already gives each chain a single element PER, so
        irrelevance is left with three: the two chains' and [head_rel]'s, whose
        level [j] need not match [i] since [per_univ_elem] irrelevance is
        cross-level. *)
    destruct_per_univ_chain Hvchain.
    destruct_per_univ_chain Huchain.
    handle_per_univ_elem_irrel.
    exists (head_rel ρσ↯ ρ'σ'↯ Hteq).
    split.
    + apply (mk_rel_exp v1 v2 v3 v4); try eassumption.
      apply rel_chain_4; eassumption.
    + (** [#0[σ]] *is* [σ 0], so the outer values are the heads too. *)
      apply (mk_rel_exp (ρσ 0) (ρσ 0) (ρ'σ' 0) (ρ'σ' 0));
        try apply eval_exp_var; try (apply eval_sub_index; eassumption).
      apply rel_chain_4_of_2; [ solve_chain_PER | eassumption ].
  - (** [Γ ▹ B ∋ #(S x) : A⟨↑⟩] is the weakening of [Γ ∋ #x : A]. *)
    inversion HΓ as [| ? ? ? ? HΓ0 HΓBper ?]; subst.
    exact (rel_exp_under_ctx_shift HΓBper (IH HΓ0)).
Qed.

#[export]
Hint Resolve valid_exp_var : mctt.
