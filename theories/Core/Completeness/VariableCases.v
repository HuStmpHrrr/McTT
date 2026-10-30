(** * Fundamental Theorem: Variables

    Substitution into a variable computes ([sb_extend]'s two clauses and
    [exp_sub_shift_extend]), so only the variable rule itself is validated here,
    together with the semantic weakening lemma its induction step is an instance
    of: [#(S x)] is [(#x)[↑]ʷ], and the type it reports is [A[↑]ʷ].

    Both rest on two instantiations of a judgment about [Γ]: along [Wk ⨟ σ] at
    [Γ'], whose outer values are the goal's outer values ([exp_sub_shift]), and
    along [Wk] at the substituted environments, whose outer values are the goal's
    inner values ([exp_sub_of_shift]).  The two share their inner values, since
    both evaluate the unweakened expression in [ρσ ↯] and [ρ'σ' ↯], and as
    evaluation is functional this shared pair merges the two chains into the one
    the goal asks for.  [⟦σ[↑]ʷ⟧ρ] and [⟦σ⟧(ρ↯)] are different environments,
    which is why the bridge is a merge and not a rewrite. *)

From Stdlib Require Import List Morphisms_Relations RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution SystemOpt.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation UniverseCases.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.

(** ** Semantic Weakening

    A judgment of a context still holds when read in an extension of it, with
    everything weakened.  This is the form the induction step of [valid_exp_under_ctx_vlookup]
    needs.

    The premise is the context PER of the extension, not its [rel_ctx_wf]: the
    extension is only needed for the [Wk] instantiation, and [rel_sub_shift]
    factors through [rel_wk_shift], which asks only for the two PERs, the
    tail's coming from [M]'s relation.  This lets the η-rule use the lemma,
    since no premise of that rule mentions [Γ] and so [⊨ Γ] is not
    available there. *)

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_exp_under_ctx_shift : forall {Γ e A M M' env_relΓC},
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ env_relΓC ->
    Γ ⊨ M ≈ M' : A ->
    (e :: Γ)%list ⊨ M[↑]ʷ ≈ M'[↑]ʷ : A[↑]ʷ.
Proof.
  intros * HΓCper HM.
  destruct HM as [env_relΓ HΓ i HMgen].
  pose proof (rel_sub_of_wk_rel HΓCper HΓ (rel_wk_shift HΓ HΓCper)) as HWk.
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** The substituted environments are related in [Γ ▹ C] — needed to instantiate
      along [Wk] at them. *)
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓC)
    by (eapply rel_sub_under_ctx_at'; eassumption).
  destruct (eval_sub_shift_rel HΓCper Hρσ) as [Hs Hs'].
  (** The two instantiations. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_shift Hσj) _ _ _ _ Hρ
                  (eval_sub_shift_pre _ _ _ _ _ Hev) (eval_sub_shift_pre _ _ _ _ _ Hev'))
    as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓCper _ _ HWk _ _ _ _ Hρσ Hs Hs')
    as [R2 [Htyp2 Hexp2]].
  pose proof Htyp1 as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hvchain].
  pose proof Htyp2 as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Huchain].
  assert (Euv : u2 = v2) by (eapply functional_eval_exp; eassumption).
  (** The weakened type is a proposition exactly when the type is, in the
      tails: at a relevant one both instantiations relate the terms. *)
  destruct (domain_relevance v2) eqn:Er;
    [ apply (rel_exp_or_prop_relevant Htyp1 (ex_intro _ v2 (conj Hv2 Er))) in Hexp1;
      assert (Er' : domain_relevance u2 = relevant) by congruence;
      apply (rel_exp_or_prop_relevant Htyp2 (ex_intro _ u2 (conj Hu2 Er'))) in Hexp2;
      destruct Hexp1 as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain];
      destruct Hexp2 as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain]
    | clear Hexp1 Hexp2 ];
    clear Htyp1 Htyp2;
    (** Naming the values as the goal names them: the first instantiation's
        outer values are the goal's outer ones, the second's are the goal's
        inner ones. *)
    rewrite <- exp_sub_shift in Hv1, Hv4;
    rewrite exp_sub_of_shift in Hu1, Hu4;
    (** [v2 = u2] and [v3 = u3] by functionality: the two chains meet at the
        values of the unweakened type in the tails, and that shared link
        identifies the two element PERs. *)
    handle_per_univ_elem_irrel;
    assert (Hmid1 : DF v2 ≈ v3 ∈ per_univ_elem i ↘ R1) by pairwise;
    assert (Hmid2 : DF v2 ≈ v3 ∈ per_univ_elem i ↘ R2) by pairwise;
    handle_per_univ_elem_irrel;
    exists R1; split;
    try solve [ apply (mk_rel_exp v1 u1 u4 v4); try eassumption; merge_rel_chain Hvchain Huchain v2 ].
  - rewrite <- exp_sub_shift in Hm1, Hm4.
    rewrite exp_sub_of_shift in Hn1, Hn4.
    right; apply (mk_rel_exp m1 n1 n4 m4); try eassumption.
    merge_rel_chain Hmchain Hnchain m2.
  - left; exists v1; split; [ exact Hv1 |].
    assert (H12 : DF v1 ≈ v2 ∈ per_univ_elem i ↘ R1) by pairwise.
    pose proof (per_univ_elem_relevance _ _ _ _ H12); congruence.
Qed.

Hint Resolve rel_exp_under_ctx_shift : mctt.

(** ** The Variable Case

    The head of an assumption entry is read off the head clause of its context
    PER.  The head of a definition entry is a head of the assumption entry of
    the same type, by restriction.  A lookup one entry deeper is a weakened
    lookup, so the induction step is [rel_exp_under_ctx_shift]. *)

(** [Γ ▹ A ∋ #0 : A[↑]ʷ].  The type is weakened, so its four values come from
    the weakening lemma applied to [A]'s judgment.  The term's values are all
    [ρσ 0] and [ρ'σ' 0], given by the head clause of the context PER of [Γ ▹ A].
    That clause speaks of the values of [A] in the tails, so the [Wk] instance of
    [A]'s judgment is used a second time, to bridge those values to the values of
    [A[↑]ʷ]. *)
Lemma valid_exp_under_ctx_var_here_any_entry : forall {Γ e A S R},
    ctx_entry_type (e :: nil) 0 = Some A ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    type_sort S ->
    Γ ⊨ A : S ->
    (e :: Γ)%list ⊨ #0 : A[↑]ʷ.
Proof.
  intros * He HR HS HA.
  (** The type is of either sort; its judgment as a type, and that of its
      weakening, are read at levels of their own. *)
  destruct (rel_type_of_sort HS HA) as [k Hk].
  pose proof (rel_exp_under_ctx_shift HR HA) as HAwk.
  rewrite (type_sort_wk _ HS) in HAwk.
  destruct (rel_type_of_sort HS HAwk) as [i Hk'].
  pose proof (rel_type_inversion Hk) as [env_relΓ [HΓ HAgen]].
  pose proof (rel_type_inversion_simple Hk) as [env_relΓ2 [HΓ2 HAs]].
  pose proof (rel_type_inversion Hk') as [R' [HR' HAwkgen]].
  pose proof (per_ctx_env_head_split He HR) as [T [HT Hsplit]].
  assert (E2 : T <~> env_relΓ2) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E3 : R <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
  refine (mk_rel_exp_under_ctx _ _ _ _ R HR i _).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ R)
    by (eapply rel_sub_under_ctx_at'; eassumption).
  (** The type's four values, and the [Wk]-instantiation that bridges them to the
      values of [A] in the tails, which the head PER is stated at. *)
  destruct (HAwkgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [v1 v2 v3 v4 Hv1 Hv2 Hv3 Hv4 Hvchain].
  destruct (eval_sub_shift_rel HR Hρσ) as [Hs Hs'].
  destruct (HAgen _ _ HR _ _ (rel_sub_of_wk_rel HR HΓ (rel_wk_shift HΓ HR)) _ _ _ _ Hρσ Hs Hs')
    as [u1 u2 u3 u4 Hu1 Hu2 Hu3 Hu4 Huchain].
  rewrite exp_sub_of_shift in Hu1, Hu4.
  destruct (Hsplit _ _ Hρσ) as [Hteq Hhead].
  apply E2 in Hteq.
  (** The variable is a proof exactly when [A] is a proposition in the
      tails; then so is the weakened type, and nothing is asked of the
      variable. *)
  functionalize_per_univ_chain Hvchain Rv.
  functionalize_per_univ_chain Huchain Ru.
  assert (Evu : v2 = u1) by (eapply functional_eval_exp; eassumption).
  subst u1.
  assert (Hu23 : DF u2 ≈ u3 ∈ per_univ_elem k ↘ Ru) by pairwise.
  assert (Hv12 : DF v1 ≈ v2 ∈ per_univ_elem i ↘ Rv) by pairwise.
  assert (Hv22 : DF v2 ≈ u2 ∈ per_univ_elem k ↘ Ru) by pairwise.
  pose proof (per_univ_elem_relevance _ _ _ _ Hu23) as Eu23.
  pose proof (per_univ_elem_relevance _ _ _ _ Hv12) as Ev12.
  pose proof (per_univ_elem_relevance _ _ _ _ Hv22) as Ev22.
  pose proof (head_propositional_iff HΓ2 He HAs Hteq Hu2) as I2.
  pose proof (head_propositional_iff_right HΓ2 He HAs Hteq Hu3) as I3.
  exists Rv; split.
  { apply (mk_rel_exp v1 v2 v3 v4); eassumption. }
  destruct (domain_relevance u2) eqn:Er2.
  2:{ left; exists v1; split; [ exact Hv1 | congruence ]. }
  right.
  assert (Hnp : ~ entry_propositional gc_deps gc_stack (e :: Γ)%list ρσ 0)
    by (rewrite entry_propositional_zero_head, I2; congruence).
  assert (Hnp' : ~ entry_propositional gc_deps gc_stack (e :: Γ)%list ρ'σ' 0)
    by (rewrite entry_propositional_zero_head, I3; congruence).
  (** The heads, related at the PER of [A] in the tails, which is that of
      the weakened type. *)
  assert (Hh : Dom ρσ 0 ≈ ρ'σ' 0 ∈ Ru) by (apply (Hhead k Ru u2 u3 Hu2 Hu3 Hu23)).
  assert (Hv23 : DF v2 ≈ v3 ∈ per_univ_elem i ↘ Rv) by pairwise.
  assert (Hvu : Rv <~> Ru) by (eapply per_univ_elem_right_irrel; eassumption).
  assert (PER Rv) by (eapply per_elem_PER; eassumption).
  (** [#0[σ]] is [σ 0], so the outer values are the heads too. *)
  apply (mk_rel_exp (ρσ 0) (ρσ 0) (ρ'σ' 0) (ρ'σ' 0));
    [ exact (eval_sub_var _ _ _ _ 0 Hev ltac:(cbn; lia) Hnp) | apply eval_exp_var | apply eval_exp_var
    | exact (eval_sub_var _ _ _ _ 0 Hev' ltac:(cbn; lia) Hnp') |].
  apply rel_chain_4_of_2; [ assumption | apply Hvu; exact Hh ].
Qed.

Lemma valid_exp_under_ctx_var_here : forall {Γ A},
    ⊨ Γ ▹ A ->
    Γ ▹ A ⊨ #0 : A[↑]ʷ.
Proof.
  intros * HΓ.
  inversion HΓ as [| ? ? Srt ? HΓ0 HΓAper HS HA | | |]; subst.
  eapply valid_exp_under_ctx_var_here_any_entry; [ reflexivity | exact HΓAper | exact HS | exact HA ].
Qed.

Lemma valid_exp_under_ctx_vlookup : forall {Γ x A},
    Γ ∋ #x : A ->
    ⊨ Γ ->
    Γ ⊨ #x : A.
Proof.
  induction 1 as [A Γ | A M Γ | A M U Γ | x A Γ e Hx IH]; intros HΓ.
  - apply valid_exp_under_ctx_var_here; assumption.
  - (** [Γ ▸ A ≔ M ∋ #0 : A[↑]ʷ]: its head is read as an assumption's. *)
    inversion HΓ as [| | ? ? ? Srt ? HΓ0 HΓAper HS HA HM | |]; subst.
    eapply valid_exp_under_ctx_var_here_any_entry; [ reflexivity | exact HΓAper | exact HS | exact HA ].
  - (** [Γ ▸ₘ A ≔ M ‖ U ∋ #0 : A[↑]ʷ] likewise. *)
    inversion HΓ as [| | | | ? ? ? ? i ? HΓ0 HΓAper HA HM _ _]; subst.
    eapply valid_exp_under_ctx_var_here_any_entry; [ reflexivity | exact HΓAper | exact (type_sort_universe i) | exact HA ].
  - (** [e :: Γ ∋ #(S x) : A[↑]ʷ] is the weakening of [Γ ∋ #x : A]. *)
    pose proof (rel_ctx_wf_per_ctx_env HΓ) as [env_relΓe HΓeper].
    exact (rel_exp_under_ctx_shift HΓeper (IH (rel_ctx_wf_tail HΓ))).
Qed.

Hint Resolve valid_exp_under_ctx_vlookup : mctt.

End Fixed_GCtx.

#[local] Generalizable All Variables.

Lemma sem_vlookup :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x : A ).
Proof. intros * HΓ Hx; sem_intro; [ assumption | exact (valid_exp_under_ctx_vlookup Hx HΓ) ]. Qed.

Lemma sem_exp_eq_var :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ #x : A ).
Proof. intros; eapply sem_vlookup; eassumption. Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** δ for Local Definitions

    At [#0] both sides are valid, so it suffices to relate their values
    pointwise ([rel_exp_under_ctx_of_simple]).  The value of [#0] is the head
    of the environment, the value of [M[↑]ʷ] is related to the value of [M] in
    the tail, and the tie relates those two.  A deeper lookup is again a
    weakened one. *)
Lemma rel_exp_under_ctx_var_delta_here_any_entry : forall {Γ e A M R} {i : nat},
    (e = ce_def A M \/ exists U, e = ce_dm A M U) ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ R ->
    Γ ⊨ A : Typeω@i ->
    Γ ⊨ M : A ->
    (e :: Γ)%list ⊨ #0 ≈ M[↑]ʷ : A[↑]ʷ.
Proof.
  intros * He HR HA HM.
  assert (Hent : ctx_entry_type (e :: nil) 0 = Some A) by (destruct He as [-> | [? ->]]; reflexivity).
  pose proof (per_ctx_env_head_split Hent HR) as [T [HT Hsplit]].
  pose proof (per_ctx_env_def_tie_split He HA HR) as Htie.
  eapply rel_exp_under_ctx_of_simple; [ exact HR | | | ].
  - exact (valid_exp_under_ctx_var_here_any_entry Hent HR (type_sort_universe i) HA).
  - exact (rel_exp_under_ctx_shift HR HM).
  - intros ρ ρ' Hρ; right.
    (** [M[↑]ʷ] against [M] in the tail, along the weakening [↑]. *)
    pose proof (rel_wk_under_ctx_shift_per HR HT) as Hwk.
    pose proof (rel_exp_under_ctx_wk_simple Hwk HM) as [R0 [HR0 [j Hws]]].
    assert (E : R <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
    assert (PER R) by (eapply per_env_PER; eassumption).
    assert (Hρ'ρ' : Dom ρ' ≈ ρ' ∈ R) by solve_per.
    destruct (Hws _ _ (proj1 (E _ _) Hρ'ρ')) as [a1 [a1' [R1 [Ha1 [Ha1' [HR1 [Hp1 | [m1 [m1' [Hm1 [Hm1' Hmm1]]]]]]]]]]].
    { (** [A] is a type of a universe, so its weakening is no proposition. *)
      exfalso.
      destruct (Hsplit _ _ Hρ'ρ') as [Ht' _].
      destruct (rel_exp_of_typ_relevant_at HT HA _ _ Ht') as (b0 & Eb0 & Hr0).
      rewrite eval_wk_shift in Ha1'.
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_relevance _ _ _ _ HR1); congruence. }
    destruct (Hws _ _ (proj1 (E _ _) Hρ)) as [a0 [a0' [R2 [Ha0 [Ha0' [HR2 _]]]]]].
    destruct (Hsplit _ _ Hρ) as [Ht Hh].
    destruct (Htie _ _ Hρ) as [_ [m' [Hm' Htie']]].
    destruct (rel_exp_of_typ_inversion_simple_at HT HA _ _ Ht) as [b [b' [Hb [Hb' [R3 HR3]]]]].
    rewrite eval_wk_shift in *.
    (** The tie, read at the element PER. *)
    assert (Ha11 : DF a1' ≈ a1' ∈ per_univ_elem j ↘ R1) by (etransitivity; [ symmetry |]; eassumption).
    assert (Htie2 : Dom m' ≈ ρ' 0 ∈ R1) by (apply (Htie' _ _ _ _ Ha1' Ha1' Ha11)).
    exists (ρ 0), m1.
    split; [ apply eval_exp_var | split; [ eassumption |] ].
    hnf; intros k R' a a' Ha Ha' HR'.
    functional_eval_rewrite_clear.
    (** The head clause, read at the element PER. *)
    assert (Hh' : Dom ρ 0 ≈ ρ' 0 ∈ R3) by (apply (Hh _ _ _ _ Hb Ha1' HR3)).
    handle_per_univ_elem_irrel.
    match goal with |- ?R _ _ => assert (PER R) by (eapply per_elem_PER; eassumption) end.
    solve_per.
Qed.

Lemma rel_exp_under_ctx_var_delta_here : forall {Γ A M},
    ⊨ Γ ▸ A ≔ M ->
    Γ ▸ A ≔ M ⊨ #0 ≈ M[↑]ʷ : A[↑]ʷ.
Proof.
  intros * HΓ.
  pose proof HΓ as HΓd.
  inversion HΓd as [| | ? ? ? Srt ? HΓ0 HΓdper HS HA HM | |]; subst.
  pose proof (rel_ctx_wf_per_ctx_env HΓ0) as [env_relΓ HΓper].
  destruct HS as [i |].
  2:{ (** At a proposition both sides are proofs: the weakened type is a
        proposition at every environment. *)
      eapply rel_exp_under_ctx_of_simple; [ exact HΓdper | | | ].
      - eapply valid_exp_under_ctx_vlookup; [ constructor | assumption ].
      - exact (rel_exp_under_ctx_shift HΓdper HM).
      - intros ρ ρ' Hρ; left.
        pose proof (rel_exp_under_ctx_shift HΓdper HA) as HAwk; cbn [exp_wk] in HAwk.
        destruct (rel_exp_of_prop_inversion_simple_at HΓdper HAwk _ _ Hρ) as (a & a' & Ha & Ha' & [Hl _ _]).
        exists a; split; assumption. }
  exact (rel_exp_under_ctx_var_delta_here_any_entry (or_introl eq_refl) HΓdper HA HM).
Qed.

(** δ at a definition with a module part: the same, read off its term
    part. *)
Lemma rel_exp_under_ctx_var_delta_here_dm : forall {Γ A M U},
    ⊨ Γ ▸ₘ A ≔ M ‖ U ->
    Γ ▸ₘ A ≔ M ‖ U ⊨ #0 ≈ M[↑]ʷ : A[↑]ʷ.
Proof.
  intros * HΓ.
  inversion HΓ as [| | | | ? ? ? ? i ? HΓ0 HΓdper HA HM _ _]; subst.
  exact (rel_exp_under_ctx_var_delta_here_any_entry (or_intror (ex_intro _ U eq_refl)) HΓdper HA HM).
Qed.

End Fixed_GCtx.

Lemma sem_exp_eq_var_delta :
  `( ⊨ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊨ #x ≈ M : A ).
Proof.
  intros * HΓ Hx; sem_intro; [ assumption |].
  clear - Hx HΓ; revert HΓ.
  induction Hx as [A M Γ | A M U Γ | x A M Γ e Hx IH]; intros HΓ.
  - apply rel_exp_under_ctx_var_delta_here; assumption.
  - apply rel_exp_under_ctx_var_delta_here_dm; assumption.
  - pose proof (rel_ctx_wf_per_ctx_env HΓ) as [env_relΓe HΓeper].
    exact (rel_exp_under_ctx_shift HΓeper (IH (rel_ctx_wf_tail HΓ))).
Qed.

#[export]
Hint Resolve rel_exp_under_ctx_shift : mctt.
#[export]
Hint Resolve valid_exp_under_ctx_vlookup : mctt.
