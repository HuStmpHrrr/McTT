(** * Strengthening: the Semantic Toolkit

    A judgment in a context that has one more variable can sometimes be read
    back as a judgment in the shorter context: if its subject and type are
    already terms of the shorter one, the extra variable is irrelevant to
    them.  The induction that does this (on normal forms, in the second half of
    this file) descends under binders, so the extra variable sits at an
    arbitrary position [k], between a telescope [Δ] of assumptions and the
    shorter context [Γ]:

      short: Δ ++ Γ          long: tele_wk Δ ↑ ++ A :: Γ        φ := q^k ↑

    where [k = length Δ].  Nothing here inducts on a *derivation*: a derivation
    in the long context may pass through terms that do mention the variable
    (the [P] of [Core.Syntactic.Fresh]'s companion experiment), and those can
    never be strengthened.  Instead every equation whose two ends are typed in
    the short context is pushed through the PER model, where the extra variable
    simply never appears. *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic Require Import CoreInversions Fresh.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong IndConv.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas MemberWf.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import DescTyping LookupSound Presup.
From Mctt.Algorithmic Require Import Subtyping.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Completeness.Records Require Model.
From Mctt.Core.Completeness.Modules Require Import MemberTypes Values.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness Require Import LetCases.
Import Domain_Notations Fixed_Notations Wk_Notations.

(** ** The Weakening that Inserts a Variable

    [q^k ↑] keeps the [k] innermost variables and shifts the rest by one: it is
    the weakening from the long context to the short one.  It is monotone, so
    it acts on environments by [⟪_⟫]. *)
Lemma wk_mono_qn : forall n φ, wk_mono φ -> wk_mono (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_mono_q; auto ]. Qed.

#[local]
Instance WkMono_qn_shift : forall k, WkMono (wk_qn k ↑).
Proof. intros k; apply wk_mono_qn, wk_mono_shift. Qed.

(** An environment under [q φ] splits: the innermost entry is kept, the rest
    is the environment under [φ].  Both halves are [Core.Semantic.Domain]
    lemmas; this is the two of them as one list equation. *)
Lemma eval_wk_q_cons : forall φ e ρ `{Hφ : WkMono φ},
    ⟪wk_q φ⟫ (e :: ρ) = e :: ⟪φ⟫ ρ.
Proof.
  intros.
  (** A list is determined by its head and its tail. *)
  pose proof (eval_wk_q_tail φ (e :: ρ)) as Htl.
  pose proof (eval_wk_q_zero_entry φ (e :: ρ)) as Hhd.
  destruct (⟪wk_q φ⟫ (e :: ρ)) as [| e' ρ'] eqn:E.
  - (** The result cannot be empty: it has the entry [e] at index 0. *)
    exfalso.
    assert (Hl : List.length (⟪wk_q φ⟫ (e :: ρ)) = 0) by (rewrite E; reflexivity).
    rewrite eval_wk_length in Hl.
    pose proof (wk_len_spec (wk_q φ) (List.length (e :: ρ)) (wk_mono_q φ Hφ) 0) as Hs.
    rewrite Hl in Hs; cbn in Hs; lia.
  - cbn in Htl, Hhd; rewrite Htl; f_equal; exact Hhd.
Qed.

(** Inserting an entry at position [k], and dropping it again. *)
Definition env_insert (k : nat) (e : dentry) (ρ : env) : env :=
  List.firstn k ρ ++ e :: List.skipn k ρ.

Lemma env_insert_zero : forall e ρ, env_insert 0 e ρ = e :: ρ.
Proof. reflexivity. Qed.

Lemma env_insert_succ : forall k e e' ρ, env_insert (S k) e (e' :: ρ) = e' :: env_insert k e ρ.
Proof. reflexivity. Qed.

Lemma eval_wk_qn_shift_insert : forall k e ρ,
    k <= List.length ρ ->
    ⟪wk_qn k ↑⟫ (env_insert k e ρ) = ρ.
Proof.
  induction k as [| k IH]; intros * Hk; cbn [wk_qn].
  - rewrite env_insert_zero; apply eval_wk_shift.
  - destruct ρ as [| e' ρ]; cbn [List.length] in Hk; [ lia |].
    rewrite env_insert_succ, eval_wk_q_cons by typeclasses eauto.
    rewrite IH by lia; reflexivity.
Qed.

(** ** Semantic Weakening at Position [k]

    [rel_wk_under_ctx_q] lifts a semantic weakening over one assumption; the
    telescope is [k] of those.  The entry types come from the well-formedness
    of the short context. *)
Section Fixed_GCtx.
Context {GC : GCtx}.

(** A term of a type of a universe: its type is no proposition, so the
    propositional disjunct of its relatedness ([type_propositional]) is
    impossible. *)
Ltac univ_not_propositional H :=
  let x := fresh "x" in let Hx := fresh "Hx" in let Hxp := fresh "Hxp" in
  destruct H as [(x & Hx & Hxp) | H];
  [ exfalso; cbn in Hx; inversion Hx; subst; cbn in Hxp; discriminate Hxp |].

(** A subtyping of values of a universe is not the one of propositions
    ([per_prop]), which relates only propositional values. *)
Ltac drop_per_prop :=
  try (match goal with Hp : per_prop _ _ |- _ => destruct Hp; cbn in *; discriminate end).

(** A semantic weakening evaluates, at the environments its source's PER
    relates, to their images: the proofs it needs are the target's, which
    the target's PER gives. *)
Lemma eval_sub_of_wk_under : forall {Γ Δ φ R ρ ρ'},
    Γ ⊨ʷ φ : Δ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> Dom ρ ≈ ρ' ∈ R ->
    ⟦ ι φ : Δ ⟧s ρ ↘ ctx_retag Δ (⟪φ⟫ ρ) /\ ⟦ ι φ : Δ ⟧s ρ' ↘ ctx_retag Δ (⟪φ⟫ ρ').
Proof.
  intros * [R1 HR1 R2 HR2 Hw _ _] HR Hρ.
  assert (Hirr : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hirr ρ ρ') as [Hf _].
  exact (eval_sub_of_wk_pair Hw HR2 (Hf Hρ)).
Qed.

Lemma rel_wk_under_ctx_qn : forall Δ Γ κ A,
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    ⊨ (Γ ▹{κ} A) ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊨ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΓs HΓf HA;
    cbn [tele_wk List.app length wk_qn] in *.
  - apply rel_wk_under_ctx_shift; assumption.
  - (** The head of an assumption telescope is an assumption, so the step is
        [rel_wk_under_ctx_q] with the type the short context gives it. *)
    inversion Hass as [| ? ? (κ' & T & ->) Hass']; subst.
    assert (⊢ (Δ ++ Γ)%list) by (eapply ctx_decomp_left; eassumption).
    assert (⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by (eapply ctx_decomp_left; eassumption).
    pose proof (IH _ _ _ Hass' ltac:(eassumption) ltac:(eassumption) HA) as Hψ.
    destruct (rel_ctx_wf_ass_typ (completeness_fundamental_ctx _ HΓs)) as [k Hk].
    cbn [centry_wk]; exact (rel_wk_under_ctx_q Hψ Hk).
Qed.


(** ** The Types of the Long Environment

    A type of the short context, read in an environment of the long one and
    in its image: the two values are related, at the type's level.  The
    fundamental theorem at the weakening relates the first to the type's
    value at the retagged image, and at the identity of the short context
    the value at the image to the same; evaluation under a weakening is
    only related, not equal, as a kept proof records the term as written. *)
Lemma typ_along_qn : forall Δ Γ κ A T (i : nat) ρ R,
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊨ᵗ T ≈ T at i ->
    EF (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ ∈ R ->
    exists a b, ⟦ T[wk_qn (length Δ) ↑]ʷ ⟧ ρ ↘ a /\ ⟦ T ⟧ ⟪wk_qn (length Δ) ↑⟫ ρ ↘ b /\
      Dom a ≈ b ∈ per_univ i.
Proof.
  intros * Hass HΓs HΓf HT HR Hρ.
  assert (⊨ Γ ▹{κ} A) as HA
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof (rel_wk_under_ctx_qn _ _ _ _ Hass HΓs HΓf HA) as Hψ.
  pose proof Hψ as [R1 HR1 R2 HR2 Hw _ _].
  assert (E1 : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  (** The image is an environment of the short context *)
  pose proof (Hw _ _ (proj1 (E1 _ _) Hρ)) as Hρs.
  destruct HT as [R0 HR0 HTg _].
  assert (E2 : R2 <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E2 in Hρs.
  (** Along the weakening *)
  destruct (HTg _ _ HR _ _ (rel_sub_of_wk Hψ) _ _ _ _ Hρ
                 (proj1 (eval_sub_of_wk_under Hψ HR Hρ)) (proj2 (eval_sub_of_wk_under Hψ HR Hρ)))
    as [a1 c1 ? ? Ha1 Hc1 ? ? [H1 _]].
  rewrite exp_sub_of_wk in Ha1.
  (** At the identity of the short context, at the image *)
  destruct (eval_sub_id_rel HR0 Hρs) as [Hid _].
  destruct (HTg _ _ HR0 _ _ (rel_sub_id (ex_intro _ _ HR0)) _ _ _ _ Hρs Hid Hid)
    as [b1 c2 ? ? Hb1 Hc2 ? ? [H2 _]].
  rewrite exp_sub_id in Hb1.
  assert (c2 = c1) as -> by (eapply functional_eval_exp; eassumption).
  destruct H1 as [Ra1 Ha1c], H2 as [Rb1 Hb1c].
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Ha1c (per_univ_sym _ _ _ _ Hb1c)) as (Rx & Hx & _).
  exists a1, b1; repeat split; [ exact Ha1 | exact Hb1 | exists Rx; exact Hx ].
Qed.

(** The same for a term of the short context and its type: their values in
    an environment of the long one and in its image, the types related and,
    unless the type is a proposition, the terms related at them. *)
Lemma term_along_qn : forall Δ Γ κ A M T ρ R,
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊨ M : T ->
    EF (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ∈ per_ctx_env ↘ R ->
    Dom ρ ≈ ρ ∈ R ->
    exists (k : nat) a b Rab, ⟦ T[wk_qn (length Δ) ↑]ʷ ⟧ ρ ↘ a /\ ⟦ T ⟧ ⟪wk_qn (length Δ) ↑⟫ ρ ↘ b /\
      DF a ≈ b ∈ per_univ_elem k ↘ Rab /\
      (domain_kind a = ak_propositional \/
       exists m m', ⟦ M[wk_qn (length Δ) ↑]ʷ ⟧ ρ ↘ m /\ ⟦ M ⟧ ⟪wk_qn (length Δ) ↑⟫ ρ ↘ m' /\ Dom m ≈ m' ∈ Rab).
Proof.
  intros * Hass HΓs HΓf HM HR Hρ.
  assert (⊨ Γ ▹{κ} A) as HA
    by (apply completeness_fundamental_ctx; eapply ctx_app_wf_tail; exact HΓf).
  pose proof (rel_wk_under_ctx_qn _ _ _ _ Hass HΓs HΓf HA) as Hψ.
  pose proof Hψ as [R1 HR1 R2 HR2 Hw _ _].
  assert (E1 : R <~> R1) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hw _ _ (proj1 (E1 _ _) Hρ)) as Hρs.
  destruct HM as [R0 HR0 k HMg].
  assert (E2 : R2 <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E2 in Hρs.
  (** Along the weakening, and at the identity of the short context: both
      reach the retagged image *)
  destruct (HMg _ _ HR _ _ (rel_sub_of_wk Hψ) _ _ _ _ Hρ
                 (proj1 (eval_sub_of_wk_under Hψ HR Hρ)) (proj2 (eval_sub_of_wk_under Hψ HR Hρ)))
    as (R3 & [a1 c1 ? ? Ha1 Hc1 ? ? [Hac _]] & HM1).
  destruct (eval_sub_id_rel HR0 Hρs) as [Hid _].
  destruct (HMg _ _ HR0 _ _ (rel_sub_id (ex_intro _ _ HR0)) _ _ _ _ Hρs Hid Hid)
    as (R4 & [b1 c2 ? ? Hb1 Hc2 ? ? [Hbc _]] & HM2).
  rewrite exp_sub_of_wk in Ha1; rewrite exp_sub_id in Hb1.
  assert (c2 = c1) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Hac (per_univ_sym _ _ _ _ Hbc)) as (Rab & Hab & E3).
  assert (E4 : R3 <~> R4) by (eapply per_univ_elem_left_irrel; eassumption).
  exists k, a1, b1, Rab; repeat split; [ exact Ha1 | exact Hb1 | exact Hab |].
  destruct HM1 as [(a2 & Ea2 & Hp) | [m1 m2 ? ? Hm1 Hm2 ? ? [H12 _]]].
  - left; cbn in Ea2; rewrite exp_sub_of_wk in Ea2.
    assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption); exact Hp.
  - destruct HM2 as [(a2 & Ea2 & Hp) | [n1 n2 ? ? Hn1 Hn2 ? ? [H34 _]]].
    + left; cbn in Ea2; rewrite exp_sub_id in Ea2.
      assert (a2 = b1) as -> by (eapply functional_eval_exp; eassumption).
      rewrite (per_univ_elem_kind _ _ _ _ Hab); exact Hp.
    + right; rewrite exp_sub_of_wk in Hm1; rewrite exp_sub_id in Hn1.
      assert (n2 = m2) as -> by (eapply functional_eval_exp; eassumption).
      exists m1, n1; repeat split; [ exact Hm1 | exact Hn1 |].
      assert (HP : PER R3) by (eapply per_elem_PER; exact Hac).
      apply E3; etransitivity; [ exact H12 | symmetry; apply E4; exact H34 ].
Qed.

(** ** The Long Environment

    Reading back in the short context means reading back at its initial
    environment, so the environment of the long context must be one whose image
    under the drop is exactly that.  It cannot be the long context's own
    initial environment: that would give every variable of [Δ] a level one too
    big.  So the short initial environment is used, with an entry for the
    dropped variable spliced in at position [k]: a fresh variable of its type
    ([var_per_elem]).  The entries of [Δ] keep the values and the type
    annotations they have in the short environment, which [typ_along_qn]
    shows are related to the ones the long context evaluates. *)
Lemma long_env : forall Δ Γ κ A R ρs,
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    EF (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ∈ per_ctx_env ↘ R ->
    initial_env_f (Δ ++ Γ)%list ρs ->
    exists ρ, Dom ρ ≈ ρ ∈ R /\ ⟪wk_qn (length Δ) ↑⟫ ρ = ρs.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΓs HΓf HR Hρs;
    cbn [tele_wk List.app length wk_qn] in *.
  - (** The dropped variable is outermost: the entry is a fresh variable of
        the type the context PER evaluates at the short environment. *)
    destruct (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓs)) as [RΓ HRΓ].
    destruct (per_ctx_env_cons_clean_inversion HRΓ HR) as (i & head_rel & Hhead & HAn & HE).
    pose proof (wf_ctx_scoped _ _ _ HΓs) as HsΓ.
    destruct (per_ctx_then_per_env_initial_env HRΓ HsΓ HsΓ) as (ρ0 & ρ0' & Hρ0 & Hρ0' & Hrel).
    assert (ρ0 = ρs) as -> by (eapply functional_initial_env; eassumption).
    assert (ρ0' = ρs) as -> by (eapply functional_initial_env; eassumption).
    destruct (Hhead _ _ Hrel) as [a a' Ha Ha' HRa].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (HAn _ _ Hrel) as (a0 & Ea0 & Hna); assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (var_per_elem (length Γ) HRa Hna) as Hv.
    exists (ρs ↦ ⇑! a (length Γ) ⦂ entry_type_value a); split; [| rewrite eval_wk_shift; reflexivity ].
    apply HE; unshelve eapply mk_per_ctx_env_cons_rel;
      [ exact Hrel | exact Hv | intros _; eexists; reflexivity | intros _; eexists; reflexivity
      | exact (conj (proj1 (entry_readable_of_elem HRa Hv)) (le_n 0))
      | exact (conj (proj2 (entry_readable_of_elem HRa Hv)) (le_n 0)) ].
  - (** Under an assumption of the telescope: the entry of the short initial
        environment stays as it is, at its short type, which is related to
        the long one ([typ_along_qn]). *)
    inversion Hass as [| ? ? (κ' & T & ->) Hass']; subst; cbn [centry_wk] in *.
    assert (HΓs' : ⊢ (Δ ++ Γ)%list) by (eapply ctx_decomp_left; eassumption).
    assert (HΓf' : ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by (eapply ctx_decomp_left; eassumption).
    destruct (rel_ctx_wf_per_ctx_env (completeness_fundamental_ctx _ HΓf')) as [RL HRL].
    destruct (per_ctx_env_cons_clean_inversion HRL HR) as (i & head_rel & Hhead & HAn & HE).
    inversion Hρs as [| ? ρs' ? t ? Hρs' Ht | | | |]; subst.
    destruct (IH _ _ _ _ _ Hass' HΓs' HΓf' HRL Hρs') as (ρ' & Hρ' & Himg).
    destruct (Hhead _ _ Hρ') as [a1 a1' Ha1 Ha1' HRa1].
    assert (a1' = a1) as -> by (eapply functional_eval_exp; eassumption).
    destruct (rel_ctx_wf_ass_typ (completeness_fundamental_ctx _ HΓs)) as [k HT].
    destruct (typ_along_qn _ _ _ _ _ _ _ _ Hass' HΓs' HΓf' HT HRL Hρ') as (b1 & b2 & Hb1 & Hb2 & [Rt HRt]).
    rewrite Himg in Hb2.
    assert (b1 = a1) as -> by (eapply functional_eval_exp; eassumption).
    assert (b2 = t) as -> by (eapply functional_eval_exp; eassumption).
    (** The long and the short value of [T] are related, at the larger of
        their levels, so the variable of the short type is in the head PER. *)
    set (m := max i k).
    assert (Helem' : per_univ_elem m (head_rel _ _ Hρ') a1 a1)
      by (eapply per_univ_elem_cumu_ge; [| exact HRa1 ]; lia).
    assert (HR'm : per_univ_elem m Rt a1 t) by (eapply per_univ_elem_cumu_ge; [| exact HRt ]; lia).
    assert (HR's : per_univ_elem m Rt t a1) by (apply per_univ_sym; exact HR'm).
    assert (Hiff : head_rel _ _ Hρ' <~> Rt)
      by (eapply per_univ_elem_left_irrel; [ exact Helem' | exact HR's ]).
    assert (Htt : per_univ_elem m Rt t t) by (eapply per_univ_trans; [ exact HR's | exact HR'm ]).
    destruct (HAn _ _ Hρ') as (a0 & Ea0 & Hna); assert (a0 = a1) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (proj1 (per_univ_elem_not_level_sort_iff _ _ _ _ HR'm) Hna) as Hnt.
    pose proof (var_per_elem (length (Δ ++ Γ)) Htt Hnt) as Hv.
    exists (ρ' ↦ ⇑! t (length (Δ ++ Γ)) ⦂ entry_type_value t); split;
      [| cbn [wk_qn extend_env]; rewrite eval_wk_q_cons by typeclasses eauto; rewrite Himg; reflexivity ].
    apply HE; unshelve eapply mk_per_ctx_env_cons_rel;
      [ exact Hρ' | apply Hiff; exact Hv | intros _; eexists; reflexivity | intros _; eexists; reflexivity
      | exact (conj (proj1 (entry_readable_of_elem Htt Hv)) (le_n 0))
      | exact (conj (proj2 (entry_readable_of_elem Htt Hv)) (le_n 0)) ].
Qed.


(** ** EqStr: Strengthening an Equation

    Both ends are typed in the short context, so each of them has the same
    value in the long environment under the weakening as it has in the short
    one.  The long equation links the two long values; the two instantiations
    of the ends link each long value to its short one; and the chain gives the
    short equation, read back at the short context's own length. *)
Lemma exp_eq_strengthen : forall Δ Γ κ A M N T,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ M : T ->
    (Δ ++ Γ)%list ⊢ N : T ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list
      ⊢ M[wk_qn (length Δ) ↑]ʷ ≈ N[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ M ≈ N : T.
Proof.
  intros * Hass HΓf HM HN HL.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  pose proof (completeness_fundamental_exp _ _ _ HM) as HMs.
  pose proof (completeness_fundamental_exp _ _ _ HN) as HNs.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ HL) as HLs.
  pose proof HLs as [R1 HR1 _ _].
  pose proof HMs as [R0 HR0 _ _].
  (** The environment of the long context whose image is the short initial
      one *)
  pose proof (wf_ctx_scoped _ _ _ HΓs) as Hsc.
  destruct (per_ctx_then_per_env_initial_env HR0 Hsc Hsc) as (ρs & ρs' & Hρs & Hρs' & Hrel0).
  assert (ρs' = ρs) as -> by (eapply functional_initial_env; eassumption).
  destruct (long_env _ _ _ _ _ _ Hass HΓs HΓf HR1 Hρs) as (ρ & Hρ & Himg).
  (** The long equation there; each end along the weakening *)
  destruct (rel_exp_under_ctx_simple_full_at HR1 HLs) as [i HLat].
  destruct (HLat _ _ Hρ) as (aL & aL' & RL & EaL & EaL' & HRL & HLe).
  assert (aL' = aL) as -> by (eapply functional_eval_exp; eassumption).
  destruct (term_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HMs HR1 Hρ) as (k1 & a1 & b1 & R1' & Ea1 & Eb1 & H1 & HMe).
  destruct (term_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HNs HR1 Hρ) as (k2 & a2 & b2 & R2' & Ea2 & Eb2 & H2 & HNe).
  rewrite Himg in Eb1, Eb2, HMe, HNe.
  assert (a1 = aL) as -> by (eapply functional_eval_exp; eassumption).
  assert (a2 = aL) as -> by (eapply functional_eval_exp; eassumption).
  assert (b2 = b1) as -> by (eapply functional_eval_exp; eassumption).
  pose proof (per_univ_elem_kind _ _ _ _ H1) as Hk.
  (** The short type against itself *)
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ H1) H1) as (Rbb & Hbb & E3).
  destruct (evaluated_kind_or_propositional (domain_kind aL)) as [Hr | Hp].
  - (** The ends' values are related: [⟦M⟧ρs ≈ ⟦M[φ]⟧ρ ≈ ⟦N[φ]⟧ρ ≈ ⟦N⟧ρs] *)
    destruct HLe as [Hp | (m & n & Hm & Hn & Hmn)]; [ rewrite Hp in Hr; inversion Hr |].
    destruct HMe as [Hp | (m1 & m2 & Hm1 & Hm2 & Hmm)]; [ rewrite Hp in Hr; inversion Hr |].
    destruct HNe as [Hp | (n1 & n2 & Hn1 & Hn2 & Hnn)]; [ rewrite Hp in Hr; inversion Hr |].
    assert (m1 = m) as -> by (eapply functional_eval_exp; eassumption).
    assert (n1 = n) as -> by (eapply functional_eval_exp; eassumption).
    assert (E1 : RL <~> R1') by (eapply per_univ_elem_right_irrel; eassumption).
    assert (E2 : RL <~> R2') by (eapply per_univ_elem_right_irrel; eassumption).
    assert (HP : PER R1') by (eapply per_elem_PER; exact H1).
    assert (Hm2n2 : R1' m2 n2).
    { etransitivity; [ symmetry; exact Hmm |].
      etransitivity; [ apply E1; exact Hmn |].
      apply (proj1 (E1 _ _)), (proj2 (E2 _ _)); exact Hnn. }
    destruct (per_elem_then_per_top Hbb (proj1 (E3 _ _) Hm2n2) (length (Δ ++ Γ)%list)) as [W W' HW HW' HE].
    eapply soundness_upto_proofs; [ exact HM | exact HN | | | exact HE ];
      (eapply nbe_evaluated_intro; [ exact Hρs | exact Eb1 | eassumption | eassumption | rewrite <- Hk; exact Hr ]).
  - (** A proposition: both ends are proofs of it, read back at its
        readback *)
    rewrite Hk in Hp.
    destruct (per_ctx_env_kept_proof_readable _ _ _ M HR0
                (exp_scoped_free_bound _ _ (wf_exp_scoped_term _ _ _ _ _ HM)) _ _ Hrel0) as [HPm _].
    destruct (per_ctx_env_kept_proof_readable _ _ _ N HR0
                (exp_scoped_free_bound _ _ (wf_exp_scoped_term _ _ _ _ _ HN)) _ _ Hrel0) as [HPn _].
    destruct (HPm (length (Δ ++ Γ)%list)) as [Pm HPm'], (HPn (length (Δ ++ Γ)%list)) as [Pn HPn'].
    destruct (per_univ_then_per_top_typ Hbb (length (Δ ++ Γ)%list)) as [Q _ HQ _ _].
    apply (@soundness_upto_proofs _ _ _ _ _ _ (nf_proof Q Pm) (nf_proof Q Pn) HM HN).
    + econstructor; [ exact Hρs | exact Eb1 | apply nbe_term_proof; [ exact Hp | apply read_nf_proof; [ exact Hp | exact HQ | exact HPm' ] ] ].
    + econstructor; [ exact Hρs | exact Eb1 | apply nbe_term_proof; [ exact Hp | apply read_nf_proof; [ exact Hp | exact HQ | exact HPn' ] ] ].
    + unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; change (nf_eq_upto_proofs Q Q); reflexivity.
Qed.


(** The syntactic weakening at position [k], the companion of the semantic one:
    a term of the short context is a term of the long one. *)
Lemma wf_wk_qn : forall Δ Γ κ A,
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list.
Proof.
  intros * HΓs HΓf.
  eapply wf_wk_ext; [| exact HΓf | exact HΓs ].
  (** The base case is the weakening by one, over the inserted assumption. *)
  apply wf_wk_shift; eapply ctx_app_wf_tail; exact HΓf.
Qed.


(** ** A Long Subtyping of a Short Type

    A subtyping in the long context whose left side is a short type, read
    at the long environment over the short initial one: the left value is
    related to the short type's value there, and below the right side's
    value, the shape of which its syntax gives. *)
Lemma subtyp_along_qn : forall Δ Γ κ A T X (i : nat),
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊨ᵗ T ≈ T at i ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊨ T[wk_qn (length Δ) ↑]ʷ ⊆ X ->
    exists ρs ρ' a b c (j k : nat), initial_env_f (Δ ++ Γ)%list ρs /\ ⟦ T ⟧ ρs ↘ b /\ ⟦ X ⟧ ρ' ↘ c /\
      Dom a ≈ b ∈ per_univ j /\ Sub a <: c at k.
Proof.
  intros * Hass HΓs HΓf HT [R1 HR1 k Hsg].
  pose proof HT as [R0 HR0 _ _].
  pose proof (wf_ctx_scoped _ _ _ HΓs) as Hsc.
  destruct (per_ctx_then_per_env_initial_env HR0 Hsc Hsc) as (ρs & ρs' & Hρs & Hρs' & _).
  assert (ρs' = ρs) as -> by (eapply functional_initial_env; eassumption).
  destruct (long_env _ _ _ _ _ _ Hass HΓs HΓf HR1 Hρs) as (ρ & Hρ & Himg).
  assert (HsA : ⊨ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by (eexists; exact HR1).
  destruct (eval_sub_id_rel HR1 Hρ) as [Hid Hid'].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ Hid Hid')
    as [aσ a c' c Ha1 Ha2 Hc1 Hc2 [Rl Hl] _ Hsub].
  rewrite exp_sub_id in Ha1.
  destruct (typ_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HT HR1 Hρ) as (a1 & b1 & Ea1 & Eb1 & [Rab Hab]).
  rewrite Himg in Eb1.
  assert (a1 = aσ) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hl) Hab) as (Rx & Hx & _).
  exists ρs, (ctx_retag (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ρ), a, b1, c, k, k; repeat split; try eassumption.
  exists Rx; exact Hx.
Qed.

(** The same with the short type on the right. *)
Lemma subtyp_along_qn_r : forall Δ Γ κ A T X (i : nat),
    all_assumptions Δ ->
    ⊢ (Δ ++ Γ)%list ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊨ᵗ T ≈ T at i ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊨ X ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    exists ρs ρ' a b c (j k : nat), initial_env_f (Δ ++ Γ)%list ρs /\ ⟦ T ⟧ ρs ↘ b /\ ⟦ X ⟧ ρ' ↘ c /\
      Dom a ≈ b ∈ per_univ j /\ Sub c <: a at k.
Proof.
  intros * Hass HΓs HΓf HT [R1 HR1 k Hsg].
  pose proof HT as [R0 HR0 _ _].
  pose proof (wf_ctx_scoped _ _ _ HΓs) as Hsc.
  destruct (per_ctx_then_per_env_initial_env HR0 Hsc Hsc) as (ρs & ρs' & Hρs & Hρs' & _).
  assert (ρs' = ρs) as -> by (eapply functional_initial_env; eassumption).
  destruct (long_env _ _ _ _ _ _ Hass HΓs HΓf HR1 Hρs) as (ρ & Hρ & Himg).
  assert (HsA : ⊨ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by (eexists; exact HR1).
  destruct (eval_sub_id_rel HR1 Hρ) as [Hid Hid'].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ Hid Hid')
    as [cσ c aσ a Hc1 Hc2 Ha1 Ha2 _ [Rr Hr] Hsub].
  rewrite exp_sub_id in Ha1.
  destruct (typ_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HT HR1 Hρ) as (a1 & b1 & Ea1 & Eb1 & [Rab Hab]).
  rewrite Himg in Eb1.
  assert (a1 = aσ) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hr) Hab) as (Rx & Hx & _).
  exists ρs, (ctx_retag (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ρ), a, b1, c, k, k; repeat split; try eassumption.
  exists Rx; exact Hx.
Qed.

(** ** ShapePi: a Short Type below a [Π]

    What the long context knows about a short type can be read off in the short
    one as well: a type below a [Π] there has a [Π] for its own normal form
    here.  The subtyping is taken through the PER model rather than through the
    algorithm, because the algorithm would normalize in the long context, whose
    initial environment is not the image of ours: [per_subtyp] has a [Π] on the
    left of nothing but [per_subtyp_pi], so the type's value is a [Πᵈ], and so
    is the value it has in the short environment. *)
Lemma typ_pi_shape_strengthen : forall Δ Γ κ A T i κd κc C D,
    all_assumptions Δ ->
    evaluated_kind κc ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : abs_kind_sort κc Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ a_pi κd κc C D ->
    exists C' D', nbe_ty_f (Δ ++ Γ)%list T (nf_pi κd κc C' D').
Proof.
  intros * Hass Hev HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (subtyp_along_qn _ _ _ _ _ _ _ Hass HΓs HΓf (rel_type_of_abs_kind_sort (completeness_fundamental_exp _ _ _ HT))
              (completeness_fundamental_subtyp _ _ _ Hs))
    as (ρs & ρ' & a & b & c & j & k & Hρs & Eb & Ec & [Rab Hab] & Hsub).
  (** The right-hand side is a [Πᵈ], and [per_subtyp_pi] is the only rule with
      one there, so the long value of [T] is a [Πᵈ]; so is the short one,
      [per_univ_elem] relating only values of one head.  The codomain kind
      is evaluated, so the [Πᵈ] is no proposition ([per_prop]). *)
  inversion Ec; subst.
  inversion Hsub; subst; drop_per_prop;
    try (match goal with Hp : per_prop _ _ |- _ =>
           destruct Hp as [_ Hp _]; cbn in Hp; subst; inversion Hev end).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hab) Hab) as (Rs & HRs & _).
  invert_per_univ_elem Hab.
  (** The short value reads back, and the readback of a [Πᵈ] is a [Πⁿ]. *)
  destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W _ HW1 _ _].
  inversion HW1; subst.
  do 2 eexists; econstructor; [ exact Hρs | exact Eb | exact HW1 ].
Qed.

(** ** ShapeAll: a Short Proposition below a [∀]

    The same for a proposition below a [∀]: propositions are below each
    other only as [per_prop], by equal readbacks, and the long and the short
    values of the proposition read back equally, as elements of [Prop]; the
    readback of a [∀ᵈ] is a [∀ₚⁿ]. *)
(** A normal form equal up to proofs to a [Π] is a [Π] of the same
    kinds. *)
Lemma nf_eq_upto_proofs_pi_shape : forall W κd κc C D,
    nf_eq_upto_proofs W (nf_pi κd κc C D) -> exists C' D', W = nf_pi κd κc C' D'.
Proof.
  intros [] * H; unfold nf_eq_upto_proofs in H; cbn [nf_eqb_upto_proofs] in H; try discriminate.
  repeat (apply Bool.andb_true_iff in H as [H ?]).
  repeat match goal with Hk : dec_eqb abs_kind_eq_dec _ _ = true |- _ => apply dec_eqb_true in Hk; subst end.
  eauto.
Qed.

Lemma typ_all_shape_strengthen : forall Δ Γ κ A T κd C D,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : Propₘ ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ ∀ₚ{κd} C D ->
    exists C' D', nbe_ty_f (Δ ++ Γ)%list T (∀ₚⁿ{κd} C' D').
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (subtyp_along_qn _ _ _ _ _ _ 0 Hass HΓs HΓf (rel_type_of_prop 0 (completeness_fundamental_exp _ _ _ HT))
              (completeness_fundamental_subtyp _ _ _ Hs))
    as (ρs & ρ' & a & b & c & j & k & Hρs & Eb & Ec & [Rab Hab] & Hsub).
  (** The right-hand side is a [∀ᵈ], a proposition: the subtyping is
      [per_prop], equal readbacks; the short value reads back as the long
      one does. *)
  inversion Ec; subst.
  inversion Hsub; subst;
    try (match goal with Hk : evaluated_kind ak_propositional |- _ => inversion Hk end).
  match goal with Hp : per_prop _ _ |- _ => destruct Hp as [_ _ Htop] end.
  destruct (Htop (length (Δ ++ Γ)%list)) as [Wa Wc HWa HWc HEac].
  destruct (per_univ_then_per_top_typ Hab (length (Δ ++ Γ)%list)) as [Wa' Wb HWa' HWb HEab].
  functional_read_rewrite_clear.
  inversion HWc; subst.
  destruct (nf_eq_upto_proofs_pi_shape Wb κd ak_propositional _ _ (transitivity (symmetry HEab) HEac)) as (C' & D' & ->).
  exists C', D'; econstructor; [ exact Hρs | exact Eb | exact HWb ].
Qed.

(** ** ShapeInd: a Short Type below an Inductive Type

    The same for a type below an inductive type: [per_subtyp] has an
    inductive type on the right only in [per_subtyp_indty], whose left-hand
    side is one, so the type's value is an inductive type, and so is the
    value it has in the short environment, which reads back as an inductive
    type's normal form. *)
Lemma typ_ind_shape_strengthen : forall Δ Γ κ A T i p k Ps,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ apps (a_ind p k) Ps ->
    exists Rs, nbe_ty_f (Δ ++ Γ)%list T (nf_indty p k Rs).
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (subtyp_along_qn _ _ _ _ _ _ _ Hass HΓs HΓf (rel_type_of_typ (completeness_fundamental_exp _ _ _ HT))
              (completeness_fundamental_subtyp _ _ _ Hs))
    as (ρs & ρ' & a & b & c & j & k' & Hρs & Eb & Ec & [Rab Hab] & Hsub).
  (** An inductive type is below only itself ([per_subtyp_indty]), and the
      short value is one too *)
  destruct (eval_ind_value _ _ _ _ _ Ec) as [ms ->].
  inversion Hsub; subst; drop_per_prop.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hab) Hab) as (Rs & HRs & _).
  invert_per_univ_elem Hab.
  destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W _ HW1 _ _].
  inversion HW1; subst.
  eexists; econstructor; [ exact Hρs | exact Eb | exact HW1 ].
Qed.

(** The same for a type below a record type. *)
Lemma typ_record_shape_strengthen : forall Δ Γ κ A T i p Ps,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ apps (a_record p) Ps ->
    exists Rs, nbe_ty_f (Δ ++ Γ)%list T (nf_record p Rs).
Proof.
  intros * Hass HΓf HT Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (subtyp_along_qn _ _ _ _ _ _ _ Hass HΓs HΓf (rel_type_of_typ (completeness_fundamental_exp _ _ _ HT))
              (completeness_fundamental_subtyp _ _ _ Hs))
    as (ρs & ρ' & a & b & c & j & k & Hρs & Eb & Ec & [Rab Hab] & Hsub).
  destruct (eval_record_value _ _ _ _ Ec) as [ms ->].
  inversion Hsub; subst; drop_per_prop.
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hab) Hab) as (Rs & HRs & _).
  invert_per_univ_elem Hab.
  destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W _ HW1 _ _].
  inversion HW1; subst.
  eexists; econstructor; [ exact Hρs | exact Eb | exact HW1 ].
Qed.

(** ** ShapeUniv: a Short Type above a Universe

    The same for a type above a universe: [per_subtyp] has a universe on the
    left of nothing but the three universe rules, whose right-hand sides are
    universes, so the type's value is a universe, and so is the value it has in
    the short environment, which reads back as a universe normal form. *)
Lemma typ_univ_shape_strengthen : forall Δ Γ κ A T i U,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    univ_term U ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ U ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    (exists j, nbe_ty_f (Δ ++ Γ)%list T (Typeωⁿ@j)) \/ (exists L, nbe_ty_f (Δ ++ Γ)%list T (nf_univ_of L)).
Proof.
  intros * Hass HΓf HT HU Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (subtyp_along_qn_r _ _ _ _ _ _ _ Hass HΓs HΓf (rel_type_of_typ (completeness_fundamental_exp _ _ _ HT))
              (completeness_fundamental_subtyp _ _ _ Hs))
    as (ρs & ρ' & a & b & c & j & k & Hρs & Eb & Ec & [Rab Hab] & Hsub).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hab) Hab) as (Rs & HRs & _).
  (** The left-hand side is a universe, so the right-hand one is too, and
      the short value. *)
  destruct HU; inversion Ec; subst; inversion Hsub; subst; drop_per_prop.
  all: invert_per_univ_elem Hab.
  all: destruct (per_univ_then_per_top_typ HRs (length (Δ ++ Γ)%list)) as [W _ HW1 _ _].
  all: inversion HW1; subst.
  all: first [ left; eexists; econstructor; [ exact Hρs | exact Eb | exact HW1 ]
             | right; eexists; econstructor; [ exact Hρs | exact Eb | exact HW1 ] ].
Qed.

(** ** The Semantic Subtyping, Read Back

    Two types related by [per_subtyp] read back, at every length, to normal
    forms the algorithmic subtyping relates.  It is what lets a subtyping in
    the long context be read in the short one: the long subtyping is a
    semantic one between the values the short types have in the short
    initial environment, and their readbacks are the short normal forms. *)
Lemma per_subtyp_read : forall i a b,
    Sub a <: b at i ->
    forall s, exists A B, Rtyp a in s ↘ A /\ Rtyp b in s ↘ B /\ ⊢anf A ⊆ B.
Proof.
  induction 1; intros s.
  - (** Neutrals, read back alike, at the relevant kind *)
    destruct (H1 s) as [L L' HL HL' HLL].
    do 2 eexists; split; [ econstructor; exact HL | split; [ econstructor; exact HL' |] ].
    rewrite H, H0; apply alg_subtyping_nf_refl_case; [ exact I |].
    unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; rewrite dec_eqb_refl; exact HLL.
  - do 2 eexists; split; [ econstructor | split; [ econstructor |] ]; apply alg_subtyping_nf_level; assumption.
  - do 2 eexists; split; [ econstructor | split; [ econstructor |] ]; apply alg_subtyping_nf_refl_case; [ exact I | reflexivity ].
  - do 2 eexists; split; [ econstructor | split; [ econstructor |] ]; apply alg_subtyping_nf_refl_case; [ exact I | reflexivity ].
  - do 2 eexists; split; [ econstructor | split; [ econstructor |] ]; apply alg_subtyping_nf_univ; assumption.
  - destruct (H s) as [[c xs] [d ys] HL HL' Hle _ _].
    do 2 eexists; split; [ econstructor; exact HL | split; [ econstructor; exact HL' |] ].
    apply alg_subtyping_nf_suniv; exact Hle.
  - destruct (per_lvl_reads _ _ H s) as ([c xs] & HW & _ & _).
    do 2 eexists; split; [ econstructor; exact HW | split; [ econstructor |] ].
    apply alg_subtyping_nf_small_large.
  - (** The domains read back equally; the codomains at the fresh variable are
        below each other by the induction hypothesis. *)
    assert (Ha : per_univ_elem i in_rel a a) by (eapply per_univ_trans; [ exact H0 | apply per_univ_sym; exact H0 ]).
    assert (Ha' : per_univ_elem i in_rel a' a') by (eapply per_univ_trans; [ apply per_univ_sym; exact H0 | exact H0 ]).
    pose proof (per_univ_elem_pi_domain_not_level_sort H H3) as Hna.
    pose proof (per_univ_elem_pi_domain_not_level_sort H H4) as Hna'.
    destruct (per_univ_then_per_top_typ H0 s) as [A A' HA HA' HAA].
    destruct (per_univ_elem_pi_clean_inversion H Ha H3) as [out1 [Hout1 _]].
    destruct (per_univ_elem_pi_clean_inversion H Ha' H4) as [out2 [Hout2 _]].
    destruct (Hout1 _ _ (var_per_elem s Ha Hna)) as [b ? Hb ? _].
    destruct (Hout2 _ _ (var_per_elem s Ha' Hna')) as [b' ? Hb' ? _].
    destruct (H2 _ _ _ _ (var_per_elem s H0 Hna) Hb Hb' (S s)) as (C & C' & HC & HC' & HCC').
    exists (nf_pi κd κc A C), (nf_pi κd κc A' C'); split; [| split ].
    + econstructor; [ exact HA | exact Hb | exact HC ].
    + econstructor; [ exact HA' | exact Hb' | exact HC' ].
    + apply alg_subtyping_nf_pi; [ exact H | exact HAA | exact HCC' ].
  - (** Related inductive types read back alike. *)
    destruct (per_univ_then_per_top_typ H s) as [W W' HW HW' HE].
    exists W, W'; split; [ exact HW | split; [ exact HW' |] ].
    inversion HW; subst; apply alg_subtyping_nf_refl_case; [ exact I | exact HE ].
  - (** So do related record types. *)
    destruct (per_univ_then_per_top_typ H s) as [W W' HW HW' HE].
    exists W, W'; split; [ exact HW | split; [ exact HW' |] ].
    inversion HW; subst; apply alg_subtyping_nf_refl_case; [ exact I | exact HE ].
  - (** So do related propositions, which are no universe and no [Π] into
        an evaluated kind. *)
    destruct H as [Hl Hr Htop]; destruct (Htop s) as [W W' HW HW' HE].
    exists W, W'; split; [ exact HW | split; [ exact HW' |] ].
    apply alg_subtyping_nf_refl_case; [| exact HE ].
    inversion HW; subst; cbn in Hl |- *; try discriminate; try exact I; subst; cbn; exact I.
Qed.

(** ** SubStr: Strengthening a Subtyping

    Both sides are short types, so the long subtyping is a semantic one between
    the values they have in the long environment, and those are related to the
    values they have in the short one; the readbacks of the latter are their
    short normal forms ([per_subtyp_read]), so the algorithmic subtyping holds
    in the short context, and with it the declarative one. *)
Lemma subtyp_strengthen_sort : forall Δ Γ κ A T T' S S',
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    type_sort S -> type_sort S' ->
    (Δ ++ Γ)%list ⊢ T : S ->
    (Δ ++ Γ)%list ⊢ T' : S' ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ T'[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ T ⊆ T'.
Proof.
  intros * Hass HΓf HS HS' HT HT' Hs.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; mauto 3).
  destruct (rel_type_of_sort HS (completeness_fundamental_exp _ _ _ HT)) as [i HTs].
  destruct (rel_type_of_sort HS' (completeness_fundamental_exp _ _ _ HT')) as [i' HTs'].
  apply completeness_fundamental_subtyp in Hs as [R1 HR1 k Hsg].
  pose proof HTs as [R0 HR0 _ _].
  pose proof (wf_ctx_scoped _ _ _ HΓs) as Hsc.
  destruct (per_ctx_then_per_env_initial_env HR0 Hsc Hsc) as (ρs & ρs' & Hρs & Hρs' & _).
  assert (ρs' = ρs) as -> by (eapply functional_initial_env; eassumption).
  destruct (long_env _ _ _ _ _ _ Hass HΓs HΓf HR1 Hρs) as (ρ & Hρ & Himg).
  assert (HsA : ⊨ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ≈ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by (eexists; exact HR1).
  destruct (eval_sub_id_rel HR1 Hρ) as [Hid Hid'].
  destruct (Hsg _ _ HR1 _ _ (rel_sub_id HsA) _ _ _ _ Hρ Hid Hid')
    as [aσ a a'σ a' Ha1 Ha2 Ha3 Ha4 [Rl Hl] [Rr Hr] Hsub].
  rewrite exp_sub_id in Ha1, Ha3.
  (** Both type values at the long environment are related to the short
      ones; the subtyping moves along them. *)
  destruct (typ_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HTs HR1 Hρ) as (x1 & b & Ex1 & Eb & [R2 H2]).
  destruct (typ_along_qn _ _ _ _ _ _ _ _ Hass HΓs HΓf HTs' HR1 Hρ) as (x2 & b' & Ex2 & Eb' & [R3 H3]).
  rewrite Himg in Eb, Eb'.
  assert (x1 = aσ) as -> by (eapply functional_eval_exp; eassumption).
  assert (x2 = a'σ) as -> by (eapply functional_eval_exp; eassumption).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hl) H2) as (Rx & Hx & _).
  destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hr) H3) as (Ry & Hy & _).
  pose proof (per_subtyp_transp _ _ _ _ _ _ _ Hsub Hx Hy) as Hs2.
  destruct (per_subtyp_read _ _ _ Hs2 (length (Δ ++ Γ)%list)) as (W & W' & HW & HW' & HWW').
  eapply alg_subtyping_sound_sort; [ exact HS | exact HS' | | exact HT | exact HT' ].
  econstructor; [ econstructor; [ exact Hρs | exact Eb | exact HW ]
                | econstructor; [ exact Hρs | exact Eb' | exact HW' ] | exact HWW' ].
Qed.


(** * Strengthening Normal Forms

    A normal form typed in the long context at a short type is typed at that
    type in the short context.  The induction is on the normal form, not on the
    derivation: each case inverts the long typing of its head ([CoreInversions]),
    strengthens the parts by the induction hypotheses, and moves the remaining
    subtyping and equations with [subtyp_strengthen] and [exp_eq_strengthen].
    A neutral has no type of its own to be checked against, so its statement
    returns one: a short type whose weakening is below the long one. *)

(** ** Syntactic Helpers *)

Lemma exp_wk_sub_id_extend : forall M N φ, M[Id,,N][φ]ʷ = M[wk_q φ]ʷ[Id,,N[φ]ʷ].
Proof.
  intros; rewrite exp_wk_sub_extend_head, exp_sub_wk_q_extend.
  apply exp_sub_sb_eq; pointwise_solve.
Qed.

(** A variable of the long context that is the image of a short one has the
    weakened short type. *)
Lemma lookup_strengthen : forall Δ Γ κ A x A1,
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ∋ #(wk_qn (length Δ) ↑ x) : A1 ->
    exists T, (Δ ++ Γ)%list ∋ #x : T /\ A1 = T[wk_qn (length Δ) ↑]ʷ.
Proof.
  induction Δ as [| e Δ IH]; intros * H; cbn [tele_wk List.app length wk_qn] in *.
  - inversion H; subst; eexists; split; [ eassumption | reflexivity ].
  - destruct x as [| y]; cbn in H.
    + destruct e; cbn [centry_wk] in H; inversion H; subst.
      all: eexists; split; [ constructor | rewrite exp_wk_shift_wk_q; reflexivity ].
    + inversion H; subst.
      destruct (IH _ _ _ _ _ ltac:(eassumption)) as [T [HT ->]].
      eexists; split; [ constructor; exact HT | rewrite exp_wk_shift_wk_q; reflexivity ].
Qed.

(** The level expressions: a canonical level is typed at a [Level@n] with
    atoms typed at the same [Level@n], or it is a single atom with no offset,
    which is the atom itself.  The typing rules of the level formers take
    their arguments at a common sort, and [wf_subtyp_level] moves every part
    to the sort of the whole. *)
Lemma succl_n_wf_inv : forall Γ k M C,
    Γ ⊢ succl_n (S k) M : C ->
    exists n, Γ ⊢ succl_n (S k) M : Level@n /\ Γ ⊢ Level@n ⊆ C /\ Γ ⊢ M : Level@n.
Proof.
  intros * H; cbn [succl_n] in H.
  apply wf_succl_inversion in H as (n & HM & HC).
  exists n; split; [ mauto 3 | split; [ exact HC | eapply (wf_succl_n_inversion k); exact HM ] ].
Qed.

Lemma lvl_fold_wf_list : forall Γ n xs hd,
    Γ ⊢ lvl_fold hd xs : Level@n ->
    Γ ⊢ hd : Level@n /\ List.Forall (fun p => Γ ⊢ snd p : Level@n) xs.
Proof.
  intros Γ n xs; induction xs as [| [k a] r IH]; cbn; intros hd H; [ split; [ exact H | constructor ] |].
  apply IH in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh & Ha & Hmn).
  split; [ eapply wf_exp_subtyp'; [ exact Hh | exact Hmn ] |].
  constructor; [ cbn; eapply (wf_succl_n_inversion k); eapply wf_exp_subtyp'; [ exact Ha | exact Hmn ] | exact Hr ].
Qed.

Lemma lvl_fold_maxl_inv : forall Γ xs M N C,
    Γ ⊢ lvl_fold (maxl M N) xs : C ->
    exists n, Γ ⊢ lvl_fold (maxl M N) xs : Level@n /\ Γ ⊢ Level@n ⊆ C.
Proof.
  intros Γ xs; induction xs as [| [k a] r IH]; cbn; intros * H.
  - apply wf_maxl_inversion in H as (n & ? & ? & ?); exists n; split; [ mauto 3 | assumption ].
  - apply IH in H; exact H.
Qed.

(** The constant of a fold typed at [Level@n] is a literal of a tier at most
    [n]. *)
Lemma lvl_fold_maxl_const : forall Γ c X r n,
    Γ ⊢ lvl_fold (maxl (𝕃ᵒ c) X) r : Level@n ->
    fst c <= n.
Proof.
  intros * H; apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m & Hc & _ & Hs).
  apply subtyp_level_inv in Hs; apply wf_llit_sort in Hc; lia.
Qed.

Lemma lvl_exp_of_inv : forall Γ c xs C,
    Γ ⊢ lvl_exp_of c xs : C ->
    (exists n, Γ ⊢ Level@n ⊆ C /\ fst c <= n /\ List.Forall (fun p => Γ ⊢ snd p : Level@n) xs) \/
      (exists a, c = ordinal_zero /\ xs = (0, a) :: nil).
Proof.
  intros * H; destruct xs as [| [k a] r].
  - cbn in H; left; destruct (wf_llit_inversion_sort _ _ _ _ _ H) as (n & Hcn & Hn).
    exists n; split; [ exact Hn | split; [ exact Hcn | constructor ] ].
  - destruct (o2_eq_dec c ordinal_zero) as [-> | Hc]; [ cbn in H |].
    2: assert (E : lvl_exp_of c ((k, a) :: r) = lvl_fold (maxl (𝕃ᵒ c) (succl_n k a)) r)
         by (destruct c as [[|] [|]]; [ exfalso; apply Hc; reflexivity | reflexivity .. ]);
       rewrite E in H; clear E.
    all: destruct r as [| [k' a'] r'], k as [| k]; cbn [lvl_fold] in H.
    + right; eexists; split; reflexivity.
    + left; apply succl_n_wf_inv in H as (n & ? & ? & ?); exists n;
        split; [ assumption | split; [ cbn; lia | repeat constructor; assumption ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC | split; [ cbn; lia |] ].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & ? & ? & Hmn).
      constructor; [ eapply wf_exp_subtyp'; eassumption
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC | split; [ cbn; lia |] ].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hk & ? & Hmn).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); eapply wf_exp_subtyp'; [ exact Hk | exact Hmn ]
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply wf_maxl_inversion in H as (n & Hcl & Ha & HC); exists n;
        split; [ exact HC | split; [ exact (wf_llit_sort Hcl) |] ].
      repeat constructor; cbn; exact Ha.
    + left; apply wf_maxl_inversion in H as (n & Hcl & Ha & HC); exists n;
        split; [ exact HC | split; [ exact (wf_llit_sort Hcl) |] ].
      repeat constructor; cbn; eapply (wf_succl_n_inversion (S k)); exact Ha.
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC |].
      split; [ apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m0 & H0 & _ & Hs0);
               apply subtyp_level_inv in Hs0; pose proof (lvl_fold_maxl_const _ _ _ nil _ H0); lia |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh1 & ? & Hmn).
      apply wf_maxl_inversion in Hh1 as (m' & _ & ? & Hm'm).
      assert (Γ ⊢ Level@m' ⊆ Level@n) by (etransitivity; eassumption).
      constructor; [ eapply wf_exp_subtyp'; eassumption
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
    + left; apply lvl_fold_maxl_inv in H as (n & H & HC); exists n; split; [ exact HC |].
      split; [ apply lvl_fold_hd_sort in H; apply wf_maxl_inversion in H as (m0 & H0 & _ & Hs0);
               apply subtyp_level_inv in Hs0; pose proof (lvl_fold_maxl_const _ _ _ nil _ H0); lia |].
      apply lvl_fold_wf_list in H as [Hh Hr]; apply wf_maxl_inversion in Hh as (m & Hh1 & ? & Hmn).
      apply wf_maxl_inversion in Hh1 as (m' & _ & Hk & Hm'm).
      assert (Γ ⊢ Level@m' ⊆ Level@n) by (etransitivity; eassumption).
      constructor; [ cbn; eapply (wf_succl_n_inversion (S k)); eapply wf_exp_subtyp'; [ exact Hk | eassumption ]
                   | constructor; [ cbn; eapply (wf_succl_n_inversion k'); eapply wf_exp_subtyp'; eassumption | exact Hr ] ].
Qed.

(** A path names a closed module: it is a module expression in every
    well-formed context, denoting the same there ([mdenote_closed_any]). *)
Lemma path_wf_any_ctx : forall H p Γ Γ',
    mod_qname H = Some p ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    ⊢ Γ' ->
    gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H ≈ H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hp HH HΓ'; cbn in Hp; try discriminate.
  - destruct (me_denotes _ _ _ _ _ HH) as (R & _ & Hm & _).
    destruct (mdenote_unit_inv _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) _ _ _ Hm) as (T & Φ & Hu & _).
    eapply wf_me_unit; [ exact HΓ' | exact Hu ].
  - destruct (mod_qname H) as [p0 |] eqn:E; [| discriminate ].
    pose proof (ctx_wf_gctx _ _ _ HΓ') as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as HH0; cbn in HH0.
    destruct (me_denotes _ _ _ _ _ HH) as (R & Rm & Hm & Hmd).
    destruct (desc_ok_tele _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd)
                (mdesc_mod_is_mod _ _ Hmd)) as [T HT].
    assert (Hmt : mdesc_mod_tele R = Some T) by (unfold mdesc_mod_tele; rewrite Hmd; exact HT).
    pose proof (mdenote_closed_any _ _ (wf_gstack_closed _ _ Hg) _ _ _ Γ' Hm
                  (mod_qname_scoped (me_mem H y) (qname_app p0 (y :: nil)) 0 ltac:(cbn; rewrite E; reflexivity))) as Hm'.
    eapply wf_me_mem; [ eapply IH; [ reflexivity | exact HH0 | exact HΓ' ] | exact Hm' | exact Hmt | exact Hm' | exact Hmt ].
Qed.

(** A member of a path is typed, at a closed type, in every well-formed
    context: the type it is looked up at. *)
Lemma path_mem_any_ctx : forall Γ H p x C,
    mod_qname H = Some p ->
    Γ ⊢ a_mem H x : C ->
    exists T, exp_scoped 0 T /\ Γ ⊢ T ⊆ C /\ (forall Γ', ⊢ Γ' -> Γ' ⊢ a_mem H x : T).
Proof.
  intros * Hp HM.
  remember gc_deps as Θ0 eqn:HΘ; remember gc_stack as Ξ0 eqn:HΞ.
  remember (a_mem H x) as M eqn:EM.
  revert H p x Hp EM.
  induction HM; intros Hm pm xm Hpm EMm; subst; try discriminate; try (injection EMm as <- <-).
  - (** The type the member is looked up at: closed, as the lookup reads
        nothing of the context. *)
    match goal with HH : _ ⍮ _ ⍮ _ ⊢ᵐ ?H0 ≈ ?H0, Hd : mdenote _ _ _ (me_mem ?H0 ?y) ?R, Ht : mdesc_type ?R = Some ?A0,
                    HA0 : _ ⊢ ?A0 : ?S, HS : type_sort ?S |- _ =>
      pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg;
      pose proof (wf_gstack_closed _ _ Hg) as Hc;
      assert (HHs : modexp_scoped 0 (me_mem H0 y)) by (cbn; exact (mod_qname_scoped _ _ _ Hpm));
      assert (HA : exp_scoped 0 A0)
        by (pose proof (proj1 (mdenote_scoped_all _ _ Hc) _ _ _ Hd 0 ltac:(intros ? ? Hx; lia) HHs) as HR;
            exact (mdesc_type_scoped _ _ _ HR Ht));
      exists A0; split; [ exact HA | split; [ eapply wf_subtyp_refl; [ exact HA0 | exact HS | apply wf_exp_eq_refl; exact HA0 ] |] ];
      intros Γ' HΓ';
      eapply wf_mem_desc; [ eapply path_wf_any_ctx; [ exact Hpm | exact HH | exact HΓ' ] | | exact Ht ];
      exact (mdenote_closed_any _ _ Hc _ _ _ Γ' Hd HHs) end.
  - match goal with IH : _ = _ -> _ = _ -> forall _ _ _, _ -> _ -> _ |- _ =>
      destruct (IH eq_refl eq_refl _ _ _ Hpm eq_refl) as (T & HT & HTs & HT') end.
    exists T; split; [ exact HT | split; [ etransitivity; eassumption | exact HT' ] ].
Qed.

(** [subtyp_strengthen_sort] with the two sides at universes. *)
Corollary subtyp_strengthen' : forall Δ Γ κ A T T' i j,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    (Δ ++ Γ)%list ⊢ T' : Typeω@j ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T[wk_qn (length Δ) ↑]ʷ ⊆ T'[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ T ⊆ T'.
Proof.
  intros * Hass HΓf HT HT' Hs.
  exact (subtyp_strengthen_sort _ _ _ _ _ _ _ _ Hass HΓf (type_sort_universe i) (type_sort_universe j) HT HT' Hs).
Qed.

(** Two propositions are below each other only when they are equal: a
    proposition is no universe and no [Π] ([typ_prop_absurd]). *)
Lemma subtyp_prop_eq : forall Γ P Q,
    Γ ⊢ P ⊆ Q -> Γ ⊢ P : Propₘ -> Γ ⊢ Q : Propₘ -> Γ ⊢ P ≈ Q : Propₘ.
Proof.
  intros * Hs HP HQ.
  destruct (subtyp_spec Hs)
    as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & HUV) | [(κ & κc & A1 & A2 & B1 & B2 & Hev & [k1 Ha] & _) | (m & n & _ & HPl & _)]]].
  - destruct HS as [k | |]; [| exact Heq |].
    + exfalso; assert (Γ ⊢ P : Typeω@k) by (gen_presups; assumption); eapply typ_prop_absurd; eassumption.
    + exfalso; assert (Γ ⊢ P : LevelSort) by (gen_presups; assumption); eapply level_type_not_prop; eassumption.
  - exfalso; assert (Γ ⊢ P : Typeω@k1) by (gen_presups; assumption); eapply typ_prop_absurd; eassumption.
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *.
    + assert (Γ ⊢ P : Typeω@k1) by (gen_presups; assumption); eapply typ_prop_absurd; eassumption.
    + assert (Γ ⊢ P : LevelSort) by (gen_presups; assumption); eapply level_type_not_prop; eassumption.
  - exfalso; assert (Γ ⊢ P : LevelSort) by (gen_presups; assumption); eapply level_type_not_prop; eassumption.
Qed.

(** A [Π] over a domain of a sort, into a type of a large universe, is a
    type of a large universe. *)
Lemma wf_pi_sort : forall Γ κd A B S i,
    sort_kind S κd -> Γ ⊢ A : S -> Γ ▹{κd} A ⊢ B : Typeω@i -> exists j, Γ ⊢ Π{κd} A B : Typeω@j.
Proof.
  intros * HS HA HB; inversion HS; subst.
  - exists (max i0 i); exact (wf_pi_at_max _ _ _ ak_relevant ak_relevant _ _ i0 i HA HB (pi_kinds_relevant _)).
  - exists (max 0 i); exact (wf_pi_at_max _ _ _ ak_propositional ak_relevant _ _ 0 i HA HB (pi_kinds_relevant _)).
  - exists (max 0 i); exact (wf_pi_at_max _ _ _ ak_level ak_relevant _ _ 0 i HA HB (pi_kinds_relevant _)).
Qed.

(** A [∀] over a domain of a sort, into a proposition, is a proposition. *)
Lemma wf_all_sort : forall Γ κd A P S,
    sort_kind S κd -> Γ ⊢ A : S -> Γ ▹{κd} A ⊢ P : Propₘ -> Γ ⊢ ∀ₚ{κd} A P : Propₘ.
Proof.
  intros * HS HA HP; inversion HS; subst.
  - exact (wf_pi_at_max _ _ _ ak_relevant ak_propositional _ _ i 0 HA HP (pi_kinds_prop _)).
  - exact (wf_pi_at_max _ _ _ ak_propositional ak_propositional _ _ 0 0 HA HP (pi_kinds_prop _)).
  - exact (wf_pi_at_max _ _ _ ak_level ak_propositional _ _ 0 0 HA HP (pi_kinds_prop _)).
Qed.

(** For a type the weakening fixes, such as a constant. *)
Corollary subtyp_strengthen_closed : forall Δ Γ κ A K T i j,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ K : Typeω@j ->
    (Δ ++ Γ)%list ⊢ T : Typeω@i ->
    K[wk_qn (length Δ) ↑]ʷ = K ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ K ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ K ⊆ T.
Proof.
  intros * Hass HΓf HK HT HKφ Hs; rewrite <- HKφ in Hs.
  eapply subtyp_strengthen'; eassumption.
Qed.

(** A [Π] below a [Π]: the domains are equal, at their sort (a type or a
    proposition), and the codomains below each other, under the left
    domain. *)
Lemma subtyp_pi_inv : forall Γ κ κ' A B A' B',
    Γ ⊢ Π{κ} A B ⊆ Π{κ'} A' B' ->
    κ = κ' /\ (exists S, sort_kind S κ /\ Γ ⊢ A ≈ A' : S) /\ Γ ▹{κ} A ⊢ B ⊆ B'.
Proof.
  intros * H.
  assert (exists C, Γ ⊢ Π{κ} A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  destruct (subtyp_spec_large (k := k0) H (or_introl Hk0))
    as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & HUV)
                 | (κ1 & A1 & A2 & B1 & B2 & [k1 Ha] & [k2 Hb] & (S3 & HS3 & Hab) & Hsub)]].
  - destruct (exp_eq_pi_inversion Heq) as (<- & HA & HB).
    split; [ reflexivity | split; [ exists (abs_kind_sort κ Typeω@k); split; [ apply sort_kind_abs_kind_sort | exact HA ]
                                  | eapply wf_subtyp_refl'; exact HB ] ].
  - exfalso; destruct (univ_sub_sort_term HUV) as [HUt _].
    eapply (pi_sort_term_absurd HUt); exact HU.
  - destruct (exp_eq_pi_inversion Ha) as (<- & HA1 & HA2).
    destruct (exp_eq_pi_inversion Hb) as (<- & HB1 & HB2).
    destruct (exp_eq_trans_sort_kind (sort_kind_abs_kind_sort κ k1) HS3 HA1 Hab) as (S4 & HS4 & HAB1).
    assert (HId : Γ ▹{κ} A ⊢ˢ Id : Γ ▹{κ} B1) by exact (sub_id_extend_of_exp_eq HS4 HAB1).
    split; [ reflexivity | split; [ exact (exp_eq_trans_sort_kind HS4 (sort_kind_abs_kind_sort κ k2) HAB1 HB1) |] ].
    etransitivity; [ eapply wf_subtyp_refl'; exact HA2 |].
    etransitivity; [ eapply ctxsub_subtyp; [ exact HId | exact Hsub ] |].
    eapply wf_subtyp_refl', ctxsub_exp_eq; [ exact HId | exact HB2 ].
Qed.

(** A [Π] into an evaluated kind is of the sort at that kind, at some
    index: a large universe ([wf_pi_typed_large]) or [LevelSort]. *)
Lemma wf_pi_typed_kind : forall {Γ κd κc A B C},
    evaluated_kind κc -> Γ ⊢ a_pi κd κc A B : C -> exists k, Γ ⊢ a_pi κd κc A B : abs_kind_sort κc Typeω@k.
Proof.
  intros * [] H; [ exact (wf_pi_typed_large H) |].
  destruct (wf_pi_inversion_at H) as [U HU HA HB Hk _].
  exists 0; change (abs_kind_sort ak_level Typeω@0) with (abs_kind_sort ak_level U); eapply wf_pi; eassumption.
Qed.

(** The parts of a [Π]: its kinds are those of a [Π], its domain is of a
    sort at its kind, and its codomain of the sort at its kind at some
    index, a small universe moved to a large one. *)
Lemma wf_pi_parts : forall {Γ κd κc A B C}, Γ ⊢ a_pi κd κc A B : C ->
    pi_kinds κd κc /\ (exists S, sort_kind S κd /\ Γ ⊢ A : S) /\ exists i, Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i.
Proof.
  intros * H.
  destruct (wf_pi_inversion_at H) as [U HU HA HB Hk _].
  split; [ exact Hk |].
  destruct (pi_domain_eq_sort HU HA HA (wf_exp_eq_refl HA)) as (S & HS & HA' & _).
  split; [ exists S; split; assumption |].
  inversion HU; subst; destruct κc; cbn [abs_kind_sort exp_wk] in HB |- *; try (exists 0; exact HB); try (eexists; exact HB).
  assert (⊢ Γ ▹{κd} A) by (gen_presups; assumption).
  assert (Γ ▹{κd} A ⊢ʷ ↑ : Γ) by mauto 2.
  assert (Γ ▹{κd} A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ (Level@n)); eassumption).
  exists 0; eapply wf_exp_suniv_large; eassumption.
Qed.

(** An equation at the sort of an evaluated kind is a subtyping. *)
Lemma subtyp_of_exp_eq_kind : forall {Γ A B κc k},
    evaluated_kind κc -> Γ ⊢ A ≈ B : abs_kind_sort κc Typeω@k -> Γ ⊢ A ⊆ B.
Proof.
  intros * Hev H.
  eapply wf_subtyp_refl; [ gen_presups; eassumption | destruct Hev; constructor | exact H ].
Qed.

(** A [Π] below a [Π] into the same evaluated kind: the domains are
    equal, at their sort, and the codomains below each other, under the
    left domain.  The middle of [subtyp_spec]'s [Π] disjunct is into the
    same kind: a type of levels is of no large universe. *)
Lemma subtyp_pi_kind_inv : forall Γ κ κ' κc A B A' B',
    evaluated_kind κc ->
    Γ ⊢ a_pi κ κc A B ⊆ a_pi κ' κc A' B' ->
    κ = κ' /\ (exists S, sort_kind S κ /\ Γ ⊢ A ≈ A' : S) /\ Γ ▹{κ} A ⊢ B ⊆ B'.
Proof.
  intros * Hev H.
  assert (exists C, Γ ⊢ a_pi κ κc A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_kind Hev HC) as [k0 Hk0].
  destruct (subtyp_spec H)
    as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & HUV)
       | [(κ1 & κc1 & A1 & A2 & B1 & B2 & Hev1 & [k1 Ha] & [k2 Hb] & (S3 & HS3 & Hab) & Hsub) | (m & n & _ & HL & _)]]].
  - assert (exists k, Γ ⊢ a_pi κ κc A B ≈ a_pi κ' κc A' B' : abs_kind_sort κc Typeω@k) as [k Heq']
      by (eapply exp_eq_kind_sort; [ exact HS | exact Hev | exact Heq | left; exact Hk0 ]).
    destruct (exp_eq_pi_kind_inversion Hev Heq') as (<- & HA & HB).
    split; [ reflexivity | split; [ exact HA | exact (subtyp_of_exp_eq_kind Hev HB) ] ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *.
    + destruct (univ_sub_sort_term HUV) as [HUt _]; eapply (pi_sort_term_absurd HUt); exact HU.
    + assert (Γ ⊢ a_pi κ ak_level A B : Typeω@k1) by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
  - assert (κc1 = κc) as ->.
    { destruct Hev, Hev1; cbn [abs_kind_sort] in *; try reflexivity; exfalso;
        (assert (Γ ⊢ a_pi κ _ A B : LevelSort) by (gen_presups; first [ exact Hk0 | eassumption ]));
        (assert (exists k, Γ ⊢ a_pi κ _ A B : Typeω@k) as [? ?] by (gen_presups; eexists; first [ exact Hk0 | eassumption ]));
        eapply level_type_not_large; eassumption. }
    destruct (exp_eq_pi_kind_inversion Hev Ha) as (<- & (S1 & HS1 & HA1) & HA2).
    destruct (exp_eq_pi_kind_inversion Hev Hb) as (<- & (S2 & HS2 & HB1) & HB2).
    destruct (exp_eq_trans_sort_kind HS1 HS3 HA1 Hab) as (S4 & HS4 & HAB1).
    assert (HId : Γ ▹{κ} A ⊢ˢ Id : Γ ▹{κ} B1) by exact (sub_id_extend_of_exp_eq HS4 HAB1).
    split; [ reflexivity | split; [ exact (exp_eq_trans_sort_kind HS4 HS2 HAB1 HB1) |] ].
    etransitivity; [ exact (subtyp_of_exp_eq_kind Hev HA2) |].
    etransitivity; [ eapply ctxsub_subtyp; [ exact HId | exact Hsub ] |].
    eapply (subtyp_of_exp_eq_kind Hev), ctxsub_exp_eq; [ exact HId | exact HB2 ].
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *.
    + assert (Γ ⊢ a_pi κ ak_relevant A B : LevelSort) by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
    + eapply exp_eq_level_pi_level_absurd; symmetry; exact HL.
Qed.

(** A type above a type of levels is a type of levels: a type of levels is
    of no large universe and below only types of levels ([subtyp_spec]). *)
Lemma subtyp_level_type_right : forall {Γ T B}, Γ ⊢ T : LevelSort -> Γ ⊢ T ⊆ B -> Γ ⊢ B : LevelSort.
Proof.
  intros * HT H.
  destruct (subtyp_spec H)
    as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & HUV)
       | [(κ1 & κc1 & A1 & A2 & B1 & B2 & Hev1 & [k1 Ha] & [k2 Hb] & _ & _) | (m & n & _ & HL & HR)]]].
  - assert (Γ ⊢ T : S) by (gen_presups; assumption).
    rewrite (level_type_sort_unique HS HT ltac:(eassumption)) in Heq; gen_presups; assumption.
  - exfalso; assert (Γ ⊢ T : Typeω@k1) by (gen_presups; assumption); eapply level_type_not_large; eassumption.
  - destruct Hev1; cbn [abs_kind_sort] in *.
    + exfalso; assert (Γ ⊢ T : Typeω@k1) by (gen_presups; assumption); eapply level_type_not_large; eassumption.
    + gen_presups; assumption.
  - gen_presups; assumption.
Qed.

(** A [∀] below a [∀]: the domains are equal, at their sort, and the
    propositions below each other, under the left domain. *)
Lemma subtyp_all_inv : forall Γ κ κ' A P A' P',
    Γ ⊢ ∀ₚ{κ} A P ⊆ ∀ₚ{κ'} A' P' ->
    κ = κ' /\ (exists S, sort_kind S κ /\ Γ ⊢ A ≈ A' : S) /\ Γ ▹{κ} A ⊢ P ⊆ P'.
Proof.
  intros * H.
  assert (exists C, Γ ⊢ ∀ₚ{κ} A P : C) as [C HC] by (gen_presups; eexists; eassumption).
  assert (exists C', Γ ⊢ ∀ₚ{κ'} A' P' : C') as [C' HC'] by (gen_presups; eexists; eassumption).
  pose proof (prop_former_typed HC ltac:(right; right; left; do 3 eexists; reflexivity)) as H1.
  pose proof (prop_former_typed HC' ltac:(right; right; left; do 3 eexists; reflexivity)) as H2.
  destruct (exp_eq_all_inversion (subtyp_prop_eq _ _ _ H H1 H2)) as (<- & [i Hd] & HP).
  split; [ reflexivity | split; [ exists (abs_kind_sort κ Typeω@i); split; [ apply sort_kind_abs_kind_sort | exact Hd ] |] ].
  assert (Γ ▹{κ} A ⊢ P' : Propₘ) by (gen_presups; assumption).
  eapply wf_subtyp_refl; [ eassumption | constructor | exact HP ].
Qed.

(** A type above a [Π] is a [Π]. *)
Lemma subtyp_pi_left_shape : forall Γ κ A B T,
    Γ ⊢ Π{κ} A B ⊆ T ->
    exists A' B' k, Γ ⊢ T ≈ Π{κ} A' B' : Typeω@k.
Proof.
  intros * H.
  assert (exists C, Γ ⊢ Π{κ} A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_large HC) as [k0 Hk0].
  destruct (subtyp_spec_large (k := k0) H (or_introl Hk0))
    as [[k Heq] | [(U & V & [k1 HU] & [k2 HV] & HUV) | (κ1 & A1 & A2 & B1 & B2 & [k1 Ha] & [k2 Hb] & _ & _)]].
  - do 3 eexists; symmetry; exact Heq.
  - exfalso; destruct (univ_sub_sort_term HUV) as [HUt _].
    eapply (pi_sort_term_absurd HUt); exact HU.
  - destruct (exp_eq_pi_inversion Ha) as (<- & _ & _).
    do 3 eexists; symmetry; exact Hb.
Qed.

(** ** The Arguments of an Application of a Head of a [Π] over a Telescope

    A head every type of which is above a [Π] over a telescope, applied to
    as many arguments, has them of the instances of the telescope's types. *)
Lemma wf_apps_ctx_pi_inv : forall n Δ Γ B i M Ms T,
    List.length Δ = n ->
    all_assumptions Δ -> ⊢ (Δ ++ Γ)%list -> (Δ ++ Γ)%list ⊢ B : Typeω@i ->
    (forall T', Γ ⊢ M : T' -> Γ ⊢ ctx_pi Δ B ⊆ T') ->
    List.length Ms = List.length Δ ->
    Γ ⊢ apps M Ms : T ->
    forall k N T', List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T' -> Γ ⊢ N : T'.
Proof.
  induction n as [| n IH]; intros * Hn Hass HΔ HB HP Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; intros [|] ? ? H; discriminate.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ (SA & HSA & HA0)].
    cbn [apps_exp] in HMs.
    (** The first argument, of the first type. *)
    assert (Happ : forall T', Γ ⊢ M $ M0 : T' -> Γ ⊢ M0 : A0 /\ Γ ⊢ (ctx_pi Δ B)[Id,,M0] ⊆ T').
    { intros T' HT'.
      destruct (wf_app_inversion HT') as [κd κc X Y HM HM0 HYT].
      pose proof (HP _ HM) as Hs; rewrite ctx_pi_snoc in Hs.
      (** A function is no proof of a [∀], nor a [Π] of levels; the [Π]
          above is one into types *)
      destruct κc; [| exfalso; exact (subtyp_pi_all_absurd Hs) |].
      2:{ exfalso.
          assert (exists C, Γ ⊢ a_pi κd ak_level X Y : C) as [C0 HC0] by (gen_presups; eexists; eassumption).
          destruct (wf_pi_inversion_at HC0) as [U HU HX HY Hk _].
          assert (HL : Γ ⊢ a_pi κd ak_level X Y : abs_kind_sort ak_level U) by (eapply wf_pi; eassumption).
          assert (exists C, Γ ⊢ Π{κ0} A0 (ctx_pi Δ B) : C) as [C1 HC1] by (gen_presups; eexists; eassumption).
          destruct (wf_pi_typed_large HC1) as [k1 Hk1].
          cbn [abs_kind_sort] in HL.
          discriminate (subtyp_same_kind _ _ _ ak_relevant ak_level k1 0 Hs Hk1 HL). }
      destruct (subtyp_pi_inv _ _ _ _ _ _ _ Hs) as (<- & (S & HS & HAX) & HBY).
      assert (HM0' : Γ ⊢ M0 : A0)
        by (eapply exp_conv_sort; [ exact (sort_kind_type_sort _ _ HS) | symmetry; exact HAX | exact HM0 ]).
      split; [ exact HM0' |].
      etransitivity; [| exact HYT ].
      eapply sub_preserves_subtyp; [ exact HBY | eapply wf_sub_single; [ exact HA0 | exact HSA | exact HM0' ] ]. }
    destruct (wf_apps_head _ _ _ HMs) as (T1 & HT1).
    destruct (Happ _ HT1) as [HM0 _].
    pose proof (wf_sub_single _ _ _ _ _ _ _ HA0 HSA HM0) as Hs.
    assert (HΔ' : ⊢ (tele_sub Δ (Id,,M0) ++ Γ)%list) by (eapply ctx_sub_wf; eassumption).
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
    intros [| k'] N T' HN HT'.
    + cbn in HN; injection HN as <-.
      rewrite tele_insts_snoc in HT'; cbn in HT'; injection HT' as <-; rewrite exp_sub_id; exact HM0.
    + cbn in HN.
      eapply (IH (tele_sub Δ (Id,,M0)) Γ (B[sb_qn (List.length Δ) (Id,,M0)]) i (M $ M0) Ms T);
        [ rewrite length_tele_sub; lia | apply all_assumptions_sub; exact Hass | exact HΔ'
        | exact (sub_preserves_exp _ _ _ _ _ _ _ HB Hs') | | rewrite length_tele_sub; lia | exact HMs | exact HN |].
      * intros T'' HT''; destruct (Happ _ HT'') as [_ H']; rewrite ctx_pi_sub in H'; exact H'.
      * rewrite tele_insts_snoc in HT'; cbn [List.nth_error] in HT'.
        rewrite tele_insts_tele_sub; rewrite <- HT'; f_equal.
        apply tele_insts_sb_eq; apply sb_compose_id_right.
Qed.

(** The parameters of a member's type former applied, typed at the
    member's telescope. *)
Lemma wf_ind_apps_inv : forall Γ p D k Mk Ms T, ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    Γ ⊢ apps (a_ind p k) Ms : T -> List.length Ms = im_np D Mk ->
    forall j P T', List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T' -> Γ ⊢ P : T'.
Proof.
  intros * Hl Hk HMs HMl.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ) as [i Hi].
  pose proof (decl_closed_params_ass D k Mk Hc Hk) as Hass.
  pose proof (ctx_pi_inv_outer _ _ _ _ Hass Hi) as HB.
  assert (HPΓ : ⊢ (im_params D Mk ++ Γ)%list) by (gen_presups; assumption).
  eapply (wf_apps_ctx_pi_inv _ (im_params D Mk) Γ _ i (a_ind p k) Ms T eq_refl Hass HPΓ HB);
    [ | rewrite length_im_params; exact HMl | exact HMs ].
  intros T' HT'; destruct (wf_ind_inversion HT') as [D' Mk' Hl' Hk' _ Hsub].
  assert (D' = D) as -> by congruence; assert (Mk' = Mk) as -> by congruence; exact Hsub.
Qed.

(** ** Record Types, Applied *)

(** The parameters of a record's type former applied, typed at the
    parameters' telescope. *)
Lemma wf_record_apps_inv : forall Γ p R Ms T, record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢ apps (a_record p) Ms : T -> List.length Ms = List.length (record_params R) ->
    forall j P T', List.nth_error Ms j = Some P -> List.nth_error (tele_insts (record_params R) Id Ms) j = Some T' -> Γ ⊢ P : T'.
Proof.
  intros * Hl HMs HMl.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (wf_record_own_apps _ _ _ _ _ _ _ HMs Hl) as Hrt.
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  pose proof (closed_weaken_exp _ _ _ _ _ HΓ Hty (record_ty_scoped _ Hc) ltac:(cbn; exact I)) as HtyΓ.
  unfold record_ty in HtyΓ.
  pose proof (ctx_pi_inv_outer _ _ _ _ Hass HtyΓ) as HB.
  assert (HPΓ : ⊢ (record_params R ++ Γ)%list) by (gen_presups; assumption).
  eapply (wf_apps_ctx_pi_inv _ (record_params R) Γ _ i (a_record p) Ms T eq_refl Hass HPΓ HB); [ | exact HMl | exact HMs ].
  intros T' HT'; destruct (wf_record_inversion HT') as [R' Hl' _ _ _ _ _ _ _ Hsub].
  rewrite Hl in Hl'; injection Hl' as <-; exact Hsub.
Qed.

(** A record type former applied and typed at a universe is applied to all
    its parameters: its value is a record type, which the PER model relates
    only at all of them. *)
Lemma wf_record_apps_len : forall Γ p R Ms i, record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢ apps (a_record p) Ms : Typeω@i -> List.length Ms = List.length (record_params R).
Proof.
  intros * Hl H.
  pose proof (wf_ctx_scoped_exp H) as Hsc.
  apply wf_exp_eq_refl, completeness_fundamental_exp_eq in H.
  destruct (rel_typ_under_ctx_at_initial_env Hsc H) as [ρ [a [a' [Hρ [Ha [Ha' [R0 HR]]]]]]].
  apply Modules.eval_apps_exp in Ha as (f & Ef & Hargs).
  inversion Ef; subst; apply Modules.eval_app_args_record in Hargs as (xs & Exs & Eap).
  apply eval_apps_record_inv in Eap; cbn in Eap; subst.
  destruct (eval_record_value _ _ _ _ Ha') as [ys ->].
  invert_per_univ_elem HR.
  match goal with H' : record_lookup _ _ p = Some ?R1 |- _ => rewrite Hl in H'; injection H' as <- end.
  rewrite <- (Completeness.Inductives.Model.eval_exps_length _ _ _ Exs); assumption.
Qed.

(** A record's type former, typed at its type in every context, which is a
    type. *)
Lemma record_former_typed : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    exists j, Γ ⊢ a_record p : record_ty R /\ Γ ⊢ record_ty R : Typeω@j.
Proof.
  intros * HΓ Hl.
  destruct (record_params_facts _ _ _ HΓ Hl) as (Ht & Hc & _).
  pose proof (typed_sort _ _ _ Ht) as HS.
  destruct (wf_is_univ_typ HS) as [i Hi].
  assert (HP : ⊢ (record_params R ++ ⋅)%list) by (rewrite List.app_nil_r; exact (presup_is_univ_ctx HS)).
  destruct (ctx_pi_wf _ _ (record_params R) ⋅ (record_sort R) i HP ltac:(rewrite List.app_nil_r; exact Hi)) as [j Hj].
  exists j; split.
  - eapply wf_record; [ exact HΓ | exact Hl | exact (typed_nodup _ _ _ Ht) | exact (typed_params_ass _ _ _ Ht) | exact Hj
                      | exact (record_typed_fctx_wf _ _ _ Ht _ (le_n _)) | exact HS | exact (typed_fields _ _ _ Ht)
                      | exact (typed_kinds_length _ _ _ Ht) | exact (typed_field_kinds _ _ _ Ht) ].
  - exact (closed_weaken_exp _ _ _ _ _ HΓ Hj (record_ty_scoped _ Hc) ltac:(cbn; exact I)).
Qed.

(** The parameters and the fields of a tuple before the field [k], typed
    at the instances of the fields' telescope, from their typings at their
    types. *)
Lemma tuple_prefix_insts : forall Γ R Ns (fs : list (String.string * exp)), all_assumptions (record_params R) ->
    List.length Ns = List.length (record_params R) -> List.map fst fs = List.map fst (record_fields R) ->
    (forall j N B, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some B -> Γ ⊢ N : B) ->
    forall k, k <= List.length (record_fields R) ->
    (forall j f M U, j < k -> List.nth_error fs j = Some (f, M) -> List.nth_error (record_fields R) j = Some (f, U) ->
       Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn j (List.map snd fs))]) ->
    forall j N B, List.nth_error (Ns ++ List.firstn k (List.map snd fs)) j = Some N ->
      List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ List.firstn k (List.map snd fs))) j = Some B ->
      Γ ⊢ N : B.
Proof.
  intros * Hass Hn Hfs HNs k Hk HMs j N B HN HB.
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  rewrite tele_insts_app in HB by (try exact Hass; exact Hn).
  assert (HlT : List.length (tele_insts (record_params R) Id Ns) = List.length Ns)
    by (rewrite length_tele_insts by exact Hass; lia).
  destruct (Nat.lt_ge_cases j (List.length Ns)) as [Hj | Hj].
  - rewrite List.nth_error_app1 in HN by exact Hj; rewrite List.nth_error_app1 in HB by lia.
    exact (HNs _ _ _ HN HB).
  - rewrite List.nth_error_app2 in HN by exact Hj; rewrite List.nth_error_app2, HlT in HB by lia.
    set (j' := j - List.length Ns) in *.
    rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j' k) as [Hj'k |]; [| discriminate ].
    rewrite List.nth_error_map in HN.
    destruct (List.nth_error fs j') as [[g M] |] eqn:Hg; cbn in HN; [ injection HN as <- | discriminate ].
    destruct (nth_error_lt_some (record_fields R) j' ltac:(lia)) as [[f U] Hj'].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hj') as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    destruct (tele_insts_nth _ _ _ _ _ HB) as (κ0 & A0 & HA0 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, nth_error_firstn_lt in HA0 by exact Hj'k.
    destruct (Completeness.Records.Model.field_tele_nth _ _ _ _ HA0) as (f' & Hf' & _).
    rewrite Hj' in Hf'; injection Hf' as _ <-.
    rewrite <- sb_of_list_app, List.firstn_firstn, Nat.min_l by lia.
    exact (HMs _ _ _ _ Hj'k Hg Hj').
Qed.

(** The fields of a tuple, typed one after the other: each at its type,
    a type once the fields before it are typed. *)
Lemma tuple_fields_typed_seq : forall Γ p R Ns (fs : list (String.string * exp)),
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) -> List.map fst fs = List.map fst (record_fields R) ->
    (forall j N B, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some B -> Γ ⊢ N : B) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       (exists S, type_sort S /\ Γ ⊢ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : S) ->
       Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
      Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))].
Proof.
  intros * Hrt Hl Hn Hfs HNs HMs.
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  intros k; induction k as [k IH] using lt_wf_ind; intros f M U Hk Hfk.
  assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
  apply (HMs _ _ _ _ Hk Hfk).
  pose proof (tuple_prefix_insts _ _ _ _ Hass Hn Hfs HNs k ltac:(lia)
                ltac:(intros j g M' U' Hj HM' HU'; exact (IH j Hj _ _ _ HM' HU'))) as Hins.
  assert (Hl1 : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
    by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
  destruct (record_field_typ_cong _ _ _ R k f U _ _ Hc Hass HF HΓ Hfk Hl1 Hl1
              ltac:(intros j0 N N' B HN HN' HB; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (Hins _ _ _ HN HB)))
    as (S & HS' & HUU).
  exists S; split; [ exact HS' | gen_presups; assumption ].
Qed.

(** Two equal record types at their type formers have one path, and
    as many parameters. *)
Lemma exp_eq_record_apps_head : forall Γ p p' R X Y i,
    Γ ⊢ apps (a_record p) X ≈ apps (a_record p') Y : Typeω@i ->
    record_lookup gc_deps gc_stack p' = Some R -> List.length Y = List.length (record_params R) ->
    p = p' /\ List.length X = List.length (record_params R).
Proof.
  intros * H Hl HYl.
  pose proof (wf_ctx_scoped_exp_eq H) as Hsc.
  apply completeness_fundamental_exp_eq in H.
  destruct (rel_typ_under_ctx_at_initial_env Hsc H) as [ρ [a [a' [Hρ [Ha [Ha' [R0 HR]]]]]]].
  apply Modules.eval_apps_exp in Ha as (f & Ef & Hargs).
  inversion Ef; subst; apply Modules.eval_app_args_record in Hargs as (xs & Exs & Eap).
  apply eval_apps_record_inv in Eap; cbn in Eap; subst.
  destruct (eval_record_value _ _ _ _ Ha') as [ys ->].
  invert_per_univ_elem HR.
  match goal with H' : record_lookup _ _ p' = Some ?R1 |- _ => rewrite Hl in H'; injection H' as <- end.
  split; [ reflexivity |].
  rewrite <- (Completeness.Inductives.Model.eval_exps_length _ _ _ Exs); assumption.
Qed.

(** ** Instances of Telescopes

    An entry of a telescope instantiated at terms of the instances of the
    entries before it is a type of a sort ([type_sort]): a type or a
    proposition; so terms each typed at its instance once that instance is
    a type are all typed. *)
Lemma tele_insts_typed : forall Δ Γ0 Γ σ Ms,
    all_assumptions Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ : Γ0 ->
    forall j T, List.nth_error (tele_insts Δ σ Ms) j = Some T ->
      (forall j' N T', j' < j -> List.nth_error Ms j' = Some N -> List.nth_error (tele_insts Δ σ Ms) j' = Some T' ->
         Γ ⊢ N : T') ->
      exists S, type_sort S /\ Γ ⊢ T : S.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ j T HT HMs.
  - unfold tele_insts in HT; cbn in HT; destruct Ms, j; discriminate.
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    destruct Ms as [| M0 Ms].
    + unfold tele_insts in HT; rewrite List.rev_app_distr in HT; cbn in HT; destruct j; discriminate.
    + rewrite tele_insts_snoc in HT, HMs.
      rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
      destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 (SA & HSk & HA0)].
      pose proof (sort_kind_type_sort _ _ HSk) as HS.
      destruct j as [| j]; cbn in HT.
      * injection HT as <-; exists SA; split; [ exact HS | exact (sub_preserves_sort _ _ _ _ _ _ _ HA0 HS Hσ) ].
      * eapply IH; [ exact Hass | exact HΔ | | exact HT |].
        -- eapply wf_sub_extend; [ exact Hσ | exact HA0 | exact HSk |].
           apply (HMs 0); [ lia | reflexivity | reflexivity ].
        -- intros j' N T' Hj' HN HT'; apply (HMs (S j')); [ lia | exact HN | exact HT' ].
Qed.

Lemma tele_insts_typed_all : forall Δ Γ0 Γ σ Ms,
    all_assumptions Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ : Γ0 ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T ->
       (exists S, type_sort S /\ Γ ⊢ T : S) -> Γ ⊢ N : T) ->
    forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * Hass HΔ Hσ HMs j; induction j as [j IH] using lt_wf_ind; intros N T HN HT.
  apply (HMs j); [ exact HN | exact HT |].
  eapply tele_insts_typed; [ exact Hass | exact HΔ | exact Hσ | exact HT |].
  intros j' N' T' Hj' HN' HT'; exact (IH j' Hj' _ _ HN' HT').
Qed.

(** ** A Member's Type at the Parameters of its Type Former

    The type of the member [m] of the group at [p], at the uniform
    parameters [Us], is that of the declared member [k] of the group at
    [pc] ([im_ref]) at the member's uniform arguments ([im_pre]) and its
    non-uniform parameters.  Parameters [Rs] of that type former whose
    uniform ones are equal to the member's uniform arguments give the
    member's non-uniform parameters. *)

(** What parameters [Rs] of the type former of [k] at [pc] give the member
    [m], [Mm], of the group [D] at [p], at the uniform parameters [Us]:
    non-uniform parameters [Ns] of the member, and the equality of the two
    types. *)
Record mty_params_link (Γ : ctx) (p : qname) (D : ind_decl) (m : nat) (Mm : imember) (Us Ns : list exp)
    (pc : qname) (k : nat) (Rs : list exp) : Prop := mk_mty_params_link
  { (** As many as the member has *)
    link_nparams_length : List.length Ns = im_nn Mm
    (** Each at the member's non-uniform telescope at [Us] *)
  ; link_nparams_typed : forall j N T, List.nth_error Ns j = Some N ->
      List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T
    (** The type former at [Rs] is the member's type at [Us] and [Ns] *)
  ; link_types_equal : exists i, Γ ⊢ apps (a_ind pc k) Rs ≈ ind_mty p D m Us Ns : Typeω@i }.

(** A member with a block of an eliminator is not a record view: those
    come last, past the blocks. *)
Lemma block_member_not_rview : forall D (Bks : list eblock) k Mk b, rview_suffix_ok D ->
    List.length Bks = ind_nblk D -> ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> im_is_rview Mk = false.
Proof.
  intros * Hs Hl Hk Hb; destruct (im_is_rview Mk) eqn:E; [| reflexivity ].
  apply (Hs _ _ Hk) in E.
  assert (k < List.length Bks) by (apply List.nth_error_Some; congruence); lia.
Qed.

(** The uniform arguments of a member's type at typed uniform parameters
    are typed at its type former's uniform telescope.  Not at a record
    view: its type is a record type, not an inductive type former's
    application, and its "uniform arguments" are the record's
    parameters. *)
Lemma im_pre_typed : forall Γ p D m Mm pc k Dq Us,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_is_rview Mm = false ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length (im_pre Mm Us) = ind_nu Dq /\
    forall j N T, List.nth_error (im_pre Mm Us) j = Some N ->
      List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * HΓ Hl Hm Hnr Hr Hlq HUl HUs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  unfold im_ref, im_pre in *;
    destruct (im_head Mm) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-;
    [| | exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate ].
  - assert (Dq = D) as -> by congruence; split; [ exact HUl | exact HUs ].
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _ & _ & HIl & _).
    assert (D' = Dq) as -> by congruence.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    split; [ rewrite List.length_map; exact HIl |].
    intros j N T HN HT.
    rewrite <- (tele_insts_sub (ind_uparams Dq) 0 Id Id (sb_of_list Id Us) Is (decl_closed_ass _ Hcq) (decl_closed_uparams _ Hcq)
                  ltac:(intros; lia)) in HT.
    apply nth_error_map_inv in HN as (I & HI & ->); apply nth_error_map_inv in HT as (T0 & HT0 & ->).
    exact (sub_preserves_exp _ _ _ _ _ _ _ (decl_typed_view_is _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq HI HT0) Hσ).
Qed.

(** The group of a member's type former is filed, and has that member. *)
Lemma im_ref_lookup : forall Γ p D m Mm pc k,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    exists Dq, ind_lookup gc_deps gc_stack pc = Some Dq.
Proof.
  intros * HΓ Hl Hm Hr.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-; [ eauto | | eauto ].
  destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _); eauto.
Qed.

Lemma im_ref_member : forall Γ p D m Mm pc k Dq,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> exists Mk, ind_member Dq k = Some Mk.
Proof.
  intros * HΓ Hl Hm Hr Hlq.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; eauto.
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _).
    assert (D' = Dq) as -> by congruence; eauto.
  - assert (Dq = D) as -> by congruence; eauto.
Qed.

(** A member has as many non-uniform parameters as the member of its type
    former. *)
Lemma im_ref_nn : forall Γ p D m Mm pc k Dq Mk,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) ->
    ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk -> im_nn Mm = im_nn Mk.
Proof.
  intros * HΓ Hl Hm Hr Hlq Hk.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k1 Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-.
  - assert (Dq = D) as -> by congruence; congruence.
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & _ & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    pose proof (decl_typed_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity.
  - assert (Dq = D) as -> by congruence; congruence.
Qed.

(** The parameters of a member's type former at typed parameters of the
    member are typed.  Not at a record view, whose type is a record type
    ([im_pre_typed]); without record views the premise always holds. *)
Lemma im_pre_params_typed : forall Γ p D m Mm pc k Dq Mk Us Ns,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_is_rview Mm = false ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm ->
    (forall j N T, List.nth_error Ns j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T) ->
    List.length (im_pre Mm Us ++ Ns) = im_np Dq Mk /\
    forall j P T, List.nth_error (im_pre Mm Us ++ Ns) j = Some P ->
      List.nth_error (tele_insts (im_params Dq Mk) Id (im_pre Mm Us ++ Ns)) j = Some T -> Γ ⊢ P : T.
Proof.
  intros * HΓ Hl Hm Hnr Hr Hlq Hk HUl HUs HNl HNs.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (im_ref_nn _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq Hk) as Hnn.
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUs) as [HPl _].
  split; [ rewrite List.length_app, HPl, HNl, Hnn; unfold im_np; lia |].
  unfold im_ref, im_pre in *;
    destruct (im_head Mm) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-;
    [| | exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate ].
  - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence.
    exact (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUs HNs).
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & HIl & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    exact (proj2 (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl HNs)).
Qed.

(** Parameters of the type former whose uniform ones are the member's
    uniform arguments give the member's non-uniform parameters.  Not at a
    record view: its type is a record type, not the type former's
    application ([im_pre_typed]); without record views the premise always
    holds. *)
Lemma mty_params_conv : forall Γ p D m Mm pc k Dq Mk Us Rs,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm -> im_is_rview Mm = false ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Rs = im_np Dq Mk ->
    (forall j R T, List.nth_error Rs j = Some R -> List.nth_error (tele_insts (im_params Dq Mk) Id Rs) j = Some T -> Γ ⊢ R : T) ->
    (forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error Rs j = Some R ->
       List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N ≈ R : T) ->
    mty_params_link Γ p D m Mm Us (List.skipn (ind_nu Dq) Rs) pc k Rs.
Proof.
  intros * HΓ Hl Hm Hnr Hr Hlq Hk HUl HUs HRl HRs HPR.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUs) as [HPl HPt].
  set (Ps := im_pre Mm Us) in *.
  set (Ns := List.skipn (ind_nu Dq) Rs).
  assert (HRl' : List.length (List.firstn (ind_nu Dq) Rs) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HRl; lia).
  destruct (params_typed_split _ _ Dq Hcq _ _ _ Rs Hk HRl HRs) as [HRu HRn].
  (** The uniform arguments as a substitution, equal to the first [Rs]. *)
  assert (Hσσ : Γ ⊢ˢ sb_of_list Id Ps ≈ sb_of_list Id (List.firstn (ind_nu Dq) Rs) : ind_uparams Dq ++ Γ).
  { eapply wf_sub_eq_of_list; [ exact (decl_closed_ass _ Hcq) | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓ)
                              | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite HPl; reflexivity | rewrite HRl'; reflexivity |].
    intros j N R T HN HR HT; apply (HPR j); [ exact HN | | exact HT ].
    rewrite <- (List.firstn_skipn (ind_nu Dq) Rs), List.nth_error_app1 by (apply List.nth_error_Some; congruence); exact HR. }
  (** The rest of [Rs], at the type former's non-uniform telescope at the
      uniform arguments. *)
  assert (HNl : List.length Ns = List.length (im_nparams Mk))
    by (unfold Ns; rewrite List.length_skipn, HRl; unfold im_np, im_nn; lia).
  assert (HPΓ : ⊢ (im_nparams Mk ++ ind_uparams Dq ++ Γ)%list)
    by (rewrite List.app_assoc; exact (wf_params_app _ _ _ HDq Hcq _ _ _ Hk HΓ)).
  assert (HNp : forall j N T, List.nth_error Ns j = Some N ->
             List.nth_error (tele_insts (im_nparams Mk) (sb_of_list Id Ps) Ns) j = Some T -> Γ ⊢ N : T).
  { intros j N T HN HT.
    destruct (nth_error_lt_some (tele_insts (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu Dq) Rs)) Ns) j) as [T' HT'].
    { rewrite length_tele_insts by (eapply decl_closed_nparams_ass; eassumption).
      assert (j < List.length Ns) by (apply List.nth_error_Some; congruence); lia. }
    destruct (tele_insts_cong _ _ _ _ _ _ _ (decl_closed_nparams_ass _ Hcq _ _ Hk) HPΓ (wf_sub_eq_sym _ _ _ _ _ _ Hσσ) HNl HNl
                ltac:(intros j1 N1 N1' T1 HN1 HN1' HT1; rewrite HN1 in HN1'; injection HN1' as <-;
                      apply wf_exp_eq_refl; exact (HRn _ _ _ HN1 HT1)) _ _ _ HT' HT) as (Si & HSi & Hi).
    eapply exp_conv_sort; [ exact HSi | exact Hi | exact (HRn _ _ _ HN HT') ]. }
  (** The type former at the uniform arguments and the rest, equal to it
      at [Rs]. *)
  assert (Hkl : k < ind_ndecl Dq).
  { unfold im_ref in Hr; destruct (im_head Mm) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-.
    - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence; eapply member_decl_lt; eassumption.
    - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & _ & Hlt & _); congruence.
    - exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate. }
  assert (HLc : List.length (Ps ++ Ns) = im_np Dq Mk) by (rewrite List.length_app, HPl, HNl; unfold im_np, im_nn; lia).
  pose proof (params_typed_join _ _ Dq Hcq _ _ _ Ps Ns Hk HPl HPt HNp) as HLt.
  assert (HLR : forall j N R T, List.nth_error (Ps ++ Ns) j = Some N -> List.nth_error Rs j = Some R ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (Ps ++ Ns)) j = Some T -> Γ ⊢ N ≈ R : T).
  { intros j N R T HN HR HT; unfold im_params in HT.
    rewrite tele_insts_app in HT by (try exact (decl_closed_ass _ Hcq); exact HPl).
    assert (Hl1 : List.length (tele_insts (ind_uparams Dq) Id Ps) = ind_nu Dq)
      by (rewrite length_tele_insts by exact (decl_closed_ass _ Hcq); rewrite HPl; unfold ind_nu; lia).
    destruct (Nat.lt_ge_cases j (ind_nu Dq)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN, HT by lia; exact (HPR _ _ _ _ HN HR HT).
    - rewrite List.nth_error_app2 in HN, HT by lia; rewrite HPl in HN; rewrite Hl1 in HT.
      assert (HR' : List.nth_error Ns (j - ind_nu Dq) = Some R)
        by (unfold Ns; rewrite List.nth_error_skipn; replace (ind_nu Dq + (j - ind_nu Dq)) with j by lia; exact HR).
      rewrite HN in HR'; injection HR' as <-; apply wf_exp_eq_refl; exact (HNp _ _ _ HN HT). }
  destruct (ind_apps_conv_large _ _ _ _ _ _ _ _ _ Hg HDs Hlq Hk Hkl HΓ HLc HRl HLt HRs HLR) as (i & _ & _ & Heq).
  assert (Hmty : ind_mty p D m Us Ns = apps (a_ind pc k) (Ps ++ Ns))
    by (unfold ind_mty; rewrite Hm; unfold im_ty_at;
        destruct (im_head Mm) eqn:Hh0; [ rewrite Hr; reflexivity | rewrite Hr; reflexivity |];
        exfalso; unfold im_is_rview in Hnr; rewrite Hh0 in Hnr; discriminate).
  clear HLR HLt HRu.
  (** At a view, its own non-uniform telescope is its container's at the
      view's instance. *)
  unfold Ps in *; clear Ps; unfold im_ref in Hr;
    destruct (im_head Mm) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-;
    [| | exfalso; unfold im_is_rview in Hnr; rewrite Hh in Hnr; discriminate ].
  - assert (Dq = D) as -> by congruence; assert (Mk = Mm) as -> by congruence.
    assert (Epre : im_pre Mm Us = Us) by (unfold im_pre; rewrite Hh; reflexivity); rewrite Epre in *.
    constructor; [ rewrite HNl; reflexivity | exact HNp | exists i; rewrite Hmty; symmetry; exact Heq ].
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (D' & Mk' & Hl' & Hk' & _ & HIl & _ & Hself & _).
    assert (D' = Dq) as -> by congruence; assert (Mk' = Mk) as -> by congruence.
    assert (Epre : im_pre Mm Us = List.map (fun I => I[sb_of_list Id Us]) Is) by (unfold im_pre; rewrite Hh; reflexivity);
      rewrite Epre in *.
    pose proof (decl_typed_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
    rewrite (nparams_sub Dq k' Mk Is (sb_of_list Id Us) Hcq Hk HIl) in HNeq'.
    constructor.
    + rewrite HNl; unfold im_nn; rewrite (ext_eq_length _ _ _ _ _ HNeq), length_tele_sub; reflexivity.
    + intros j N T HN HT.
      rewrite (tele_insts_sb_eq _ (sb_of_list Id Us) (sb_of_list Id Us ⨟ Id)) in HT by (intro; symmetry; apply sb_compose_id_right).
      rewrite <- tele_insts_tele_sub in HT.
      eapply (tele_insts_conv_rev _ _ _ _ _ _ HNeq');
        [ apply all_assumptions_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hm)
        | apply all_assumptions_sub; exact (decl_typed_nparams_ass _ _ _ HDq _ _ Hk)
        | rewrite length_tele_sub; exact HNl | | exact HN | exact HT ].
      intros k1 N1 T1 HN1 HT1; apply (HNp _ _ _ HN1).
      rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is))) in HT1
        by apply sb_compose_id_right.
      exact HT1.
    + exists i; rewrite Hmty; symmetry; exact Heq.
Qed.

(** Equal terms at the instances of a telescope are equal at those of an
    equal one. *)
Lemma tele_insts_eq_conv_rev : forall Γ Δ Δ' Ms Ms',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' -> all_assumptions Δ -> all_assumptions Δ' ->
    List.length Ms = List.length Δ' -> List.length Ms' = List.length Δ' ->
    (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
       List.nth_error (tele_insts Δ' Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T) ->
    forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
      List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T.
Proof.
  intros * HΔ Ha Ha' Hl Hl' HMs.
  assert (HΓ : ⊢ Γ) by (eapply ctx_app_wf_tail, ext_eq_ctx_left; exact HΔ).
  assert (Hσ : Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : Δ' ++ Γ)
    by (eapply wf_sub_eq_of_list; [ exact Ha' | exact (ext_eq_ctx_right _ _ _ _ _ HΔ) | apply wf_sub_eq_refl, wf_sub_id, HΓ
                                  | exact Hl | exact Hl' | exact HMs ]).
  pose proof (wf_sub_eq_compose_right _ _ _ _ _ _ _ _ (ctxsub_ext _ _ _ _ _ HΔ Ha) Hσ) as Hσ'.
  eapply wf_sub_eq_sb_eq in Hσ'; [| intro; apply sb_compose_id_left | intro; apply sb_compose_id_left ].
  eapply wf_sub_eq_of_list_inv; [ exact Ha | rewrite (ext_eq_length _ _ _ _ _ HΔ); exact Hl
                                | rewrite (ext_eq_length _ _ _ _ _ HΔ); exact Hl' | exact Hσ' ].
Qed.

(** Equal types of a member at the same uniform parameters have equal
    non-uniform parameters. *)
Lemma mty_params_inj : forall Γ p D m Mm Us Ns Ns' i,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T) ->
    List.length Ns = im_nn Mm -> List.length Ns' = im_nn Mm ->
    (forall j N T, List.nth_error Ns j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N : T) ->
    (forall j N T, List.nth_error Ns' j = Some N ->
       List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns') j = Some T -> Γ ⊢ N : T) ->
    Γ ⊢ ind_mty p D m Us Ns ≈ ind_mty p D m Us Ns' : Typeω@i ->
    forall j N N' T, List.nth_error Ns j = Some N -> List.nth_error Ns' j = Some N' ->
      List.nth_error (tele_insts (im_nparams Mm) (sb_of_list Id Us) Ns) j = Some T -> Γ ⊢ N ≈ N' : T.
Proof.
  intros * Hl Hm HUl HUs HNl HNl' HNs HNs' Heq.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  unfold ind_mty in Heq; rewrite Hm in Heq; unfold im_ty_at, im_ref, im_pre in Heq.
  destruct (im_head Mm) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; cbn [fst snd] in Heq.
  3: { (** A record view has no non-uniform parameters. *)
       destruct (rview_params _ _ _ _ _ _ _ _ HD Hm Hh) as [_ Hn0].
       rewrite Hn0 in HNl; apply List.length_zero_iff_nil in HNl as ->.
       intros j N N' T HN; rewrite List.nth_error_nil in HN; discriminate. }
  - pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUs HNs) as HX.
    pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns' Hm HUl HUs HNs') as HX'.
    assert (HXl : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
    assert (HXl' : List.length (Us ++ Ns') = im_np D Mm) by (rewrite List.length_app, HUl, HNl'; unfold im_np; lia).
    destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hl Hm Heq HXl HXl' HX HX') as [_ HE].
    destruct (params_eq_split _ D _ _ _ _ Hc Hm HXl HXl' HE) as [_ HEn].
    rewrite !firstn_app_len, !skipn_app_len in HEn by exact HUl; exact HEn.
  - destruct (decl_typed_view _ _ _ HD _ _ _ _ _ _ Hm Hh) as (Dq & Mk & Hlq & Hk & _ & HIl & _ & Hself & _).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
    destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl HNs)
      as [HNk HX].
    destruct (view_params_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hl HDs HD Hc Hcq Hm Hh Hlq Hk Hself HIl HΓ HUl HUs HNl' HNs')
      as [_ HX'].
    set (Ps := List.map (fun I => I[sb_of_list Id Us]) Is) in *.
    assert (HPl : List.length Ps = ind_nu Dq) by (unfold Ps; rewrite List.length_map; exact HIl).
    assert (HXl : List.length (Ps ++ Ns) = im_np Dq Mk) by (rewrite List.length_app, HPl, HNk; unfold im_np; lia).
    assert (HXl' : List.length (Ps ++ Ns') = im_np Dq Mk) by (rewrite List.length_app, HPl, HNl', <- HNl, HNk; unfold im_np; lia).
    destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hlq Hk Heq HXl HXl' HX HX') as [_ HE].
    destruct (params_eq_split _ Dq _ _ _ _ Hcq Hk HXl HXl' HE) as [_ HEn].
    rewrite !firstn_app_len, !skipn_app_len in HEn by exact HPl.
    pose proof (decl_typed_view_nparams _ _ _ _ Hg HD Hl _ _ _ _ _ _ _ _ _ _ _ Hm Hh Hlq Hk Hself Hm) as HNeq.
    pose proof (wf_uparams_sub _ _ _ _ _ HD HΓ HUl HUs) as Hσ.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HNeq Hσ) as HNeq'.
    rewrite (nparams_sub Dq k' Mk Is (sb_of_list Id Us) Hcq Hk HIl) in HNeq'; fold Ps in HNeq'.
    intros j N N' T HN HN' HT.
    rewrite (tele_insts_sb_eq _ (sb_of_list Id Us) (sb_of_list Id Us ⨟ Id)) in HT by (intro; symmetry; apply sb_compose_id_right).
    rewrite <- tele_insts_tele_sub in HT.
    eapply (tele_insts_eq_conv_rev _ _ _ _ _ HNeq');
      [ apply all_assumptions_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hm)
      | apply all_assumptions_sub; exact (decl_typed_nparams_ass _ _ _ HDq _ _ Hk)
      | rewrite length_tele_sub; unfold im_nn in HNk; exact HNk
      | rewrite length_tele_sub; unfold im_nn in HNk; rewrite HNl', <- HNl; exact HNk | | exact HN | exact HN' | exact HT ].
    intros k1 N1 N1' T1 HN1 HN1' HT1; apply (HEn _ _ _ _ HN1 HN1').
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (sb_of_list Id Ps)) in HT1 by apply sb_compose_id_right.
    exact HT1.
Qed.

(** The instances of an entry of a telescope at terms equal up to it are
    equal. *)
Lemma tele_insts_cong_upto : forall Δ Γ0 Γ σ σ' Ms Ms',
    all_assumptions Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ ≈ σ' : Γ0 ->
    forall j T T', List.nth_error (tele_insts Δ σ Ms) j = Some T -> List.nth_error (tele_insts Δ σ' Ms') j = Some T' ->
      (forall j' N N' T0, j' < j -> List.nth_error Ms j' = Some N -> List.nth_error Ms' j' = Some N' ->
         List.nth_error (tele_insts Δ σ Ms) j' = Some T0 -> Γ ⊢ N ≈ N' : T0) ->
      exists S, type_sort S /\ Γ ⊢ T ≈ T' : S.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ j T T' HT HT' HMs.
  - unfold tele_insts in HT; cbn in HT; destruct Ms, j; discriminate.
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    destruct Ms as [| M0 Ms]; [ unfold tele_insts in HT; rewrite List.rev_app_distr in HT; cbn in HT; destruct j; discriminate |].
    destruct Ms' as [| M0' Ms']; [ unfold tele_insts in HT'; rewrite List.rev_app_distr in HT'; cbn in HT'; destruct j; discriminate |].
    rewrite tele_insts_snoc in HT, HT', HMs.
    rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
    destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 (S0 & HSk0 & HA0)].
    pose proof (sort_kind_type_sort _ _ HSk0) as HS0.
    assert (HAA : Γ ⊢ A0[σ] ≈ A0[σ'] : S0) by (eapply sub_eq_preserves_sort; eassumption).
    destruct j as [| j]; cbn in HT, HT'.
    + injection HT as <-; injection HT' as <-; exists S0; split; [ exact HS0 | exact HAA ].
    + assert (HMM : Γ ⊢ M0 ≈ M0' : A0[σ]) by (apply (HMs 0); [ lia | reflexivity | reflexivity | reflexivity ]).
      pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA0 HS0 (wf_sub_eq_right _ _ _ _ _ _ Hσ)) as HA0'.
      eapply IH; [ exact Hass | exact HΔ | | exact HT | exact HT' |].
      * eapply wf_sub_eq_extend;
          [ exact Hσ | exact HA0 | exact HSk0 | exact (presup_exp_eq_left HMM)
          | eapply wf_conv_sort; [ exact (presup_exp_eq_right HMM) | exact HA0' | exact HS0 | exact HAA ] | exact HMM ].
      * intros j' N N' T0 Hj' HN HN' HT0; apply (HMs (S j')); [ lia | exact HN | exact HN' | exact HT0 ].
Qed.

(** Terms of a closed telescope whose weakenings are equal are equal. *)
Lemma tele_eq_strengthen : forall Δ Γ κ A Δt Xs Ys,
    all_assumptions Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> all_assumptions Δt -> ⊢ (Δt ++ Δ ++ Γ)%list ->
    List.length Xs = List.length Δt -> List.length Ys = List.length Δt ->
    (forall j N T, List.nth_error Xs j = Some N -> List.nth_error (tele_insts Δt Id Xs) j = Some T -> (Δ ++ Γ)%list ⊢ N : T) ->
    (forall j N T, List.nth_error Ys j = Some N -> List.nth_error (tele_insts Δt Id Ys) j = Some T -> (Δ ++ Γ)%list ⊢ N : T) ->
    (forall j N N' T, List.nth_error Xs j = Some N -> List.nth_error Ys j = Some N' ->
       List.nth_error (tele_insts Δt Id Xs) j = Some T ->
       (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ N[wk_qn (length Δ) ↑]ʷ ≈ N'[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ) ->
    forall j N N' T, List.nth_error Xs j = Some N -> List.nth_error Ys j = Some N' ->
      List.nth_error (tele_insts Δt Id Xs) j = Some T -> (Δ ++ Γ)%list ⊢ N ≈ N' : T.
Proof.
  intros * Hass HΓf Hat HΔt HXl HYl HXs HYs HL j; induction j as [j IH] using lt_wf_ind; intros N N' T HN HN' HT.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (eapply ctx_app_wf_tail; exact HΔt).
  destruct (nth_error_lt_some (tele_insts Δt Id Ys) j) as [T' HT'].
  { rewrite length_tele_insts by exact Hat.
    assert (j < List.length Ys) by (apply List.nth_error_Some; congruence); lia. }
  destruct (tele_insts_cong_upto _ _ _ _ _ _ _ Hat HΔt (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓs)) _ _ _ HT HT')
    as (Si & HSi & Hi); [ intros j' N1 N1' T1 Hj' HN1 HN1' HT1; exact (IH j' Hj' _ _ _ HN1 HN1' HT1) |].
  eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact (HXs _ _ _ HN HT) | | exact (HL _ _ _ _ HN HN' HT) ].
  eapply exp_conv_sort; [ exact HSi | symmetry; exact Hi | exact (HYs _ _ _ HN' HT') ].
Qed.


(** Short judgments hold, weakened, in the long context. *)
Lemma short_wk_exp : forall Δ Γ κ A M T,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ M : T ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ.
Proof.
  intros * HΓf HM; eapply wk_preserves_exp; [ exact HM | apply wf_wk_qn; [ gen_presups; assumption | exact HΓf ] ].
Qed.

Lemma short_wk_exp_eq : forall Δ Γ κ A M M' T,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ M ≈ M' : T ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ ≈ M'[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ.
Proof.
  intros * HΓf HM; eapply wk_preserves_exp_eq; [ exact HM | apply wf_wk_qn; [ gen_presups; assumption | exact HΓf ] ].
Qed.

(** A short type of a sort is, weakened, of that sort in the long context. *)
Lemma short_wk_sort : forall Δ Γ κ A M S,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ M : S -> type_sort S ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : S.
Proof.
  intros * HΓf HM HS; eapply wk_preserves_sort; [ exact HM | exact HS | apply wf_wk_qn; [ gen_presups; assumption | exact HΓf ] ].
Qed.

(** ** The Induction on Normal Forms

    What is proved of a neutral: it has a short type, a type or a
    proposition, whose weakening is below the long one. *)
#[warnings="-cannot-define-projection"]
Record short_typ (Γ : ctx) (κ : abs_kind) (A : typ) (Δ : ctx) (C : typ) (M : exp) : Prop := mk_short_typ
  { (** The short type *)
    short_typ_typ : typ
    (** Its sort *)
  ; short_typ_sort : typ
    (** A sort: a large universe or [Prop] *)
  ; short_typ_sort_ok : type_sort short_typ_sort
    (** The term is of it in the short context *)
  ; short_typ_exp : (Δ ++ Γ)%list ⊢ M : short_typ_typ
    (** It is of its sort there *)
  ; short_typ_wf : (Δ ++ Γ)%list ⊢ short_typ_typ : short_typ_sort
    (** Its weakening is below the long type *)
  ; short_typ_sub : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ short_typ_typ[wk_qn (length Δ) ↑]ʷ ⊆ C }.

Definition exp_str (Γ : ctx) (κ : abs_kind) (A : typ) (M : exp) : Prop :=
  forall Δ C,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : C ->
    short_typ Γ κ A Δ C M.

Definition ne_str (Γ : ctx) (κ : abs_kind) (A : typ) (u : ne) : Prop := exp_str Γ κ A u.

(** What is proved of a normal form: typed long at a weakened short type
    ([⊢ᵗ]: a type of a sort, or [LevelSort] for the types of levels), it is
    typed short at that type. *)
Definition nf_str_exp (Γ : ctx) (κ : abs_kind) (A : typ) (W : exp) : Prop :=
  forall Δ T,
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    (Δ ++ Γ)%list ⊢ᵗ T ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ W[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ W : T.

(** The same at a type of a sort. *)
Lemma nf_str_sorted : forall Γ κ A W, nf_str_exp Γ κ A W ->
    forall Δ T S,
      all_assumptions Δ ->
      ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
      type_sort S ->
      (Δ ++ Γ)%list ⊢ T : S ->
      (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ W[wk_qn (length Δ) ↑]ʷ : T[wk_qn (length Δ) ↑]ʷ ->
      (Δ ++ Γ)%list ⊢ W : T.
Proof. intros * IH Δ T S Hass HΓf HS HT HW; exact (IH Δ T Hass HΓf (wf_type_of_sort _ HS HT) HW). Qed.

(** A term of [LevelSort] is a type of levels: [LevelSort] is of no sort
    ([level_sort_untyped]). *)
Lemma level_sort_typed_former : forall {Γ M}, Γ ⊢ M : LevelSort -> level_type_former M.
Proof.
  intros * H; pose proof (presup_exp_typ_cases H) as Hp; inversion Hp; [ exfalso; eapply level_sort_untyped; eassumption | assumption ].
Qed.

(** A term strengthened with a short type is strengthened at any short type
    of which the long one is a weakening; nothing is below [LevelSort],
    which is of no sort ([level_sort_untyped]). *)
Lemma exp_str_at : forall Γ κ A M, exp_str Γ κ A M -> nf_str_exp Γ κ A M.
Proof.
  intros * Hu Δ T Hass HΓf HTt HW.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (destruct HTt; [ gen_presups; assumption | assumption ]).
  destruct (Hu _ _ Hass HΓf HΓs HW) as [T0 S0 HS0 HuT HT0 Hs].
  destruct HTt as [T S HS HT | _].
  - eapply wf_exp_subtyp; [ exact HuT | exact HT | exact HS |].
    exact (subtyp_strengthen_sort _ _ _ _ _ _ _ _ Hass HΓf HS0 HS HT0 HT Hs).
  - exfalso; destruct (presup_subtyp_right_sorted Hs) as (S & _ & HL); exact (level_sort_untyped HL).
Qed.

(** The sort of a short type whose weakening is below a type of the sort
    at a kind is the sort at the same kind ([subtyp_same_kind]). *)
Lemma short_sort_kind : forall Δ Γ κ A T0 S0 C r k,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> ⊢ (Δ ++ Γ)%list ->
    type_sort S0 -> (Δ ++ Γ)%list ⊢ T0 : S0 ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ C : abs_kind_sort r Typeω@k ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T0[wk_qn (length Δ) ↑]ʷ ⊆ C ->
    exists j, S0 = abs_kind_sort r Typeω@j.
Proof.
  intros * HΓf HΓs HS0 HT0 HC Hs.
  assert (Hwk : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list) by (apply wf_wk_qn; assumption).
  pose proof (wk_preserves_sort _ _ _ _ _ _ _ HT0 HS0 Hwk) as HT0f.
  destruct HS0 as [j | |]; cbn in HT0f.
  - pose proof (subtyp_same_kind _ _ _ ak_relevant r j k Hs HT0f HC) as <-; exists j; reflexivity.
  - pose proof (subtyp_same_kind _ _ _ ak_propositional r 0 k Hs HT0f HC) as <-; exists 0; reflexivity.
  - pose proof (subtyp_same_kind _ _ _ ak_level r 0 k Hs HT0f HC) as <-; exists 0; reflexivity.
Qed.

(** An application: the head's short type is a [Π] into a universe or
    between levels ([typ_pi_shape_strengthen]) or, the head a proof, a [∀]
    ([typ_all_shape_strengthen]), whose domain the argument is checked
    against. *)
Lemma app_str : forall Γ κ A M w, exp_str Γ κ A M -> nf_str_exp Γ κ A w -> exp_str Γ κ A (a_app M w).
Proof.
  intros Γ κ A u w IHu IHw Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_app_inversion HW) as [κd κc X Y Hu Hw HsC].
  destruct (IHu _ _ Hass HΓf HΓs Hu) as [T0 S0 HS0 HuT HT0 Hs0].
  assert (exists C0, (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ a_pi κd κc X Y : C0) as [C0 HC0] by (gen_presups; eexists; eassumption).
  destruct (evaluated_kind_or_propositional κc) as [Hev | ->].
  - (** A function, into a universe or between levels: the [Π] is of the
        sort at its codomain's kind *)
    destruct (wf_pi_typed_kind Hev HC0) as [kP HkP].
    destruct (short_sort_kind _ _ _ _ _ _ _ κc kP HΓf HΓs HS0 HT0 HkP Hs0) as [j0 ->].
    destruct (typ_pi_shape_strengthen _ _ _ _ _ _ _ _ _ _ Hass Hev HΓf HT0 Hs0) as (C' & D' & HCD).
    assert (HSk : type_sort (abs_kind_sort κc Typeω@j0)) by (destruct Hev; constructor).
    assert (HTCD : (Δ ++ Γ)%list ⊢ T0 ≈ (nf_pi κd κc C' D' : exp) : abs_kind_sort κc Typeω@j0)
      by (eapply soundness_ty_at_sort; eassumption).
    cbn [nf_to_exp] in HTCD.
    assert (HCDt : (Δ ++ Γ)%list ⊢ a_pi κd κc C' D' : abs_kind_sort κc Typeω@j0) by (gen_presups; assumption).
    destruct (wf_pi_parts HCDt) as (Hpk & (SC & HSC & HC) & (iD & HD)).
    pose proof (sort_kind_type_sort _ _ HSC) as HSCt.
    pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf.
    assert (HTCDf' : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T0[wk_qn (length Δ) ↑]ʷ
                       ≈ a_pi κd κc (C' : exp)[wk_qn (length Δ) ↑]ʷ (D' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ : abs_kind_sort κc Typeω@j0)
      by (destruct Hev; exact HTCDf).
    assert (Hs' : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ a_pi κd κc (C' : exp)[wk_qn (length Δ) ↑]ʷ (D' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ ⊆ a_pi κd κc X Y)
      by (etransitivity; [ eapply (subtyp_of_exp_eq_kind Hev); symmetry; exact HTCDf' | exact Hs0 ]).
    destruct (subtyp_pi_kind_inv _ _ _ _ _ _ _ _ Hev Hs') as (_ & (SX & HSX & HCX) & HDY).
    pose proof (short_wk_sort _ _ _ _ _ _ HΓf HC HSCt) as HCf.
    assert (HCfX : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ (C' : exp)[wk_qn (length Δ) ↑]ʷ : SX) by (gen_presups; assumption).
    assert (Hwf : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ w[wk_qn (length Δ) ↑]ʷ : (C' : exp)[wk_qn (length Δ) ↑]ʷ)
      by (eapply wf_exp_subtyp'; [ exact Hw | eapply wf_subtyp_refl; [ exact HCfX | exact (sort_kind_type_sort _ _ HSX) | symmetry; exact HCX ] ]).
    assert (Hws : (Δ ++ Γ)%list ⊢ w : C') by (eapply (nf_str_sorted _ _ _ _ IHw _ _ SC); [ exact Hass | exact HΓf | exact HSCt | exact HC | exact Hwf ]).
    assert (Hus : (Δ ++ Γ)%list ⊢ u : a_pi κd κc C' D')
      by (eapply wf_exp_subtyp; [ exact HuT | exact HCDt | exact HSk | exact (subtyp_of_exp_eq_kind Hev HTCD) ]).
    apply (mk_short_typ _ _ _ _ _ _ ((D' : exp)[Id,,w]) (abs_kind_sort κc Typeω@iD) ltac:(destruct Hev; constructor)).
    + eapply wf_app; [ exact HC | exact HSC | exact HD | exact Hpk | exact Hus | exact Hws ].
    + pose proof (exp_sub_single _ _ _ _ _ _ _ _ HD Hws) as HDw; destruct Hev; exact HDw.
    + rewrite exp_wk_sub_id_extend; etransitivity; [| exact HsC ].
      eapply sub_preserves_subtyp; [ exact HDY | eapply wf_sub_single; [ exact HCf | exact HSC | exact Hwf ] ].
  - (** A proof of a [∀] *)
    pose proof (prop_former_typed HC0 ltac:(right; right; left; do 3 eexists; reflexivity)) as HkP.
    change Propₘ with (abs_kind_sort ak_propositional Typeω@0) in HkP.
    destruct (short_sort_kind _ _ _ _ _ _ _ ak_propositional 0 HΓf HΓs HS0 HT0 HkP Hs0) as [j0 ->]; cbn [abs_kind_sort] in HT0.
    destruct (typ_all_shape_strengthen _ _ _ _ _ _ _ _ Hass HΓf HT0 Hs0) as (C' & D' & HCD).
    assert (HTCD : (Δ ++ Γ)%list ⊢ T0 ≈ (∀ₚⁿ{κd} C' D' : exp) : Propₘ)
      by (eapply soundness_ty_at_sort; [ constructor | exact HT0 | exact HCD ]).
    cbn [nf_to_exp] in HTCD.
    assert (HCDt : (Δ ++ Γ)%list ⊢ ∀ₚ{κd} C' D' : Propₘ) by (gen_presups; assumption).
    destruct (wf_all_inversion _ _ _ _ _ _ _ HCDt) as [SC HSC HC HD _].
    pose proof (sort_kind_type_sort _ _ HSC) as HSCt.
    pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf.
    assert (Hs' : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ ∀ₚ{κd} (C' : exp)[wk_qn (length Δ) ↑]ʷ (D' : exp)[wk_q (wk_qn (length Δ) ↑)]ʷ ⊆ ∀ₚ{κd} X Y).
    { etransitivity; [| exact Hs0 ].
      assert ((tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T0[wk_qn (length Δ) ↑]ʷ : Propₘ) by (gen_presups; assumption).
      eapply wf_subtyp_refl; [ eassumption | constructor | symmetry; exact HTCDf ]. }
    destruct (subtyp_all_inv _ _ _ _ _ _ _ Hs') as (_ & (SX & HSX & HCX) & HDY).
    pose proof (short_wk_sort _ _ _ _ _ _ HΓf HC HSCt) as HCf.
    assert (HCfX : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ (C' : exp)[wk_qn (length Δ) ↑]ʷ : SX) by (gen_presups; assumption).
    assert (Hwf : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ w[wk_qn (length Δ) ↑]ʷ : (C' : exp)[wk_qn (length Δ) ↑]ʷ)
      by (eapply wf_exp_subtyp'; [ exact Hw | eapply wf_subtyp_refl; [ exact HCfX | exact (sort_kind_type_sort _ _ HSX) | symmetry; exact HCX ] ]).
    assert (Hws : (Δ ++ Γ)%list ⊢ w : C') by (eapply (nf_str_sorted _ _ _ _ IHw _ _ SC); [ exact Hass | exact HΓf | exact HSCt | exact HC | exact Hwf ]).
    assert (Hus : (Δ ++ Γ)%list ⊢ u : ∀ₚ{κd} C' D')
      by (eapply wf_exp_subtyp; [ exact HuT | exact HCDt | constructor | eapply wf_subtyp_refl; [ exact HCDt | constructor | exact HTCD ] ]).
    apply (mk_short_typ _ _ _ _ _ _ ((D' : exp)[Id,,w]) Propₘ type_sort_prop).
    + eapply wf_app with (κc := ak_propositional) (i := 0); [ exact HC | exact HSC | exact HD | constructor | exact Hus | exact Hws ].
    + exact (exp_sub_single _ _ _ _ _ _ _ _ HD Hws).
    + rewrite exp_wk_sub_id_extend; etransitivity; [| exact HsC ].
      eapply sub_preserves_subtyp; [ exact HDY | eapply wf_sub_single; [ exact HCf | exact HSC | exact Hwf ] ].
Qed.

Lemma apps_str : forall Γ κ A Xs M, List.Forall (nf_str_exp Γ κ A) Xs -> exp_str Γ κ A M -> exp_str Γ κ A (apps M Xs).
Proof.
  intros Γ κ A Xs; induction Xs as [| X Xs IH]; intros M HXs HM; cbn [apps_exp]; [ exact HM |].
  inversion HXs as [| ? ? HX HXs']; subst.
  apply IH; [ exact HXs' | exact (app_str _ _ _ _ _ HM HX) ].
Qed.

(** The type former and the constructors: typed at their closed types in
    every context. *)
Lemma ind_str : forall Γ κ A p k, exp_str Γ κ A (a_ind p k).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_ind_inversion HW) as [D Mk Hl Hk Hlt Hs].
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓs) as [j Hj].
  apply (mk_short_typ _ _ _ _ _ _ (ind_ty D Mk) Typeω@j (type_sort_universe j)); [ eapply wf_ind; eassumption | exact Hj |].
  rewrite (ind_ty_wk D k Mk) by assumption; exact Hs.
Qed.

(** A constructor of any member, at its closed type. *)
Lemma wf_con_closed : forall Γ p D k Mk c gs,
    ⊢ Γ -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
    Γ ⊢ a_con p k c : con_ty p D k Mk gs.
Proof.
  intros * HΓ Hl Hk Hcon.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (con_ty_typed0 _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hcon) as [j0 Hj0].
  destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hg HDs Hl Hk (cons_lookup_in _ _ _ Hcon) gs nil (eq_sym (List.app_nil_r gs)))
    as (HΨ0 & _ & _).
  eapply wf_con_of_lookup; eassumption.
Qed.

Lemma con_str : forall Γ κ A p k c, exp_str Γ κ A (a_con p k c).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_con_inversion HW) as [D Mk gs Hl Hk Hcon Hs].
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓs) (decls_of_ctx _ _ _ HΓs) Hl Hk Hcon HΓs) as [j Hj].
  apply (mk_short_typ _ _ _ _ _ _ (con_ty p D k Mk gs) Typeω@j (type_sort_universe j)); [ eapply wf_con_closed; eassumption | exact Hj |].
  rewrite (con_ty_wk p D k Mk c gs) by assumption; exact Hs.
Qed.

(** A neutral typed at [Level@n] in the long context is in the short one. *)
Lemma ne_str_level : forall Γ κ A Δ n (u : ne),
    ne_str Γ κ A u ->
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ (u : exp)[wk_qn (length Δ) ↑]ʷ : Level@n ->
    (Δ ++ Γ)%list ⊢ u : Level@n.
Proof.
  intros * Hu Hass HΓf HΓs H.
  destruct (Hu _ _ Hass HΓf HΓs H) as [T S HS HuT HT Hs].
  eapply wf_exp_subtyp; [ exact HuT | apply wf_level, HΓs | constructor |].
  eapply subtyp_strengthen_sort;
    [ exact Hass | exact HΓf | exact HS | constructor | exact HT | apply wf_level, HΓs | exact Hs ].
Qed.

Lemma level_atoms_wf_strengthen : forall Γ κ A Δ n xs,
    level_atoms_all (ne_str Γ κ A) xs ->
    all_assumptions Δ ->
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    ⊢ (Δ ++ Γ)%list ->
    List.Forall (fun p => (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ snd p : Level@n)
      (List.map (fun p => (fst p, (snd p)[wk_qn (length Δ) ↑]ʷ)) (List.map atom_exp xs)) ->
    @level_atoms_wf gc_deps gc_stack n (Δ ++ Γ)%list xs.
Proof.
  intros Γ κ A Δ n xs; induction xs as [| [k s u] r IH]; cbn; [ intros; exact I |].
  intros [Hu Hr] Hass HΓf HΓs HF.
  inversion HF as [| ? ? Hk HF']; subst.
  split; [ eapply ne_str_level; eassumption | apply IH; assumption ].
Qed.

(** The atoms of a level expression typed at [Level@n] are. *)
Lemma lvl_exp_of_atoms : forall Γ n c xs,
    Γ ⊢ lvl_exp_of c xs : Level@n ->
    List.Forall (fun p => Γ ⊢ snd p : Level@n) xs.
Proof.
  intros * H; destruct (lvl_exp_of_inv _ _ _ _ H) as [(m & Hmn & _ & HF) | (a & -> & ->)].
  - eapply List.Forall_impl; [| exact HF ]; intros p Hp; eapply wf_exp_subtyp'; [ exact Hp | exact Hmn ].
  - repeat constructor; exact H.
Qed.

(** A weakened atom list with a single entry and no offset. *)
Lemma level_atoms_map_single : forall φ xs a,
    List.map (fun p => (fst p, (snd p)[φ]ʷ)) (List.map atom_exp xs) = (0, a) :: nil ->
    exists s u, xs = cons (mk_level_atom 0 s u) nil /\ a = (u : exp)[φ]ʷ.
Proof.
  intros φ [| [k s u] [| [k' s' u'] r]] a H; cbn in H; try discriminate.
  injection H as -> <-; do 2 eexists; split; reflexivity.
Qed.

(** A stuck eliminator, at the uniform parameters it carries: the
    scrutinee's short type is the type former the member's type is headed
    by ([typ_ind_shape_strengthen]), at parameters whose uniform ones are
    the member's uniform arguments ([tele_eq_strengthen]), so the rest are
    the member's non-uniform parameters ([mty_params_conv]), equal to the
    long ones ([mty_params_inj]); the blocks are typed short by the
    induction hypotheses. *)
Lemma elim_str : forall Γ κ A pc Us k Bks u,
    List.Forall (nf_str_exp Γ κ A) Us ->
    List.Forall (fun b => nf_str_exp Γ κ A (eb_scrutinee_type b) /\ nf_str_exp Γ κ A (eb_motive b) /\
                          List.Forall (fun br => nf_str_exp Γ κ A (snd br)) (eb_brs b)) Bks ->
    exp_str Γ κ A u ->
    exp_str Γ κ A (a_elim ak_relevant pc Us k Bks u).
Proof.
  intros * IHUs IHBs IHu Δ C Hass HΓf HΓs HW.
  rewrite exp_wk_elim in HW.
  set (φ := wk_qn (length Δ) ↑) in *.
  set (Lf := (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) in *.
  assert (Hwk : Lf ⊢ʷ φ : (Δ ++ Γ)%list) by (apply wf_wk_qn; [ exact HΓs | exact HΓf ]).
  destruct (wf_elim_inversion HW) as [D Mm bm Ps i Hl Hm Hb HPl HPs HuL HUL HBt Hs].
  pose proof (ctx_wf_gctx _ _ _ HΓs) as Hg; pose proof (decls_of_ctx _ _ _ HΓs) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hl) as [HD Hc].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hm Hb) as Hnr.
  assert (HUl : List.length Us = ind_nu D)
    by (apply (f_equal (@List.length _)) in HUL; rewrite List.length_map, List.length_firstn in HUL; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ _ Ps Hm HPl HPs) as [HUtL HNtL].
  rewrite <- HUL in HUtL, HNtL, HuL, HBt.
  set (NsL := List.skipn (ind_nu D) Ps) in *.
  (** The uniform parameters, short. *)
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
             (Δ ++ Γ)%list ⊢ U : T).
  { eapply tele_insts_typed_all; [ exact (decl_closed_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓs) | apply wf_sub_id, HΓs |].
    intros j U T HU HT (ST & HST & HTt).
    pose proof (proj1 (List.Forall_forall _ _) IHUs U (List.nth_error_In _ _ HU)) as IHU.
    eapply (nf_str_sorted _ _ _ _ IHU Δ T ST Hass HΓf HST HTt).
    apply (HUtL j); [ rewrite List.nth_error_map, HU; reflexivity |].
    rewrite <- tele_insts_closed_wk by (try exact (decl_closed_ass _ Hc); exact (decl_closed_uparams _ Hc)).
    rewrite List.nth_error_map, HT; reflexivity. }
  (** The scrutinee's short type: the type former the member's type is
      headed by, at parameters [PsS]. *)
  destruct (IHu _ _ Hass HΓf HΓs HuL) as [T0 S0 HS0 HuT HT0 Hs0].
  fold φ Lf in Hs0.
  destruct (im_ref pc k Mm) as [qr k'] eqn:Hr.
  assert (Emty : forall Us' Ns', ind_mty pc D k Us' Ns' = apps (a_ind qr k') (im_pre Mm Us' ++ Ns'))
    by (intros; unfold ind_mty; rewrite Hm; unfold im_ty_at;
        destruct (im_head Mm) eqn:Hh0; [ rewrite Hr; reflexivity | rewrite Hr; reflexivity |];
        exfalso; unfold im_is_rview in Hnr; rewrite Hh0 in Hnr; discriminate).
  rewrite Emty in Hs0.
  (** No proposition and no type of levels is below an inductive type, so
      the short type is at a universe. *)
  destruct HS0 as [j0 | |];
    [| exfalso; exact (subtyp_prop_ind_absurd Hs0 (short_wk_sort _ _ _ _ _ _ HΓf HT0 type_sort_prop))
     | exfalso; exact (ind_type_not_level (subtyp_level_type_right (short_wk_sort _ _ _ _ _ _ HΓf HT0 type_sort_level) Hs0)) ].
  destruct (typ_ind_shape_strengthen _ _ _ _ _ _ _ _ _ Hass HΓf HT0 Hs0) as [Rs HRs].
  destruct (typ_ind_shape _ _ _ _ _ _ HT0 HRs) as (Dq & Mk & PsS & Hlq & Hk & HSl & HSt & HTeq & _).
  destruct (decl_of_lookup _ _ _ _ _ HΓs Hlq) as [HDq Hcq].
  pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTeq) as HTeqL; rewrite wk_apps_ind in HTeqL; fold φ Lf in HTeqL.
  assert (HsubL : Lf ⊢ apps (a_ind qr k') (List.map (fun P => P[φ]ʷ) PsS)
                    ⊆ apps (a_ind qr k') (im_pre Mm (List.map (fun U => U[φ]ʷ) Us) ++ NsL))
    by (etransitivity; [ eapply wf_subtyp_refl'; symmetry; exact HTeqL | exact Hs0 ]).
  assert (HSL : Lf ⊢ apps (a_ind qr k') (List.map (fun P => P[φ]ʷ) PsS) : Typeω@j0) by (gen_presups; assumption).
  destruct (subtyp_ind_inv HsubL) as (SL & HSLs & HeqL0).
  destruct (exp_eq_sort_large HSLs HeqL0 (or_introl HSL)) as [kk HeqL]; clear SL HSLs HeqL0 HSL.
  assert (Hnn : im_nn Mm = im_nn Mk).
  { exact (im_ref_nn _ _ _ _ _ _ _ _ _ HΓs Hl Hm Hr Hlq Hk). }
  (** The long parameters, the short ones weakened, are equal. *)
  assert (HUlL : List.length (List.map (fun U => U[φ]ʷ) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓf Hl Hm Hnr Hr Hlq HUlL HUtL) as [HPlL HPtL].
  assert (HNlL : List.length NsL = im_nn Mm) by (unfold NsL; rewrite List.length_skipn, HPl; unfold im_np; lia).
  assert (HLl : List.length (im_pre Mm (List.map (fun U => U[φ]ʷ) Us) ++ NsL) = im_np Dq Mk)
    by (rewrite List.length_app, HPlL, HNlL, Hnn; unfold im_np; lia).
  assert (HSlL : List.length (List.map (fun P => P[φ]ʷ) PsS) = im_np Dq Mk) by (rewrite List.length_map; exact HSl).
  assert (Hkt : Lf ⊢ apps (a_ind qr k') (im_pre Mm (List.map (fun U => U[φ]ʷ) Us) ++ NsL) : Typeω@kk)
    by (gen_presups; assumption).
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkt HLl) as HLt.
  assert (HStL : forall j P T, List.nth_error (List.map (fun P => P[φ]ʷ) PsS) j = Some P ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (List.map (fun P => P[φ]ʷ) PsS)) j = Some T -> Lf ⊢ P : T).
  { intros j P T HP HT.
    rewrite <- tele_insts_closed_wk in HT by (try (eapply decl_closed_params_ass; eassumption); eapply decl_closed_params; eassumption).
    apply nth_error_map_inv in HP as (P0 & HP0 & ->); apply nth_error_map_inv in HT as (T1 & HT1 & ->).
    eapply wk_preserves_exp; [ exact (HSt _ _ _ HP0 HT1) | exact Hwk ]. }
  destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hlq Hk HeqL HSlL HLl HStL HLt) as [_ HPP].
  pose proof (params_eq_sym _ _ _ _ _ _ _ Hlq Hk HΓf HSlL HLl HPP) as HPP'.
  clear HPP HStL HsubL Hs0 HTeqL HRs Hkt HLt.
  (** The short uniform parameters of [PsS] are the member's uniform
      arguments. *)
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓs Hl Hm Hnr Hr Hlq HUl HUt) as [HPlS HPtS].
  destruct (params_typed_split _ _ Dq Hcq _ _ _ PsS Hk HSl HSt) as [HSu HSn].
  assert (HSl' : List.length (List.firstn (ind_nu Dq) PsS) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HSl; lia).
  pose proof (im_pre_wk D k Mm Us φ Hc Hm HUl) as Epw.
  clear IHu HSn.
  assert (HPR : forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error PsS j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> (Δ ++ Γ)%list ⊢ N ≈ R : T).
  { intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPlS; apply List.nth_error_Some; congruence).
    assert (HR' : List.nth_error (List.firstn (ind_nu Dq) PsS) j = Some R)
      by (rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (ind_nu Dq)); [ exact HR | lia ]).
    eapply (tele_eq_strengthen _ _ _ _ (ind_uparams Dq)); [ exact Hass | exact HΓf | exact (decl_closed_ass _ Hcq)
           | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓs) | rewrite HPlS; reflexivity | rewrite HSl'; reflexivity
           | exact HPtS | exact HSu | | exact HN | exact HR' | exact HT ].
    clear j N R T HN HR HT Hj HR'.
    intros j N R T HN HR HT; fold φ Lf.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPlS; apply List.nth_error_Some; congruence).
    apply (HPP' j).
    - rewrite List.nth_error_app1 by lia; rewrite <- Epw, List.nth_error_map, HN; reflexivity.
    - rewrite List.nth_error_map; rewrite List.nth_error_firstn in HR; destruct (Nat.ltb_spec j (ind_nu Dq)); [| discriminate ].
      rewrite HR; reflexivity.
    - unfold im_params; rewrite tele_insts_app by (try exact (decl_closed_ass _ Hcq); exact HPlL).
      rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact (decl_closed_ass _ Hcq); rewrite HPlL; unfold ind_nu in *; lia).
      rewrite <- Epw, <- tele_insts_closed_wk by (try exact (decl_closed_ass _ Hcq); exact (decl_closed_uparams _ Hcq)).
      rewrite List.nth_error_map, HT; reflexivity. }
  clear HPP' HSu HSl' HPtS HPtL HLl HSlL.
  (** So the rest of [PsS] are the member's non-uniform parameters, and the
      scrutinee is short of the member's type. *)
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓs Hl Hm Hnr Hr Hlq Hk HUl HUt HSl HSt HPR) as [HNl HNt [iE HE]].
  set (NsS := List.skipn (ind_nu Dq) PsS) in *.
  assert (HuS : (Δ ++ Γ)%list ⊢ u : ind_mty pc D k Us NsS)
    by (eapply wf_conv'; [ eapply wf_conv'; [ exact HuT | exact HTeq ] | exact HE ]).
  pose proof (params_typed_join _ _ D Hc _ _ _ Us NsS Hm HUl HUt HNt) as HPsS.
  set (PsW := List.map (fun P => P[φ]ʷ) (Us ++ NsS)).
  assert (HPWl : List.length PsW = im_np D Mm) by (unfold PsW; rewrite List.length_map, List.length_app, HUl, HNl; unfold im_np; lia).
  assert (HPWt : forall j P T, List.nth_error PsW j = Some P -> List.nth_error (tele_insts (im_params D Mm) Id PsW) j = Some T -> Lf ⊢ P : T).
  { intros j P T HP HT; unfold PsW in HP, HT.
    rewrite <- tele_insts_closed_wk in HT by (try (eapply decl_closed_params_ass; eassumption); eapply decl_closed_params; eassumption).
    apply nth_error_map_inv in HP as (P0 & HP0 & ->); apply nth_error_map_inv in HT as (T1 & HT1 & ->).
    eapply wk_preserves_exp; [ exact (HPsS _ _ _ HP0 HT1) | exact Hwk ]. }
  assert (HPWu : List.firstn (ind_nu D) PsW = List.map (fun U => U[φ]ʷ) Us)
    by (unfold PsW; rewrite List.map_app, firstn_app_len by (rewrite List.length_map; exact HUl); reflexivity).
  assert (HPWn : List.skipn (ind_nu D) PsW = List.map (fun N => N[φ]ʷ) NsS)
    by (unfold PsW; rewrite List.map_app, skipn_app_len by (rewrite List.length_map; exact HUl); reflexivity).
  destruct (params_typed_split _ _ D Hc _ _ _ PsW Hm HPWl HPWt) as [_ HNWt].
  rewrite HPWu, HPWn in HNWt.
  clear HPR HSt HTeq HPsS.
  (** The long non-uniform parameters are the short ones, weakened, so
      the long motive's instance is the short one's, weakened. *)
  pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HE) as HEL; rewrite wk_apps_ind, (ind_mty_wk pc D k Us NsS _ Hc HUl) in HEL;
    fold φ Lf in HEL.
  rewrite <- Emty in HeqL.
  assert (HmL : Lf ⊢ ind_mty pc D k (List.map (fun U => U[φ]ʷ) Us) NsL
                  ≈ ind_mty pc D k (List.map (fun U => U[φ]ʷ) Us) (List.map (fun N => N[φ]ʷ) NsS) : Typeω@(max kk iE))
    by (etransitivity; [ symmetry; eapply lift_exp_eq_max_left; exact HeqL | eapply lift_exp_eq_max_right; exact HEL ]).
  assert (HNlW : List.length (List.map (fun N => N[φ]ʷ) NsS) = im_nn Mm) by (rewrite List.length_map; exact HNl).
  pose proof (mty_params_inj _ _ _ _ _ _ _ _ _ Hl Hm HUlL HUtL HNlL HNlW HNtL HNWt HmL) as HNN.
  clear HmL HEL HeqL HE.
  assert (HPPW : forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error PsW j = Some P' ->
             List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Lf ⊢ P ≈ P' : T).
  { intros j P P' T HP HP' HT.
    assert (EPs : Ps = List.map (fun U => U[φ]ʷ) Us ++ NsL) by (rewrite HUL; unfold NsL; symmetry; apply List.firstn_skipn).
    assert (EPW : PsW = List.map (fun U => U[φ]ʷ) Us ++ List.map (fun N => N[φ]ʷ) NsS) by (unfold PsW; apply List.map_app).
    rewrite EPs in HP, HT; rewrite EPW in HP'.
    unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (decl_closed_ass _ Hc); exact HUlL).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id (List.map (fun U => U[φ]ʷ) Us)) = ind_nu D)
      by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); rewrite HUlL; unfold ind_nu in *; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP, HP', HT by lia; rewrite HP in HP'; injection HP' as <-.
      apply wf_exp_eq_refl; exact (HUtL _ _ _ HP HT).
    - rewrite List.nth_error_app2 in HP, HP', HT by lia; rewrite HUlL in HP, HP'; rewrite Hl1 in HT.
      exact (HNN _ _ _ _ HP HP' HT). }
  rewrite HUL in HuL, HBt.
  destruct (wf_elim_params_conv _ _ _ _ _ _ _ _ _ _ ak_relevant i Hl Hm Hb HPl HPs HPWl HPWt HPPW HuL HBt) as (_ & _ & Hmot).
  fold NsL in Hmot; rewrite HPWn in Hmot.
  clear HPPW HNN HNWt HPWt.
  rewrite <- HUL in HBt, HuL.
  clear Emty Hr Rs HSl HDq Hcq Hnn HPlL HPlS Epw HNtL HPs HPWu HPWn HPWl PsW HNlW.
  (** The blocks, short. *)
  assert (Hbw : forall j b, List.nth_error Bks j = Some b ->
             List.nth_error (blocks_wk Bks φ) j =
               Some (eb_mk (eb_binder_count b) (eb_scrutinee_type b)[wk_qn (eb_binder_count b - 1) φ]ʷ (eb_motive b)[wk_qn (eb_binder_count b) φ]ʷ
                       (List.map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) (eb_brs b))))
    by (intros j [nm oZ A0 Bs0] Hj; unfold blocks_wk; rewrite List.nth_error_map, Hj; reflexivity).
  assert (HBnm : blocks_binder_count_ok D Bks).
  { intros j Mj b Hj Hb0; pose proof (blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as H; exact H. }
  assert (HUt' : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx pc D j Mj Us ++ Δ ++ Γ)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  assert (HBmot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             (elim_mctx pc D j Mj Us ++ Δ ++ Γ)%list ⊢ eb_motive b : Typeω@i).
  { intros j Mj b Hj Hb0.
    pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (_ & IHm & _).
    pose proof (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as HmL; cbn [eb_motive] in HmL.
    rewrite (HBnm _ _ _ Hj Hb0) in HmL.
    assert (HLm : (tele_wk (elim_mctx pc D j Mj Us ++ Δ) ↑ ++ Γ ▹{κ} A)%list
                  = (elim_mctx pc D j Mj (List.map (fun U => U[φ]ʷ) Us) ++ Lf)%list)
      by (rewrite tele_wk_app, elim_mctx_wk by assumption; unfold Lf; rewrite <- List.app_assoc; reflexivity).
    rewrite List.app_assoc.
    eapply (nf_str_sorted _ _ _ _ IHm (elim_mctx pc D j Mj Us ++ Δ) _ Typeω@(S i)).
    - apply List.Forall_app; split; [ eapply elim_mctx_ass; eassumption | exact Hass ].
    - rewrite HLm; eapply blocks_mctx_wf; eassumption.
    - apply type_sort_universe.
    - rewrite <- List.app_assoc; apply wf_typ; exact (HUt' _ _ Hj).
    - rewrite HLm, List.length_app, length_elim_mctx, wk_qn_plus; cbn [exp_wk]; exact HmL. }
  assert (HBl : List.length Bks = ind_nblk D)
    by (pose proof (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) as H; unfold blocks_wk in H; rewrite List.length_map in H; exact H).
  assert (HAs : motives_typed gc_deps gc_stack (Δ ++ Γ)%list pc D Us (blocks_motives Bks) ak_relevant i).
  { intros j Mj Hj Hjr; destruct (blocks_nth _ _ _ _ Hsuf HBl Hj Hjr) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0); exact (HBmot _ _ _ Hj Hb0). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓs HUl HUt) as Hσ.
  assert (HBbr : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
             (elim_bctx ak_relevant pc D Mj gs (blocks_motives Bks) Us ++ Δ ++ Γ)%list ⊢ B : elim_branch_type pc D j Mj c gs (eb_motive b) Us).
  { intros j Mj b c gs n B Hj Hb0 Hcon Hin.
    pose proof (block_member_not_rview _ _ _ _ _ Hsuf HBl Hj Hb0) as Hjr.
    pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (_ & _ & IHbr).
    pose proof (proj1 (List.Forall_forall _ _) IHbr _ Hin) as IHB; cbn [snd] in IHB.
    pose proof (List.in_map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) _ _ Hin) as Hin'; cbn [fst snd] in Hin'.
    pose proof (blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin') as Hn.
    pose proof (blocks_typed_brs _ _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin') as HBL; cbn [eb_motive] in HBL.
    rewrite (HBnm _ _ _ Hj Hb0) in HBL.
    pose proof (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hj Hjr HΓs HUl HUt HUt' HAs (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt) Hcon) as Hbs.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HBmot _ _ _ Hj Hb0) Hbs) as Hbt.
    assert (HLb : (tele_wk (elim_bctx ak_relevant pc D Mj gs (blocks_motives Bks) Us ++ Δ) ↑ ++ Γ ▹{κ} A)%list
                  = (elim_bctx ak_relevant pc D Mj gs (blocks_motives (blocks_wk Bks φ)) (List.map (fun U => U[φ]ʷ) Us) ++ Lf)%list).
    { rewrite tele_wk_app; fold φ.
      rewrite (elim_bctx_wk ak_relevant pc D j Mj c gs (blocks_motives Bks) (blocks_motives (blocks_wk Bks φ)) Us φ);
        [ unfold Lf; rewrite <- List.app_assoc; reflexivity | exact Hc | exact Hj | exact (cons_lookup_in _ _ _ Hcon) | exact HUl |].
      intros j' Mj' Hj'; exact (blocks_motives_wk _ _ _ _ _ HBnm Hj'). }
    rewrite List.app_assoc.
    eapply (nf_str_sorted _ _ _ _ IHB (elim_bctx ak_relevant pc D Mj gs (blocks_motives Bks) Us ++ Δ) _ Typeω@i).
    - apply List.Forall_app; split; [ eapply elim_bctx_ass; eassumption | exact Hass ].
    - rewrite HLb; eapply ext_eq_ctx_left; exact (blocks_typed_bctx _ _ _ _ _ _ _ _ _ HBt _ _ _ _ Hj Hcon).
    - apply type_sort_universe.
    - rewrite <- List.app_assoc; exact Hbt.
    - rewrite HLb, List.length_app, length_elim_bctx, wk_qn_plus; fold φ.
      replace (cargs_nrec D gs + List.length gs + im_nn Mj) with (im_nn Mj + List.length gs + cargs_nrec D gs) by lia.
      rewrite (elim_branch_type_wk pc D j Mj c gs (eb_motive b) Us φ Hc Hj HUl), <- Hn; exact HBL. }
  assert (HBts : blocks_typed gc_deps gc_stack (Δ ++ Γ)%list pc D Us Bks ak_relevant i).
  { constructor; [ exact HBl | exact HBnm | | exact HBmot | | | | | exact HBbr | exact (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt) ].
    - (** The scrutinee type, short: typed by its induction hypothesis,
          and below the member's type and above it by
          [subtyp_strengthen_sort], under the non-uniform parameters. *)
      intros j Mj b Hj Hb0.
      pose proof (proj1 (List.Forall_forall _ _) IHBs b (List.nth_error_In _ _ Hb0)) as (IHz & _ & _).
      pose proof (blocks_typed_scrutinee_type _ _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as HzL.
      rewrite (HBnm _ _ _ Hj Hb0) in HzL; cbn [Nat.sub] in HzL.
      pose proof (elim_mctx_wk pc D j Mj Us φ Hc Hj HUl) as EW.
      unfold elim_mctx in EW, HzL |- *; cbn [tele_wk] in EW; injection EW as EWh EWt.
      set (Ψ := tele_sub (im_nparams Mj) (sb_of_list Id Us)) in *.
      assert (HΨl : List.length Ψ = im_nn Mj) by (unfold Ψ, im_nn; apply length_tele_sub).
      rewrite HΨl in EWh.
      cbn [eb_scrutinee_type] in HzL; rewrite Nat.sub_0_r in HzL.
      destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ HzL) as [SZ HSZ SX' HSX' _ HZt _ HZs HZs'].
      pose proof (HUt' _ _ Hj) as HmS; unfold elim_mctx in HmS; fold Ψ in HmS.
      pose proof (ctx_decomp_left HmS) as HΨS; destruct (ctx_decomp_kind HmS) as (SX & HSX & HX).
      assert (HassΨ : all_assumptions (Ψ ++ Δ)%list)
        by (apply List.Forall_app; split; [ apply all_assumptions_sub; eapply decl_closed_nparams_ass; eassumption | exact Hass ]).
      assert (HLz : (tele_wk (Ψ ++ Δ) ↑ ++ Γ ▹{κ} A)%list = (tele_sub (im_nparams Mj) (sb_of_list Id (List.map (fun U => U[φ]ʷ) Us)) ++ Lf)%list)
        by (rewrite tele_wk_app; fold φ; rewrite EWt; unfold Lf; rewrite <- List.app_assoc; reflexivity).
      assert (Ewk : wk_qn (List.length (Ψ ++ Δ)) ↑ = wk_qn (im_nn Mj) φ)
        by (rewrite List.length_app, HΨl, wk_qn_plus; reflexivity).
      assert (HΓz : ⊢ (tele_wk (Ψ ++ Δ) ↑ ++ Γ ▹{κ} A)%list) by (rewrite HLz; gen_presups; assumption).
      inversion HSZ; subst.
      assert (HZs0 : (Ψ ++ Δ ++ Γ)%list ⊢ eb_scrutinee_type b : Typeω@i0).
      { rewrite List.app_assoc.
        eapply (nf_str_sorted _ _ _ _ IHz (Ψ ++ Δ) _ Typeω@(S i0)); [ exact HassΨ | exact HΓz | apply type_sort_universe
                                               | rewrite <- List.app_assoc; apply wf_typ; exact HΨS |].
        rewrite HLz, Ewk; exact HZt. }
      eapply wf_ext_eq_ass; [ apply ctx_ext_refl; [ apply all_assumptions_sub; eapply decl_closed_nparams_ass; eassumption | exact HΨS ]
                            | exact HZs0 | constructor | exact HX | exact HSX | |].
      + rewrite List.app_assoc.
        eapply (subtyp_strengthen_sort (Ψ ++ Δ) Γ κ A); [ exact HassΨ | exact HΓz | apply (type_sort_universe i0)
                                                        | exact (sort_kind_type_sort _ _ HSX)
                                                        | rewrite <- List.app_assoc; exact HZs0
                                                        | rewrite <- List.app_assoc; exact HX |].
        rewrite HLz, Ewk, EWh; exact HZs.
      + rewrite List.app_assoc.
        eapply (subtyp_strengthen_sort (Ψ ++ Δ) Γ κ A); [ exact HassΨ | exact HΓz | exact (sort_kind_type_sort _ _ HSX)
                                                        | apply (type_sort_universe i0)
                                                        | rewrite <- List.app_assoc; exact HX
                                                        | rewrite <- List.app_assoc; exact HZs0 |].
        rewrite HLz, Ewk, EWh; exact HZs'.
    - intros j Mj Hj; apply ctx_ext_refl; [ eapply elim_mctx_ass; eassumption | exact (HUt' _ _ Hj) ].
    - intros j Mj b Hj Hb0; pose proof (blocks_typed_names _ _ _ _ _ _ _ _ _ HBt _ _ _ Hj (Hbw _ _ Hb0)) as H; cbn [eb_brs] in H.
      unfold brs_names in *; rewrite List.map_map in H; exact H.
    - intros j Mj c gs Hj Hcon; apply ctx_ext_refl; [ eapply elim_bctx_ass; eassumption |].
      eapply elim_bctx_wf; [ exact Hg | exact HDs | exact Hl | exact Hj | exact HΓs | exact HUl | exact Hσ | exact HUt'
                           | exact HAs | exact (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt) | exact Hcon ].
    - intros j Mj b c gs n B Hj Hb0 Hcon Hin.
      pose proof (List.in_map (fun br => (fst br, (snd br)[wk_qn (snd (fst br)) φ]ʷ)) _ _ Hin) as Hin'; cbn [fst snd] in Hin'.
      exact (blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt _ _ _ _ _ _ _ Hj (Hbw _ _ Hb0) Hcon Hin'). }
  (** The eliminator, short, at a type whose weakening is below [C]. *)
  destruct (blocks_nth _ _ _ _ Hsuf HBl Hm Hnr) as [bm0 Hbm0].
  rewrite (Hbw _ _ Hbm0) in Hb; injection Hb as <-.
  pose proof (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hm Hbm0 HBts HUl HUt HNl HNt HuS) as Hel.
  assert (exists Se, type_sort Se /\ (Δ ++ Γ)%list ⊢ (eb_motive bm0)[sb_of_list Id (NsS ++ u :: nil)] : Se) as (Se & HSe & Hi').
  { (** an eliminator is no type of levels *)
    pose proof (presup_exp_typ_cases Hel) as Hp; inversion Hp; [ eexists; split; eassumption |].
    match goal with H : level_type_former _ |- _ => inversion H end. }
  apply (mk_short_typ _ _ _ _ _ _ _ Se HSe Hel Hi'); fold φ Lf.
  cbn [eb_motive] in Hmot, Hs; rewrite (HBnm _ _ _ Hm Hbm0) in Hmot, Hs.
  rewrite exp_wk_sb_of_list, List.map_app; cbn [List.map].
  replace (List.length (NsS ++ u :: nil)) with (S (im_nn Mm)) by (rewrite List.length_app, HNl; cbn; lia).
  etransitivity; [| exact Hs ].
  eapply wf_subtyp_refl'; symmetry; exact Hmot.
Qed.

(** ** Records *)

(** A record's type former: typed at its closed type in every context. *)
Lemma record_str : forall Γ κ A p, exp_str Γ κ A (a_record p).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_record_inversion HW) as [R Hl Hnd Hass0 i Hty HF HS HFs Hs].
  pose proof (wf_record_closed _ _ _ _ _ HΓs Hl) as Hc.
  apply (mk_short_typ _ _ _ _ _ _ (record_ty R) Typeω@i (type_sort_universe i)).
  - eapply wf_record; [ exact HΓs | eassumption .. ].
  - exact (closed_weaken_exp _ _ _ _ _ HΓs Hty (record_ty_scoped _ Hc) ltac:(cbn; exact I)).
  - rewrite (record_ty_wk R _ Hc); exact Hs.
Qed.

(** The parameters and the fields of a tuple, as one instance of the
    fields' telescope over the parameters. *)
Lemma tuple_insts_all : forall Γ R Ns (fs : list (String.string * exp)), all_assumptions (record_params R) ->
    List.length Ns = List.length (record_params R) -> List.map fst fs = List.map fst (record_fields R) ->
    (forall j N B, List.nth_error (Ns ++ List.map snd fs) j = Some N ->
       List.nth_error (tele_insts (record_fctx R (List.length (record_fields R)) ++ record_params R) Id (Ns ++ List.map snd fs)) j
         = Some B -> Γ ⊢ N : B) <->
    ((forall j N B, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some B -> Γ ⊢ N : B) /\
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))])).
Proof.
  intros * Hass Hn Hfs.
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  set (n := List.length (record_fields R)) in *.
  assert (Hti : tele_insts (record_fctx R n ++ record_params R) Id (Ns ++ List.map snd fs)
                = tele_insts (record_params R) Id Ns ++ tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs))
    by (apply tele_insts_app; [ exact Hass | exact Hn ]).
  assert (HlT : List.length (tele_insts (record_params R) Id Ns) = List.length Ns)
    by (rewrite length_tele_insts by exact Hass; lia).
  (** The entry of the field [k] is its type at the parameters and the
      fields before it. *)
  assert (Hfield : forall k f U, List.nth_error (record_fields R) k = Some (f, U) ->
            List.nth_error (tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs)) k
            = Some U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]).
  { intros k f U Hk.
    assert (Hkl : k < n) by exact (nth_error_lt_length _ _ _ Hk).
    destruct (nth_error_lt_some (tele_insts (record_fctx R n) (sb_of_list Id Ns) (List.map snd fs)) k) as [T HT].
    { rewrite length_tele_insts by exact (record_fctx_ass R n).
      rewrite length_record_fctx, List.length_map by lia; lia. }
    rewrite HT; destruct (tele_insts_nth _ _ _ _ _ HT) as (κ0 & A0 & HA0 & ->).
    rewrite Completeness.Records.Model.rev_record_fctx, nth_error_firstn_lt in HA0 by exact Hkl.
    unfold Completeness.Records.Model.field_tele in HA0.
    destruct (Completeness.Records.Model.fields_tele_in_order_nth _ _ _ _ _ HA0) as (f' & Hk' & _).
    rewrite Hk in Hk'; injection Hk' as _ <-; rewrite <- sb_of_list_app; reflexivity. }
  split.
  - intros H; split.
    + intros j N B HN HB.
      assert (Hj : j < List.length Ns) by exact (nth_error_lt_length _ _ _ HN).
      apply (H j); [ rewrite List.nth_error_app1 by exact Hj; exact HN | rewrite Hti, List.nth_error_app1 by lia; exact HB ].
    + intros k f M U Hk Hfk.
      apply (H (List.length Ns + k)).
      * rewrite List.nth_error_app2 by lia.
        replace (List.length Ns + k - List.length Ns) with k by lia.
        rewrite List.nth_error_map, Hk; reflexivity.
      * rewrite Hti, List.nth_error_app2 by lia; rewrite HlT.
        replace (List.length Ns + k - List.length Ns) with k by lia.
        exact (Hfield _ _ _ Hfk).
  - intros [HN HM] j N B Hj HB.
    rewrite Hti in HB.
    destruct (Nat.lt_ge_cases j (List.length Ns)) as [Hlt | Hge].
    + rewrite List.nth_error_app1 in Hj by exact Hlt; rewrite List.nth_error_app1 in HB by lia.
      exact (HN _ _ _ Hj HB).
    + rewrite List.nth_error_app2 in Hj by exact Hge; rewrite List.nth_error_app2 in HB by lia; rewrite HlT in HB.
      set (k := j - List.length Ns) in *.
      rewrite List.nth_error_map in Hj.
      destruct (List.nth_error fs k) as [[g M] |] eqn:Hk; cbn in Hj; [ injection Hj as <- | discriminate ].
      assert (Hkl : k < n) by (rewrite <- Hlf; exact (nth_error_lt_length _ _ _ Hk)).
      destruct (nth_error_lt_some (record_fields R) k Hkl) as [[f U] Hfk].
      assert (g = f) as ->.
      { pose proof (List.map_nth_error fst _ _ Hk) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
        rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      rewrite (Hfield _ _ _ Hfk) in HB; injection HB as <-.
      exact (HM _ _ _ _ Hk Hfk).
Qed.

(** A tuple of a record type: its parameters and fields, strengthened as
    one instance of the fields' telescope over the parameters, at its
    record type, whose weakening is below the long type. *)
Lemma tuple_str : forall Γ κ A p Ms fs, List.Forall (nf_str_exp Γ κ A) Ms -> List.Forall (nf_str_exp Γ κ A) (List.map snd fs) ->
    nf_str_exp Γ κ A (a_tuple (apps (a_record p) Ms) fs).
Proof.
  intros * IHMs IHFs Δ T Hass HΓf HTt HW.
  (** A tuple is no type of levels. *)
  destruct HTt as [T S HS HT | _]; [| exfalso; cbn [exp_wk] in HW; pose proof (level_sort_typed_former HW) as Hf; inversion Hf ].
  set (φ := wk_qn (length Δ) ↑) in *.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
  cbn [exp_wk] in HW; rewrite apps_exp_wk in HW; cbn [exp_wk] in HW.
  set (fsφ := List.map (fun f => (fst f, (snd f)[φ]ʷ)) fs) in *.
  destruct (wf_tuple_inversion HW) as [p' R Ns' i' HTa HTe Hr Hl Hn HNs Hnames HFt Hsub].
  destruct (exp_eq_record_apps_head _ _ _ _ _ _ _ HTe Hl Hn) as [<- HMl].
  rewrite List.length_map in HMl.
  destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd HassR i0 Hty HF HSR HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓs Hl) as Hc.
  assert (HΓl : ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) by exact HΓf.
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), <- Hnames;
        unfold fsφ; rewrite !List.map_map; reflexivity).
  assert (Hnames0 : List.map fst fs = List.map fst (record_fields R))
    by (rewrite <- Hnames; unfold fsφ; rewrite List.map_map; reflexivity).
  (** The long parameters, and their equations with the inverted ones. *)
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HTa ltac:(rewrite List.length_map; exact HMl)) as HMsL.
  pose proof (exp_eq_record_apps_inv _ _ _ _ _ _ Hl (symmetry HTe) Hn ltac:(rewrite List.length_map; exact HMl) HNs HMsL) as [_ HNM].
  (** The long fields, at the long parameters. *)
  assert (HFtL : forall k f M U, List.nth_error fsφ k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
            (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M : U[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ms ++ List.firstn k (List.map snd fsφ))]).
  { intros k f M U Hk Hfk.
    assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    pose proof (record_fields_insts_eq _ _ _ p R Ns' (List.map (fun N => N[φ]ʷ) Ms) fsφ fsφ Hr Hl Hn
                  ltac:(rewrite List.length_map; exact HMl) HNM Hnames eq_refl
                  ltac:(intros * HM HM' HU; rewrite HM in HM'; injection HM' as <-; apply wf_exp_eq_refl; eapply HFt; eassumption)
                  k ltac:(lia)) as Hins.
    destruct (record_field_typ_cong _ _ _ R k f U (Ns' ++ List.firstn k (List.map snd fsφ))
                (List.map (fun N => N[φ]ʷ) Ms ++ List.firstn k (List.map snd fsφ)) Hc HassR HF HΓl Hfk
                ltac:(rewrite List.length_app, List.length_firstn, List.length_map; unfold fsφ; rewrite List.length_map; lia)
                ltac:(rewrite !List.length_app, List.length_firstn, !List.length_map; unfold fsφ; rewrite List.length_map; lia)
                Hins) as (S0 & HS0 & HUU).
    exact (exp_conv_sort HS0 HUU (HFt _ _ _ _ Hk Hfk)). }
  assert (HallL := proj2 (tuple_insts_all _ R (List.map (fun N => N[φ]ʷ) Ms) fsφ HassR ltac:(rewrite List.length_map; exact HMl) Hnames)
                     (conj HMsL HFtL)).
  (** The short parameters and fields, as one instance. *)
  set (C := record_fctx R (List.length (record_fields R)) ++ record_params R).
  assert (HsC : ctx_scoped 0 C)
    by (apply record_fctx_scoped; [ lia | intros; eapply closed_fields; eassumption | exact (closed_params _ Hc) ]).
  assert (HassC : all_assumptions C) by (apply record_fctx_params_ass; exact HassR).
  assert (HCΓ : ⊢ (C ++ (Δ ++ Γ))%list) by (exact (record_fctx_app_wf _ _ R _ _ (le_n _) Hc HassR HF HΓs)).
  assert (Hsφ : List.map snd fsφ = List.map (fun N => N[φ]ʷ) (List.map snd fs))
    by (unfold fsφ; rewrite !List.map_map; reflexivity).
  assert (Hall : forall j N B, List.nth_error (Ms ++ List.map snd fs) j = Some N -> List.nth_error (tele_insts C Id (Ms ++ List.map snd fs)) j = Some B ->
            (Δ ++ Γ)%list ⊢ N : B).
  { eapply tele_insts_typed_all; [ exact HassC | exact HCΓ | apply wf_sub_id; exact HΓs |].
    intros j N B HN HB (SB & HSB & HBt).
    assert (HNstr : nf_str_exp Γ κ A N).
    { pose proof (List.nth_error_In _ _ HN) as HNi; apply List.in_app_or in HNi as [HNi | HNi];
        [ exact (proj1 (List.Forall_forall _ _) IHMs _ HNi) | exact (proj1 (List.Forall_forall _ _) IHFs _ HNi) ]. }
    apply (nf_str_sorted _ _ _ _ HNstr Δ B SB Hass HΓf HSB HBt).
    apply (HallL j).
    - rewrite Hsφ, <- List.map_app, List.nth_error_map, HN; reflexivity.
    - rewrite Hsφ, <- List.map_app, <- (tele_insts_closed_wk _ _ _ HassC HsC), List.nth_error_map, HB; reflexivity. }
  destruct (proj1 (tuple_insts_all _ R Ms fs HassR HMl Hnames0) Hall) as [HMsS HFsS].
  (** The short tuple, at its record type. *)
  assert (Hrs : (Δ ++ Γ)%list ⊢ a_record p : record_ty R) by (eapply wf_record; [ exact HΓs | eassumption .. ]).
  destruct (record_sort_large _ _ _ _ _ _ Hrs Hl HMl HMsS) as [m Hm].
  assert (HaS : (Δ ++ Γ)%list ⊢ apps (a_record p) Ms : Typeω@m).
  { pose proof (wf_exp_eq_record_apps _ _ _ _ _ _ _ Hrs Hl HMl HMl
                  ltac:(intros j0 X Y B HX HY HB; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HMsS; eassumption))
      as HE.
    eapply wf_exp_subtyp; [ gen_presups; eassumption | apply wf_typ; exact HΓs | constructor | exact Hm ]. }
  assert (Hts : (Δ ++ Γ)%list ⊢ a_tuple (apps (a_record p) Ms) fs : apps (a_record p) Ms)
    by (eapply wf_tuple; [ exact HaS | apply wf_exp_eq_refl; exact HaS | exact Hrs | exact Hl | exact HMl | exact HMsS
                         | exact Hnames0 | exact HFsS ]).
  eapply wf_exp_subtyp; [ exact Hts | exact HT | exact HS |].
  eapply subtyp_strengthen_sort; [ exact Hass | exact HΓf | apply type_sort_universe | exact HS | exact HaS | exact HT |].
  rewrite apps_exp_wk; exact Hsub.
Qed.

(** A projection of a neutral: the neutral's short type is a record type
    ([typ_record_shape_strengthen]), whose field the projection is at. *)
Lemma proj_str : forall Γ κ A f u, exp_str Γ κ A u -> exp_str Γ κ A (a_proj f u).
Proof.
  intros Γ κ A f u IHu Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  set (φ := wk_qn (length Δ) ↑) in *.
  destruct (wf_proj_inversion HW) as [p R Ns k U Sp HM Hr Hl Hn HNs Hfk HU HSp Hsub].
  destruct (IHu _ _ Hass HΓf HΓs HM) as [T0 S0 HS0 HuT HT0 Hs0].
  (** A record type is of a large universe, so no proposition is below
      it: the short type is at a universe. *)
  destruct (record_sort_large _ _ _ _ _ _ Hr Hl Hn HNs) as [nR HnR].
  assert (HRt : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ apps (a_record p) Ns : Typeω@nR).
  { eapply wf_exp_subtyp; [| apply wf_typ; exact HΓf | constructor | exact HnR ].
    eapply presup_exp_eq_left, wf_exp_eq_record_apps; [ exact Hr | exact Hl | exact Hn | exact Hn |].
    intros j0 X Y B HX HY HB; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HNs; eassumption. }
  destruct HS0 as [j0 | |];
    [| exfalso; exact (subtyp_prop_relevant_absurd Hs0 (short_wk_sort _ _ _ _ _ _ HΓf HT0 type_sort_prop) HRt)
     | exfalso; exact (record_type_not_level (subtyp_level_type_right (short_wk_sort _ _ _ _ _ _ HΓf HT0 type_sort_level) Hs0)) ].
  destruct (typ_record_shape_strengthen _ _ _ _ _ _ _ _ Hass HΓf HT0 Hs0) as [Rs HRs].
  destruct (typ_record_shape _ _ _ _ _ HT0 HRs) as (R' & Ps & Hl' & HPl & HPt & HTP & _).
  rewrite Hl in Hl'; injection Hl' as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓs Hl) as Hc.
  assert (Hrs : (Δ ++ Γ)%list ⊢ a_record p : record_ty R)
    by (destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd HassR i0 Hty HF HS HFs _];
        rewrite Hl in Hl0; injection Hl0 as <-; eapply wf_record; [ exact HΓs | eassumption .. ]).
  assert (Hus : (Δ ++ Γ)%list ⊢ u : apps (a_record p) Ps) by (eapply wf_conv'; [ exact HuT | exact HTP ]).
  destruct (record_sort_large _ _ _ _ _ _ Hrs Hl HPl HPt) as [m Hm].
  destruct (record_proj_cong_at _ _ _ u u p R Ps m k f U ltac:(apply wf_exp_eq_refl; exact Hus) Hrs Hl HPl HPt Hm Hfk)
    as [HUU Hpp].
  assert (HUs : (Δ ++ Γ)%list ⊢ U[sb_of_list Id (Ps ++ record_pre R k u)] : abs_kind_sort (record_field_kind R k) Typeω@m)
    by (gen_presups; assumption).
  apply (mk_short_typ _ _ _ _ _ _ (U[sb_of_list Id (Ps ++ record_pre R k u)]) (abs_kind_sort (record_field_kind R k) Typeω@m)
           (type_sort_abs_kind _ _(type_sort_universe m))); [ gen_presups; assumption | exact HUs |].
  (** The weakened short type is the long one at equal parameters. *)
  fold φ.
  rewrite (record_field_wk R k f U Ps (record_pre R k u) φ Hc Hfk HPl ltac:(apply length_record_pre; pose proof (nth_error_lt_length _ _ _ Hfk); lia)),
    record_pre_wk.
  assert (HTPφ : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ T0[φ]ʷ ≈ apps (a_record p) (List.map (fun N => N[φ]ʷ) Ps) : Typeω@j0)
    by (pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTP) as H; rewrite apps_exp_wk in H; exact H).
  assert (HPN : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ apps (a_record p) (List.map (fun N => N[φ]ʷ) Ps) ⊆ apps (a_record p) Ns)
    by (etransitivity; [ eapply wf_subtyp_refl'; symmetry; exact HTPφ | exact Hs0 ]).
  destruct (subtyp_record_inv HPN) as (SL & HSLs & HPNe0).
  destruct (exp_eq_sort_large HSLs HPNe0 (or_intror HRt)) as [kk HPNe]; clear SL HSLs HPNe0.
  assert (HPφl : List.length (List.map (fun N => N[φ]ʷ) Ps) = List.length (record_params R)) by (rewrite List.length_map; exact HPl).
  assert (HPφt : forall j N B, List.nth_error (List.map (fun N => N[φ]ʷ) Ps) j = Some N ->
             List.nth_error (tele_insts (record_params R) Id (List.map (fun N => N[φ]ʷ) Ps)) j = Some B ->
             (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ N : B)
    by (eapply wf_record_apps_inv; [ exact Hl | gen_presups; eassumption | exact HPφl ]).
  destruct (exp_eq_record_apps_inv _ _ _ _ _ _ Hl HPNe HPφl Hn HPφt HNs) as [_ HPNs].
  assert (Huφ : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ u[φ]ʷ : apps (a_record p) (List.map (fun N => N[φ]ʷ) Ps))
    by (pose proof (short_wk_exp _ _ _ _ _ _ HΓf Hus) as H; rewrite apps_exp_wk in H; exact H).
  destruct (record_sort_large _ _ _ _ _ _ Hr Hl HPφl HPφt) as [n Hn'].
  pose proof (record_field_params_cong _ _ _ (u[φ]ʷ) p R (List.map (fun N => N[φ]ʷ) Ps) Ns n k f U Huφ Hr Hl HPφl Hn HPφt HPNs Hn' Hfk)
    as HE.
  etransitivity; [| exact Hsub ].
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE)
                  (type_sort_abs_kind _ _(type_sort_universe n)) HE)).
Qed.

(** ** The Cases at a Sort *)

(** A sort is unchanged by a weakening. *)
Lemma type_sort_wk : forall Srt φ, type_sort Srt -> Srt[φ]ʷ = Srt.
Proof. intros * [i | |]; reflexivity. Qed.

(** A sort is a type ([⊢ᵗ]): the large universes and [Prop] are of a large
    universe, [LevelSort] is the sort of the types of levels. *)
Lemma type_sort_wf_type : forall Γ Srt, ⊢ Γ -> type_sort Srt -> Γ ⊢ᵗ Srt.
Proof.
  intros * HΓ [i | |];
    [ eapply wf_type_of_sort; [ apply (type_sort_universe (S i)) | apply wf_typ, HΓ ]
    | eapply wf_type_of_sort; [ apply (type_sort_universe 0) | eapply wf_prop_large; exact HΓ ]
    | apply wf_type_level_sort, HΓ ].
Qed.

(** A term strengthens at a sort: the sort is its own weakening. *)
Lemma nf_str_at_sort : forall Γ κ A W Δ Srt,
    nf_str_exp Γ κ A W -> all_assumptions Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> ⊢ (Δ ++ Γ)%list -> type_sort Srt ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ W[wk_qn (length Δ) ↑]ʷ : Srt ->
    (Δ ++ Γ)%list ⊢ W : Srt.
Proof.
  intros * IH Hass HΓf HΓs HS HW.
  apply (IH Δ Srt Hass HΓf (type_sort_wf_type _ _ HΓs HS)).
  rewrite (type_sort_wk _ _ HS); exact HW.
Qed.

(** A term of a closed type [K] below the weakened [T] is of [T]. *)
Lemma typed_at_closed_strengthen : forall Δ Γ κ A W K SK T Srt,
    all_assumptions Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> type_sort SK -> type_sort Srt ->
    (Δ ++ Γ)%list ⊢ W : K -> (Δ ++ Γ)%list ⊢ K : SK -> (Δ ++ Γ)%list ⊢ T : Srt ->
    K[wk_qn (length Δ) ↑]ʷ = K ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ K ⊆ T[wk_qn (length Δ) ↑]ʷ ->
    (Δ ++ Γ)%list ⊢ W : T.
Proof.
  intros * Hass HΓf HSK HS HW HK HT HKc Hs.
  eapply wf_exp_subtyp; [ exact HW | exact HT | exact HS |].
  eapply subtyp_strengthen_sort; [ exact Hass | exact HΓf | exact HSK | exact HS | exact HK | exact HT | rewrite HKc; exact Hs ].
Qed.

(** Two types of sorts in the short context, equal weakened at a sort, are
    equal at a sort the first is of. *)
Lemma exp_eq_strengthen_sort : forall Δ Γ κ A M N S1 S2 S0,
    all_assumptions Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> type_sort S1 -> type_sort S2 -> type_sort S0 ->
    (Δ ++ Γ)%list ⊢ M : S1 -> (Δ ++ Γ)%list ⊢ N : S2 ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ ≈ N[wk_qn (length Δ) ↑]ʷ : S0 ->
    exists Srt, type_sort Srt /\ (Δ ++ Γ)%list ⊢ M : Srt /\ (Δ ++ Γ)%list ⊢ M ≈ N : Srt.
Proof.
  intros * Hass HΓf HS1 HS2 HS0 HM HN HMN.
  pose proof (short_wk_sort _ _ _ _ _ _ HΓf HM HS1) as HMl.
  pose proof (short_wk_sort _ _ _ _ _ _ HΓf HN HS2) as HNl.
  assert ((tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ M[wk_qn (length Δ) ↑]ʷ : S0 /\
          (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ N[wk_qn (length Δ) ↑]ʷ : S0) as [HM0 HN0] by (gen_presups; split; assumption).
  destruct HS0 as [k | |].
  - destruct HS1 as [j1 | |]; [| exfalso; exact (typ_prop_absurd HM0 HMl) | exfalso; exact (level_type_not_large HMl HM0) ].
    destruct HS2 as [j2 | |]; [| exfalso; exact (typ_prop_absurd HN0 HNl) | exfalso; exact (level_type_not_large HNl HN0) ].
    exists Typeω@(max k (max j1 j2)); split; [ constructor | split ]; [ eapply lift_exp_ge; [| exact HM ]; lia |].
    eapply exp_eq_strengthen; [ exact Hass | exact HΓf | eapply lift_exp_ge; [| exact HM ]; lia
                              | eapply lift_exp_ge; [| exact HN ]; lia |].
    eapply lift_exp_eq_ge; [| exact HMN ]; lia.
  - destruct HS1 as [j1 | |]; [ exfalso; exact (typ_prop_absurd HMl HM0) | | exfalso; exact (level_type_not_prop HMl HM0) ].
    destruct HS2 as [j2 | |]; [ exfalso; exact (typ_prop_absurd HNl HN0) | | exfalso; exact (level_type_not_prop HNl HN0) ].
    exists Propₘ; split; [ constructor | split; [ exact HM |] ].
    eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact HM | exact HN | exact HMN ].
  - (** Types of levels, of [LevelSort] only *)
    destruct HS1 as [j1 | |]; [ exfalso; exact (level_type_not_large HM0 HMl) | exfalso; exact (level_type_not_prop HM0 HMl) |].
    destruct HS2 as [j2 | |]; [ exfalso; exact (level_type_not_large HN0 HNl) | exfalso; exact (level_type_not_prop HN0 HNl) |].
    exists LevelSort; split; [ constructor | split; [ exact HM |] ].
    eapply exp_eq_strengthen; [ exact Hass | exact HΓf | exact HM | exact HN | exact HMN ].
Qed.

(** ** The Cases of the Theorem

    A closed constant [W], typed in every context at a closed type [K] of a
    sort and below every type it has, and no type of levels, strengthens
    ([typed_at_closed_strengthen]); at [LevelSort] it has no type
    ([level_sort_typed_former]). *)
Lemma closed_const_str : forall Γ κ A W K SK,
    (forall φ, W[φ]ʷ = W) -> (forall φ, K[φ]ʷ = K) -> type_sort SK -> ~ level_type_former W ->
    (forall Γ', ⊢ Γ' -> Γ' ⊢ W : K /\ Γ' ⊢ K : SK) ->
    (forall Γ' C, Γ' ⊢ W : C -> Γ' ⊢ K ⊆ C) ->
    nf_str_exp Γ κ A W.
Proof.
  intros * HWc HKc HSK Hnl Hty Hinv Δ T Hass HΓf HTt HW.
  rewrite HWc in HW.
  destruct HTt as [T S HS HT | HΓs].
  - assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
    destruct (Hty _ HΓs) as [HWK HK].
    eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | exact HSK | exact HS | exact HWK | exact HK | exact HT | apply HKc | exact (Hinv _ _ HW) ].
  - exfalso; exact (Hnl (level_sort_typed_former HW)).
Qed.

(** A large universe, [Prop], [⊤] and [⊥]. *)
Lemma typ_str : forall Γ κ A i, nf_str_exp Γ κ A Typeω@i.
Proof.
  intros; apply (closed_const_str _ _ _ _ Typeω@(S i) Typeω@(S (S i)));
    [ intros; reflexivity | intros; reflexivity | constructor | inversion 1 | intros; split; apply wf_typ; assumption
    | intros * H; exact (wf_typ_inversion H) ].
Qed.

Lemma prop_str : forall Γ κ A, nf_str_exp Γ κ A Propₘ.
Proof.
  intros; apply (closed_const_str _ _ _ _ Type@0 (Typeω@0));
    [ intros; reflexivity | intros; reflexivity | constructor | inversion 1 | intros; split; [ apply wf_prop | apply (wf_univ_large (i := 0)) ]; assumption
    | intros * H; exact (wf_prop_inversion _ _ _ _ H) ].
Qed.

Lemma True_str : forall Γ κ A, nf_str_exp Γ κ A ⊤.
Proof.
  intros; apply (closed_const_str _ _ _ _ Propₘ (Typeω@0));
    [ intros; reflexivity | intros; reflexivity | constructor | inversion 1 | intros; split; [ apply wf_True | apply wf_prop_large ]; assumption
    | intros * H; exact (wf_True_inversion _ _ _ _ H) ].
Qed.

Lemma False_str : forall Γ κ A, nf_str_exp Γ κ A ⊥.
Proof.
  intros; apply (closed_const_str _ _ _ _ Propₘ (Typeω@0));
    [ intros; reflexivity | intros; reflexivity | constructor | inversion 1 | intros; split; [ apply wf_False | apply wf_prop_large ]; assumption
    | intros * H; exact (wf_False_inversion _ _ _ _ H) ].
Qed.

(** [Level@n] is of [LevelSort] only ([wf_level_inversion]), which no type
    of a sort weakens to. *)
Lemma level_str : forall Γ κ A n, nf_str_exp Γ κ A Level@n.
Proof.
  intros * Δ T Hass HΓf HTt HW; cbn [exp_wk] in HW.
  apply wf_level_inversion in HW.
  destruct HTt as [T S HS HT | HΓs]; [| apply wf_level, HΓs ].
  exfalso; destruct T; cbn [exp_wk] in HW; try discriminate.
  exact (level_sort_untyped HT).
Qed.

(** [LevelSort] is of no type. *)
Lemma level_sort_str : forall Γ κ A, nf_str_exp Γ κ A LevelSort.
Proof. intros * Δ T Hass HΓf HTt HW; exfalso; exact (level_sort_untyped HW). Qed.

(** A level: a constant with atoms, at the type of levels the atoms are
    of; or a single atom, a neutral.  A level is below no [LevelSort],
    which is of no sort. *)
Lemma lvl_str : forall Γ κ A c xs, level_atoms_all (ne_str Γ κ A) xs -> nf_str_exp Γ κ A (lvl_exp_of c (List.map atom_exp xs)).
Proof.
  intros * IHs Δ T Hass HΓf HTt HW.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (destruct HTt; [ gen_presups; assumption | assumption ]).
  rewrite lvl_exp_of_wk in HW.
  destruct (lvl_exp_of_inv _ _ _ _ HW) as [(n & HsL & Hcn & HF) | (a & -> & Hmap)].
  - destruct HTt as [T S HS HT | _];
      [| exfalso; destruct (presup_subtyp_right_sorted HsL) as (S & _ & HL); exact (level_sort_untyped HL) ].
    assert (Hla : @level_atoms_wf gc_deps gc_stack n (Δ ++ Γ)%list xs)
      by (eapply level_atoms_wf_strengthen; [ exact IHs | exact Hass | exact HΓf | exact HΓs | exact HF ]).
    assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n)
      by (apply lvl_exp_of_wf; [ exact Hcn | assumption | assumption ]).
    eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | apply type_sort_level | exact HS
                                       | exact HL | apply wf_level, HΓs | exact HT | reflexivity | exact HsL ].
  - (** A single atom with no offset is the atom itself. *)
    destruct (level_atoms_map_single _ _ _ Hmap) as (s & u & -> & ->).
    destruct IHs as [Hu _].
    cbn in HW |- *.
    exact (exp_str_at _ _ _ _ Hu Δ T Hass HΓf HTt HW).
Qed.

(** A small universe: its level strengthens atom by atom. *)
Lemma univ_str : forall Γ κ A c xs, level_atoms_all (ne_str Γ κ A) xs ->
    nf_str_exp Γ κ A (a_univ (lvl_exp_of c (List.map atom_exp xs))).
Proof.
  intros * IHs Δ T Hass HΓf HTt HW; cbn [exp_wk] in HW.
  destruct HTt as [T Srt HS HT | _]; [| exfalso; pose proof (level_sort_typed_former HW) as Hf; inversion Hf ].
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
  pose proof (wf_univ_inversion HW) as Hs.
  apply wf_univ_lvl_inversion in HW as [n HW].
  rewrite lvl_exp_of_wk in HW.
  assert (Hla : @level_atoms_wf gc_deps gc_stack n (Δ ++ Γ)%list xs)
    by (eapply level_atoms_wf_strengthen; [ exact IHs | exact Hass | exact HΓf | exact HΓs | eapply lvl_exp_of_atoms; exact HW ]).
  assert (HL : (Δ ++ Γ)%list ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n)
    by (apply lvl_exp_of_wf; [ exact (lvl_exp_of_const_sort HW) | assumption | assumption ]).
  eapply wf_exp_subtyp; [ eapply wf_univ; exact HL | exact HT | exact HS |].
  eapply subtyp_strengthen_sort;
    [ exact Hass | exact HΓf | apply (type_sort_universe 0) | exact HS
    | apply (wf_univ_large_tm (i := 0) (n := n)); [ exact HΓs | eapply wf_succl; exact HL ] | exact HT |].
  exact Hs.
Qed.

(** A conjunction: both parts are propositions. *)
Lemma and_str : forall Γ κ A P Q, nf_str_exp Γ κ A P -> nf_str_exp Γ κ A Q -> nf_str_exp Γ κ A (Σₚ P Q).
Proof.
  intros * IHP IHQ Δ T Hass HΓf HTt HW; cbn [exp_wk] in HW.
  destruct HTt as [T Srt HS HT | _]; [| exfalso; pose proof (level_sort_typed_former HW) as Hf; inversion Hf ].
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
  assert (Hass' : all_assumptions (ce_ass ak_propositional P :: Δ)) by (constructor; [ do 2 eexists; reflexivity | exact Hass ]).
  destruct (wf_and_inversion _ _ _ _ _ _ HW) as [HPl HQl Hs].
  assert (HPs : (Δ ++ Γ)%list ⊢ P : Propₘ)
    by (eapply nf_str_at_sort; [ exact IHP | exact Hass | exact HΓf | exact HΓs | constructor | exact HPl ]).
  assert (HΓs' : ⊢ ((Δ ++ Γ) ▹{ak_propositional} P)%list) by (eapply wf_ctx_extend; [ exact HPs | constructor ]).
  assert (HΓf' : ⊢ (tele_wk (ce_ass ak_propositional P :: Δ) ↑ ++ Γ ▹{κ} A)%list) by (gen_presups; assumption).
  assert (HQs : ((Δ ++ Γ) ▹{ak_propositional} P)%list ⊢ Q : Propₘ)
    by (eapply (nf_str_at_sort _ _ _ _ (ce_ass ak_propositional P :: Δ)); [ exact IHQ | exact Hass' | exact HΓf' | exact HΓs' | constructor | exact HQl ]).
  eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | apply (type_sort_universe 0) | exact HS
                                     | apply wf_and; assumption | eapply wf_prop_large; exact HΓs | exact HT | reflexivity | exact Hs ].
Qed.

(** The sort at a kind next to a universe is a type ([⊢ᵗ]). *)
Lemma univ_kind_sort_wf_type : forall Γ U κ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U -> Γ ⊢ᵗ abs_kind_sort κ U.
Proof.
  intros * HU.
  assert (HΓ : ⊢ Γ) by (inversion HU; subst; [ assumption | gen_presups; assumption ]).
  destruct κ; cbn [abs_kind_sort].
  - inversion HU; subst.
    + eapply wf_type_of_sort; [ apply (type_sort_universe (S i)) | apply wf_typ, HΓ ].
    + eapply wf_type_of_sort; [ apply (type_sort_universe 0) | eapply wf_univ_large_tm; eassumption ].
  - eapply wf_type_of_sort; [ apply (type_sort_universe 0) | apply wf_prop_large, HΓ ].
  - apply wf_type_level_sort, HΓ.
Qed.

(** A [Π] next to a short universe [U], its parts typed long next to the
    weakening of [U], is typed short next to [U] ([wf_pi]). *)
Lemma pi_at_univ_str : forall Γ κ A Δ κd κc A' B' U,
    nf_str_exp Γ κ A A' -> nf_str_exp Γ κ A B' ->
    all_assumptions Δ -> ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ->
    gc_deps ⍮ gc_stack ⍮ (Δ ++ Γ)%list ⊢ᵤ U -> pi_kinds κd κc ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ A'[wk_qn (length Δ) ↑]ʷ : abs_kind_sort κd U[wk_qn (length Δ) ↑]ʷ ->
    ((tele_wk Δ ↑ ++ Γ ▹{κ} A) ▹{κd} A'[wk_qn (length Δ) ↑]ʷ)%list
      ⊢ B'[wk_q (wk_qn (length Δ) ↑)]ʷ : abs_kind_sort κc U[wk_qn (length Δ) ↑]ʷ[↑]ʷ ->
    (Δ ++ Γ)%list ⊢ a_pi κd κc A' B' : abs_kind_sort κc U.
Proof.
  intros * IHA IHB Hass HΓf HU Hk HA HB.
  rewrite <- exp_wk_shift_wk_q, <- !abs_kind_sort_wk in HB; rewrite <- abs_kind_sort_wk in HA.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (inversion HU; subst; [ assumption | gen_presups; assumption ]).
  assert (HAs : (Δ ++ Γ)%list ⊢ A' : abs_kind_sort κd U) by (exact (IHA Δ _ Hass HΓf (univ_kind_sort_wf_type _ _ _ HU) HA)).
  assert (HΓs' : ⊢ ((Δ ++ Γ) ▹{κd} A')%list) by (eapply wf_ctx_extend_univ_kind; eassumption).
  assert (Hass' : all_assumptions (ce_ass κd A' :: Δ)) by (constructor; [ do 2 eexists; reflexivity | exact Hass ]).
  assert (HΓf' : ⊢ (tele_wk (ce_ass κd A' :: Δ) ↑ ++ Γ ▹{κ} A)%list) by (gen_presups; assumption).
  assert (HU' : gc_deps ⍮ gc_stack ⍮ ((Δ ++ Γ) ▹{κd} A')%list ⊢ᵤ U[↑]ʷ).
  { inversion HU; subst; cbn [exp_wk]; [ apply wf_is_univ_large, HΓs' |].
    eapply wf_is_univ_small, (wk_preserves_exp _ _ _ _ Level@_); [ eassumption | mauto 2 ]. }
  assert (HBs : ((Δ ++ Γ) ▹{κd} A')%list ⊢ B' : (abs_kind_sort κc U)[↑]ʷ).
  { apply (IHB (ce_ass κd A' :: Δ) _ Hass' HΓf'); [ rewrite abs_kind_sort_wk; exact (univ_kind_sort_wf_type _ _ _ HU') | exact HB ]. }
  eapply wf_pi; eassumption.
Qed.

(** A [Π]: between types of levels at [LevelSort]; into a proposition, a
    proposition; into a universe next to a large universe, of that one
    ([pi_at_univ_str]); next to a small universe at a long level, the
    short type is a universe ([typ_univ_shape_strengthen]), and the parts,
    moved up to it, are checked against it. *)
Lemma pi_str : forall Γ κ A κd κc A' B', nf_str_exp Γ κ A A' -> nf_str_exp Γ κ A B' -> nf_str_exp Γ κ A (a_pi κd κc A' B').
Proof.
  intros * IHA IHB Δ T Hass HΓf HTt HW; cbn [exp_wk] in HW.
  set (φ := wk_qn (length Δ) ↑) in *.
  set (Lf := (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) in *.
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (destruct HTt; [ gen_presups; assumption | assumption ]).
  destruct (wf_pi_inversion_at HW) as [U HU HA HB Hk Hsub].
  rewrite abs_kind_sort_wk in HB.
  destruct HTt as [T Srt HS HT | _].
  2:{ (** At [LevelSort]: a [Π] between types of levels *)
      pose proof (level_sort_typed_former HW) as Hf; inversion Hf; subst.
      exact (pi_at_univ_str _ _ _ _ _ _ _ _ Typeω@0 IHA IHB Hass HΓf (wf_is_univ_large _ _ _ 0 HΓs) Hk HA HB). }
  destruct (abs_kind_eq_dec κc ak_level) as [-> | Hl].
  - (** A [Π] between types of levels is of no sort's type. *)
    exfalso; destruct Hsub as [Hsub | Hsub]; cbn [abs_kind_sort] in Hsub.
    + destruct T; cbn [exp_wk] in Hsub; try discriminate; exact (level_sort_untyped HT).
    + destruct (presup_subtyp_left_sorted Hsub) as (S0 & _ & HL); exact (level_sort_untyped HL).
  - pose proof (pi_inv_sort_sub HU Hl Hsub) as Hs; clear Hsub.
    inversion HU; subst.
    + (** Next to a large universe *)
      pose proof (pi_at_univ_str _ _ _ _ _ _ _ _ Typeω@i IHA IHB Hass HΓf (wf_is_univ_large _ _ _ i HΓs) Hk HA HB) as HP.
      destruct κc; [| | contradiction Hl; reflexivity ]; cbn [abs_kind_sort] in HP, Hs.
      * eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | apply (type_sort_universe (S i)) | exact HS
                                         | exact HP | apply wf_typ, HΓs | exact HT | reflexivity | exact Hs ].
      * eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | apply (type_sort_universe 0) | exact HS
                                         | exact HP | apply wf_prop_large, HΓs | exact HT | reflexivity | exact Hs ].
    + (** Next to a small universe at a long level: the parts move up to
          any short universe the small one is below. *)
      assert (HLu : Lf ⊢ Type⟨L⟩ : Typeω@0) by (eapply wf_univ_large_tm; eassumption).
      assert (Hlift : forall U2, gc_deps ⍮ gc_stack ⍮ (Δ ++ Γ)%list ⊢ᵤ U2 -> Lf ⊢ Type⟨L⟩ ⊆ U2[φ]ʷ ->
                 (Δ ++ Γ)%list ⊢ a_pi κd κc A' B' : abs_kind_sort κc U2).
      { intros U2 HU2 HsU.
        assert (exists k2, (Δ ++ Γ)%list ⊢ U2 : Typeω@k2) as [k2 Hk2]
          by (inversion HU2; subst; [ eexists; apply wf_typ, HΓs | exists 0; eapply wf_univ_large_tm; eassumption ]).
        pose proof (short_wk_sort _ _ _ _ _ _ HΓf Hk2 (type_sort_universe k2)) as Hk2f; fold φ Lf in Hk2f.
        assert (HΓf1 : ⊢ (Lf ▹{κd} A'[φ]ʷ)%list) by (gen_presups; assumption).
        assert (Hw1 : (Lf ▹{κd} A'[φ]ʷ)%list ⊢ʷ ↑ : Lf) by mauto 2.
        apply (pi_at_univ_str _ _ _ _ _ _ _ _ U2 IHA IHB Hass HΓf HU2 Hk).
        - destruct κd; cbn [abs_kind_sort] in HA |- *; [ eapply wf_exp_subtyp; [ exact HA | exact Hk2f | constructor | exact HsU ] | exact HA | exact HA ].
        - destruct κc; cbn [abs_kind_sort] in HB |- *; [| exact HB | contradiction Hl; reflexivity ].
          eapply wf_exp_subtyp; [ exact HB | | constructor | exact (wk_preserves_subtyp _ _ _ _ _ _ _ HsU Hw1) ].
          eapply (wk_preserves_exp _ _ _ _ Typeω@k2); eassumption. }
      destruct κc; [| | contradiction Hl; reflexivity ]; cbn [abs_kind_sort] in Hs, Hlift.
      * (** Into a universe: the short type is a universe *)
        destruct HS as [i | |].
        -- destruct (typ_univ_shape_strengthen _ _ _ _ _ _ _ Hass HΓf HT (univ_term_suniv L) Hs) as [[j Hj] | [M HM]].
           ++ assert (HTj : (Δ ++ Γ)%list ⊢ T ≈ (Typeωⁿ@j : exp) : Typeω@i) by (eapply soundness_ty'; eassumption).
              cbn [nf_to_exp] in HTj.
              pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTj) as HTjf; cbn [exp_wk] in HTjf; fold φ Lf in HTjf.
              assert (HP : (Δ ++ Γ)%list ⊢ a_pi κd ak_relevant A' B' : Typeω@j)
                by (apply (Hlift Typeω@j (wf_is_univ_large _ _ _ j HΓs)); etransitivity; [ exact Hs | eapply wf_subtyp_refl'; exact HTjf ]).
              eapply wf_exp_subtyp; [ exact HP | exact HT | constructor | eapply wf_subtyp_refl'; symmetry; exact HTj ].
           ++ assert (HTM : (Δ ++ Γ)%list ⊢ T ≈ (nf_univ_of M : exp) : Typeω@i) by (eapply soundness_ty'; eassumption).
              cbn [nf_to_exp nf_univ_of] in HTM.
              set (Mx := lvl_exp_of (fst M) (List.map atom_exp (snd M))) in *.
              assert (exists k, (Δ ++ Γ)%list ⊢ Type⟨Mx⟩ : Typeω@k) as [k Hk'] by (gen_presups; eexists; eassumption).
              destruct (wf_univ_lvl_inversion Hk') as [nM HMx].
              pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTM) as HTMf; cbn [exp_wk] in HTMf; fold φ Lf in HTMf.
              assert (HP : (Δ ++ Γ)%list ⊢ a_pi κd ak_relevant A' B' : Type⟨Mx⟩)
                by (apply (Hlift Type⟨Mx⟩ (wf_is_univ_small _ _ _ _ _ HMx)); etransitivity; [ exact Hs | eapply wf_subtyp_refl'; exact HTMf ]).
              eapply wf_exp_subtyp; [ exact HP | exact HT | constructor | eapply wf_subtyp_refl'; symmetry; exact HTM ].
        -- exfalso; exact (subtyp_relevant_prop_absurd Hs HLu (short_wk_sort _ _ _ _ _ _ HΓf HT type_sort_prop)).
        -- exfalso; pose proof (short_wk_sort _ _ _ _ _ _ HΓf HT type_sort_level) as HTl.
           discriminate (subtyp_same_kind _ _ _ ak_relevant ak_level 0 0 Hs HLu HTl).
      * (** Into a proposition: a proposition *)
        assert (HP : (Δ ++ Γ)%list ⊢ a_pi κd ak_propositional A' B' : Propₘ)
          by (apply (Hlift Typeω@0 (wf_is_univ_large _ _ _ 0 HΓs)); eapply wf_subtyp_small_large; eassumption).
        eapply typed_at_closed_strengthen; [ exact Hass | exact HΓf | apply (type_sort_universe 0) | exact HS
                                           | exact HP | apply wf_prop_large, HΓs | exact HT | reflexivity | exact Hs ].
Qed.

(** A type above a [Π] into an evaluated kind is a [Π] into that kind
    ([subtyp_spec]). *)
Lemma subtyp_pi_kind_left_shape : forall Γ κd κc A B T, evaluated_kind κc -> Γ ⊢ a_pi κd κc A B ⊆ T ->
    exists A' B' k, Γ ⊢ T ≈ a_pi κd κc A' B' : abs_kind_sort κc Typeω@k.
Proof.
  intros * Hev H.
  assert (exists C, Γ ⊢ a_pi κd κc A B : C) as [C HC] by (gen_presups; eexists; eassumption).
  destruct (wf_pi_typed_kind Hev HC) as [k0 Hk0].
  destruct (subtyp_spec H)
    as [(S & HS & Heq) | [(U & V & [k1 HU] & [k2 HV] & HUV)
       | [(κ1 & κc1 & A1 & A2 & B1 & B2 & Hev1 & [k1 Ha] & [k2 Hb] & _ & _) | (m & n & _ & HL & _)]]].
  - assert (exists k, Γ ⊢ a_pi κd κc A B ≈ T : abs_kind_sort κc Typeω@k) as [k Heq']
      by (eapply exp_eq_kind_sort; [ exact HS | exact Hev | exact Heq | left; exact Hk0 ]).
    exists A, B, k; symmetry; exact Heq'.
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *.
    + destruct (univ_sub_sort_term HUV) as [HUt _]; eapply (pi_sort_term_absurd HUt); exact HU.
    + assert (Γ ⊢ a_pi κd ak_level A B : Typeω@k1) by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
  - assert (κc1 = κc) as ->.
    { destruct Hev, Hev1; cbn [abs_kind_sort] in *; try reflexivity; exfalso;
        (assert (Γ ⊢ a_pi κd _ A B : LevelSort) by (gen_presups; first [ exact Hk0 | eassumption ]));
        (assert (exists k, Γ ⊢ a_pi κd _ A B : Typeω@k) as [? ?] by (gen_presups; eexists; first [ exact Hk0 | eassumption ]));
        eapply level_type_not_large; eassumption. }
    destruct (exp_eq_pi_kind_inversion Hev Ha) as (<- & _ & _).
    exists B1, B2, k2; symmetry; exact Hb.
  - exfalso; destruct Hev; cbn [abs_kind_sort] in *.
    + assert (Γ ⊢ a_pi κd ak_relevant A B : LevelSort) by (gen_presups; assumption).
      eapply level_type_not_large; eassumption.
    + eapply exp_eq_level_pi_level_absurd; symmetry; exact HL.
Qed.

(** [short_sort_kind] with the short type above. *)
Lemma short_sort_kind_r : forall Δ Γ κ A T0 S0 C r k,
    ⊢ (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list -> ⊢ (Δ ++ Γ)%list ->
    type_sort S0 -> (Δ ++ Γ)%list ⊢ T0 : S0 ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ C : abs_kind_sort r Typeω@k ->
    (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ C ⊆ T0[wk_qn (length Δ) ↑]ʷ ->
    exists j, S0 = abs_kind_sort r Typeω@j.
Proof.
  intros * HΓf HΓs HS0 HT0 HC Hs.
  assert (Hwk : (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list ⊢ʷ (wk_qn (length Δ) ↑) : (Δ ++ Γ)%list) by (apply wf_wk_qn; assumption).
  pose proof (wk_preserves_sort _ _ _ _ _ _ _ HT0 HS0 Hwk) as HT0f.
  destruct HS0 as [j | |]; cbn in HT0f.
  - pose proof (subtyp_same_kind _ _ _ r ak_relevant k j Hs HC HT0f) as ->; exists j; reflexivity.
  - pose proof (subtyp_same_kind _ _ _ r ak_propositional k 0 Hs HC HT0f) as ->; exists 0; reflexivity.
  - pose proof (subtyp_same_kind _ _ _ r ak_level k 0 Hs HC HT0f) as ->; exists 0; reflexivity.
Qed.

(** A type of a sort at a kind is, at any other sort it has, at the same
    kind ([subtyp_same_kind]). *)
Lemma sort_kind_of_typed : forall Γ M S S' κ, Γ ⊢ M : S -> sort_kind S κ -> Γ ⊢ M : S' -> type_sort S' -> sort_kind S' κ.
Proof.
  intros * HM HS HM' HS'.
  destruct (sort_kind_abs_kind_sort_inv _ _ HS) as [a ->].
  assert (Hs : Γ ⊢ M ⊆ M) by (eapply wf_subtyp_refl; [ exact HM' | exact HS' | apply wf_exp_eq_refl; exact HM' ]).
  destruct HS' as [j | |].
  - rewrite (subtyp_same_kind _ _ _ κ ak_relevant a j Hs HM HM'); constructor.
  - rewrite (subtyp_same_kind _ _ _ κ ak_propositional a 0 Hs HM HM'); constructor.
  - rewrite (subtyp_same_kind _ _ _ κ ak_level a 0 Hs HM HM'); constructor.
Qed.

(** A λ-abstraction: its short type is a [Π] into an evaluated kind
    ([typ_pi_shape_strengthen]) or a [∀] ([typ_all_shape_strengthen]),
    whose domain is the abstraction's, and the body is checked against its
    codomain. *)
Lemma fn_str : forall Γ κ A A' M', nf_str_exp Γ κ A A' -> nf_str_exp Γ κ A M' -> nf_str_exp Γ κ A (λ A' M').
Proof.
  intros * IHA IHM Δ T Hass HΓf HTt HW; cbn [exp_wk] in HW.
  set (φ := wk_qn (length Δ) ↑) in *.
  set (Lf := (tele_wk Δ ↑ ++ Γ ▹{κ} A)%list) in *.
  destruct HTt as [T Srt HS HT | _]; [| exfalso; pose proof (level_sort_typed_former HW) as Hf; inversion Hf ].
  assert (HΓs : ⊢ (Δ ++ Γ)%list) by (gen_presups; assumption).
  destruct (wf_fn_inversion HW) as (κd & κc & B & HM & Hs).
  assert (HΓf' : ⊢ (Lf ▹{κd} A'[φ]ʷ)%list) by (gen_presups; assumption).
  destruct (ctx_decomp_kind HΓf') as (SA & HSA & HA).
  assert (HAs : (Δ ++ Γ)%list ⊢ A' : SA)
    by (eapply nf_str_at_sort; [ exact IHA | exact Hass | exact HΓf | exact HΓs | exact (sort_kind_type_sort _ _ HSA) | exact HA ]).
  assert (HΓs' : ⊢ ((Δ ++ Γ) ▹{κd} A')%list) by (eapply wf_ctx_extend; [ exact HAs | exact HSA ]).
  assert (Hass' : all_assumptions (ce_ass κd A' :: Δ)) by (constructor; [ do 2 eexists; reflexivity | exact Hass ]).
  assert (exists C0, Lf ⊢ a_pi κd κc A'[φ]ʷ B : C0) as [C0 HC0] by (gen_presups; eexists; eassumption).
  destruct (evaluated_kind_or_propositional κc) as [Hev | ->].
  - (** A function, into a universe or between levels *)
    destruct (wf_pi_typed_kind Hev HC0) as [kP HkP].
    destruct (short_sort_kind_r _ _ _ _ _ _ _ κc kP HΓf HΓs HS HT HkP Hs) as [i ->].
    destruct (subtyp_pi_kind_left_shape _ _ _ _ _ _ Hev Hs) as (X & Y & k0 & HTXY).
    destruct (typ_pi_shape_strengthen _ _ _ _ _ _ _ _ _ _ Hass Hev HΓf HT (subtyp_of_exp_eq_kind Hev HTXY)) as (C & D & HCD).
    assert (HTCD : (Δ ++ Γ)%list ⊢ T ≈ (nf_pi κd κc C D : exp) : abs_kind_sort κc Typeω@i)
      by (eapply soundness_ty_at_sort; eassumption).
    cbn [nf_to_exp] in HTCD.
    assert (HCDt : (Δ ++ Γ)%list ⊢ a_pi κd κc C D : abs_kind_sort κc Typeω@i) by (gen_presups; assumption).
    destruct (wf_pi_parts HCDt) as (Hpk & (SC & HSC & HCs) & (iD & HD)).
    pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf; fold φ Lf in HTCDf.
    assert (HTCDf' : Lf ⊢ T[φ]ʷ ≈ a_pi κd κc (C : exp)[φ]ʷ (D : exp)[wk_q φ]ʷ : abs_kind_sort κc Typeω@i)
      by (destruct Hev; exact HTCDf).
    assert (Hs' : Lf ⊢ a_pi κd κc A'[φ]ʷ B ⊆ a_pi κd κc (C : exp)[φ]ʷ (D : exp)[wk_q φ]ʷ)
      by (etransitivity; [ exact Hs | exact (subtyp_of_exp_eq_kind Hev HTCDf') ]).
    destruct (subtyp_pi_kind_inv _ _ _ _ _ _ _ _ Hev Hs') as (_ & (S0 & HS0 & HAC) & HBD).
    destruct (exp_eq_strengthen_sort _ _ _ _ _ _ _ _ _ Hass HΓf (sort_kind_type_sort _ _ HSA) (sort_kind_type_sort _ _ HSC)
                (sort_kind_type_sort _ _ HS0) HAs HCs HAC) as (Sx & HSx & HAx & HACs).
    pose proof (sort_kind_of_typed _ _ _ _ _ HAs HSA HAx HSx) as HSxk.
    assert (HDs : ((Δ ++ Γ) ▹{κd} A')%list ⊢ D : abs_kind_sort κc Typeω@iD)
      by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq HSxk HACs) | exact HD ]).
    assert (HSkD : type_sort (abs_kind_sort κc Typeω@iD)) by (destruct Hev; constructor).
    pose proof (short_wk_sort (ce_ass κd A' :: Δ) _ _ _ _ _ HΓf' HDs HSkD) as HDf; cbn [exp_wk] in HDf.
    assert (HMf : (Lf ▹{κd} A'[φ]ʷ)%list ⊢ M'[wk_q φ]ʷ : (D : exp)[wk_q φ]ʷ)
      by (eapply wf_exp_subtyp; [ exact HM | exact HDf | exact HSkD | exact HBD ]).
    assert (HMs : ((Δ ++ Γ) ▹{κd} A')%list ⊢ M' : D)
      by (eapply (nf_str_sorted _ _ _ _ IHM (ce_ass κd A' :: Δ) _ _); [ exact Hass' | exact HΓf' | exact HSkD | exact HDs | exact HMf ]).
    assert (HWs : (Δ ++ Γ)%list ⊢ λ A' M' : a_pi κd κc A' D)
      by (eapply wf_fn; [ exact HAs | exact HSA | exact HDs | exact Hpk | exact HMs ]).
    destruct (wf_pi_cong_at_kinds _ _ _ κd κc A' (C : exp) (D : exp) (D : exp) Sx iD HAx HSxk HACs HDs (wf_exp_eq_refl HDs) Hpk)
      as [Spi HSpi _ HPc].
    eapply wf_exp_subtyp; [ exact HWs | exact HT | exact HS |].
    etransitivity; [ eapply (wf_subtyp_refl _ _ _ Spi); [ exact (presup_exp_eq_right HPc) | exact HSpi | exact HPc ] |].
    eapply (subtyp_of_exp_eq_kind Hev); symmetry; exact HTCD.
  - (** A proof of a [∀]: [T] is a proposition *)
    pose proof (prop_former_typed HC0 ltac:(right; right; left; do 3 eexists; reflexivity)) as Hp1.
    change Propₘ with (abs_kind_sort ak_propositional Typeω@0) in Hp1.
    destruct (short_sort_kind_r _ _ _ _ _ _ _ ak_propositional 0 HΓf HΓs HS HT Hp1 Hs) as [j0 ->]; cbn [abs_kind_sort] in HT, Hp1.
    pose proof (short_wk_sort _ _ _ _ _ _ HΓf HT type_sort_prop) as HTl.
    pose proof (subtyp_prop_eq _ _ _ Hs Hp1 HTl) as HsE.
    destruct (typ_all_shape_strengthen _ _ _ _ _ _ _ _ Hass HΓf HT
                (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ Hp1 HTl type_sort_prop HsE))) as (C & D & HCD).
    pose proof (soundness_ty_at_sort type_sort_prop HT HCD) as HTCD; cbn [nf_to_exp] in HTCD.
    assert (HCDt : (Δ ++ Γ)%list ⊢ ∀ₚ{κd} C D : Propₘ) by (gen_presups; assumption).
    destruct (wf_all_inversion _ _ _ _ _ _ _ HCDt) as [SC HSC HCs HD _].
    pose proof (short_wk_exp_eq _ _ _ _ _ _ _ HΓf HTCD) as HTCDf; cbn [exp_wk] in HTCDf; fold φ Lf in HTCDf.
    assert (Hs' : Lf ⊢ ∀ₚ{κd} A'[φ]ʷ B ⊆ ∀ₚ{κd} (C : exp)[φ]ʷ (D : exp)[wk_q φ]ʷ).
    { etransitivity; [ exact Hs |].
      assert (Lf ⊢ ∀ₚ{κd} (C : exp)[φ]ʷ (D : exp)[wk_q φ]ʷ : Propₘ) by (gen_presups; assumption).
      exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HTl ltac:(eassumption) type_sort_prop HTCDf)). }
    destruct (subtyp_all_inv _ _ _ _ _ _ _ Hs') as (_ & (S0 & HS0 & HAC) & HBD).
    destruct (exp_eq_strengthen_sort _ _ _ _ _ _ _ _ _ Hass HΓf (sort_kind_type_sort _ _ HSA) (sort_kind_type_sort _ _ HSC)
                (sort_kind_type_sort _ _ HS0) HAs HCs HAC) as (Sx & HSx & HAx & HACs).
    pose proof (sort_kind_of_typed _ _ _ _ _ HAs HSA HAx HSx) as HSxk.
    assert (HDs : ((Δ ++ Γ) ▹{κd} A')%list ⊢ D : Propₘ)
      by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq HSxk HACs) | exact HD ]).
    pose proof (short_wk_sort (ce_ass κd A' :: Δ) _ _ _ _ _ HΓf' HDs type_sort_prop) as HDf; cbn [exp_wk] in HDf.
    assert (HMf : (Lf ▹{κd} A'[φ]ʷ)%list ⊢ M'[wk_q φ]ʷ : (D : exp)[wk_q φ]ʷ)
      by (eapply wf_exp_subtyp; [ exact HM | exact HDf | constructor | exact HBD ]).
    assert (HMs : ((Δ ++ Γ) ▹{κd} A')%list ⊢ M' : D)
      by (eapply (nf_str_sorted _ _ _ _ IHM (ce_ass κd A' :: Δ) _ Propₘ); [ exact Hass' | exact HΓf' | constructor | exact HDs | exact HMf ]).
    assert (HWs : (Δ ++ Γ)%list ⊢ λ A' M' : ∀ₚ{κd} A' D)
      by (eapply wf_fn with (κc := ak_propositional) (i := 0); [ exact HAs | exact HSA | exact HDs | constructor | exact HMs ]).
    pose proof (all_cong_sort HSxk HAx HACs (wf_exp_eq_refl HDs)) as Hall.
    assert (HE : (Δ ++ Γ)%list ⊢ ∀ₚ{κd} A' D ≈ T : Propₘ) by (etransitivity; [ exact Hall | symmetry; exact HTCD ]).
    eapply wf_exp_subtyp; [ exact HWs | exact HT | constructor |].
    exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) HT type_sort_prop HE)).
Qed.

(** ** The Induction Hypotheses Under the Premise *)

(** The generated hypothesis at a list, of a motive under a premise each
    element meets, gives the conclusion at each element. *)
Lemma list_all_Forall_map_premise {X Y : Set} (P : X -> Set) (Q : X -> Prop) (R : Y -> Prop) (f : X -> Y) : forall l,
    list_all X P l -> all_list Q l -> (forall x, P x -> Q x -> R (f x)) -> List.Forall R (List.map f l).
Proof. intros l Hl; induction Hl as [| x Hx l Hl IH]; cbn; [ constructor | intros [Hq Hr] H; constructor; auto ]. Qed.

(** The same at the atoms of a level. *)
Lemma level_atoms_all_premise : forall (P Q : ne -> Prop) xs,
    level_atoms_all (fun u => P u -> Q u) xs -> level_atoms_all P xs -> level_atoms_all Q xs.
Proof. intros P Q; induction xs as [| [k s a] r IH]; cbn; [ auto | intros [Ha Hr] [Hp Hq]; split; auto ]. Qed.

(** The generated induction hypothesis at a list of normal forms, under
    their proof-freedom [Hpf], as the lemmas on application spines above
    take it: [nf_str_exp] of each term. *)
Ltac nfs_str_ih Γ κ A IH Hpf :=
  let H := fresh "H" in
  pose proof (list_all_Forall_map_premise _ _ (nf_str_exp Γ κ A) nf_to_exp _ IH Hpf (fun _ Hx Hy => Hx Hy)) as H;
  clear IH Hpf; rename H into IH.

(** The same at the blocks of a stuck eliminator, as [elim_str] takes it:
    of each block's scrutinee type, motive and branches. *)
Ltac blocks_str_ih Γ κ A IH Hpf :=
  let H := fresh "H" in
  match type of IH with list_all _ _ ?l =>
  assert (H : List.Forall (fun b => nf_str_exp Γ κ A (eb_scrutinee_type b) /\ nf_str_exp Γ κ A (eb_motive b) /\
                                    List.Forall (fun br => nf_str_exp Γ κ A (snd br)) (eb_brs b))
                (List.map block_exp l));
  [ apply (list_all_Forall_map_premise _ _ _ block_exp _ IH Hpf);
    let x := fresh "x" in let Hx := fresh "Hx" in let Hy := fresh "Hy" in
    let HZ := fresh "HZ" in let HA := fresh "HA" in let Hbrs := fresh "Hbrs" in
    let HyZ := fresh "HyZ" in let HyA := fresh "HyA" in let Hybrs := fresh "Hybrs" in
    intros x Hx Hy; destruct Hx as [? ? HZ ? HA ? Hbrs]; destruct Hy as [HyZ [HyA Hybrs]]; cbn;
    split; [ exact (HZ HyZ) | split; [ exact (HA HyA) |] ];
    apply (list_all_Forall_map_premise _ _ (fun br => nf_str_exp Γ κ A (snd br)) branch_exp _ Hbrs Hybrs);
    let y := fresh "y" in let Hy' := fresh "Hy" in let Hz := fresh "Hz" in let HB := fresh "HB" in
    intros y Hy' Hz; destruct Hy' as [? ? ? HB]; exact (HB Hz)
  | clear IH Hpf; rename H into IH ]
  end.

(** A variable: the long variable is the image of a short one. *)
Lemma var_str : forall Γ κ A x, exp_str Γ κ A (a_var x).
Proof.
  intros * Δ C Hass HΓf HΓs HW; cbn [exp_wk] in HW.
  destruct (wf_vlookup_inversion HW) as (A1 & Hl & HsC).
  destruct (lookup_strengthen _ _ _ _ _ _ Hl) as (T & HlT & ->).
  assert (Hx : (Δ ++ Γ)%list ⊢ #x : T) by (apply wf_vlookup; assumption).
  assert (exists ST, type_sort ST /\ (Δ ++ Γ)%list ⊢ T : ST) as (ST & HST & HTj).
  { (** a variable is no type of levels *)
    pose proof (presup_exp_typ_cases Hx) as Hp; inversion Hp; [ eexists; split; eassumption |].
    match goal with H : level_type_former _ |- _ => inversion H end. }
  exact (mk_short_typ _ _ _ _ _ _ T ST HST Hx HTj HsC).
Qed.

(** A global: a closed member of a chain from a unit, typed in any
    context at a closed type; the empty chain names [Prop]. *)
Lemma glob_str : forall Γ κ A p, exp_str Γ κ A (qname_term p).
Proof.
  intros * Δ C Hass HΓf HΓs HW.
  rewrite qname_term_wk in HW.
  destruct p as [fp ch].
  destruct (List.rev ch) as [| x pre] eqn:Er.
  - apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
    unfold qname_term in *; cbn [q_unit q_chain member_ref] in *.
    apply (mk_short_typ _ _ _ _ _ _ Type@0 Typeω@0 (type_sort_universe 0));
      [ apply wf_prop, HΓs | apply (wf_univ_large (i := 0)), HΓs | exact (wf_prop_inversion _ _ _ _ HW) ].
  - apply (f_equal (@List.rev _)) in Er; rewrite List.rev_involutive in Er; cbn in Er; subst ch.
    change (qname_mk fp (List.rev pre ++ x :: nil)) with (qname_app (qname_mk fp (List.rev pre)) (x :: nil)) in *.
    rewrite qname_term_snoc in *.
    destruct (path_mem_any_ctx _ _ _ _ _ (qname_mod_qname _) HW) as (T & HTc & HsT & Hany).
    pose proof (Hany _ HΓs) as HTs.
    assert (exists ST, type_sort ST /\ (Δ ++ Γ)%list ⊢ T : ST) as (ST & HST & HTj).
    { pose proof (presup_exp_typ_cases HTs) as Hp; inversion Hp; [ eexists; split; eassumption |].
      match goal with H : level_type_former _ |- _ => inversion H end. }
    apply (mk_short_typ _ _ _ _ _ _ T ST HST); [ exact HTs | exact HTj | rewrite exp_closed_wk by exact HTc; exact HsT ].
Qed.

(** ** The Theorem

    A normal form free of proofs ([nf_proof_free]; [Core.Syntactic.Fresh]
    shows why the premise is needed), typed weakened at a weakened type
    ([⊢ᵗ]), is typed at that type; a proof-free neutral is typed short
    ([ne_str]).  The kept proofs are not proof-free, so their case is
    vacuous. *)
Theorem nf_strengthen : forall Γ κ A,
    (forall (W : nf), nf_proof_free W -> nf_str_exp Γ κ A W) /\
    (forall u, ne_proof_free u -> ne_str Γ κ A u).
Proof.
  intros Γ κ A; apply nf_ne_ind.
  - intros i _; exact (typ_str _ _ _ i).
  - intros c xs IH Hpf; apply list_all_level_atoms_all in IH; apply level_atoms_all_all_list in Hpf.
    exact (univ_str _ _ _ c xs (level_atoms_all_premise _ _ _ IH Hpf)).
  - intros n _; exact (level_str _ _ _ n).
  - intros _; exact (level_sort_str _ _ _).
  - intros c xs IH Hpf; apply list_all_level_atoms_all in IH; apply level_atoms_all_all_list in Hpf.
    exact (lvl_str _ _ _ c xs (level_atoms_all_premise _ _ _ IH Hpf)).
  - intros _; exact (prop_str _ _ _).
  - intros _; exact (True_str _ _ _).
  - (** A kept proof is not proof-free. *)
    intros P _ M Hpf; destruct Hpf.
  - intros _; exact (False_str _ _ _).
  - intros P IHP Q IHQ [HpP HpQ]; exact (and_str _ _ _ _ _ (IHP HpP) (IHQ HpQ)).
  - intros κd κc A' IHA B' IHB [HpA HpB]; exact (pi_str _ _ _ κd κc _ _ (IHA HpA) (IHB HpB)).
  - intros A' IHA M' IHM [HpA HpM]; exact (fn_str _ _ _ _ _ (IHA HpA) (IHM HpM)).
  - intros p k Ms IHMs Hpf; nfs_str_ih Γ κ A IHMs Hpf; exact (exp_str_at _ _ _ _ (apps_str _ _ _ _ _ IHMs (ind_str _ _ _ p k))).
  - intros p k c Ms IHMs Hpf; nfs_str_ih Γ κ A IHMs Hpf; exact (exp_str_at _ _ _ _ (apps_str _ _ _ _ _ IHMs (con_str _ _ _ p k c))).
  - intros r u IH Hpf; exact (exp_str_at _ _ _ _ (IH Hpf)).
  - intros p Ms IHMs Hpf; nfs_str_ih Γ κ A IHMs Hpf; exact (exp_str_at _ _ _ _ (apps_str _ _ _ _ _ IHMs (record_str _ _ _ p))).
  - (** A tuple ([tuple_str]). *)
    intros p Ms IHMs fs Fs IHFs [HpMs HpFs]; nfs_str_ih Γ κ A IHMs HpMs; nfs_str_ih Γ κ A IHFs HpFs; cbn [nf_to_exp].
    apply tuple_str; [ exact IHMs |].
    apply List.Forall_forall; intros x Hx.
    apply List.in_map_iff in Hx as ([g y] & <- & Hin); apply List.in_combine_r in Hin.
    exact (proj1 (List.Forall_forall _ _) IHFs _ Hin).
  - (** Ex falso is not proof-free. *)
    intros A' IHA M Hpf; destruct Hpf.
  - (** A stuck eliminator ([elim_str]). *)
    intros pc Us IHUs k Bks IHBs u IHu (HpUs & HpBs & Hpu); nfs_str_ih Γ κ A IHUs HpUs; blocks_str_ih Γ κ A IHBs HpBs.
    exact (elim_str _ _ _ _ _ _ _ _ IHUs IHBs (IHu Hpu)).
  - intros u IHu w IHw [Hpu Hpw]; exact (app_str _ _ _ _ _ (IHu Hpu) (IHw Hpw)).
  - intros x _; exact (var_str _ _ _ x).
  - intros p _; exact (glob_str _ _ _ p).
  - intros f u IHu Hpf; exact (proj_str _ _ _ f _ (IHu Hpf)).
Qed.
(** ** At the Outermost Variable *)

(** A proof-free normal form typed, weakened, in [Γ ▹{κ} A] at a weakened
    type ([⊢ᵗ]) of [Γ] is typed at that type in [Γ]. *)
Corollary nf_strengthen_shift : forall Γ κ A (W : nf) T,
    nf_proof_free W ->
    ⊢ Γ ▹{κ} A ->
    Γ ⊢ᵗ T ->
    Γ ▹{κ} A ⊢ (W : exp)[↑]ʷ : T[↑]ʷ ->
    Γ ⊢ W : T.
Proof.
  intros * Hpf HΓA HT HW.
  exact (proj1 (nf_strengthen Γ κ A) W Hpf nil T ltac:(constructor) HΓA HT HW).
Qed.

(** The case the algorithmic [Π] needs: the level of a codomain's universe,
    when it does not mention the bound variable and holds no proof. *)
Corollary level_nf_strengthen : forall Γ κ A n (L : nf),
    nf_proof_free L ->
    ⊢ Γ ▹{κ} A ->
    Γ ▹{κ} A ⊢ (L : exp)[↑]ʷ : Level@n ->
    Γ ⊢ L : Level@n.
Proof.
  intros * Hpf HΓA HL.
  destruct (ctx_decomp HΓA) as [HΓ _].
  exact (nf_strengthen_shift Γ κ A L Level@n Hpf HΓA (wf_type_of_sort _ type_sort_level (wf_level _ _ _ n HΓ)) HL).
Qed.

End Fixed_GCtx.
