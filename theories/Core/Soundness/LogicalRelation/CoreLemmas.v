From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Corollaries Substitution.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations Wk_Notations.

Lemma glu_nat_per_nat : forall Γ M a,
    glu_nat Γ M a ->
    {{ Dom a ≈ a ∈ per_nat }}.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mctt.

Lemma glu_nat_escape : forall Γ M a,
    glu_nat Γ M a ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ M : ℕ }}.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert {{ Γ ⊢k wk_id : Γ }} by mauto 2.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert {{ Γ ⊢ M⟨wk_id⟩ ≈ M' : ℕ }} as HM by mauto.
  rewrite exp_wk_id in HM.
  gen_presups.
  mauto.
Qed.

#[export]
Hint Resolve glu_nat_escape : mctt.

(** Where the explicit-substitution development transported [glu_nat] along a
    context *equality*, it now travels along a refinement: [{{ ⊢ Δ ⊆ Γ }}] is
    what the [ctxsub_*] lemmas need, and an equality gives refinements both
    ways.  The same replacement happens to every [wf_ctx_eq] morphism instance
    below. *)
Lemma glu_nat_resp_ctxsub : forall Γ M a Δ,
    glu_nat Γ M a ->
    {{ ⊢ Δ ⊆ Γ }} ->
    glu_nat Δ M a.
Proof.
  induction 1; intros.
  - mauto 4.
  - assert {{ Δ ⊢ M ≈ succ M' : ℕ }} by mauto 3.
    econstructor; [ eassumption | mauto 2 ].
  - econstructor; trivial.
    intros; mauto 4.
Qed.

#[export]
Hint Resolve glu_nat_resp_ctxsub : mctt.

Lemma glu_nat_resp_exp_eq : forall Γ M a,
    glu_nat Γ M a ->
    forall M',
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    glu_nat Γ M' a.
Proof.
  induction 1; intros; mauto 4.
  econstructor; trivial.
  intros.
  transitivity {{{ M⟨φ⟩ }}}; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_exp_eq : mctt.

Add Parametric Morphism Γ : (glu_nat Γ)
    with signature wf_exp_eq Γ {{{ ℕ }}} ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; mauto using glu_nat_resp_exp_eq.
Qed.

Lemma glu_nat_readback : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ M',
      {{ Δ ⊢k φ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Δ ↘ M' }} ->
      {{ Δ ⊢ M⟨φ⟩ ≈ M' : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - rewrite <- (exp_wk_zero φ); mauto 4.
  - assert {{ Δ ⊢ M'⟨φ⟩ ≈ M0 : ℕ }} by mauto 4.
    assert {{ Δ ⊢ M⟨φ⟩ ≈ (succ M')⟨φ⟩ : ℕ }} as H' by mauto 4.
    rewrite exp_wk_succ in H'.
    etransitivity; [ eassumption | mauto 3 ].
  - mauto 4.
Qed.

#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Lemma glu_univ_elem_univ_lvl : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A,
      {{ Γ ⊢ A ® P }} ->
      {{ Γ ⊢ A : Type@i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_typ_resp_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A A',
      {{ Γ ⊢ A ® P }} ->
      {{ Γ ⊢ A ≈ A' : Type@i }} ->
      {{ Γ ⊢ A' ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  split; [trivial |].
  intros.
  transitivity {{{ A⟨φ⟩ }}}; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (P Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> iff as glu_univ_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 2.
Qed.

Lemma glu_univ_elem_trm_resp_typ_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m A',
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A ≈ A' : Type@i }} ->
      {{ Γ ⊢ M : A' ® m ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; repeat split; intros; mauto 3;
    [firstorder | | transitivity {{{ A⟨φ⟩ }}}; mauto 4 | assert {{ Δ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }}; mauto 3].

  econstructor; mauto 3.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (El Γ)
    with signature wf_exp_eq Γ {{{Type@i}}} ==> eq ==> eq ==> iff as glu_univ_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_typ_resp_ctxsub : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A Δ,
      {{ Γ ⊢ A ® P }} ->
      {{ ⊢ Δ ⊆ Γ }} ->
      {{ Δ ⊢ A ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 3.

  - assert {{ Δ ⊢ IT : Type@i }} by mauto 3.
    assert {{ ⊢ Δ , IT ⊆ Γ , IT }} by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_typ).
    econstructor; mauto 3; intros; mauto 4.

  - split; [ mauto 3 | intros; mauto 4 ].
Qed.

Lemma glu_univ_elem_trm_resp_ctxsub : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m Δ,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ ⊢ Δ ⊆ Γ }} ->
      {{ Δ ⊢ M : A ® m ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel.

  - repeat apply conj; [ mauto 3 | mauto 3 | ].
    do 2 eexists; split; [ eassumption | eapply glu_univ_elem_typ_resp_ctxsub; eassumption ].

  - split; mauto 3.

  - assert {{ Δ ⊢ IT : Type@i }} by mauto 3.
    assert {{ ⊢ Δ , IT ⊆ Γ , IT }} by (eapply ctx_sub_extend; mauto 3 using wf_subtyp_refl_typ).
    econstructor; mauto 3; intros; mauto 4.

  - econstructor; [ split | | | ]; mauto 3; intros; mauto 4.
Qed.

Lemma glu_nat_resp_wk' : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      {{ Γ ⊢ M : ℕ }} ->
      {{ Δ ⊢k φ : Γ }} ->
      glu_nat Δ {{{ M⟨φ⟩ }}} a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    rewrite <- (exp_wk_zero φ); mauto 4.
  - econstructor; [ |mauto].
    rewrite <- (exp_wk_succ φ); mauto 4.
  - econstructor; trivial.
    intros Δ' ψ M' **.
    rewrite exp_wk_wk.
    assert {{ Δ' ⊢k φ ⊙ ψ : Γ }} by mauto 3.
    mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ φ,
      {{ Δ ⊢k φ : Γ }} ->
      glu_nat Δ {{{ M⟨φ⟩ }}} a.
Proof.
  intros * ? * ?.
  assert {{ ⊢ Γ }} by (eapply kripke_cod; eassumption).
  mauto using glu_nat_resp_wk'.
Qed.

#[export]
Hint Resolve glu_nat_resp_wk : mctt.

Lemma glu_univ_elem_trm_escape : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ M : A }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Dom a ≈ a ∈ per_univ i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros; eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
Qed.

#[export]
Hint Resolve glu_univ_elem_per_univ : mctt.

Lemma glu_univ_elem_per_elem : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m R,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
      {{ Dom m ≈ m ∈ R }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H);
    simpl_glu_rel;
    try fold (per_univ j m m);
    mauto 4.

  intros.
  destruct_rel_mod_app.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  do_per_univ_elem_irrel_assert.

  econstructor; firstorder eauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  intros ? ? N n ? ? equiv_n.
  destruct_rel_mod_eval.
  enough (exists mn : domain, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M⟨φ⟩ N : OT[^(ι φ),,N] ® mn ∈ OEl n equiv_n }}) as [? []]; eauto 3.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A : Type@i }}.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [| eapply glu_univ_elem_trm_typ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m M',
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ M ≈ M' : A }} ->
      {{ Γ ⊢ M' : A ® m ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq; mauto.

  - econstructor; eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros.
    destruct_rel_mod_eval.
    assert {{ Δ ⊢ N : IT⟨φ⟩ }} by eauto using glu_univ_elem_trm_escape.
    assert (exists mn : domain, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M⟨φ⟩ N : OT[^(ι φ),,N] ® mn ∈ OEl n equiv_n }}) as [? []] by intuition.
    eexists; split; eauto.
    enough {{ Δ ⊢ M⟨φ⟩ N ≈ M'⟨φ⟩ N : OT[^(ι φ),,N] }} by eauto.
    assert {{ Γ ⊢ M ≈ M' : Π IT OT }} as Hty by mauto.
    assert {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : (Π IT OT)⟨φ⟩ }} as Hty' by mauto 2.
    rewrite exp_wk_pi in Hty'.
    eapply wf_exp_eq_app_cong' with (N := N) (N' := N) in Hty'; [| mauto 2].
    rewrite exp_sub_wk_q_extend in Hty'.
    eassumption.
  - intros.
    enough {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }}; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ T : (El Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as glu_univ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    j < i ->
    (typ_rel <∙> univ_glu_typ_pred j i) ->
    (el_rel <∙> univ_glu_exp_pred j i) ->
    {{ DG 𝕌@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel }}.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

#[export]
Hint Resolve glu_univ_elem_core_univ' : mctt.

Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + basic_glu_univ_elem_econstructor.

Lemma glu_univ_elem_univ_simple_constructor : forall {i},
    glu_univ_elem (S i) (univ_glu_typ_pred i (S i)) (univ_glu_exp_pred i (S i)) d{{{ 𝕌@i }}}.
Proof.
  intros.
  glu_univ_elem_econstructor; mauto; reflexivity.
Qed.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.

Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    induction Horig using glu_univ_elem_ind; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Lemma functional_glu_univ_elem : forall i a P P' El El',
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  induction Ha using glu_univ_elem_ind; intros; basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
  apply_predicate_equivalence.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  split; [intros Γ C | intros Γ M C m].
  - split; intros []; econstructor; intuition;
      [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
      | assert (equiv0_m : in_rel0 m m) by intuition ];
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
      intuition.
  - split; intros []; econstructor; intuition;
      [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
      | assert (equiv0_n : in_rel0 n n) by intuition];
      destruct_rel_mod_eval;
      [assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0⟨φ⟩ N : OT[^(ι φ),,N] ® m0n ∈ OEl n equiv_n }}) by intuition
      | assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0⟨φ⟩ N : OT[^(ι φ),,N] ® m0n ∈ OEl0 n equiv0_n }}) by intuition];
      destruct_conjs;
      assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
      eexists; split; intuition.
Qed.

Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ^?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1 }},
      H2 : {{ DG ^?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 }} |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_univ_elem_pi_clean_inversion1 : forall {i a ρ B in_rel P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists IP IEl (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
      {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} /\
        (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
        {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
        (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ A ® Pb }}).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert {{ Dom m ≈ m ∈ in_rel0 }} as equiv0_m by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert {{ Dom n ≈ n ∈ in_rel0 }} as equiv0_n by intuition.
    assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M⟨φ⟩ N : OT[^(ι φ),,N] ® mn ∈ OEl n equiv0_n }}) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               {{ $| m & n |↘ mn }} /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
                     {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                     {{ Δ ⊢ M⟨φ⟩ N : OT[^(ι φ),,N] ® mn ∈ Elb }})) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Lemma glu_univ_elem_pi_clean_inversion2 : forall {i a ρ B in_rel IP IEl P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
    (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
        {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
      {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
      (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Lemma glu_univ_elem_resp_per_univ : forall i a a' P El,
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [elem_rel Hper] Horig.
  pose proof Hper.
  gen P El.
  induction Hper using per_univ_elem_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig; glu_univ_elem_econstructor; try eassumption; mauto;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem.
  - intros.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - reflexivity.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
Qed.

(** *** Morphism instances for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; mauto.
Qed.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_univ_elem ?i ?P ?El ?a,
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_univ_elem ?i ?P ?El ?a',
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Lemma per_univ_glu_univ_elem : forall i a,
    {{ Dom a ≈ a ∈ per_univ i }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [? Hper].
  induction Hper using per_univ_elem_ind; intros;
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ M : A ® m ∈ El }}).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ A ® P }}).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

#[export]
Hint Resolve per_univ_glu_univ_elem : mctt.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

#[export]
Hint Resolve per_univ_elem_glu_univ_elem : mctt.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ _,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

(** Kripke weakenings compose, so a gluing predicate stated at [Γ] survives
    being pushed along one: the two [⟨⟩]s that appear collapse to a single
    [⟨φ ⊙ ψ⟩] by [exp_wk_wk], and the [q] of a [Π] codomain absorbs the second
    weakening's extension by [exp_sub_wk_q_extend_wk].  Both were judgmental
    rearrangements of the substitution calculus before; they are propositional
    equalities now, which is why every case here is a [rewrite] away from the
    hypothesis it came from. *)

Lemma glu_univ_elem_typ_monotone : forall i a P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Δ φ Γ A,
      {{ Γ ⊢ A ® P }} ->
      {{ Δ ⊢k φ : Γ }} ->
      {{ Δ ⊢ A⟨φ⟩ ® P }}.
Proof.
  simpl. induction 1 using glu_univ_elem_ind; intros;
    saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    try solve [mauto 2].
  - simpl_glu_rel.
    assert {{ Δ ⊢ A⟨φ⟩ ≈ (Π IT OT)⟨φ⟩ : Type@i }} as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - destruct_conjs.
    split; [mauto 2 |].
    intros.
    rewrite exp_wk_wk.
    mauto 4.
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Δ φ Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Δ ⊢k φ : Γ }} ->
      {{ Δ ⊢ M⟨φ⟩ : A⟨φ⟩ ® m ∈ El }}.
Proof.
  simpl. induction 1 using glu_univ_elem_ind; intros;
    saturate_kripke;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all.
  - repeat eexists; mauto 2.
    eapply glu_univ_elem_typ_monotone; eauto.
  - split; mauto 2.

  - simpl_glu_rel.
    assert {{ Δ ⊢ A⟨φ⟩ ≈ (Π IT OT)⟨φ⟩ : Type@i }} as HAeq by mauto 2.
    rewrite exp_wk_pi in HAeq.
    econstructor; [ mauto 2 | eassumption | eassumption | mauto 2 | mauto 2 | | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + rewrite exp_wk_wk in *.
      rewrite exp_sub_wk_q_extend_wk.
      mauto 4.

  - simpl_glu_rel.
    econstructor; [ split; [ mauto 2 | ] | mauto 2 | eassumption | ]; intros.
    + rewrite exp_wk_wk; mauto 4.
    + do 2 rewrite exp_wk_wk; mauto 4.
Qed.

(** The [wf_ctx_eq] instances of the explicit-substitution development become
    refinement lemmas, as with [glu_nat_resp_ctxsub]: a Kripke weakening into
    [Δ] extends to one into [Γ] by [kripke_ctxsub], which is all three of these
    need. *)

Lemma glu_elem_bot_resp_ctxsub : forall i a Γ A M m Δ,
    {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} ->
    {{ ⊢ Δ ⊆ Γ }} ->
    {{ Δ ⊢ M : A ® m ∈ glu_elem_bot i a }}.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_elem_top_resp_ctxsub : forall i a Γ A M m Δ,
    {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }} ->
    {{ ⊢ Δ ⊆ Γ }} ->
    {{ Δ ⊢ M : A ® m ∈ glu_elem_top i a }}.
Proof.
  intros * [] ?; econstructor;
    [ mauto 3 | eassumption | eapply glu_univ_elem_typ_resp_ctxsub | eassumption | intros ];
    mauto 4.
Qed.

Lemma glu_typ_top_resp_ctxsub : forall i a Γ A Δ,
    {{ Γ ⊢ A ® glu_typ_top i a }} ->
    {{ ⊢ Δ ⊆ Γ }} ->
    {{ Δ ⊢ A ® glu_typ_top i a }}.
Proof.
  intros * [] ?; econstructor; [ mauto 3 | eassumption | intros ]; mauto 4.
Qed.

#[export]
Hint Resolve glu_elem_bot_resp_ctxsub glu_elem_top_resp_ctxsub glu_typ_top_resp_ctxsub : mctt.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }} as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }} as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }} as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M⟨φ⟩ ≈ M'⟨φ⟩ : A⟨φ⟩ }} as HMφM'φ by mauto 4;
    [rewrite <- HMφM'φ | rewrite -> HMφM'φ];
    mauto.
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert {{ Δ ⊢ A⟨φ⟩ ≈ A'⟨φ⟩ : Type@i }} as HAφA'φ by mauto 4;
    [rewrite <- HAφA'φ | rewrite -> HAφA'φ];
    mauto.
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.
