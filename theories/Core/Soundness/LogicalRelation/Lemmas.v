From Stdlib Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases FundamentalTheorem UniverseCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Export Realizability.
From Mctt.Core.Syntactic Require Import LevelEq Substitution.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Add Parametric Morphism i a Γ A M : (glu_elem_bot i a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Add Parametric Morphism i a Γ A M R (H : per_univ_elem i R a a) : (glu_elem_top i a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    pose proof (per_elem_then_per_top H Hmm') as Hmm'';
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm'' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Lemma glu_univ_elem_typ_unique_upto_exp_eq : forall {i j : uidx} {a P P' El El' Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Type@(max (ulvl i) (ulvl j)).
Proof.
  intros.
  assert (Γ ⊢ A ® glu_typ_top i a) as [] by mauto 3.
  assert (Γ ⊢ A' ® glu_typ_top j a) as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  (** Both are types of the large universe of their index's tier, and both
      are equal to the common readback there. *)
  assert (Γ ⊢ A : Type@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_max_left.
  assert (Γ ⊢ A' : Type@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_max_right.
  assert (Γ ⊢ A ≈ V : Type@(ulvl i)) as HAV by (rewrite <- (exp_wk_id A); mauto 4).
  assert (Γ ⊢ A' ≈ V : Type@(ulvl j)) as HA'V by (rewrite <- (exp_wk_id A'); mauto 4).
  assert (Γ ⊢ A ≈ V : Type@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_eq_max_left.
  assert (Γ ⊢ A' ≈ V : Type@(max (ulvl i) (ulvl j))) by mauto 4 using lift_exp_eq_max_right; mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq_ge : forall {i j : uidx} {a P P' El El' Γ A A'},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Type@(ulvl j).
Proof.
  intros.
  replace (ulvl j) with (max (ulvl i) (ulvl j)) by (pose proof (uidx_le_ulvl_le _ _ ltac:(eassumption)); lia); mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mctt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq' : forall {i : uidx} {a P El Γ A A'},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P ->
    Γ ⊢ A ≈ A' : Type@(ulvl i).
Proof.
  intros * Hglu HA HA'.
  assert (Γ ⊢ A ® glu_typ_top i a) as [] by mauto 3.
  assert (Γ ⊢ A' ® glu_typ_top i a) as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert (Γ ⊢ A ≈ V : Type@(ulvl i)) by (rewrite <- (exp_wk_id A); mauto 4).
  assert (Γ ⊢ A' ≈ V : Type@(ulvl i)) by (rewrite <- (exp_wk_id A'); mauto 4).
  etransitivity; [ eassumption | symmetry; eassumption ].
Qed.

Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mctt.

Lemma glu_univ_elem_per_univ_elem_typ_escape : forall {i : uidx} {a a' elem_rel P P' El El' Γ A A'},
    DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Type@(ulvl i).
Proof.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert (DG a ∈ glu_univ_elem i ↘ P' ↘ El') by (setoid_rewrite Hper; eassumption).
  handle_functional_glu_univ_elem; mautosolve 4.
Qed.

Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mctt.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i : uidx} {a a' P P' El El' Γ A A'},
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ≈ A' : Type@(ulvl i).
Proof.
  intros * [] **.
  mauto 4.
Qed.

Hint Resolve glu_univ_elem_per_univ_typ_escape : mctt.

Lemma glu_univ_elem_per_univ_typ_iff : forall {i : uidx} {a a' P P' El El'},
    Dom a ≈ a' ∈ per_univ i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  intros * Hper **.
  eapply functional_glu_univ_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.

Corollary glu_univ_elem_cumu_ge : forall {i : nat} {j : nat} {a P El},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem j ↘ P' ↘ El'.
Proof.
  intros.
  assert (Dom a ≈ a ∈ per_univ i) as [R] by mauto.
  assert (DF a ≈ a ∈ per_univ_elem j ↘ R) by mauto.
  mauto.
Qed.

Hint Resolve glu_univ_elem_cumu_ge : mctt.

(** The same along the order of universe indices: in particular, a small type
    is glued at every large index. *)
Corollary glu_univ_elem_cumu_ge_uidx : forall {i j : uidx} {a P El},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem j ↘ P' ↘ El'.
Proof.
  intros.
  assert (Dom a ≈ a ∈ per_univ i) as [R] by mauto 2.
  assert (DF a ≈ a ∈ per_univ_elem j ↘ R) by (eapply per_univ_elem_cumu_uidx; eassumption).
  mauto 2.
Qed.

Corollary glu_univ_elem_cumu_max_left : forall {i : nat} {j : nat} {a P El},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  mauto.
Qed.

Corollary glu_univ_elem_cumu_max_right : forall {i : nat} {j : nat} {a P El},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  mauto.
Qed.

Section glu_univ_elem_cumulativity.
  #[local]
  Lemma glu_univ_elem_cumulativity_ge : forall {i j : uidx} {a P P' El El'},
      uidx_le i j ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
      (forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® P') /\
        (forall Γ A M m, Γ ⊢ M : A ® m ∈ El -> Γ ⊢ M : A ® m ∈ El') /\
        (forall Γ A M m, Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El' -> Γ ⊢ M : A ® m ∈ El).
  Proof.
    simpl.
    intros * Hge Hglu Hglu'. gen El' P' j.
    glu_univ_elem_induction Hglu; repeat split; intros;
      try assert (DF a ≈ a ∈ per_univ_elem j ↘ in_rel) by (eapply per_univ_elem_cumu_uidx; eassumption);
      invert_glu_univ_elem Hglu';
      handle_functional_glu_univ_elem;
      simpl in *;
      (** Every equation of a glued type is in the ambient universe of its
          index, the large universe [Type@(ulvl u)], so each is lifted along
          the order on large levels ([uidx_le_ulvl_le]). *)
      try match goal with Hge : uidx_le ?u ?v |- _ =>
        let Hl := fresh "Hl" in
        pose proof (uidx_le_ulvl_le _ _ Hge) as Hl;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A ≈ ?B : Type@(ulvl u) |- _ =>
          let T := constr:(wf_exp_eq gc_deps gc_stack _ (Type@(ulvl v)) A B) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_eq_ge _ _ _ _ _ _ _ Hl H) end;
        repeat match goal with H : _ ⍮ _ ⍮ _ ⊢ ?A : Type@(ulvl u) |- _ =>
          let T := constr:(wf_exp gc_deps gc_stack _ (Type@(ulvl v)) A) in
          assert_fails (assert T by assumption);
          pose proof (lift_exp_ge _ _ _ _ _ _ Hl H) end end;
      try solve [repeat split; intros; destruct_conjs; mauto 2 | intuition mauto 3].
    (** A small universe: only the ambient universe of its type-level gluing
        changes between the two indices; the level term, the element's gluing
        at the realiser of the level and its readback clause carry over. *)
    all: try solve
      [ match goal with
        | H : exists t, glu_lvl _ t _ /\ _ |- exists t, glu_lvl _ t _ /\ _ =>
            destruct H as (t & Ht & Heq); exists t; split; [ exact Ht | eapply lift_exp_eq_ge; eassumption ]
        | H : _ /\ (exists t, glu_lvl _ t _ /\ _) /\ _ /\ _ |- _ /\ (exists t, glu_lvl _ t _ /\ _) /\ _ /\ _ =>
            destruct H as (HM & (t & Ht & Heq) & HP & Hr);
            repeat apply conj;
            [ exact HM | exists t; split; [ exact Ht | eapply lift_exp_eq_ge; eassumption ] | exact HP | exact Hr ]
        | H : _ /\ (exists t, glu_lvl _ t _ /\ _) /\ _ /\ _,
            H' : exists t, glu_lvl _ t _ /\ _ |- _ /\ (exists t, glu_lvl _ t _ /\ _) /\ _ /\ _ =>
            destruct H as (HM & _ & HP & Hr);
            repeat apply conj; [ exact HM | exact H' | exact HP | exact Hr ]
        end ].

    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      econstructor; intros; mauto 4.
      + assert (Δ ⊢ IT[φ]ʷ ® IP) by mauto.
        enough (forall Γ A, Γ ⊢ A ® IP -> Γ ⊢ A ® IP') by mauto 4.
        eapply proj1; mautosolve 4.
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        assert (forall Γ A, Γ ⊢ A ® OP m equiv_m -> Γ ⊢ A ® OP' m equiv_m) by (eapply proj1; mauto).
        enough (Δ ⊢ OT[(ι φ),,M] ® OP m equiv_m) by mauto.
        enough (Δ ⊢ M : IT[φ]ʷ ® m ∈ IEl) by mauto.
        eapply IHHglu; mautosolve 4.
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto 4.
      + enough (forall Γ A, Γ ⊢ A ® IP -> Γ ⊢ A ® IP') by mauto 4.
        eapply proj1; mautosolve 4.
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct_rel_mod_app.
        handle_per_univ_elem_irrel.
        eexists; split; mauto 4.
        assert (forall Γ A M m, Γ ⊢ M : A ® m ∈ OEl n equiv_n -> Γ ⊢ M : A ® m ∈ OEl' n equiv_n) by (eapply proj1, proj2; mauto 4).
        enough (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® fa ∈ OEl n equiv_n) by mauto 4.
        assert (Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl) by (eapply IHHglu; mauto 3).
        assert (exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® mn ∈ OEl n equiv_n) by mauto 4.
        destruct_conjs.
        functional_eval_rewrite_clear; mautosolve 4.
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      handle_per_univ_elem_irrel.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      handle_per_univ_elem_irrel.
      match goal with
      | _: ⟦ B ⟧ ρ ↦ n ↘ ?a |- _ =>
          rename a into b
      end.
      eexists; split; mauto 4.
      assert (forall Γ A M m, Γ ⊢ A ® OP n equiv_n -> Γ ⊢ M : A ® m ∈ OEl' n equiv_n -> Γ ⊢ M : A ® m ∈ OEl n equiv_n) by (eapply proj2, proj2; eauto 3).
      assert (Δ ⊢ OT[(ι φ),,N] ® OP n equiv_n) by mauto 4.
      enough (Δ ⊢ M[φ]ʷ $ N : OT[(ι φ),,N] ® fa ∈ OEl' n equiv_n) by mauto 4.
      assert (Δ ⊢ N : IT[φ]ʷ ® n ∈ IEl') by (eapply IHHglu; mauto 3).
      assert (Δ ⊢ IT[φ]ʷ ® IP') by (eapply glu_univ_elem_trm_typ; mauto 2).
      assert (Δ ⊢ IT0[φ]ʷ ® IP') by mauto 2.
      assert (Δ ⊢ IT[φ]ʷ ≈ IT0[φ]ʷ : Type@(ulvl j)) as HITeq by mauto 2.
      assert (Δ ⊢ N : IT0[φ]ʷ ® n ∈ IEl') by (rewrite <- HITeq; mauto 3).
      assert (exists mn, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT0[(ι φ),,N] ® mn ∈ OEl' n equiv_n) by mauto 3.
      destruct_conjs.
      functional_eval_rewrite_clear.
      assert (DG b ∈ glu_univ_elem j ↘ OP' n equiv_n ↘ OEl' n equiv_n) as Hbj by mauto 3.
      assert (Δ ⊢ OT0[(ι φ),,N] ® OP' n equiv_n) by (eapply glu_univ_elem_trm_typ; mauto 3).
      (** Both codomains are glued at [j], so they are equal in [Type@(ulvl j)];
          the one at [i] is moved up by the induction hypothesis. *)
      match goal with HOT : _ ⊢ OT[(ι φ),,N] ® OP ?n0 ?eq0, Hev : ⟦ B ⟧ _ ↦ _ ↘ b |- _ =>
        assert (Δ ⊢ OT[(ι φ),,N] ® OP' n0 eq0)
          by (eapply (proj1 (H2 n0 eq0 b Hev j Hge (OP' n0 eq0) (OEl' n0 eq0) Hbj)); exact HOT) end.
      assert (Δ ⊢ OT[(ι φ),,N] ≈ OT0[(ι φ),,N] : Type@(ulvl j)) as Heq
        by (eapply (glu_univ_elem_typ_unique_upto_exp_eq' (i := j)); [ exact Hbj | eassumption | eassumption ]).
      rewrite Heq; eassumption.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
      destruct_by_head neut_glu_typ_pred.
      econstructor; mautosolve 4.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mautosolve 4.
  Qed.

  (** The two instances the development uses: along the levels of the large
      tier, and from a small universe into every large one. *)
  Lemma glu_univ_elem_cumulativity_nat : forall {i j : nat} {a P P' El El'},
      i <= j ->
      DG a ∈ glu_univ_elem i ↘ P ↘ El ->
      DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
      (forall Γ A, Γ ⊢ A ® P -> Γ ⊢ A ® P') /\
        (forall Γ A M m, Γ ⊢ M : A ® m ∈ El -> Γ ⊢ M : A ® m ∈ El') /\
        (forall Γ A M m, Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El' -> Γ ⊢ M : A ® m ∈ El).
  Proof. intros; eapply (glu_univ_elem_cumulativity_ge (i := ul i) (j := ul j)); [ cbn; lia | eassumption | eassumption ]. Qed.

End glu_univ_elem_cumulativity.

(** The index-order instances of cumulativity for a type and an element. *)
Corollary glu_univ_elem_typ_cumu_ge_uidx : forall {i j : uidx} {a P P' El El' Γ A},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros * Hle Hi Hj HA.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (Htyp & _); exact (Htyp _ _ HA).
Qed.

Corollary glu_univ_elem_exp_cumu_ge_uidx : forall {i j : uidx} {a P P' El El' Γ A M m},
    uidx_le i j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * Hle Hi Hj HM.
  destruct (glu_univ_elem_cumulativity_ge Hle Hi Hj) as (_ & Hexp & _); exact (Hexp _ _ _ _ HM).
Qed.

Corollary glu_univ_elem_typ_cumu_ge : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_left : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_right : forall {i : nat} {j : nat} {a P P' El El' Γ A},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A ® P'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_ge : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_left : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_right : forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    i <= j ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros * ? ? ?. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_nat; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_left :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_right :  forall {i : nat} {j : nat} {a P P' El El' Γ A M m},
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ M : A ® m ∈ El' ->
    Γ ⊢ M : A ® m ∈ El.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

Lemma glu_univ_elem_exp_conv : forall {i : nat} {j : nat} {k : nat} {a a' P P' El El' Γ A M m},
    Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ A ® P' ->
    Γ ⊢ M : A ® m ∈ El'.
Proof.
  intros * [] ? ? ? ?.
  assert (Dom a ≈ a' ∈ per_univ (max i k)) as Haa' by (eexists; mauto using per_univ_elem_cumu_max_right).
  assert (exists P El, DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El) as [Pik [Elik]] by mauto using glu_univ_elem_cumu_max_left.
  assert (DG a' ∈ glu_univ_elem (max i k) ↘ Pik ↘ Elik) by (setoid_rewrite <- Haa'; eassumption).
  assert (Γ ⊢ M : A ® m ∈ Elik) by (eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption).
  assert (exists P El, DG a' ∈ glu_univ_elem (max j (max i k)) ↘ P ↘ El) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_max_right.
  assert (Γ ⊢ M : A ® m ∈ Eltop) by (eapply glu_univ_elem_exp_cumu_max_right; [| | eassumption]; eassumption).
  eapply glu_univ_elem_exp_lower_max_left; mauto.
Qed.

(** ** The Order on Levels, Syntactically

    Two level terms glued to levels in the canonical order ([per_sublvl]) are
    in the syntactic order [maxl t t' ≈ t'].  Each is equal to its readback,
    and the readbacks are canonical levels in [lvl_le], which the level
    equations turn into the equation ([lvl_exp_of_le]).  This is the
    syntactic content of a semantic subtyping between small universes. *)
Lemma glu_lvl_sublvl_eq : forall {Γ t t' l l'},
    ⊢ Γ ->
    Dom l ≈ l ∈ per_lvl ->
    Dom l' ≈ l' ∈ per_lvl ->
    per_sublvl l l' ->
    glu_lvl Γ t l ->
    glu_lvl Γ t' l' ->
    Γ ⊢ maxl t t' ≈ t' : Level.
Proof.
  intros * HΓ Hl Hl' Hle Ht Ht'.
  destruct (Hle (length Γ)) as [[c xs] [[d ys] [HL [HL' HLL']]]].
  assert (Γ ⊢ t ≈ nf_lvl_of (c, xs) : Level) as Htc
    by (rewrite <- (exp_wk_id t); eapply glu_lvl_readback; mauto 3).
  assert (Γ ⊢ t' ≈ nf_lvl_of (d, ys) : Level) as Htd
    by (rewrite <- (exp_wk_id t'); eapply glu_lvl_readback; mauto 3).
  assert (Γ ⊢ nf_lvl_of (c, xs) : Level) as Hc by (gen_presups; eassumption).
  assert (Γ ⊢ nf_lvl_of (d, ys) : Level) as Hd by (gen_presups; eassumption).
  unfold nf_lvl_of in *; cbn [nf_to_exp fst snd] in *.
  assert (la_wf Γ xs) by (eapply lvl_exp_of_la_wf; exact Hc).
  assert (la_wf Γ ys) by (eapply lvl_exp_of_la_wf; exact Hd).
  transitivity (maxl (lvl_exp_of c (la_to_list xs)) (lvl_exp_of d (la_to_list ys)));
    [ apply wf_exp_eq_maxl_cong; assumption |].
  transitivity (lvl_exp_of d (la_to_list ys));
    [ apply lvl_exp_of_le; assumption | symmetry; assumption ].
Qed.

Lemma glu_univ_elem_per_subtyp_typ_escape : forall {i : uidx} {a a' P P' El El' Γ A A'},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A ® P ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ A ⊆ A'.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  gen A' A Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    destruct_by_head pi_glu_typ_pred;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    try solve [simpl in *; mauto 3].
  - match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert (Γ ⊢ A ≈ V : Type@(ulvl i)) as HAV by (rewrite <- (exp_wk_id A); mauto 4).
    assert (Γ ⊢ A' ≈ V : Type@(ulvl i)) as HA'V by (rewrite <- (exp_wk_id A'); mauto 4).
    rewrite HAV, HA'V.
    (** Both read back to the same neutral, so the goal is reflexivity at the
        large universe of the index. *)
    gen_presups.
    eapply wf_subtyp_refl_typ; eassumption.
  (** [Level], [ℕ], [⊤] and [⊥]: both sides are equal to the same closed type
      in the ambient universe, so the goal is reflexivity, at the large level
      the index lives at. *)
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  - simpl in *; gen_presups; bulky_rewrite; eapply (wf_subtyp_refl_typ _ _ _ _ 0); mauto 3.
  (** A universe below a larger one, in either tier, and a small one below a
      large one.  Two small universes are below each other by the syntactic
      order on their glued level terms ([glu_lvl_sublvl_eq]); a small one is
      below a large one because its level term is a level. *)
  - simpl in *; bulky_rewrite; mauto 3.
  - simpl in *; destruct_conjs; gen_presups.
    match goal with
    | Hle : per_sublvl ?l ?l', Hl : per_lvl ?l ?l, Hl' : per_lvl ?l' ?l',
        Ht : glu_lvl _ ?t ?l, Ht' : glu_lvl _ ?t' ?l',
        Heq : _ ⊢ A ≈ Typeˢ⟨?t⟩ : _, Heq' : _ ⊢ A' ≈ Typeˢ⟨?t'⟩ : _ |- _ =>
        assert (Γ ⊢ t : Level) by (eapply wf_univ_lvl_inversion; eassumption);
        assert (Γ ⊢ t' : Level) by (eapply wf_univ_lvl_inversion; eassumption);
        rewrite Heq, Heq';
        apply wf_subtyp_suniv; [ assumption | assumption | assumption |];
        let HΓ := fresh "HΓ" in
        assert (HΓ : ⊢ Γ) by (gen_presups; assumption);
        exact (glu_lvl_sublvl_eq HΓ Hl Hl' Hle Ht Ht')
    end.
  - simpl in *; destruct_conjs; gen_presups.
    match goal with
    | Ht : glu_lvl _ ?t ?l, Heq : _ ⊢ A ≈ Typeˢ⟨?t⟩ : _ |- _ =>
        assert (Γ ⊢ t : Level) by (eapply wf_univ_lvl_inversion; eassumption);
        rewrite Heq
    end.
    bulky_rewrite; mauto 3.
  - destruct_by_head pi_glu_typ_pred.
    rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl.
    rename A0 into A'. rename IT0 into IT'. rename OT0 into OT'.
    rename x3 into OP'. rename x4 into OEl'.
    assert (Γ ⊢ IT ® IP) by (rewrite <- (exp_wk_id IT); mauto 4).
    assert (Γ ⊢ IT' ® IP) by (rewrite <- (exp_wk_id IT'); mauto 4).
    do 2 bulky_rewrite1.
    assert (Γ ⊢ IT ≈ IT' : Type@(ulvl i)) as HITeq by mauto 4.
    enough (Γ ▹ IT' ⊢ OT ⊆ OT') by mauto 3.
    assert (Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel) as equiv_len_len' by (eapply per_bot_then_per_elem; mauto 4).
    assert (Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel) as equiv_len_len by (eapply per_bot_then_per_elem; mauto 4).
    assert (Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel) as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto 4).
    handle_per_univ_elem_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    apply_relation_equivalence.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    match goal with
    | _: (⟦ B ⟧ ρ ↦ ⇑! a (length Γ) ↘ ?a0),
        _: ⟦ B' ⟧ ρ' ↦ ⇑! a' (length Γ) ↘ ?a0' |- _ =>
        rename a0 into b;
        rename a0' into b'
    end.
    assert (DG b ∈ glu_univ_elem i ↘ OP ⇑! a (length Γ) equiv_len_len ↘ OEl ⇑! a (length Γ) equiv_len_len) by mauto 4.
    assert (DG b' ∈ glu_univ_elem i ↘ OP' ⇑! a' (length Γ) equiv_len'_len' ↘ OEl' ⇑! a' (length Γ) equiv_len'_len') by mauto 4.
    assert (Γ ▹ IT' ⊢ OT ® OP ⇑! a (length Γ) equiv_len_len).
    {
      assert (Γ ▹ IT ⊢ #0 : IT[↑]ʷ ® ⇑! a (length Γ) ∈ IEl) by (eapply var0_glu_elem; mauto 3).
      assert (⊢ Γ ▹ IT) by mauto 3.
      assert (Γ ▹ IT ⊢ OT[ι ↑,,#0] ® OP ⇑! a (length Γ) equiv_len_len) by mauto 4.
      assert (Γ ▹ IT ⊢ OT ® OP ⇑! a (length Γ) equiv_len_len)
        by (eapply glu_univ_elem_typ_resp_exp_eq; [ eassumption | eassumption
                                                  | eapply (shift_var_eq _ _ (Type@(ulvl i)) _ (ul (ulvl i))); eassumption ]).
      eapply glu_univ_elem_typ_resp_ctxsub; [ eassumption | eassumption | mauto 4 ].
    }
    assert (Γ ▹ IT' ⊢ OT' ® OP' ⇑! a' (length Γ) equiv_len'_len').
    {
      assert (Γ ▹ IT' ⊢ #0 : IT'[↑]ʷ ® ⇑! a' (length Γ) ∈ IEl) by (eapply var0_glu_elem; mauto 3).
      assert (⊢ Γ ▹ IT') by mauto 3.
      assert (Γ ▹ IT' ⊢ OT'[ι ↑,,#0] ® OP' ⇑! a' (length Γ) equiv_len'_len') by mauto 4.
      eapply glu_univ_elem_typ_resp_exp_eq; [ eassumption | eassumption
                                            | eapply (shift_var_eq _ _ (Type@(ulvl i)) _ (ul (ulvl i))); eassumption ].
    }
    mauto 3.
Qed.

Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mctt.

Lemma glu_univ_elem_per_subtyp_trm_if : forall {i : uidx} {a a' P P' El El' Γ A A' M m},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem i ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  assert (Γ ⊢ A ⊆ A') by (eapply glu_univ_elem_per_subtyp_typ_escape; only 4: eapply glu_univ_elem_trm_typ; mauto).
  gen m M A' A. gen Γ. gen El' El P' P.
  induction Hsubtyp; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    repeat invert_glu_rel1;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    repeat invert_glu_rel1;
    try solve [simpl in *; intuition mauto 3].
  - match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Γ)) as [V []]).
    econstructor; mauto 3.
    + econstructor; mauto 3.
    + intros.
      match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Δ)) as [? []]).
      functional_read_rewrite_clear.
      assert (Δ ⊢ A[φ]ʷ ⊆ A'[φ]ʷ) by mauto 3.
      assert (Δ ⊢ M[φ]ʷ ≈ M' : A[φ]ʷ) by mauto 3.
      mauto 3.
  - simpl in *.
    destruct_conjs.
    intuition mauto 3.
    assert (exists P El, DG m ∈ glu_univ_elem j ↘ P ↘ El) as [? [?]] by mauto 3.
    do 2 eexists; split; mauto 3.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mautosolve 3.
  (** Small universe below small universe: the element is glued at the larger
      realiser by cumulativity (the order on levels bounds the realisers), and
      its readback moves by subsumption along [A ⊆ A']. *)
  - simpl in *; destruct_conjs.
    match goal with
    | Hg : glu_univ_elem (us (dlvl_real ?l)) ?P0 _ m, Hp : ?P0 Γ M, Hle : per_sublvl ?l ?l' |- _ =>
        assert (exists P El, DG m ∈ glu_univ_elem (us (dlvl_real l')) ↘ P ↘ El) as [Pj [Elj Hj]]
          by (eapply (glu_univ_elem_cumu_ge_uidx (i := us (dlvl_real l)));
              [ cbn; apply per_sublvl_real; exact Hle | exact Hg ]);
        repeat apply conj;
        [ mauto 3
        | eexists; split; eassumption
        | do 2 eexists; split;
          [ exact Hj
          | eapply (glu_univ_elem_typ_cumu_ge_uidx (i := us (dlvl_real l)) (j := us (dlvl_real l')));
            [ cbn; apply per_sublvl_real; exact Hle | exact Hg | exact Hj | exact Hp ] ]
        | intros Δ φ W Hφ Hr; eapply wf_exp_eq_subtyp'; [ eauto | mauto 3 ] ]
    end.
  (** Small universe below a large one: the element is glued at the large
      index, by cumulativity across the tiers. *)
  - simpl in *; destruct_conjs.
    match goal with Hg : glu_univ_elem (us ?n) ?P0 _ m, Hp : ?P0 Γ M |- _ =>
      assert (exists P El, DG m ∈ glu_univ_elem (ul j) ↘ P ↘ El) as [Pj [Elj Hj]]
        by (eapply (glu_univ_elem_cumu_ge_uidx (i := us n)); [ exact I | exact Hg ]);
      repeat split; [ mauto 3 | assumption |];
      do 2 eexists; split; [ exact Hj |];
      eapply (glu_univ_elem_typ_cumu_ge_uidx (i := us n) (j := ul j));
        [ exact I | exact Hg | exact Hj | exact Hp ]
    end.
  - rename A0 into A'.
    rename IT0 into IT'. rename OT0 into OT'.
    rename x into IP. rename x0 into IEl.
    rename x1 into OP. rename x2 into OEl.
    rename x3 into OP'. rename x4 into OEl'.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
    + enough (Sub Πᵈ a ρ B <: Πᵈ a' ρ' B' at i) by (eapply per_elem_subtyping; try eassumption).
      econstructor; mauto 3.
    + intros.
      assert (Γ ⊢ IT ® IP) by (rewrite <- (exp_wk_id IT); mauto 4).
      assert (Γ ⊢ IT' ® IP) by (rewrite <- (exp_wk_id IT'); mauto 4).
      assert (Δ ⊢ IT'[φ]ʷ ≈ IT[φ]ʷ : Type@(ulvl i)) by (symmetry; mauto 4 using glu_univ_elem_per_univ_typ_escape).
      assert (Δ ⊢ N : IT'[φ]ʷ ® n ∈ IEl) by (simpl; bulky_rewrite1; eassumption).
      assert (exists mn : domain, $| m & n |↘ mn /\ Δ ⊢ M[φ]ʷ $ N : OT'[(ι φ),,N] ® mn ∈ OEl n equiv_n) by mauto 3.
      destruct_conjs.
      eexists; split; mauto 3.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      match goal with
      | _: (⟦ B ⟧ ρ ↦ n ↘ ?a),
          _: ⟦ B' ⟧ ρ' ↦ n ↘ ?a' |- _ =>
          rename a into b;
          rename a' into b'
      end.
      assert (DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n) by mauto 3.
      assert (DG b' ∈ glu_univ_elem i ↘ OP' n equiv_n ↘ OEl' n equiv_n) by mauto 3.
      assert (Δ ⊢ OT'[(ι φ),,N] ® OP n equiv_n) by (eapply glu_univ_elem_trm_typ; mauto 3).
      assert (Sub b <: b' at i) by mauto 3.
      assert (Δ ⊢ OT'[(ι φ),,N] ⊆ OT[(ι φ),,N]) by mauto 3.
      intuition.
Qed.

Lemma glu_univ_elem_per_subtyp_trm_conv : forall {i : nat} {j : nat} {k : nat} {a a' P P' El El' Γ A A' M m},
    Sub a <: a' at i ->
    DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    DG a' ∈ glu_univ_elem k ↘ P' ↘ El' ->
    Γ ⊢ A' ® P' ->
    Γ ⊢ M : A ® m ∈ El ->
    Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros.
  assert (Sub a <: a' at (max i (max j k))) by mauto using per_subtyp_cumu_left.
  assert (j <= max i (max j k)) by lia.
  assert (exists P El, DG a ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_ge.
  assert (k <= max i (max j k)) by lia.
  assert (exists P El, DG a' ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El) as [Ptop' [Eltop']] by mauto using glu_univ_elem_cumu_ge.
  assert (Γ ⊢ A' ® Ptop') by (eapply glu_univ_elem_typ_cumu_ge; mauto).
  assert (Γ ⊢ M : A ® m ∈ Eltop) by (eapply @glu_univ_elem_exp_cumu_ge with (i := j); mauto).
  assert (Γ ⊢ M : A' ® m ∈ Eltop') by (eapply glu_univ_elem_per_subtyp_trm_if; mauto).
  eapply glu_univ_elem_exp_lower; mauto.
Qed.

(** *** Lemmas for [glu_rel_typ_with_sub] and [glu_rel_exp_with_sub] *)

Lemma mk_glu_rel_typ_with_sub' : forall {i : nat} {Δ A σ ρ a},
    ⟦ A ⟧ ρ ↘ a ->
    (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

Hint Resolve mk_glu_rel_typ_with_sub' : mctt.

Lemma mk_glu_rel_typ_with_sub'' : forall {i : nat} {Δ A σ ρ a},
    ⟦ A ⟧ ρ ↘ a ->
    Dom a ≈ a ∈ per_univ i ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [] ?.
  assert (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) as [? []] by mauto.
  eapply mk_glu_rel_typ_with_sub'; mauto.
Qed.

Hint Resolve mk_glu_rel_typ_with_sub'' : mctt.

Lemma mk_glu_rel_exp_with_sub' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    ⟦ M ⟧ ρ ↘ m ->
    (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

Hint Resolve mk_glu_rel_exp_with_sub' : mctt.

Lemma mk_glu_rel_exp_with_sub'' : forall {i : nat} {Δ A M σ ρ a m},
    ⟦ A ⟧ ρ ↘ a ->
    ⟦ M ⟧ ρ ↘ m ->
    Dom a ≈ a ∈ per_univ i ->
    (forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ M[σ] : A[σ] ® m ∈ El) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [] ?.
  assert (exists P El, DG a ∈ glu_univ_elem i ↘ P ↘ El) as [? []] by mauto.
  eapply mk_glu_rel_exp_with_sub'; mauto.
Qed.

Hint Resolve mk_glu_rel_exp_with_sub'' : mctt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : forall {i : nat} {Δ A M σ Γ ρ},
  Δ ⊢s σ : Γ ->
  glu_rel_exp_with_sub i Δ M A σ ρ ->
  glu_rel_exp_with_sub (S i) Δ A Type@i σ ρ.
Proof.
  intros * ? [].
  econstructor; mauto.
  assert (Δ ⊢ A[σ] : Type@i) by (eapply (glu_univ_elem_trm_univ_lvl (ul i)); [ reflexivity | eassumption.. ]).
  repeat split; try do 2 eexists; mauto 3.
  split; [ eassumption | eapply (glu_univ_elem_trm_typ (ul i)); eassumption ].
Qed.

Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mctt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : forall {i : nat} {Δ A} {j : nat} {σ ρ},
  glu_rel_exp_with_sub i Δ A Type@j σ ρ ->
  glu_rel_typ_with_sub j Δ A σ ρ.
Proof.
  intros * [].
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  econstructor; mauto 3.
Qed.

Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mctt.

Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : forall {Δ A} {j : nat} {σ Γ ρ},
  Δ ⊢s σ : Γ ->
  glu_rel_typ_with_sub j Δ A σ ρ ->
  glu_rel_exp_with_sub (S j) Δ A Type@j σ ρ.
Proof.
  intros * ? [].
  simplify_evals.
  econstructor; mauto.
  assert (Δ ⊢ A[σ] : Type@j) by (eapply (glu_univ_elem_univ_lvl (ul j)); [ reflexivity | eassumption.. ]).
  repeat split; try do 2 eexists; mauto 3.
Qed.

Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mctt.

(** *** Lemmas for [glu_ctx_env] *)

(** Stated for context refinement, since context equality is not a judgment.
    It goes one way, and [ctxsub_sub] transports the substitution itself. *)
Lemma glu_ctx_env_sub_resp_ctxsub : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall {Δ Δ' σ ρ},
      Δ ⊢s σ ® ρ ∈ Sb ->
      Δ' ⊆ Δ ->
      Δ' ⊢s σ ® ρ ∈ Sb.
Proof.
  induction 1; intros * HSb Hctxsub;
    apply_predicate_equivalence;
    simpl in *;
    mauto 4.
  all: try destruct_by_head cons_glu_sub_pred.
  all: try destruct_by_head cons_def_glu_sub_pred.
  all: try destruct_by_head cons_mod_glu_sub_pred.
  all: econstructor; mauto 4.
  all: eapply glu_univ_elem_trm_resp_ctxsub; eassumption.
Qed.

Lemma glu_ctx_env_sub_resp_sub_eq : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall {Δ σ σ' ρ},
      Δ ⊢s σ ® ρ ∈ Sb ->
      Δ ⊢s σ ≈ σ' : Γ ->
      Δ ⊢s σ' ® ρ ∈ Sb.
Proof.
  (** [gen_presup] misses [wf_sub_eq] (its pattern is one argument short), so
      the two projections are taken by hand, here and below. *)
  induction 1; intros * HSb Hsubeq;
    apply_predicate_equivalence;
    simpl in *;
    (pose proof (wf_sub_eq_left _ _ _ _ _ _ Hsubeq) as Hσ; pose proof (wf_sub_eq_right _ _ _ _ _ _ Hsubeq) as Hσ');
    try eassumption.
  - destruct_by_head cons_glu_sub_pred.
    econstructor; mauto 4.
    (** The tail: [Wk] postcomposed with either side, by the induction hypothesis. *)
    2: eapply IHglu_ctx_env;
         [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ A[↑]ʷ : Type@i) by (eapply wk_preserves_typ; mauto 3).
    assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Type@i) as <- by mauto 3.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <- by mauto 3.
    eassumption.
  - (** A definition entry: as an assumption entry, and the tie does not
        mention [σ]. *)
    destruct_by_head cons_def_glu_sub_pred.
    econstructor; mauto 4.
    2: eapply IHglu_ctx_env;
         [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    assert (Γ ▸ A ≔ M ⊢ A[↑]ʷ : Type@i) by (eapply wk_preserves_typ; mauto 3).
    assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Type@i) as <- by mauto 3.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <- by mauto 3.
    eassumption.
  - (** A module slot: the tie does not mention [σ]. *)
    destruct_by_head cons_mod_glu_sub_pred.
    econstructor; [ exact Hσ' | eassumption |].
    eapply IHglu_ctx_env;
      [ eassumption | eapply wf_sub_eq_compose_right; [ | eassumption ]; eapply wf_sub_shift; mauto 3 ].
Qed.

Add Parametric Morphism Sb Γ (H : glu_ctx_env Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto 2 using wf_sub_eq_sym.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq : forall {i : nat} {Γ A Sb Δ σ σ' ρ},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢ A : Type@i ->
    Δ ⊢s σ ≈ σ' : Γ ▹ A ->
    Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred i Γ A Sb ->
    Δ ⊢s σ' ® ρ ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  (pose proof (wf_sub_eq_left _ _ _ _ _ _ Heq) as Hσ; pose proof (wf_sub_eq_right _ _ _ _ _ _ Heq) as Hσ').
  assert (⊢ Γ ▹ A) by mauto 3.
  assert (Γ ▹ A ⊢s Wk : Γ) by mauto 3.
  assert (Γ ▹ A ⊢ A[↑]ʷ : Type@i) by (eapply wk_preserves_typ; mauto 3).
  assert (Δ ⊢s Wk ⨟ σ : Γ) by mauto 3.
  assert (Δ ⊢s Wk ⨟ σ' : Γ) by mauto 3.
  assert (Δ ⊢s Wk ⨟ σ ≈ Wk ⨟ σ' : Γ) by mauto 3.
  econstructor; mauto 3.
  - assert (Δ ⊢ A[↑]ʷ[σ] ≈ A[↑]ʷ[σ'] : Type@i) as <- by mauto 4.
    assert (Δ ⊢ #0[σ] ≈ #0[σ'] : A[↑]ʷ[σ]) as <-; mauto 3.
  - assert (Δ ⊢s Wk ⨟ σ ≈ Wk ⨟ σ' : Γ) as <-; eassumption.
Qed.

Add Parametric Morphism i Γ A Sb Δ (Hglu : EG Γ ∈ glu_ctx_env ↘ Sb) (HA : Γ ⊢ A : Type@i) : (cons_glu_sub_pred i Γ A Sb Δ)
    with signature wf_sub_eq gc_deps gc_stack Δ (Γ ▹ A) ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq, wf_sub_eq_sym.
Qed.

Lemma glu_ctx_env_per_env : forall {Γ Sb env_rel Δ σ ρ},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    Dom ρ ≈ ρ ∈ env_rel.
Proof.
  intros * Hglu Hper.
  gen ρ σ Δ env_rel.
  induction Hglu; intros.
  4:{ (** A module slot: the tie is part of the gluing. *)
    apply_predicate_equivalence.
    destruct_by_head cons_mod_glu_sub_pred.
    invert_per_ctx_env Hper.
    apply_predicate_equivalence.
    match goal with E : env_rel <~> _ |- _ => apply E end.
    repeat split; try eassumption; eapply IHHglu; eassumption. }
  3:{ (** A definition entry, read against its canonical context PER: the
        tie is part of the gluing. *)
    apply_predicate_equivalence.
    destruct_by_head cons_def_glu_sub_pred.
    assert (HAs : Γ ⊨ A : Type@i) by (apply completeness_fundamental_exp; eassumption).
    assert (HMs : Γ ⊨ M : A) by (apply completeness_fundamental_exp; eassumption).
    assert (⊢ Γ) by mauto 3.
    destruct (sem_ctx_per_ctx_env (completeness_fundamental_ctx _ ltac:(eassumption))) as [tail_rel Htail].
    pose proof (per_ctx_env_of_def Htail HAs HMs) as Hd.
    assert (E : env_rel <~> per_env_extend_def A M tail_rel) by (eapply per_ctx_env_right_irrel; eassumption).
    apply E.
    assert (Hρ : Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (eapply IHHglu; eassumption).
    destruct (rel_exp_of_typ_inversion_simple_at Htail HAs _ _ Hρ) as [a1 [a2 [Ha1 [Ha2 [R HR]]]]].
    functional_eval_rewrite_clear.
    split; [ split; [ assumption |] | split; assumption ].
    eapply per_head_of; [ eassumption | eassumption | exact HR |].
    eapply glu_univ_elem_per_elem; eassumption. }
  all: invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto 3.

  rename i0 into j.
  inversion_clear_by_head cons_glu_sub_pred.
  assert (Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by intuition.
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  assert (exists P' El', DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El') as [? []] by mauto 3 using glu_univ_elem_cumu_max_left.
  eexists; eapply glu_univ_elem_per_elem; mauto using per_univ_elem_cumu_max_right.
  eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption.
Qed.

Lemma glu_ctx_env_wf_ctx : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    ⊢ Γ.
Proof.
  induction 1; intros; mauto.
Qed.

Lemma glu_ctx_env_sub_escape : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      Δ ⊢s σ : Γ.
Proof.
  induction 1; intros;
    handle_functional_glu_univ_elem;
    try destruct_by_head cons_glu_sub_pred;
    try destruct_by_head cons_def_glu_sub_pred;
    try destruct_by_head cons_mod_glu_sub_pred;
    eassumption.
Qed.

Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mctt.

Lemma glu_ctx_env_per_ctx_env : forall {Γ Sb},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    exists env_rel, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel.
Proof.
  intros.
  eapply sem_ctx_per_ctx_env, completeness_fundamental_ctx; mauto 2.
Qed.

Hint Resolve glu_ctx_env_per_ctx_env : mctt.

(** Stated at a single context, since syntactic context equality is not a
    judgment; this is all [functional_glu_ctx_env] needs. The two derivations
    may still assign different universe levels to the same type, which the
    final cumulativity step handles. *)
Lemma glu_ctx_env_resp_per_ctx_helper : forall {Γ Sb Sb'},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ Sb' ->
    (Sb -∙> Sb').
Proof.
  intros * Hglu Hglu'.
  gen Sb'.
  induction Hglu; intros;
    dependent destruction Hglu';
    apply_predicate_equivalence;
    try firstorder.

  (** An assumption entry and a definition entry alike: the tie does not
      depend on the level. *)
  (** A module slot: the tie does not depend on the tail's derivation. *)
  3:{ assert (HT : TSb -∙> TSb0) by intuition.
      intros Δ' σ' ρ' []; econstructor; [ eassumption | eassumption | apply HT; eassumption ]. }
  all: rename i0 into j.
  all: rename TSb0 into TSb'.
  all: assert (TSb -∙> TSb') by intuition.
  all: intros Δ' σ' ρ' [].
  all: assert (Δ ⊢s Wk ⨟ σ ® ρ↯ ∈ TSb') by intuition.
  all: assert (glu_rel_typ_with_sub j Δ A (Wk ⨟ σ) ρ↯) as [] by mauto 3.
  all: destruct_rel_typ.
  all: handle_functional_glu_univ_elem.
  all: econstructor; mauto 4.
  all: eapply (@glu_univ_elem_exp_conv i j i a a P P0 El El0); [ mauto 3 | eassumption | eassumption | eassumption | ].
  all: rewrite exp_sub_shift.
  all: eassumption.
Qed.

Corollary functional_glu_ctx_env : forall {Γ Sb Sb'},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ ∈ glu_ctx_env ↘ Sb' ->
    (Sb <∙> Sb').
Proof.
  intros; split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.

End Fixed_GCtx.

#[export] Existing Instance glu_elem_bot_morphism_iff4_Proper.
#[export] Existing Instance glu_elem_top_morphism_iff4_Proper.
#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mctt.
#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mctt.
#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mctt.
#[export]
Hint Resolve glu_univ_elem_per_univ_typ_escape : mctt.
#[export]
Hint Resolve glu_univ_elem_cumu_ge : mctt.
#[export]
Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mctt.
#[export]
Hint Resolve mk_glu_rel_typ_with_sub' : mctt.
#[export]
Hint Resolve mk_glu_rel_typ_with_sub'' : mctt.
#[export]
Hint Resolve mk_glu_rel_exp_with_sub' : mctt.
#[export]
Hint Resolve mk_glu_rel_exp_with_sub'' : mctt.
#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mctt.
#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mctt.
#[export]
Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mctt.
#[export] Existing Instance glu_ctx_env_sub_morphism_iff2_Proper.
#[export] Existing Instance cons_glu_sub_pred_morphism_iff_Proper.
#[export]
Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mctt.
#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mctt.
Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : (EG ?Γ ∈ glu_ctx_env ↘ ?Sb1),
      H2 : EG ?Γ ∈ glu_ctx_env ↘ ?Sb2 |- _ =>
      assert_fails (unify Sb1 Sb2);
      match goal with
      | H : Sb1 <∙> Sb2 |- _ => fail 1
      | _ => assert (Sb1 <∙> Sb2) by (eapply functional_glu_ctx_env; [apply H1 | apply H2]) || tactic_error Sb1 Sb2
      end
  end.

Ltac apply_functional_glu_ctx_env :=
  repeat apply_functional_glu_ctx_env1.

Ltac handle_functional_glu_ctx_env :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_ctx_env;
  apply_predicate_equivalence;
  clear_dups.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_ctx_env_cons_clean_inversion : forall {Γ TSb A Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▹ A ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : Type@i /\
      (forall Δ σ ρ,
          Δ ⊢s σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred i Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  (** [i] has to be given: the cumulativity hints let [intuition] pick any
      larger level for the type, which then no longer matches [TSb]'s. *)
  exists i; intuition.
  assert (Sb <∙> cons_glu_sub_pred i Γ A TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Lemma glu_ctx_env_cons_def_clean_inversion : forall {Γ TSb A M Sb},
  EG Γ ∈ glu_ctx_env ↘ TSb ->
  EG Γ ▸ A ≔ M ∈ glu_ctx_env ↘ Sb ->
  exists i,
    Γ ⊢ A : Type@i /\
      Γ ⊢ M : A /\
      (forall Δ σ ρ,
          Δ ⊢s σ ® ρ ∈ TSb ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (forall Δ σ ρ,
          Δ ⊢s σ ® ρ ∈ TSb ->
          glu_rel_exp_with_sub i Δ M A σ ρ) /\
      (Sb <∙> cons_def_glu_sub_pred i Γ A M TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  exists i; intuition.
  assert (Sb <∙> cons_def_glu_sub_pred i Γ A M TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

End Fixed_GCtx.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + (unshelve eapply (glu_ctx_env_cons_def_clean_inversion _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? [? [? [? []]]]])
  + dependent destruction H.

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_ctx_env_subtyp_sub_if : forall Γ Γ' Sb Sb' Δ σ ρ,
    Γ ⊆ Γ' ->
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    EG Γ' ∈ glu_ctx_env ↘ Sb' ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    Δ ⊢s σ ® ρ ∈ Sb'.
Proof.
  intros * Hsubtyp Hglu Hglu'.
  gen ρ σ Δ. gen Sb' Sb.
  induction Hsubtyp; intros;
    invert_glu_ctx_env Hglu;
    invert_glu_ctx_env Hglu';
    handle_functional_glu_ctx_env;
    eauto.

  (** [Δ] is the refining context and [A'] its type; [Γ] and [A] are the ones
      being refined.  The three cases share the head and the tail; only a
      refined definition has a tie to move. *)
  (** A module slot keeps its unit: the tie is unchanged. *)
  4:{ destruct_by_head cons_mod_glu_sub_pred.
      econstructor; [ eapply ctxsub_sub_cod; [| eassumption ]; mauto 3 | eassumption |].
      eapply IHHsubtyp; eassumption. }
  all: rename i0 into j.
  all: rename i1 into k.
  all: rename TSb0 into TSb'.
  all: try destruct_by_head cons_glu_sub_pred.
  all: try destruct_by_head cons_def_glu_sub_pred.
  all: assert (glu_rel_typ_with_sub k Δ0 A (Wk ⨟ σ) ρ↯) as [] by intuition.
  all: rename a0 into a'.
  all: rename P0 into P'.
  all: rename El0 into El'.
  all: assert (exists tail_rel, EF Δ ≈ Δ ∈ per_ctx_env ↘ tail_rel) as [tail_rel Htail]
         by mauto 3 using glu_ctx_env_per_ctx_env.
  all: assert (Htl : Dom ρ↯ ≈ ρ↯ ∈ tail_rel) by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  1: assert (Hctx : Δ ▹ A' ⊆ Γ ▹ A) by mauto 3.
  2: assert (Hctx : Δ ▸ A' ≔ M' ⊆ Γ ▸ A ≔ M) by mauto 3.
  3: assert (Hctx : Δ ▸ A' ≔ M' ⊆ Γ ▹ A) by mauto 3.
  all: econstructor; mauto; intuition.
  all: assert (Δ ⊨ A' ⊆ A) as HAA' by mauto 3 using completeness_fundamental_subtyp.
  all: destruct (subtyp_under_ctx_simple HAA') as [env_relΔ [? [l Hsub]]].
  all: handle_per_ctx_env_irrel.
  all: (on_all_hyp_rev: destruct_rel_by_assumption tail_rel).
  all: destruct_conjs.
  all: functional_eval_rewrite_clear.
  all: try (eapply glu_univ_elem_per_subtyp_trm_conv;
            [ eassumption | eassumption | eassumption | rewrite exp_sub_shift; eassumption | eassumption ]).
  all: try (eapply ctxsub_sub_cod; [| eassumption ]; mauto 3).
  (** The tie of a refined definition moves along [M' ≈ M] and the element
      inclusion of [A' ⊆ A]. *)
  match goal with
  | Htie0 : def_tie A' M' ρ, HM : Δ ⊢ M' ≈ M : A, Ha : ⟦ A' ⟧ ρ↯ ↘ ?a,
    Hsa : Sub ?a <: ?a' at ?lv |- _ =>
      rename Htie0 into Hdt; rename HM into HMeq; rename Ha into HaA'; rename Hsa into Hs
  end.
  assert (HMM : Δ ⊨ M' ≈ M : A) by (apply completeness_fundamental_exp_eq; eassumption).
  pose proof (rel_exp_under_ctx_simple HMM) as [R0 [HR0 [k1 HMMs]]].
  assert (E0 : tail_rel <~> R0) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (HMMs _ _ (proj1 (E0 _ _) Htl)) as [b1 [b2 [RA [Hb1 [Hb2 [HRA [m1 [m [Hm1 [Hm HmRA]]]]]]]]]].
  destruct Hdt as [m' [Hm' Htie]].
  functional_eval_rewrite_clear.
  destruct (per_subtyp_to_univ_elem _ _ _ Hs) as [Ra [Ra' [HRa HRa']]].
  apply (Htie _ _ _ _ HaA' HaA') in HRa as Htie'.
  pose proof (per_elem_subtyping _ _ _ Hs _ _ _ _ HRa HRa' Htie') as Htie''.
  assert (E : Ra' <~> RA) by (eapply per_univ_elem_right_irrel; eassumption).
  apply E in Htie''.
  exists m; split; [ eassumption |].
  eapply per_head_of; [ eassumption | eassumption | exact HRA |].
  assert (PER RA) by (eapply per_elem_PER; eassumption).
  solve_per.
Qed.

(** Postcomposition by a Kripke weakening, [sb_wk], the operation Lemma 6.39
    uses on the semantic side. The head clause follows from
    [glu_univ_elem_exp_monotone] by a [rewrite], since [M[σ][φ]ʷ] and
    [M[(sb_wk σ φ)]] are the same expression ([exp_wk_sub]). Only the tail
    needs a judgmental step: the rearrangement it needs is an [sb_eq], which no
    gluing predicate respects. *)
Lemma glu_ctx_env_sub_monotone : forall Γ Sb,
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    forall Δ' φ Δ τ ρ,
      Δ ⊢s τ ® ρ ∈ Sb ->
      Δ' ⊢k φ : Δ ->
      Δ' ⊢s (sb_wk τ φ) ® ρ ∈ Sb.
Proof.
  induction 1; intros * HSb Hφ;
    apply_predicate_equivalence;
    simpl in *;
    saturate_kripke_escape.
  1: (rewrite sb_wk_compose; mauto 3).
  (** A module slot: [ρ] does not move, so the tie is unchanged. *)
  3:{ destruct_by_head cons_mod_glu_sub_pred.
      econstructor; [ rewrite sb_wk_compose; mauto 3 | eassumption |].
      assert (Δ' ⊢s (sb_wk (Wk ⨟ σ) φ) ® ρ↯ ∈ TSb) by mauto 3.
      assert (Δ' ⊢s (sb_wk (Wk ⨟ σ) φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
      eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | eassumption | ].
      eapply wf_sub_eq_of_sb_eq; [ eassumption | apply sb_wk_shift_pre ]. }

  (** An assumption entry and a definition entry alike: [ρ] does not move, so
      the tie is unchanged.  Each leaves the substitution, the head and the
      tail. *)
  all: try destruct_by_head cons_glu_sub_pred.
  all: try destruct_by_head cons_def_glu_sub_pred.
  all: econstructor; mauto 3.
  1,4: (rewrite sb_wk_compose; mauto 3).
  1,3: (rewrite <- !exp_wk_sub; eapply glu_univ_elem_exp_monotone; eassumption).
  all: assert (Δ' ⊢s (sb_wk (Wk ⨟ σ) φ) ® ρ↯ ∈ TSb) by mauto 3.
  all: assert (Δ' ⊢s (sb_wk (Wk ⨟ σ) φ) : Γ) by (rewrite sb_wk_compose; mauto 3).
  all: eapply glu_ctx_env_sub_resp_sub_eq; [ eassumption | eassumption | ].
  all: eapply wf_sub_eq_of_sb_eq; [ eassumption | apply sb_wk_shift_pre ].
Qed.

(** Extension by any entry whose term projection glues as the head. *)
Lemma cons_glu_sub_pred_helper_gen : forall {Γ Sb Δ σ ρ A a} {i : nat} {P El en c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    Γ ⊢ A : Type@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ sentry_exp en : A[σ] ® c ∈ El ->
    Δ ⊢s sb_extend σ en ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  assert (Δ ⊢ sentry_exp en : A[σ]) by mauto 2 using glu_univ_elem_trm_escape.
  assert (⊢ Γ ▹ A) by mauto 3.
  assert (Δ ⊢s sb_extend σ en : Γ ▹ A).
  { apply wf_sub_extend_gen; [ assumption | assumption | | |].
    - intros B Hlk; inversion Hlk; subst; rewrite exp_sub_shift_extend; assumption.
    - intros B L Hlk; inversion Hlk.
    - intros U Hlk; inversion Hlk. }
  econstructor; mauto 3.
  rewrite exp_sub_shift_extend; eassumption.
Qed.

Lemma cons_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ A a} {i : nat} {P El M c},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Δ ⊢s σ ® ρ ∈ Sb ->
    Γ ⊢ A : Type@i ->
    ⟦ A ⟧ ρ ↘ a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    Δ ⊢ M : A[σ] ® c ∈ El ->
    Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb.
Proof.
  intros.
  assert (Δ ⊢s σ : Γ) by mauto 2.
  assert (Δ ⊢ M : A[σ]) by mauto 2 using glu_univ_elem_trm_escape.
  assert (Δ ⊢s σ,,M : Γ ▹ A) by mauto 2.
  (** [#0[σ,,M]] is [M] and [Wk ⨟ (σ,,M)] is [σ], both by computation; only
      [A[↑]ʷ[σ,,M]] needs a rewrite. *)
  econstructor; mauto 3.
  rewrite exp_sub_shift_extend; eassumption.
Qed.

Hint Resolve cons_glu_sub_pred_helper : mctt.

Lemma initial_env_glu_rel_exp : forall {Γ ρ Sb},
    initial_env_f Γ ρ ->
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊢s Id ® ρ ∈ Sb.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence;
    try solve [econstructor; mauto | cbn; mauto 3].

  - assert (glu_rel_typ_with_sub i Γ A Id ρ) as [] by mauto.
    functional_eval_rewrite_clear.
    econstructor; mauto.
    (** The head is [var0_glu_elem] once the identity substitutions are gone. *)
    1: (rewrite !exp_sub_id in H5 |- *; eapply var0_glu_elem; eassumption).
    (** The tail is the induction hypothesis pushed along [↑]: [Wk ⨟ Id] and
        [sb_wk Id ↑] both send [x] to [#(S x)], so [eapply] converts them. *)
    assert (⊢ Γ ▹ A) by mauto 3.
    eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▹ A) wk_shift Γ Id ρ); mauto 3.
  - (** A definition: the head is [⟦M⟧ρ], glued with [M[↑]ʷ] by the gluing
        of [M] along [↑], hence with [#0] by δ. *)
    assert (⊢ Γ ▸ A ≔ M) by mauto 3.
    assert (HWk : Γ ▸ A ≔ M ⊢s Wk ® ρ ∈ TSb)
      by (eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▸ A ≔ M) wk_shift Γ Id ρ);
          [ apply IHHΓ; assumption | apply kripke_shift_def; assumption ]).
    assert (glu_rel_exp_with_sub i (Γ ▸ A ≔ M) M A Wk ρ) as [] by mauto.
    functional_eval_rewrite_clear.
    econstructor; [ mauto 3 | eassumption | eassumption | | | exact HWk ].
    + rewrite !exp_sub_id.
      match goal with Hg : El _ _ M[Wk] _ |- _ => rewrite !exp_sub_of_shift in Hg end.
      eapply glu_univ_elem_trm_resp_exp_eq; [ eassumption | eassumption |].
      apply wf_exp_eq_sym; eapply wf_exp_eq_var_delta; [ eassumption | constructor ].
    + exists m; split; [ eassumption |].
      match goal with Hg : El _ _ M[Wk] _, Hglu : glu_univ_elem _ _ _ _ |- _ =>
        destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [R HR];
        pose proof (glu_univ_elem_per_elem _ _ _ _ Hglu _ _ _ _ _ Hg HR) end.
      eapply per_head_of; [ eassumption | eassumption | exact HR | eassumption ].
  - (** A module slot: its closure is related to itself, by the unit's
        validity at the initial environment. *)
    assert (⊢ Γ ▹ₘ U) by mauto 3.
    assert (HId : Γ ⊢s Id ® ρ ∈ TSb) by (apply IHHΓ; assumption).
    assert (HWk : Γ ▹ₘ U ⊢s Wk ® ρ ∈ TSb)
      by (eapply (glu_ctx_env_sub_monotone _ _ H (Γ ▹ₘ U) wk_shift Γ Id ρ);
          [ exact HId | apply kripke_shift_mod; assumption ]).
    econstructor; [ mauto 3 | | exact HWk ].
    destruct (glu_ctx_env_per_ctx_env H) as [R HR].
    pose proof (glu_ctx_env_per_env H HR HId) as Hρ.
    match goal with Hu : wf_unit_eq _ _ _ _ _ |- _ =>
      destruct (proj1 (proj2 completeness_fundamental_modules) _ _ _ Hu) as (HU & _) end.
    exact (unit_chain_at HU HR _ _ Hρ).
Qed.

(** *** Tactics for [glu_rel_*] *)

End Fixed_GCtx.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mctt.
Ltac destruct_glu_rel_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : ?Δ ⊢s ?σ ® ?ρ ∈ ?sub_glu_rel0 |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        destruct (H _ _ _ H') as [];
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.
Ltac destruct_glu_rel_exp_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ ?sub_glu_rel -> glu_rel_exp_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, Δ ⊢s σ ® ρ ∈ ?sub_glu_rel -> glu_rel_typ_with_sub _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Section Fixed_GCtx.
  Context {GC : GCtx}.


(** *** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 : forall {Γ Sb M A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ M : A ->
    exists i,
    forall Δ σ ρ,
      Δ ⊢s σ ® ρ ∈ Sb ->
      glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? [].
  destruct_conjs.
  eexists; intros.
  handle_functional_glu_ctx_env.
  mauto.
Qed.

Definition glu_rel_exp_clean_inversion2_result i Sb M A :=
  forall Δ σ ρ,
    Δ ⊢s σ ® ρ ∈ Sb ->
    glu_rel_exp_with_sub i Δ M A σ ρ.

Lemma glu_rel_exp_clean_inversion2 : forall {i : nat} {Γ Sb M A},
    EG Γ ∈ glu_ctx_env ↘ Sb ->
    Γ ⊩ A : Type@i ->
    Γ ⊩ M : A ->
    glu_rel_exp_clean_inversion2_result i Sb M A.
Proof.
  unfold glu_rel_exp_clean_inversion2_result.
  intros * ? HA HM.
  eapply glu_rel_exp_clean_inversion1 in HA; [| eassumption].
  eapply glu_rel_exp_clean_inversion1 in HM; [| eassumption].
  destruct_conjs.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  econstructor; mauto 3.
  eapply glu_univ_elem_exp_conv; revgoals; mauto 3.
Qed.

End Fixed_GCtx.

Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Section Fixed_GCtx.
  Context {GC : GCtx}.


Lemma glu_rel_exp_to_wf_exp : forall {Γ A M},
    Γ ⊩ M : A ->
    Γ ⊢ M : A.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env_f Γ ρ /\ initial_env_f Γ ρ' /\ Dom ρ ≈ ρ' ∈ env_rel) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert (Γ ⊢s Id ® ρ ∈ Sb) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  assert (Γ ⊢ M[Id] : A[Id]) as HId by mauto 3 using glu_univ_elem_trm_escape.
  rewrite !exp_sub_id in HId; eassumption.
Qed.

Hint Resolve glu_rel_exp_to_wf_exp : mctt.

End Fixed_GCtx.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mctt.
