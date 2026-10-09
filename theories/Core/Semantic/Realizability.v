From Stdlib Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE PER.
Import Domain_Notations Fixed_Notations.


Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_nat_then_per_top : forall {n m},
    Dom n ≈ m ∈ per_nat ->
    Dom ⇓ ℕᵈ n ≈ ⇓ ℕᵈ m ∈ per_top.
Proof.
  induction 1; simpl in *; intros s;
    try specialize (IHper_nat s);
    try specialize (H s); solve [destruct_conjs; eexists; repeat econstructor; eauto].
Qed.

Hint Resolve per_nat_then_per_top : mctt.

Lemma realize_per_univ_elem_gen : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ
    /\ (forall {c c'}, Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R)
    /\ (forall {b b'}, Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  per_univ_elem_induction Hunivelem; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - subst.
    eexists.
    per_univ_elem_econstructor; (solve [try (try (eexists; split); econstructor); mauto]).
  - subst.
    destruct_by_head per_univ.
    specialize (H2 _ _ _ H0).
    destruct_conjs.
    intro s.
    specialize (H1 s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  (** The small universes.  They read back as the universe at the canonical
      form their level reads back as, which the two related levels share; the
      other two components are as in the large tier, with the elements at the
      index of the realiser. *)
  - intro s.
    destruct (H0 s) as [W [HW HW']].
    destruct (read_nf_level_real _ _ _ _ HW) as [L [-> _]].
    exists (nf_univ_of L); split; apply read_typ_suniv; assumption.
  - eexists.
    per_univ_elem_econstructor; (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct_by_head per_univ.
    match goal with H : per_univ_elem _ _ _ _ |- _ => specialize (H2 _ _ _ H) end.
    destruct_conjs.
    intro s.
    match goal with H : per_top_typ _ _ |- _ => specialize (H s) as [? []] end;
      (solve [try (try (eexists; split); econstructor); mauto]).
  (** The elements of a type of levels read back at every sort. *)
  - intro s.
    match goal with H : per_lvl_at _ _ _ |- _ => apply per_lvl_at_lvl in H; destruct (H s) as [L [HL HL']] end.
    exists L; split; eapply read_nf_level_sort; eassumption.
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct IHHunivelem as [? []].
    intro s.
    assert (Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S s)) as [? []].
    specialize (H2 s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough (Dom c $ᵈ ⇓ a c0 ≈ c' $ᵈ ⇓ a' c0' ∈ per_bot) by eauto.
    intro s.
    specialize (H3 s) as [? []].
    specialize (H5 _ _ equiv_c0_c0' s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct_conjs.
    intro s.
    assert (Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: ($| ?f0 & ⇑! a s |↘ _),
        _: ($| ?f0' & ⇑! a' s |↘ _),
          _: (⟦ B ⟧ ρ ↦ ⇑! a s ↘ ?b0),
            _: ⟦ B' ⟧ ρ' ↦ ⇑! a' s ↘ ?b0' |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert (Dom ⇓ b fa ≈ ⇓ b' f'a' ∈ per_top) by eauto.
    specialize (H2 s) as [? []].
    specialize (H16 (S s)) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
Qed.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

Hint Resolve per_univ_then_per_top_typ : mctt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

(** [per_bot_then_per_elem] is not a hint: its conclusion has the relation [R]
    in head position, so the pattern would be higher-order, and Rocq rejects
    it. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

Hint Resolve per_elem_then_per_top : mctt.

Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_rel ->
    exists ρ ρ', initial_env_f Γ ρ /\ initial_env_f Γ' ρ' /\ Dom ρ ≈ ρ' ∈ env_rel.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
  - (** A definition slot holds the value of the body. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with
    | Hbody : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_elem _ _ _ _ _ |- _ =>
        destruct (Hbody _ _ Hρ)
    end.
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    exists Hρ.
    solve_def_heads.
  - (** A slot holds the closure of its unit, which the premise relates to
        the other unit's. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> per_dmod _ _ |- _ =>
      destruct (mod_closure_move _ _ _ _ _ _ (ltac:(eassumption) : tail_rel ρ ρ) HU) as (M1 & M2 & M3 & M4);
      destruct (mod_closure_move _ _ _ _ _ _ (ltac:(eassumption) : tail_rel ρ' ρ') HU) as (M1' & M2' & M3' & M4')
    end.
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    repeat split; assumption.
Qed.

Lemma var_per_elem : forall {a b i R} n,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom ⇑! a n ≈ ⇑! b n ∈ R.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_nat_then_per_top : mctt.
#[export]
Hint Resolve per_univ_then_per_top_typ : mctt.
#[export]
Hint Resolve per_elem_then_per_top : mctt.
