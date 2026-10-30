(** * Instances of Judgments along Substitutions Built from Valid Parts

    A semantic substitution is closed under weakening but not, in general,
    under composition: the semantic judgments say nothing of the syntax a
    substitution is made of.  A substitution built from the identity by
    extensions with valid terms, definitions and unit literals is different:
    each of its parts commutes with any further substitution, so composing it
    with a semantic substitution gives a semantic substitution, whose values
    are related to those of the two applied in turn ([sub_link]).  This gives
    the instances of judgments along such substitutions. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma per_univ_elem_trans_any : forall i R a b j R' c,
    per_univ_elem i R a b -> per_univ_elem j R' b c -> exists R'', per_univ_elem i R'' a c /\ (R <~> R'').
Proof.
  intros * H1 H2.
  destruct (per_univ_trans' i j a b c (ex_intro (fun R0 => per_univ_elem i R0 a b) R H1) (ex_intro (fun R0 => per_univ_elem j R0 b c) R' H2)) as [R'' H3].
  exists R''; split; [ exact H3 | eapply per_univ_elem_right_irrel; eassumption ].
Qed.

Lemma rel_sub_under_ctx_sb_eq : forall {Γ Δ σ1 σ2 τ1 τ2},
    Γ ⊨ˢ σ1 ≈ σ2 : Δ -> sb_eq σ1 τ1 -> sb_eq σ2 τ2 -> Γ ⊨ˢ τ1 ≈ τ2 : Δ.
Proof.
  intros * [R HΓ RΔ HΔ Hσ] E1 E2.
  refine (mk_rel_sub_under_ctx _ _ _ _ R HΓ RΔ HΔ _).
  intros Γ' R' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [x1 x2 x3 x4 H1 H2 H3 H4 Hc].
  econstructor; [ | | | | exact Hc ].
  - rewrite <- (sb_wk_cong _ _ φ φ E1 (reflexivity _)); exact H1.
  - rewrite <- E1; exact H2.
  - rewrite <- E2; exact H3.
  - rewrite <- (sb_wk_cong _ _ φ φ E2 (reflexivity _)); exact H4.
Qed.

(** An evaluation of a substitution is one of any equal substitution. *)
Lemma eval_sub_sb_eq : forall {Δ σ τ ρ e}, sb_eq σ τ -> ⟦ σ : Δ ⟧s ρ ↘ e -> ⟦ τ : Δ ⟧s ρ ↘ e.
Proof. intros * E H; exact (proj1 (eval_sub_Proper _ _ _ E _ _ eq_refl _ _ (reflexivity _)) H). Qed.

(** An evaluation at an extended target gives one of the substitution's
    tail at the target's tail.  It reads the definition of an evaluation
    of a substitution. *)
#[local] Transparent eval_sub.
Lemma eval_sub_tail : forall e Δ σ τ ρ ρτ,
    (forall x, σ (S x) = τ x) -> ⟦ σ : e :: Δ ⟧s ρ ↘ ρτ -> ⟦ τ : Δ ⟧s ρ ↘ ρτ↯.
Proof.
  intros * Hs H x; rewrite env_entry_drop, <- Hs; split.
  - intros Hp; apply (H (S x)); exact (proj2 (entry_propositional_succ _ _ _ _) Hp).
  - intros Hn; apply (H (S x)); intros Hp; exact (Hn (proj1 (entry_propositional_succ _ _ _ _) Hp)).
Qed.

(** An evaluation at an extended target, from one of the tail and the
    head: the proof [⋆ᵈ] at a proposition, the head's value otherwise. *)
Lemma eval_sub_cons_intro : forall e Δ σ τ ρ d ρτ,
    (forall x, σ (S x) = τ x) ->
    ⟦ τ : Δ ⟧s ρ ↘ ρτ ->
    (head_propositional gc_deps gc_stack e ρτ -> d = de_term ⋆ᵈ) ->
    (~ head_propositional gc_deps gc_stack e ρτ -> ⟦ σ 0 ⟧ᵉ gc_deps ⍮ gc_stack ⍮ ρ ↘ d) ->
    ⟦ σ : e :: Δ ⟧s ρ ↘ d :: ρτ.
Proof.
  intros * Hs H Hp Hn [| x].
  - split; [ intros Hx; apply Hp; exact (proj1 (entry_propositional_head _ _ _ _) Hx)
           | intros Hx; apply Hn; intros Hy; exact (Hx (proj2 (entry_propositional_head _ _ _ _) Hy)) ].
  - rewrite Hs, env_entry_cons_succ; split.
    + intros Hx; apply (H x); exact (entry_propositional_extend_inv _ _ _ _ _ Hx).
    + intros Hx; apply (H x); intros Hy; exact (Hx (entry_propositional_extend_intro _ _ _ _ _ Hy)).
Qed.

(** An evaluation at an extended target is one at the same tail extended by
    another entry, when neither head is a proposition. *)
Lemma eval_sub_change_head : forall e e' Δ σ ρ ρτ,
    ⟦ σ : e :: Δ ⟧s ρ ↘ ρτ ->
    ~ head_propositional gc_deps gc_stack e ρτ↯ ->
    ~ head_propositional gc_deps gc_stack e' ρτ↯ ->
    ⟦ σ : e' :: Δ ⟧s ρ ↘ ρτ.
Proof.
  intros * H Hn Hn' [| x].
  - split; [ intros Hp; exfalso; apply Hn'; exact (proj1 (entry_propositional_zero_head _ _ _) Hp) |].
    intros _; apply (H 0); intros Hp; apply Hn; exact (proj1 (entry_propositional_zero_head _ _ _) Hp).
  - split.
    + intros Hp; apply (H (S x)); apply (proj2 (entry_propositional_succ _ _ _ _)); exact (proj1 (entry_propositional_succ _ _ _ _) Hp).
    + intros Hn0; apply (H (S x)); intros Hp; apply Hn0.
      apply (proj2 (entry_propositional_succ _ _ _ _)); exact (proj1 (entry_propositional_succ _ _ _ _) Hp).
Qed.
#[local] Opaque eval_sub.

(** [σ[φ]] after [τ] is [τ ⨟ σ] weakened by [φ]. *)
Lemma sb_compose_wk_right : forall τ σ φ, sb_eq (τ ⨟ sb_wk σ φ) (sb_wk (τ ⨟ σ) φ).
Proof. intros; rewrite !sb_wk_compose; symmetry; apply sb_compose_assoc. Qed.

(** ** Composition

    [τ ⨟ σ] evaluates, at an environment of [σ]'s domain, to an environment
    related to the value of [τ] at the value of [σ]. *)

Definition sub_link (Γ Δ : ctx) (τ : sub) : Prop :=
  forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    forall RΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ) ρ ρσ,
      R' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
      exists e1, ⟦ τ ⨟ σ : Δ ⟧s ρ ↘ e1 /\ forall e2, ⟦ τ : Δ ⟧s ρσ ↘ e2 -> RΔ e1 e2.

Lemma rel_sub_compose_of_link : forall {Γ Δ τ},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    forall Γ' σ σ', Γ' ⊨ˢ σ ≈ σ' : Γ -> Γ' ⊨ˢ τ ⨟ σ ≈ τ ⨟ σ' : Δ.
Proof.
  intros * Hτj Hl * Hσj.
  pose proof Hσj as [R' HΓ' RΓ HΓ Hσ].
  pose proof Hτj as [RΓ2 HΓ2 RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  refine (mk_rel_sub_under_ctx _ _ _ _ R' HΓ' RΔ HΔ _).
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  assert (HP'' : PER R'') by (eapply per_env_PER; exact HΓ'').
  pose proof (rel_sub_under_ctx_wk_rel Hσj HΓ'' HΓ' Hφ) as Hσφ.
  destruct (Hσ _ _ HΓ'' _ Hφ _ _ Hρ) as [s1 s2 s3 s4 Hs1 Hs2 Hs3 Hs4 Hsc].
  assert (Hρρ : R'' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R'' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρρ) as Hφρ.
  pose proof (rel_wk_app _ _ _ Hφ _ _ Hρ'ρ') as Hφρ'.
  destruct (Hl _ _ HΓ'' _ _ Hσφ _ HΔ _ _ Hρρ Hs1) as [e1 [He1 L1]].
  destruct (Hl _ _ HΓ' _ _ Hσj _ HΔ _ _ Hφρ Hs2) as [e2 [He2 L2]].
  destruct (Hl _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσj) _ HΔ _ _ Hφρ' Hs3) as [e3 [He3 L3]].
  destruct (Hl _ _ HΓ'' _ _ (rel_sub_under_ctx_sym Hσφ) _ HΔ _ _ Hρ'ρ' Hs4) as [e4 [He4 L4]].
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (H11 : RΓ s1 s1) by pairwise.
  assert (H22 : RΓ s2 s2) by pairwise.
  assert (H33 : RΓ s3 s3) by pairwise.
  assert (H44 : RΓ s4 s4) by pairwise.
  destruct (Hτs _ _ (proj1 (E3 _ _) H11)) as [t1 [_ [Ht1 [_ _]]]].
  destruct (Hτs _ _ (proj1 (E3 _ _) H22)) as [t2 [_ [Ht2 [_ _]]]].
  destruct (Hτs _ _ (proj1 (E3 _ _) H33)) as [t3 [_ [Ht3 [_ _]]]].
  destruct (Hτs _ _ (proj1 (E3 _ _) H44)) as [t4 [_ [Ht4 [_ _]]]].
  assert (T : forall a b x y, RΓ a b -> ⟦ τ : Δ ⟧s a ↘ x -> ⟦ τ : Δ ⟧s b ↘ y -> RΔ x y)
    by (intros; eapply (rel_sub_under_ctx_at' Hτj HΓ HΔ); eassumption).
  apply (mk_rel_sub e1 e2 e3 e4).
  - exact (eval_sub_sb_eq (sb_compose_wk_right _ _ _) He1).
  - exact He2.
  - exact He3.
  - exact (eval_sub_sb_eq (sb_compose_wk_right _ _ _) He4).
  - pose proof (L1 _ Ht1). pose proof (L2 _ Ht2). pose proof (L3 _ Ht3). pose proof (L4 _ Ht4).
    assert (RΔ t1 t2) by (eapply T; [ | exact Ht1 | exact Ht2 ]; pairwise).
    assert (RΔ t2 t3) by (eapply T; [ | exact Ht2 | exact Ht3 ]; pairwise).
    assert (RΔ t3 t4) by (eapply T; [ | exact Ht3 | exact Ht4 ]; pairwise).
    apply rel_chain_4.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
Qed.

Lemma sub_link_id : forall {Γ}, sub_link Γ Γ Id.
Proof.
  intros * Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  assert (Hρσ : RΔ ρσ ρσ) by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΔ); eassumption).
  exists ρσ; split; [ exact (eval_sub_sb_eq (symmetry (sb_compose_id_left _)) Hev) |].
  intros e2 He2.
  assert (Heq : env_eq e2 ρσ) by (eapply functional_eval_sub; [ exact He2 | apply eval_sub_id, (proj1 (per_ctx_env_proofs _ _ _ HΔ _ _ Hρσ)) ]).
  rewrite Heq; exact Hρσ.
Qed.

(** Extension by a term of the domain: its head commutes with [σ] since the
    term is valid, at a type that [τ] relates to the entry's own. *)
Lemma sub_link_ass : forall {Γ Δ τ B} {i : nat} {N},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ᵗ B ≈ B at i -> Γ ⊨ N : B[τ] ->
    sub_link Γ (Δ ▹ B) (τ ,, N).
Proof.
  intros * Hτj Hl HB HN Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_typ HΔ HB) as HΔB'.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  pose proof (rel_type_inversion HB) as [RΔ0 [HΔ0 HBgen]].
  pose proof (rel_type_inversion_simple HB) as [RΔ1 [HΔ1 HBs]].
  handle_per_ctx_env_irrel.
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  handle_per_ctx_env_irrel.
  destruct (Hτs _ _ Hρσ) as [t [_ [Ht [_ _]]]].
  pose proof (L _ Ht) as He1t.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  destruct (HBs _ _ He1t) as (b & bt & Hb & Hbt & [Rb Hbb]).
  destruct HN as [RΓ2 HΓ2 j HNgen].
  handle_per_ctx_env_irrel.
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev) as [R1 [Htyp Hexp]].
  pose proof (HBgen _ _ HΓ3 _ _ Hτj _ _ _ _ Hρσ Ht Ht) as [y1 y2 y3 y4 Hy1 Hy2 Hy3 Hy4 Hyc].
  pose proof Htyp as [x1 x2 x3 x4 Hx1 Hx2 Hx3 Hx4 Hxc].
  functional_eval_rewrite_clear.
  (** The values of [B] at [τ ⨟ σ] and of [B[τ]] along [σ] are linked, so
      they are of one sort. *)
  assert (Hxy : per_univ_elem j R1 x1 y1) by (destruct Hxc as [? _]; assumption).
  assert (Hybt : per_univ i y1 bt) by (destruct Hyc as [? _]; assumption).
  destruct Hybt as [Ryb Hyb].
  pose proof (per_univ_elem_relevance _ _ _ _ Hbb) as Er1.
  pose proof (per_univ_elem_relevance _ _ _ _ Hyb) as Er2.
  pose proof (per_univ_elem_relevance _ _ _ _ Hxy) as Er3.
  destruct (domain_relevance b) eqn:Erb.
  - (** A relevant head: the term's value. *)
    assert (Hn1 : ~ head_propositional gc_deps gc_stack (ce_ass B) e1)
      by (eapply (head_not_propositional (e := ce_ass B) HΔ3 eq_refl HBs He1e1 Hb Erb)).
    assert (Ery : domain_relevance y1 = relevant) by congruence.
    apply (rel_exp_or_prop_relevant Htyp (ex_intro _ y1 (conj Hy1 Ery))) in Hexp.
    destruct Hexp as [n1 n2 n3 n4 Hn1e Hn2e Hn3e Hn4e Hnc].
    functional_eval_rewrite_clear.
    exists (e1 ↦ n1); split.
    + apply (eval_sub_sb_eq (symmetry (sb_extend_compose _ _ _))); apply eval_sub_extend; assumption.
    + intros e2 He2.
      destruct (eval_sub_extend_inv _ _ _ _ _ _ He2) as [Ht2 Hh2].
      pose proof (L _ Ht2) as He12.
      assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact He12 | exact He12 ]).
      destruct (HBs _ _ He12) as (b1 & b2 & Hb1 & Hb2 & [R2 Hb12]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_relevance _ _ _ _ Hb12) as Er4.
      assert (Hn2 : ~ head_propositional gc_deps gc_stack (ce_ass B) e2↯)
        by (eapply (head_not_propositional (e := ce_ass B) HΔ3 eq_refl HBs He22 Hb2); congruence).
      assert (Hm2 : ⟦ N ⟧ ρσ ↘ e2 0) by (apply Hh2; rewrite entry_propositional_zero_head; exact Hn2).
      functional_eval_rewrite_clear.
      apply per_env_extend_intro.
      * exact He12.
      * hnf; intros k R0 a a' Ha Ha' HR0; cbn in Ha.
        functional_eval_rewrite_clear.
        pose proof (proj1 (per_univ_elem_sym _ _ _ _ Hxy)) as Hyx.
        pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR0 Hb12) as F1.
        pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hb12 Hbb) as F2.
        pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hbb Hyb) as F3.
        pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hyb Hyx) as F4.
        apply F1, F2, F3, F4.
        destruct Hnc as [? _]; assumption.
      * intros (a & Ea & Hp); cbn in Ea; functional_eval_rewrite_clear; congruence.
      * intros (a & Ea & Hp); functional_eval_rewrite_clear; congruence.
  - (** A propositional head: the proof, on both sides. *)
    assert (Hp1 : head_propositional gc_deps gc_stack (ce_ass B) e1)
      by (exact (proj2 (head_propositional_iff (e := ce_ass B) HΔ3 eq_refl HBs He1e1 Hb) Erb)).
    exists (e1 ↦ ⋆ᵈ); split.
    + apply (eval_sub_sb_eq (symmetry (sb_extend_compose _ _ _))); apply eval_sub_extend_proof; assumption.
    + intros e2 He2.
      destruct (eval_sub_extend_inv _ _ _ _ _ _ He2) as [Ht2 _].
      pose proof (L _ Ht2) as He12.
      assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact He12 | exact He12 ]).
      destruct (HBs _ _ He12) as (b1 & b2 & Hb1 & Hb2 & [R2 Hb12]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_relevance _ _ _ _ Hb12) as Er4.
      assert (Hp2 : entry_propositional gc_deps gc_stack (Δ ▹ B) e2 0)
        by (rewrite entry_propositional_zero_head;
            exact (proj2 (head_propositional_iff (e := ce_ass B) HΔ3 eq_refl HBs He22 Hb2) ltac:(congruence))).
      pose proof (eval_sub_at_prop _ _ _ _ _ He2 Hp2) as Ee2.
      assert (Ev2 : e2 0 = ⋆ᵈ) by (unfold env_var; rewrite Ee2; reflexivity).
      apply per_env_extend_intro.
      * exact He12.
      * rewrite Ev2; cbn; eapply per_head_proof; eassumption.
      * intros _; reflexivity.
      * intros _; rewrite Ee2, Ev2; reflexivity.
Qed.

(** A valid term along a substitution, read at the substitution's value. *)
Lemma rel_exp_comm_head : forall {Γ' Δ τ τ' R' B M},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨ˢ τ ≈ τ' : Δ -> Δ ⊨ M : B ->
    forall ρ e m, R' ρ ρ -> ⟦ τ : Δ ⟧s ρ ↘ e -> rel_typ_sort B e relevant -> ⟦ M[τ] ⟧ ρ ↘ m ->
      exists m', ⟦ M ⟧ e ↘ m' /\ per_head B B e e m m'.
Proof.
  intros * HΓ' Hτ HM * Hρ Hev Hr Hm.
  pose proof HM as [R0 HΔ0 j HMgen].
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hτ) _ _ _ _ Hρ Hev Hev) as [E [Htyp Hexp]].
  apply (rel_exp_or_prop_relevant Htyp Hr) in Hexp.
  destruct Htyp as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac].
  destruct Hexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc].
  functional_eval_rewrite_clear.
  exists m2; split; [ exact Hm2 |].
  destruct Hac as [_ [Ha22 _]].
  eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 |].
  destruct Hmc as [Hm12 _]; exact Hm12.
Qed.

(** Extension by a definition of the codomain, read along [τ]. *)
Lemma sub_link_def : forall {Γ Δ τ B} {i : nat} {M},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ B : Typeω@i -> Δ ⊨ M : B ->
    sub_link Γ (Δ ▸ B ≔ M) (τ ,, M[τ]).
Proof.
  intros * Hτj Hl HB HM Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_def HΔ HB HM) as HΔB'.
  assert (E : RΔB <~> per_env_extend_def B M RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  destruct (rel_exp_under_ctx_sub_simple HΓ' (rel_sub_under_ctx_refl_left Hτσ) HB HM _ _ Hρ)
    as [m1 [_ [Hm1 [_ _]]]].
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HB) as HS.
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [t [_ [Ht [_ _]]]].
  pose proof (L _ Ht) as He1t.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  (** The head is of a type of a universe, so no proposition. *)
  assert (Hnp : forall e, RΔ e e -> ~ head_propositional gc_deps gc_stack (ce_def B M) e).
  { intros e He; destruct (rel_exp_of_typ_relevant_at HΔ HB _ _ He) as (a & Ea & Ha).
    exact (head_not_propositional (e := ce_def B M) HΔ eq_refl HS He Ea Ha). }
  exists (e1 ↦ m1); split.
  - apply (eval_sub_sb_eq (symmetry (sb_extend_compose _ _ _))); apply eval_sub_extend;
      [ exact He1 | exact (Hnp _ He1e1) | rewrite exp_sub_sub; exact Hm1 ].
  - intros e2 He2.
    pose proof (He2 0) as [_ Hh2].
    destruct (eval_sub_extend_inv _ _ _ _ _ _ He2) as [Ht2 _].
    pose proof (L _ Ht2) as Ht'.
    assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact Ht' | exact Ht' ]).
    destruct Hh2 as [m2 [Hm2e Hm2]]; [ rewrite entry_propositional_zero_head; exact (Hnp _ He22) |].
    apply E.
    assert (Heq : env_eq e2 (e2↯ ↦ m2)) by (intros [| x]; [ exact Hm2e | destruct e2; reflexivity ]).
    rewrite Heq.
    pose proof (rel_exp_under_ctx_simple_at_rel HΔ HB HM) as HMs.
    assert (Hr1 : rel_typ_sort B e1 relevant) by exact (rel_exp_of_typ_relevant_at HΔ HB _ _ He1e1).
    assert (Hr2 : rel_typ_sort B e2↯ relevant) by exact (rel_exp_of_typ_relevant_at HΔ HB _ _ He22).
    destruct (rel_exp_comm_head HΓ' Hτσ HM _ _ _ Hρ He1 Hr1 Hm1) as [m1' [Hm1' H1]].
    destruct (rel_exp_comm_head HΓ (rel_sub_under_ctx_refl_left Hτj) HM _ _ _ Hρσ Ht2 Hr2 Hm2)
      as [m2' [Hm2' H2]].
    destruct (HMs _ _ Ht') as [n1 [n2 [Hn1 [Hn2 H12]]]].
    functional_eval_rewrite_clear.
    assert (Q1 : per_head B B e1 e1 <~> per_head B B e1 e2↯)
      by (eapply (per_head_of_typ_resp HΔ HB); apply rel_chain_4; assumption).
    assert (Q2 : per_head B B e2↯ e2↯ <~> per_head B B e1 e2↯)
      by (eapply (per_head_of_typ_resp HΔ HB); apply rel_chain_4; [ exact He22 | symmetry; exact Ht' | exact Ht' ]).
    destruct (HS _ _ Ht') as [a [a' [Ha [Ha' [Rh HRh]]]]].
    pose proof (per_head_iff Ha Ha' HRh) as Qh.
    assert (PER Rh) by (eapply per_elem_PER; exact HRh).
    apply Q1, Qh in H1. apply Q2, Qh in H2. apply Qh in H12.
    eapply per_env_extend_def_intro; [ exact HPΔ | exact HS | exact HMs | exact Ht' | | exact Hm1' | ].
    + apply Qh; etransitivity; [ exact H1 |]; etransitivity; [ exact H12 | symmetry; exact H2 ].
    + apply Qh; symmetry; exact H1.
Qed.

(** Extension by a definition of a proposition: the head is the proof on
    both sides, the body unevaluated. *)
Lemma sub_link_def_prop : forall {Γ Δ τ B M},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ B : Propₘ ->
    sub_link Γ (Δ ▸ B ≔ M) (τ ,, M[τ]).
Proof.
  intros * Hτj Hl HB Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_def_prop (M := M) HΔ HB) as HΔB'.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  pose proof (rel_exp_of_prop_inversion_simple_at HΔ HB) as HAp.
  pose proof (rel_type_inversion_simple (rel_type_of_prop 0 HB)) as [RΔ1 [HΔ1 HBs]].
  assert (E1 : RΔ <~> RΔ1) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HBs' : forall ρ ρ', RΔ ρ ρ' -> exists a a', ⟦ B ⟧ ρ ↘ a /\ ⟦ B ⟧ ρ' ↘ a' /\ per_univ 0 a a')
    by (intros ? ? H; apply E1 in H; exact (HBs _ _ H)).
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [t [_ [Ht [_ _]]]].
  pose proof (L _ Ht) as He1t.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  assert (Hprop : forall e, RΔ e e -> head_propositional gc_deps gc_stack (ce_def B M) e).
  { intros e He; destruct (HAp _ _ He) as (a & a' & Ha & Ha' & [Hr _ _]).
    exact (proj2 (head_propositional_iff (e := ce_def B M) HΔ eq_refl HBs' He Ha) Hr). }
  exists (e1 ↦ ⋆ᵈ); split.
  - apply (eval_sub_sb_eq (symmetry (sb_extend_compose _ _ _))); apply eval_sub_extend_proof;
      [ exact He1 | exact (Hprop _ He1e1) ].
  - intros e2 He2.
    destruct (eval_sub_extend_inv _ _ _ _ _ _ He2) as [Ht2 _].
    pose proof (L _ Ht2) as He12.
    assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact He12 | exact He12 ]).
    assert (Hp2 : entry_propositional gc_deps gc_stack (Δ ▸ B ≔ M) e2 0)
      by (rewrite entry_propositional_zero_head; exact (Hprop _ He22)).
    pose proof (eval_sub_at_prop _ _ _ _ _ He2 Hp2) as Ee2.
    assert (Ev2 : e2 0 = ⋆ᵈ) by (unfold env_var; rewrite Ee2; reflexivity).
    destruct (HAp _ _ He12) as (a & a' & Ha & Ha' & [Hr _ _]).
    apply E, per_env_extend_intro.
    + exact He12.
    + rewrite Ev2; cbn; eapply per_head_proof; eassumption.
    + intros _; reflexivity.
    + intros _; rewrite Ee2, Ev2; reflexivity.
Qed.

(** Extension by the literal of a unit of the codomain, read along [τ]. *)
Lemma sub_link_mod : forall {Γ Δ τ U},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    sub_link Γ (Δ ▹ₘ U) (τ ,,ₘ me_lit U[τ]ᵘ).
Proof.
  intros * Hτj Hl HU Γ' R' HΓ' σ σ' Hσ RΔU HΔU ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_mod HΔ HU) as HΔU'.
  assert (E : RΔU <~> env_ext_mod U U RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  destruct (unit_sub_chain HΓ' (rel_sub_under_ctx_refl_left Hτσ) HU _ _ _ _ Hρ He1 He1)
    as ([g1 g2 Hg1 Hg2 G12] & _).
  exists (e1 ↦ᵐ g1); split.
  - apply (eval_sub_sb_eq (symmetry (sb_extend_compose_gen _ _ _))); apply eval_sub_extend_mod; [ exact He1 |].
    cbn [sentry_sub modexp_sub]; rewrite gunit_sub_sub; exact Hg1.
  - intros e2 He2.
    destruct (eval_sub_extend_mod_inv _ _ _ _ _ _ He2) as [Ht2 [h2 [Hh2e Hh2]]].
    apply E.
    pose proof (L _ Ht2) as Ht.
    assert (Heq : env_eq e2 (e2↯ ↦ᵐ h2))
      by (intros [| x]; [ exact Hh2e | destruct e2; reflexivity ]).
    rewrite Heq.
    destruct (unit_sub_chain HΓ (rel_sub_under_ctx_refl_left Hτj) HU _ _ _ _ Hρσ Ht2 Ht2)
      as ([k1 k2 Hk1 Hk2 K12] & _).
    pose proof (functional_eval_modexp _ _ _ _ Hh2 Hk1) as <-.
    cbn [drop_env tl env_mod env_entry hd]; repeat split;
      solve [ assumption | eexists; split; eassumption ].
Qed.

(** Extension by a definition with a module part of the codomain, read
    along [τ]: its term as a definition's, its unit as a slot's. *)
Lemma sub_link_dm : forall {Γ Δ τ B} {i : nat} {M U},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ B : Typeω@i -> Δ ⊨ M : B -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    sub_link Γ (Δ ▸ₘ B ≔ M ‖ U) (τ ,,ᵈ M[τ] ‖ me_lit U[τ]ᵘ).
Proof.
  intros * Hτj Hl HB HM HU Γ' R' HΓ' σ σ' Hσ RΔd HΔd ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (E : RΔd <~> per_env_extend_dm B M U RΔ)
    by (eapply per_ctx_env_right_irrel; [ exact HΔd | exact (per_ctx_env_of_dm HΔ HB HM HU) ]).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HB) as HS.
  (** The term part is of a type of a universe, so no proposition. *)
  assert (Hnp : forall e e', RΔ e e -> ctx_entry_type (e' :: nil) 0 = Some B -> ~ head_propositional gc_deps gc_stack e' e).
  { intros e e' He He'; destruct (rel_exp_of_typ_relevant_at HΔ HB _ _ He) as (a & Ea & Ha).
    exact (head_not_propositional HΔ He' HS He Ea Ha). }
  destruct (sub_link_def Hτj Hl HB HM _ _ HΓ' _ _ Hσ _ (per_ctx_env_of_def HΔ HB HM) _ _ Hρ Hev) as [ed [Hed Ld]].
  destruct (sub_link_mod Hτj Hl HU _ _ HΓ' _ _ Hσ _ (per_ctx_env_of_mod HΔ HU) _ _ Hρ Hev) as [em [Hem Lm]].
  destruct (eval_sub_extend_inv _ _ _ _ _ _ (eval_sub_sb_eq (sb_extend_compose _ _ _) Hed)) as [Hedt _].
  destruct (eval_sub_extend_mod_inv _ _ _ _ _ _ (eval_sub_sb_eq (sb_extend_compose_gen _ _ _) Hem)) as [Hemt _].
  assert (Q1 : env_eq em↯ ed↯) by (eapply functional_eval_sub; eassumption).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [t [_ [Ht [_ _]]]].
  pose proof (L _ Ht) as He1t.
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  assert (Hedd : RΔ ed↯ ed↯).
  { assert (Q : env_eq ed↯ e1) by (eapply functional_eval_sub; eassumption).
    eapply (per_ctx_env_resp_env_eq HΔ); [ symmetry; exact Q | symmetry; exact Q | exact He1e1 ]. }
  exists (de_dm (ed 0) (env_mod em 0) :: ed↯); split.
  - eapply eval_sub_dm_combine; [ exact Hed | exact Hem | intros; reflexivity | reflexivity | reflexivity | reflexivity
                                | exact (Hnp _ (ce_def B M) Hedd eq_refl) | exact (Hnp _ (ce_dm B M U) Hedd eq_refl) ].
  - intros e2 He2.
    pose proof (eval_sub_tail _ _ _ τ _ _ (fun _ => eq_refl) He2) as Ht2.
    pose proof (L _ Ht2) as He12.
    assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact He12 | exact He12 ]).
    destruct (eval_sub_dm_split (ce_def B M) U (ce_dm B M U) Δ (τ ,, M[τ]) (τ ,,ₘ me_lit U[τ]ᵘ) _ _ _ _ _ He2
                (fun _ => eq_refl) (fun _ => eq_refl) eq_refl eq_refl eq_refl
                (Hnp _ (ce_dm B M U) He22 eq_refl) (Hnp _ (ce_def B M) He22 eq_refl)) as (Hd2 & Hm2 & Q2).
    pose proof (Ld _ Hd2) as Dd; pose proof (Lm _ Hm2) as Dm.
    apply E.
    assert (Hc : per_env_extend_dm B M U RΔ (de_dm (ed 0) (env_mod em 0) :: ed↯)
                   (de_dm (e2 0) (env_mod e2 0) :: e2↯))
      by (exact (per_env_extend_dm_combine HΔ HU Dd Dm Q1 (fun _ => eq_refl))).
    eapply (per_ctx_env_resp_env_eq (per_ctx_env_of_dm HΔ HB HM HU)); [ reflexivity | symmetry; exact Q2 | exact Hc ].
Qed.

Lemma sub_link_sb_eq : forall {Γ Δ τ τ'}, sb_eq τ τ' -> sub_link Γ Δ τ -> sub_link Γ Δ τ'.
Proof.
  intros * Eq Hl Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  exists e1; split.
  - assert (E2 : sb_eq (τ ⨟ σ) (τ' ⨟ σ)) by (intros x; cbn; rewrite (Eq x); reflexivity).
    exact (eval_sub_sb_eq E2 He1).
  - intros e2 He2; apply L; exact (eval_sub_sb_eq (symmetry Eq) He2).
Qed.

(** A composite of substitutions that each commute with further ones
    commutes with further ones. *)
Lemma sub_link_comp : forall {Γ0 Δ τ Γ σ0},
    Γ0 ⊨ˢ τ ≈ τ : Δ -> sub_link Γ0 Δ τ ->
    Γ ⊨ˢ σ0 ≈ σ0 : Γ0 -> sub_link Γ Γ0 σ0 ->
    sub_link Γ Δ (τ ⨟ σ0).
Proof.
  intros * Hτj Hl Hσ0j Hl0 Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ0 HΓ0 RΔ0 HΔ0 _].
  pose proof Hσ0j as [RΓ HΓ RΓ0' HΓ0' _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ0 : PER RΓ0) by (eapply per_env_PER; exact HΓ0).
  pose proof (rel_sub_compose_of_link Hσ0j Hl0 _ _ _ Hσ) as Hσ1.
  destruct (Hl0 _ _ HΓ' _ _ Hσ _ HΓ0 _ _ Hρ Hev) as [f1 [Hf1 Lf]].
  destruct (Hl _ _ HΓ' _ _ Hσ1 _ HΔ _ _ Hρ Hf1) as [e1 [He1 L1]].
  exists e1; split; [ exact (eval_sub_sb_eq (symmetry (sb_compose_assoc _ _ _)) He1) |].
  intros e2 He2.
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  pose proof (rel_sub_under_ctx_simple Hσ0j) as [RΓ3 [HΓ3 [RΓ03 [HΓ03 Hσ0s]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hσ0s _ _ (proj1 (E3 _ _) Hρσ)) as [ρσ0 [_ [Hρσ0 [_ _]]]].
  destruct (Hl _ _ HΓ _ _ Hσ0j _ HΔ _ _ Hρσ Hρσ0) as [g1 [Hg1 Lg]].
  assert (Heq : env_eq e2 g1) by (eapply functional_eval_sub; eassumption).
  rewrite Heq.
  pose proof (Lf _ Hρσ0) as Hff.
  assert (Hf11 : RΓ0 f1 f1) by (etransitivity; [ exact Hff | symmetry; exact Hff ]).
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ4 [HΓ4 [RΔ4 [HΔ4 Hτs]]]].
  assert (E4 : RΓ0 <~> RΓ4) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E4 _ _) Hff)) as [t1 [t2 [Ht1 [Ht2 _]]]].
  pose proof (L1 _ Ht1) as H1. pose proof (Lg _ Ht2) as H2.
  assert (H12 : RΔ t1 t2) by exact (rel_sub_under_ctx_at' Hτj HΓ0 HΔ _ _ _ _ Hff Ht1 Ht2).
  etransitivity; [ exact H1 |]; etransitivity; [ exact H12 | symmetry; exact H2 ].
Qed.

(** A weakening commutes with any further substitution, on the nose. *)
Lemma sub_link_wk : forall {Γ ψ Δ}, Γ ⊨ʷ ψ : Δ -> sub_link Γ Δ (sb_of_wk ψ).
Proof.
  intros * Hψj Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  pose proof Hψj as [RΓ HΓ RΔ0 HΔ0 [Hψm Hψ] _].
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  assert (E : RΔ0 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  exists (⟪ψ⟫ ρσ); split.
  - exact (eval_sub_wk_pre_rel Hψj _ HΓ Hρσ Hev).
  - intros e2 He2.
    assert (Heq : env_eq e2 (⟪ψ⟫ ρσ)) by (eapply functional_eval_sub; [ exact He2 | exact (eval_sub_of_wk_rel (Hφ := Hψm) HΔ0 (Hψ _ _ Hρσ)) ]).
    rewrite Heq.
    apply E, Hψ, Hρσ.
Qed.

(** A lifted substitution commutes with further ones: its tail as [τ] does
    along the shift, and its head is the variable itself. *)
Lemma sub_link_q : forall {Γ Δ τ B} {i : nat},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ᵗ B ≈ B at i ->
    sub_link (Γ ▹ B[τ]) (Δ ▹ B) (q τ).
Proof.
  intros * Hτj Hl HB Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  pose proof (per_ctx_env_of_typ_sub HΓ Hτj HB) as HΓB.
  pose proof (per_ctx_env_of_typ HΔ HB) as HΔB'.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hwk : (Γ ▹ B[τ]) ⊨ʷ wk_shift : Γ)
    by (eapply rel_wk_under_ctx_intro; [ exact HΓB | exact HΓ | eapply rel_wk_shift; eassumption
                                       | intros ? ? _ x; apply entry_propositional_shift_wk ]).
  pose proof (rel_sub_of_wk Hwk) as HWk.
  pose proof (sub_link_wk Hwk) as HlW.
  pose proof (rel_sub_compose_of_link HWk HlW _ _ _ Hσ) as Hσw.
  assert (Hρσ : per_env_extend B[τ] B[τ] RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓB); eassumption).
  pose proof Hρσ as [Hρσt Hρσh Hρσl _].
  assert (Hevw : ⟦ (sb_of_wk wk_shift) ⨟ σ : Γ ⟧s ρ ↘ ρσ↯) by (eapply eval_sub_tail; [ intros x; reflexivity | exact Hev ]).
  destruct (Hl _ _ HΓ' _ _ Hσw _ HΔ _ _ Hρ Hevw) as [e1 [He1 L1]].
  pose proof (rel_type_inversion HB) as [RΔ0 [HΔ0 HBgen]].
  pose proof (rel_type_inversion_simple HB) as [RΔ1 [HΔ1 HBs]].
  assert (E0 : RΔ <~> RΔ1) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HBs' : forall ρ ρ', RΔ ρ ρ' -> exists a a', ⟦ B ⟧ ρ ↘ a /\ ⟦ B ⟧ ρ' ↘ a' /\ per_univ i a a')
    by (intros ? ? H; apply E0 in H; exact (HBs _ _ H)).
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E4 : RΔ3 <~> RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  (** [B[τ]] at the environments of [Γ], read through [τ]. *)
  assert (HBτ : forall ρ ρ', RΓ ρ ρ' -> exists a a', ⟦ B[τ] ⟧ ρ ↘ a /\ ⟦ B[τ] ⟧ ρ' ↘ a' /\ per_univ i a a').
  { intros r r' Hr.
    destruct (Hτs _ _ (proj1 (E3 _ _) Hr)) as [u [u' [Hu [Hu' _]]]].
    destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hr Hu Hu') as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hc].
    exists a1, a4; repeat split; [ exact Ha1 | exact Ha4 |].
    pairwise. }
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσt)) as [t [_ [Ht [_ _]]]].
  pose proof (L1 _ Ht) as He1t.
  assert (He1e1 : RΔ e1 e1) by (etransitivity; [ exact He1t | symmetry; exact He1t ]).
  destruct (HBs' _ _ He1t) as (b & bt & Hb & Hbt & Hbbt).
  destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσt Ht Ht) as [x1 c x3 x4 Hx1 Hc Hx3 Hx4 Hxc].
  functional_eval_rewrite_clear.
  assert (Hxb : per_univ i x1 b) by (destruct Hxc as (H12 & _); etransitivity; [ exact H12 | symmetry; exact Hbbt ]).
  destruct Hxb as [Rxb Hxb].
  pose proof (per_univ_elem_relevance _ _ _ _ Hxb) as Erx.
  (** The head is a proposition on one side exactly when on the other. *)
  assert (Iσ : entry_propositional gc_deps gc_stack (Γ ▹ B[τ]) ρσ 0 <-> domain_relevance b = propositional)
    by (rewrite entry_propositional_zero_head, (head_propositional_iff (e := ce_ass B[τ]) HΓ eq_refl HBτ Hρσt Hx1), Erx; reflexivity).
  assert (I1 : head_propositional gc_deps gc_stack (ce_ass B) e1 <-> domain_relevance b = propositional)
    by exact (head_propositional_iff (e := ce_ass B) HΔ eq_refl HBs' He1e1 Hb).
  exists (env_entry ρσ 0 :: e1); split.
  - eapply eval_sub_cons_intro with (τ := τ ⨟ (sb_of_wk wk_shift ⨟ σ)); [ | exact He1 | |].
    + intros x; unfold sb_q, sb_extend, sb_wk; cbn; rewrite sentry_sub_wk; reflexivity.
    + intros Hp; apply I1, Iσ in Hp; exact (eval_sub_at_prop _ _ _ _ _ Hev Hp).
    + intros Hn; unfold sb_q, sb_extend; cbn.
      apply (eval_sub_index _ _ _ _ Hev); intros Hp; apply Hn, I1, Iσ, Hp.
  - intros e2 He2.
    destruct (eval_sub_q_inv _ _ _ _ _ He2) as [Ht2 Hh2].
    pose proof (proj1 (eval_sub_shift_rel HΓB Hρσ)) as HevW.
    destruct (Hl _ _ HΓB _ _ HWk _ HΔ _ _ Hρσ HevW) as [g1 [Hg1 Lg]].
    assert (Heq : env_eq e2↯ g1) by (eapply functional_eval_sub; [ exact (eval_sub_sb_eq (sb_wk_compose _ _) Ht2) | exact Hg1 ]).
    assert (H12 : RΔ e1 e2↯).
    { pose proof (L1 _ Ht) as H1. pose proof (Lg _ Ht) as H2.
      eapply (per_ctx_env_resp_env_eq HΔ); [ reflexivity | symmetry; exact Heq |].
      etransitivity; [ exact H1 | symmetry; exact H2 ]. }
    assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact H12 | exact H12 ]).
    destruct (HBs' _ _ H12) as (b1 & b2 & Hb1 & Hb2 & [Rb12 Hb12]).
    functional_eval_rewrite_clear.
    pose proof (per_univ_elem_relevance _ _ _ _ Hb12) as Erb2.
    assert (I2 : entry_propositional gc_deps gc_stack (Δ ▹ B) e2 0 <-> domain_relevance b = propositional)
      by (rewrite entry_propositional_zero_head, (head_propositional_iff (e := ce_ass B) HΔ eq_refl HBs' He22 Hb2), Erb2; reflexivity).
    apply E; apply per_env_extend_intro.
    + exact H12.
    + destruct (domain_relevance b) eqn:Erb.
      * (** A relevant head: the variable, moved along the type's values. *)
        assert (Hn2 : ~ entry_propositional gc_deps gc_stack (Δ ▹ B) e2 0) by (rewrite I2; discriminate).
        assert (Ev : e2 0 = ρσ 0) by (unfold env_var; rewrite (Hh2 Hn2); reflexivity).
        rewrite Ev.
        destruct Hxc as (Hxx' & _).
        assert (Hxx : per_univ i x1 x1) by (etransitivity; [ exact Hxx' | symmetry; exact Hxx' ]).
        destruct Hxx as [Rx Hxx].
        unfold env_var at 1; cbn [env_entry List.nth_default List.nth].
        eapply per_head_bridge; [ exact Hρσh | exact Hx1 | exact Hx1 | exact Hxx | exact Hb | exact Hb2 | exists Rxb; exact Hxb ].
      * (** A propositional head: the proof on both sides. *)
        assert (Hp2 : entry_propositional gc_deps gc_stack (Δ ▹ B) e2 0) by (rewrite I2; reflexivity).
        assert (Ev : e2 0 = ⋆ᵈ) by (unfold env_var; rewrite (eval_sub_at_prop _ _ _ _ _ He2 Hp2); reflexivity).
        assert (Ehd : env_entry ρσ 0 = de_term ⋆ᵈ) by (apply (eval_sub_at_prop _ _ _ _ _ Hev), Iσ; reflexivity).
        rewrite Ehd, Ev; cbn.
        eapply per_head_proof; eassumption.
    + intros (a & Ea & Hp); cbn in Ea; functional_eval_rewrite_clear.
      assert (Ehd : env_entry ρσ 0 = de_term ⋆ᵈ) by (apply (eval_sub_at_prop _ _ _ _ _ Hev), Iσ; exact Hp).
      rewrite Ehd; reflexivity.
    + intros (a & Ea & Hp); functional_eval_rewrite_clear.
      assert (Hp2 : entry_propositional gc_deps gc_stack (Δ ▹ B) e2 0) by (rewrite I2; congruence).
      unfold env_var; rewrite (eval_sub_at_prop _ _ _ _ _ He2 Hp2); reflexivity.
Qed.

(** A lifted substitution into a definition: as for an assumption, and the
    head is tied to the definition's body, which [τ] relates to its own. *)
(** The environments the context PER of a definition entry relates are
    related at the assumption entry of its type: the tails and heads are,
    and a head at a proposition is the proof, a term. *)
Lemma per_ctx_env_def_as_ass : forall {Γ A M R RΓ},
    EF Γ ▸ A ≔ M ≈ Γ ▸ A ≔ M ∈ per_ctx_env ↘ R ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ ρ', Dom ρ ≈ ρ' ∈ R -> Dom ρ ≈ ρ' ∈ per_env_extend A A RΓ.
Proof.
  intros * HR HΓ ρ ρ' Hρ.
  destruct (per_ctx_env_head_split (e := ce_def A M) eq_refl HR) as [T [HT Hs]].
  assert (E : T <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ Hρ) as [Ht Hh].
  destruct (per_ctx_env_proofs _ _ _ HR _ _ Hρ) as [Pl Pr].
  apply per_env_extend_intro; [ apply E, Ht | exact Hh | intros (a & Ea & Hp) | intros (a & Ea & Hp) ].
  - assert (E0 : env_entry ρ 0 = de_term ⋆ᵈ)
      by (apply Pl; eapply mk_entry_propositional with (entry_propositional_env := ρ↯);
          [ reflexivity | intros y; rewrite ?skipn_one_drop; reflexivity | exact Ea | exact Hp ]).
    unfold env_var; rewrite E0; reflexivity.
  - assert (E0 : env_entry ρ' 0 = de_term ⋆ᵈ)
      by (apply Pr; eapply mk_entry_propositional with (entry_propositional_env := ρ'↯);
          [ reflexivity | intros y; rewrite ?skipn_one_drop; reflexivity | exact Ea | exact Hp ]).
    unfold env_var; rewrite E0; reflexivity.
Qed.

Lemma sub_link_q_def : forall {Γ Δ τ B} {i : nat} {M},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ B : Typeω@i -> Δ ⊨ M : B ->
    sub_link (Γ ▸ B[τ] ≔ M[τ]) (Δ ▸ B ≔ M) (q τ).
Proof.
  intros * Hτj Hl HB HM Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  pose proof (rel_type_of_typ HB) as HBt.
  pose proof (per_ctx_env_of_def_sub HΓ Hτj HB HM) as HΓBd.
  pose proof (per_ctx_env_of_typ_sub HΓ Hτj HBt) as HΓB.
  pose proof (per_ctx_env_of_typ HΔ HBt) as HΔBa.
  pose proof (per_ctx_env_of_def HΔ HB HM) as HΔBd.
  (** A definition entry has its type's entry type. *)
  assert (Tys : forall A N Θ0 x, ctx_entry_type (ce_def A N :: Θ0) x = ctx_entry_type (ce_ass A :: Θ0) x)
    by (intros ? ? ? []; reflexivity).
  assert (Hσa : Γ' ⊨ˢ σ ≈ σ' : Γ ▹ B[τ])
    by (eapply (rel_sub_under_ctx_restrict HΓ' HΓ' HΓBd HΓB);
        [ tauto | intros ? ? [? _]; assumption | apply ctx_props_incl_same_types; apply Tys | exact Hσ ]).
  pose proof (eval_sub_same_types (Tys _ _ _) Hev) as Hev'.
  destruct (sub_link_q Hτj Hl HBt _ _ HΓ' _ _ Hσa _ HΔBa _ _ Hρ Hev') as [e1 [He1 L]].
  exists e1; split; [ exact (eval_sub_same_types (fun x => eq_sym (Tys _ _ _ x)) He1) |].
  intros e2 He2.
  assert (E : RΔB <~> per_env_extend_def B M RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E.
  pose proof (L _ (eval_sub_same_types (Tys _ _ _) He2)) as H12.
  assert (Hρσ : per_env_extend_def B[τ] M[τ] RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓBd); eassumption).
  pose proof Hρσ as [[Hρσt _ _ _] [m0 [Hm0 Htie0]] _].
  (** The tail of [e2] is [τ] at the tail of [ρσ], up to [RΔ]; its head is [ρσ]'s. *)
  assert (Hwk : (Γ ▸ B[τ] ≔ M[τ]) ⊨ʷ wk_shift : Γ)
    by (eapply rel_wk_under_ctx_intro; [ exact HΓBd | exact HΓ | eapply rel_wk_shift; eassumption
                                       | intros ? ? _ x; apply entry_propositional_shift_wk ]).
  pose proof (rel_sub_of_wk Hwk) as HWk.
  destruct (eval_sub_q_inv _ _ _ _ _ He2) as [Ht2 Hh2].
  pose proof (proj1 (eval_sub_shift_rel HΓBd Hρσ)) as HevW.
  destruct (Hl _ _ HΓBd _ _ HWk _ HΔ _ _ Hρσ HevW) as [g1 [Hg1 Lg]].
  assert (Heq : env_eq e2↯ g1) by (eapply functional_eval_sub; [ exact (eval_sub_sb_eq (sb_wk_compose _ _) Ht2) | exact Hg1 ]).
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσt)) as [t [_ [Ht [_ _]]]].
  assert (Hte : RΔ e2↯ t) by (eapply (per_ctx_env_resp_env_eq HΔ); [ symmetry; exact Heq | reflexivity | exact (Lg _ Ht) ]).
  assert (Htt : RΔ t t) by (etransitivity; [ symmetry; exact Hte | exact Hte ]).
  assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ exact Hte | symmetry; exact Hte ]).
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HB) as HS.
  assert (Hn2 : ~ entry_propositional gc_deps gc_stack (Δ ▸ B ≔ M) e2 0).
  { rewrite entry_propositional_zero_head; destruct (rel_exp_of_typ_relevant_at HΔ HB _ _ He22) as (a & Ea & Ha).
    exact (head_not_propositional (e := ce_def B M) HΔ eq_refl HS He22 Ea Ha). }
  pose proof (Hh2 Hn2) as Hh.
  destruct (rel_exp_comm_head HΓ (rel_sub_under_ctx_refl_left Hτj) HM _ _ _ Hρσt Ht (rel_exp_of_typ_relevant_at HΔ HB _ _ Htt) Hm0)
    as [mt [Hmt Hhd]].
  pose proof (rel_exp_under_ctx_simple_at_rel HΔ HB HM) as HMs.
  destruct (HMs _ _ Hte) as [m2 [mt' [Hm2 [Hmt' Hm2t]]]].
  functional_eval_rewrite_clear.
  destruct (HS _ _ Hte) as [a2 [a [Ha2 [Ha [Ra HRa]]]]].
  pose proof (rel_type_inversion HBt) as [R0 [HΔ0 HBgen]].
  destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσt Ht Ht) as [b1 c x3 x4 Hb1 Hc Hx3 Hx4 [[Rb Hbc] _]].
  functional_eval_rewrite_clear.
  assert (HPa : PER Ra) by (eapply per_elem_PER; exact HRa).
  assert (Ebc : Rb <~> Ra) by (eapply per_univ_elem_left_irrel; [ exact Hbc | exact HRa ]).
  assert (Hbb : per_univ_elem i Rb b1 b1) by (etransitivity; [ exact Hbc | symmetry; exact Hbc ]).
  assert (Haa : per_univ_elem i Ra a a) by (etransitivity; [ symmetry; exact HRa | exact HRa ]).
  assert (Ha22 : per_univ_elem i Ra a2 a2) by (etransitivity; [ exact HRa | symmetry; exact HRa ]).
  pose proof (Htie0 _ _ _ _ Hb1 Hb1 Hbb) as T0.
  pose proof (Hhd _ _ _ _ Ha Ha Haa) as T1.
  pose proof (Hm2t _ _ _ _ Ha2 Ha HRa) as T2.
  apply Ebc in T0.
  assert (Htie2 : def_tie B M e2).
  { exists m2; split; [ exact Hm2 |].
    eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 |].
    replace (e2 0) with (ρσ 0) by (unfold env_var; rewrite Hh; reflexivity).
    etransitivity; [ exact T2 |]; etransitivity; [ symmetry; exact T1 | exact T0 ]. }
  constructor; [ exact H12 | | exact Htie2 ].
  eapply def_tie_resp; [ exact HPΔ | exact HS | exact HMs | symmetry; exact H12 | exact Htie2 ].
Qed.

(** A lifted substitution into a definition of a proposition: as for an
    assumption, the two entries having one context PER. *)
Lemma sub_link_q_def_prop : forall {Γ Δ τ B M},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ B : Propₘ ->
    sub_link (Γ ▸ B[τ] ≔ M[τ]) (Δ ▸ B ≔ M) (q τ).
Proof.
  intros * Hτj Hl HB Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (rel_type_of_prop 0 HB) as HBt.
  pose proof (per_ctx_env_of_typ_sub HΓ Hτj HBt) as HΓB.
  pose proof (per_ctx_env_of_typ HΔ HBt) as HΔBa.
  pose proof (per_ctx_env_of_def_prop (M := M) HΔ HB) as HΔBd.
  assert (Tys : forall A N Θ0 x, ctx_entry_type (ce_def A N :: Θ0) x = ctx_entry_type (ce_ass A :: Θ0) x)
    by (intros ? ? ? []; reflexivity).
  pose proof Hσ as [_ _ RΓd HΓd _].
  assert (Hσa : Γ' ⊨ˢ σ ≈ σ' : Γ ▹ B[τ])
    by (eapply (rel_sub_under_ctx_restrict HΓ' HΓ' HΓd HΓB);
        [ tauto | exact (per_ctx_env_def_as_ass HΓd HΓ) | apply ctx_props_incl_same_types; apply Tys | exact Hσ ]).
  pose proof (eval_sub_same_types (Tys _ _ _) Hev) as Hev'.
  destruct (sub_link_q Hτj Hl HBt _ _ HΓ' _ _ Hσa _ HΔBa _ _ Hρ Hev') as [e1 [He1 L]].
  exists e1; split; [ exact (eval_sub_same_types (fun x => eq_sym (Tys _ _ _ x)) He1) |].
  intros e2 He2.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  apply E, L, (eval_sub_same_types (Tys _ _ _) He2).
Qed.

(** A lifted substitution into a slot: as for an assumption, and the head
    is related to the closure of the unit along [τ], which the validity of
    the unit relates to its closure over the tail. *)
Lemma sub_link_q_mod : forall {Γ Δ τ U},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    sub_link (Γ ▹ₘ U[τ]ᵘ) (Δ ▹ₘ U) (q τ).
Proof.
  intros * Hτj Hl HU Γ' R' HΓ' σ σ' Hσ RΔU HΔU ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  pose proof (per_ctx_env_of_mod_sub HΓ Hτj HU) as HΓU.
  pose proof (per_ctx_env_of_mod HΔ HU) as HΔU'.
  assert (E : RΔU <~> env_ext_mod U U RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hwk : (Γ ▹ₘ U[τ]ᵘ) ⊨ʷ wk_shift : Γ)
    by (eapply rel_wk_under_ctx_intro; [ exact HΓU | exact HΓ | eapply rel_wk_shift; eassumption
                                       | intros ? ? _ x; apply entry_propositional_shift_wk ]).
  pose proof (rel_sub_of_wk Hwk) as HWk.
  pose proof (sub_link_wk Hwk) as HlW.
  pose proof (rel_sub_compose_of_link HWk HlW _ _ _ Hσ) as Hσw.
  assert (Hevw : ⟦ (sb_of_wk wk_shift) ⨟ σ : Γ ⟧s ρ ↘ ρσ↯) by (eapply eval_sub_tail; [ intros x; reflexivity | exact Hev ]).
  destruct (Hl _ _ HΓ' _ _ Hσw _ HΔ _ _ Hρ Hevw) as [e1 [He1 L1]].
  assert (Hρσ : env_ext_mod U[τ]ᵘ U[τ]ᵘ RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓU); eassumption).
  exists (env_entry ρσ 0 :: e1); split.
  - (** A slot is never a proposition: its head is [σ]'s. *)
    eapply eval_sub_cons_intro with (τ := τ ⨟ (sb_of_wk wk_shift ⨟ σ)); [ | exact He1 | |].
    + intros x; unfold sb_q, sb_extend, sb_wk; cbn; rewrite sentry_sub_wk; reflexivity.
    + intros Hp; exfalso; exact (head_not_propositional_mod _ _ Hp).
    + intros _; unfold sb_q, sb_extend; cbn.
      apply (eval_sub_index _ _ _ _ Hev), entry_propositional_mod; reflexivity.
  - intros e2 He2.
    destruct (eval_sub_q_inv _ _ _ _ _ He2) as [Ht2 Hh2].
    assert (Hh : env_entry e2 0 = env_entry ρσ 0) by (apply Hh2, entry_propositional_mod; reflexivity).
    pose proof (proj1 (eval_sub_shift_rel HΓU Hρσ)) as HevW.
    destruct (Hl _ _ HΓU _ _ HWk _ HΔ _ _ Hρσ HevW) as [g1 [Hg1 Lg]].
    assert (Heq : env_eq e2↯ g1) by (eapply functional_eval_sub; [ exact (eval_sub_sb_eq (sb_wk_compose _ _) Ht2) | exact Hg1 ]).
    destruct Hρσ as [Hρσt Hρσh _ _ _].
    pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
    assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hτs _ _ (proj1 (E3 _ _) Hρσt)) as [t [_ [Ht [_ _]]]].
    pose proof (L1 _ Ht) as H1. pose proof (Lg _ Ht) as H2.
    assert (H2' : RΔ e2↯ t) by (eapply (per_ctx_env_resp_env_eq HΔ); [ symmetry; exact Heq | reflexivity | exact H2 ]).
    assert (H12 : RΔ e1 e2↯) by (etransitivity; [ exact H1 | symmetry; exact H2' ]).
    destruct (unit_sub_chain HΓ Hτj HU _ _ _ _ Hρσt Ht Ht) as (C1 & _).
    pose proof (tie_mod_move _ _ _ _ _ Hρσh C1) as Tt.
    pose proof (unit_chain_at HU HΔ _ _ (symmetry H1)) as D1.
    pose proof (unit_chain_at HU HΔ _ _ (symmetry H2')) as D2.
    assert (Hm1 : tie_mod (env_mod ρσ 0) (me_lit U) e1) by exact (tie_mod_move _ _ _ _ _ Tt D1).
    assert (Hm2 : tie_mod (env_mod ρσ 0) (me_lit U) e2↯) by exact (tie_mod_move _ _ _ _ _ Tt D2).
    assert (Hme : env_mod e2 0 = env_mod ρσ 0) by (unfold env_mod; rewrite Hh; reflexivity).
    apply E; constructor;
      change (env_mod (env_entry ρσ 0 :: e1) 0) with (env_mod ρσ 0);
      cbn [drop_env List.tl]; try rewrite Hme; assumption.
Qed.

(** A lifted substitution into a definition with a module part: as into a
    definition entry and as into a slot, the source read as either. *)
Lemma sub_link_q_dm : forall {Γ Δ τ B} {i : nat} {M U},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ B : Typeω@i -> Δ ⊨ M : B -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    sub_link (Γ ▸ₘ B[τ] ≔ M[τ] ‖ U[τ]ᵘ) (Δ ▸ₘ B ≔ M ‖ U) (q τ).
Proof.
  intros * Hτj Hl HB HM HU Γ' R' HΓ' σ σ' Hσ RΔd HΔd ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  pose proof (per_ctx_env_of_dm_sub HΓ Hτj HB HM HU) as HΓdm.
  pose proof (per_ctx_env_of_def_sub HΓ Hτj HB HM) as HΓd.
  pose proof (per_ctx_env_of_mod_sub HΓ Hτj HU) as HΓm.
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  (** [B[τ]] is relevant at the tails of [Γ], so no head of [Γ]'s
      extensions by it is a proposition. *)
  assert (Hnpτ : forall e ρ0 ρ0', ctx_entry_type (e :: nil) 0 = Some B[τ] -> RΓ ρ0 ρ0' -> ~ head_propositional gc_deps gc_stack e ρ0).
  { intros e ρ0 ρ0' He Hr [T HT E HE v Ev Hv]; rewrite He in HT; injection HT as <-.
    cbn [List.skipn] in HE.
    assert (HE' : RΓ E ρ0') by (eapply per_ctx_env_resp_env_eq; [ exact HΓ | symmetry; exact HE | reflexivity | exact Hr ]).
    destruct (rel_exp_of_typ_sub_relevant HΓ Hτj HB _ _ HE') as (a & Ea & Ha).
    functional_eval_rewrite_clear; congruence. }
  assert (Hσd : Γ' ⊨ˢ σ ≈ σ' : Γ ▸ B[τ] ≔ M[τ]).
  { eapply (rel_sub_under_ctx_restrict HΓ' HΓ' HΓdm HΓd);
      [ tauto | | apply ctx_props_incl_same_types; intros []; reflexivity | exact Hσ ].
    intros e e' [Ht Hh Tl Tr _ _].
    assert (Ht' : Dom e'↯ ≈ e'↯ ∈ RΓ) by (etransitivity; [ symmetry |]; exact Ht).
    constructor; [ apply (mk_per_ctx_env_cons_rel _ _ _ _ _ _ Ht Hh) | exact Tl | exact Tr ];
      intros Hp; exfalso;
      [ exact (not_rel_typ_propositional_of_typ_sub HΓ Hτj HB _ _ Ht Hp)
      | exact (not_rel_typ_propositional_of_typ_sub HΓ Hτj HB _ _ Ht' Hp) ]. }
  assert (Hσm : Γ' ⊨ˢ σ ≈ σ' : Γ ▹ₘ U[τ]ᵘ).
  { eapply (rel_sub_under_ctx_restrict HΓ' HΓ' HΓdm HΓm);
      [ tauto | intros ? ? [Ht _ _ _ T1 T2]; constructor; assumption | | exact Hσ ].
    intros e e' He [| x] Hp.
    - exfalso; destruct He as [Ht _ _ _ _ _].
      exact (Hnpτ (ce_dm B[τ] M[τ] U[τ]ᵘ) _ _ eq_refl Ht (proj1 (entry_propositional_zero_head _ _ _) Hp)).
    - apply (proj2 (entry_propositional_succ _ _ _ _)); exact (proj1 (entry_propositional_succ _ _ _ _) Hp). }
  assert (Hρσ : per_env_extend_dm B[τ] M[τ] U[τ]ᵘ RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓdm); eassumption).
  pose proof Hρσ as [Hρσt _ _ _ _ _].
  (** A definition with a module part has its term part's entry type. *)
  assert (Tdm : forall A N V Θ0 x, ctx_entry_type (ce_dm A N V :: Θ0) x = ctx_entry_type (ce_def A N :: Θ0) x)
    by (intros ? ? ? ? []; reflexivity).
  pose proof (eval_sub_same_types (Tdm _ _ _ _) Hev) as Hevd.
  pose proof (eval_sub_change_head _ (ce_mod U[τ]ᵘ) _ _ _ _ Hev (Hnpτ (ce_dm B[τ] M[τ] U[τ]ᵘ) _ _ eq_refl Hρσt)
                (head_not_propositional_mod _ _)) as Hevm.
  destruct (sub_link_q_def Hτj Hl HB HM _ _ HΓ' _ _ Hσd _ (per_ctx_env_of_def HΔ HB HM) _ _ Hρ Hevd) as [ed [Hed Ld]].
  destruct (sub_link_q_mod Hτj Hl HU _ _ HΓ' _ _ Hσm _ (per_ctx_env_of_mod HΔ HU) _ _ Hρ Hevm) as [em [Hem Lm]].
  assert (E : RΔd <~> per_env_extend_dm B M U RΔ)
    by (eapply per_ctx_env_right_irrel; [ exact HΔd | exact (per_ctx_env_of_dm HΔ HB HM HU) ]).
  exists ed; split; [ exact (eval_sub_same_types (fun x => eq_sym (Tdm _ _ _ _ x)) Hed) |].
  intros e2 He2; apply E.
  pose proof (rel_exp_of_typ_inversion_simple_at HΔ HB) as HS.
  assert (Hnp : forall e ρ0 ρ0', ctx_entry_type (e :: nil) 0 = Some B -> RΔ ρ0 ρ0' -> ~ head_propositional gc_deps gc_stack e ρ0).
  { intros e ρ0 ρ0' He Hr.
    assert (Hr0 : RΔ ρ0 ρ0) by (etransitivity; [ exact Hr | symmetry; exact Hr ]).
    destruct (rel_exp_of_typ_relevant_at HΔ HB _ _ Hr0) as (a & Ea & Ha).
    exact (head_not_propositional HΔ He HS Hr0 Ea Ha). }
  pose proof (eval_sub_same_types (Tdm _ _ _ _) He2) as He2d.
  pose proof (Ld _ He2d) as Hdd.
  pose proof Hdd as [[Hdt _ _ _] _ _].
  assert (He22 : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact Hdt | exact Hdt ]).
  pose proof (eval_sub_change_head _ (ce_mod U) _ _ _ _ He2 (Hnp (ce_dm B M U) _ _ eq_refl He22)
                (head_not_propositional_mod _ _)) as He2m.
  pose proof (Lm _ He2m) as Hmm.
  pose proof Hmm as [Hmt _ _ _ _].
  pose proof (eval_sub_change_head _ (ce_def B M) _ _ _ _ Hem (head_not_propositional_mod _ _)
                (Hnp (ce_def B M) _ _ eq_refl Hmt)) as Hem'.
  assert (Q : env_eq em ed) by (eapply functional_eval_sub; eassumption).
  exact (per_env_extend_dm_of_parts HΔ HU Hdd Hmm Q (fun _ => eq_refl)).
Qed.

(** ** Substitutions Built from Valid Parts *)

(** A substitution that commutes with further ones moves term judgments
    along it: along [τ ⨟ σ] at [ρ] and along [τ] at the value of [σ]; the
    two inner environments are related by [sub_link], and a reflexive
    instance of the judgment at that pair bridges the two chains.  At a
    proposition the terms are not related, and nothing is bridged. *)
Lemma rel_exp_under_ctx_link : forall {Γ τ Δ T M M'},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ M ≈ M' : T -> Γ ⊨ M[τ] ≈ M'[τ] : T[τ].
Proof.
  intros * Hτj Hl HM.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  destruct (rel_exp_under_ctx_simple_full_at HΔ HMl) as [kl HBl].
  destruct (rel_exp_under_ctx_simple_full_at HΔ HMr) as [kr HBr].
  pose proof HM as [R0 HΔ0 i HMgen].
  refine (mk_rel_exp_under_ctx _ _ _ _ RΓ HΓ i _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hρσ : RΓ ρσ ρ'σ') by (exact (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev')).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρρ Hev) as [e1 [He1 L1]].
  destruct (Hl _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ HΔ _ _ Hρ'ρ' Hev') as [e1' [He1' L1']].
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [e2 [e2' [He2 [He2' _]]]].
  pose proof (L1 _ He2) as Hl1. pose proof (L1' _ He2') as Hl1'.
  destruct (HMgen _ _ HΓ' _ _ Hτσ _ _ _ _ Hρ He1 He1') as [R1 [Htyp1 Hexp1]].
  destruct (HMgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ He2 He2') as [R2 [Htyp2 Hexp2]].
  pose proof Htyp1 as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcc].
  pose proof Htyp2 as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdc].
  destruct (HBl _ _ Hl1) as [x1 [x2 [RB [Hx1 [Hx2 [HRB HBlm]]]]]].
  destruct (HBr _ _ Hl1') as [x3 [x4 [RB' [Hx3 [Hx4 [HRB' HBrm]]]]]].
  functional_eval_rewrite_clear.
  assert (Hc12 : per_univ_elem i R1 c1 c2) by pairwise.
  assert (Hc23 : per_univ_elem i R1 c2 c3) by pairwise.
  assert (Hc34 : per_univ_elem i R1 c3 c4) by pairwise.
  assert (Hd12 : per_univ_elem i R2 d1 d2) by pairwise.
  assert (Hd23 : per_univ_elem i R2 d2 d3) by pairwise.
  assert (Hd34 : per_univ_elem i R2 d3 d4) by pairwise.
  pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hc23 HRB) as E1.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRB Hd12) as E2.
  pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRB' Hd23) as E3'.
  assert (F1 : R1 <~> R2) by (rewrite E1, E2; reflexivity).
  assert (HP2 : PER R2) by (eapply per_elem_PER; exact Hd12).
  apply (fun H => per_univ_elem_resp_iff H F1) in Hc12, Hc23, Hc34.
  apply (fun H => per_univ_elem_resp_iff H E2) in HRB.
  apply (fun H => per_univ_elem_resp_iff H E3') in HRB'.
  assert (Htyp : Definitions.rel_typ i T[τ] σ ρ ρσ T[τ] σ' ρ' ρ'σ' R2).
  { apply (mk_rel_exp c1 d1 d4 c4); try (rewrite exp_sub_sub; assumption); try assumption.
    apply rel_chain_4.
    + eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hc12 | exact HRB ] | symmetry; exact Hd12 ].
    + eapply per_univ_trans; [ exact Hd12 |]; eapply per_univ_trans; [ exact Hd23 | exact Hd34 ].
    + eapply per_univ_trans; [ eapply per_univ_trans; [ symmetry; exact Hd34 | symmetry; exact HRB' ] | exact Hc34 ]. }
  exists R2; split; [ exact Htyp |].
  destruct (domain_relevance c1) eqn:Ec1; cycle 1.
  { left; exists c1; split; [ rewrite exp_sub_sub; exact Hc1 | exact Ec1 ]. }
  pose proof (per_univ_elem_relevance _ _ _ _ Hc12) as Er12.
  pose proof (per_univ_elem_relevance _ _ _ _ Hd12) as Erd12.
  pose proof (per_univ_elem_relevance _ _ _ _ HRB) as ErB.
  pose proof (per_univ_elem_relevance _ _ _ _ Hc23) as Er23.
  pose proof (per_univ_elem_relevance _ _ _ _ HRB') as ErB'.
  assert (Ec2 : domain_relevance c2 = relevant) by congruence.
  assert (Ed2 : domain_relevance d2 = relevant) by congruence.
  assert (Ec3 : domain_relevance c3 = relevant) by congruence.
  apply (rel_exp_or_prop_relevant Htyp1 (ex_intro _ c2 (conj Hc2 Ec2))) in Hexp1.
  apply (rel_exp_or_prop_relevant Htyp2 (ex_intro _ d2 (conj Hd2 Ed2))) in Hexp2.
  destruct HBlm as [Hp | [y1 [y2 [Hy1 [Hy2 Hy]]]]]; [ congruence |].
  destruct HBrm as [Hp | [y3 [y4 [Hy3 [Hy4 Hy']]]]]; [ congruence |].
  destruct Hexp1 as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc].
  destruct Hexp2 as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnc].
  functional_eval_rewrite_clear.
  apply E2 in Hy. apply E3' in Hy'.
  destruct Hmc as (Hm12 & Hm23 & Hm34). destruct Hnc as (Hn12 & Hn23 & Hn34).
  apply F1 in Hm12, Hm23, Hm34.
  right; apply (mk_rel_exp m1 n1 n4 m4); try (rewrite exp_sub_sub; assumption); try assumption.
  apply rel_chain_4.
  + etransitivity; [ exact Hm12 |]; etransitivity; [ exact Hy | symmetry; exact Hn12 ].
  + etransitivity; [ exact Hn12 |]; etransitivity; [ exact Hn23 | exact Hn34 ].
  + etransitivity; [ symmetry; exact Hn34 |]; etransitivity; [ symmetry; exact Hy' | exact Hm34 ].
Qed.

(** Module expressions likewise, the module PER having no types to move. *)
Lemma rel_modexp_under_ctx_link : forall {Γ τ Δ H H'},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H[τ]ᵐ ≈ H'[τ]ᵐ.
Proof.
  intros * Hτj Hl HH.
  pose proof Hτj as [RΓ HΓ RΔ HΔ _].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (PER per_dmod) by typeclasses eauto.
  pose proof (rel_modexp_under_ctx_trans HH (rel_modexp_under_ctx_sym HH)) as HHl.
  pose proof (rel_modexp_under_ctx_trans (rel_modexp_under_ctx_sym HH) HH) as HHr.
  pose proof HH as [R0 HΔ0 HHgen].
  refine (mk_rel_modexp_under_ctx _ _ _ RΓ HΓ _).
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hρσ : RΓ ρσ ρ'σ') by (exact (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev')).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρρ Hev) as [e1 [He1 L1]].
  destruct (Hl _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ HΔ _ _ Hρ'ρ' Hev') as [e1' [He1' L1']].
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [e2 [e2' [He2 [He2' _]]]].
  pose proof (L1 _ He2) as Hl1. pose proof (L1' _ He2') as Hl1'.
  destruct (HHgen _ _ HΓ' _ _ Hτσ _ _ _ _ Hρ He1 He1') as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 (C12 & C23 & C34)].
  destruct (HHgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ He2 He2') as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 (D12 & D23 & D34)].
  hnf in C34, D34.
  destruct (rel_modexp_at _ _ _ _ _ HHl HΔ _ _ Hl1) as (x1 & x2 & Hx1 & Hx2 & Hxx).
  destruct (rel_modexp_at _ _ _ _ _ HHr HΔ _ _ Hl1') as (y1 & y2 & Hy1 & Hy2 & Hyy).
  repeat match goal with
         | H1 : ⟦ ?M ⟧ᵐ _ ⍮ _ ⍮ ?r ↘ ?a, H2 : ⟦ ?M ⟧ᵐ _ ⍮ _ ⍮ ?r ↘ ?b |- _ =>
             tryif unify a b then fail else (pose proof (functional_eval_modexp _ _ _ _ H1 H2); subst b; clear H2)
         end.
  apply (mk_rel_modexp c1 d1 d4 c4); try (rewrite modexp_sub_sub; assumption); try assumption.
  apply rel_chain_4.
  - etransitivity; [ exact C12 |]; etransitivity; [ exact Hxx | symmetry; exact D12 ].
  - etransitivity; [ exact D12 |]; etransitivity; [ exact D23 | exact D34 ].
  - etransitivity; [ symmetry; exact D34 |]; etransitivity; [ symmetry; exact Hyy | exact C34 ].
Qed.

(** A lifted substitution into a definition of a proposition is semantic:
    the source is a context PER only once [B[τ]] is a proposition there,
    which the substitution moves from [Δ]. *)
Lemma rel_sub_under_ctx_q_def_prop_link : forall {Γ Δ τ B M},
    Γ ⊨ˢ τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ B : Propₘ ->
    Γ ▸ B[τ] ≔ M[τ] ⊨ˢ q τ ≈ q τ : Δ ▸ B ≔ M.
Proof.
  intros * Hτj Hl HB.
  pose proof Hτj as [RΓ HΓ _ _ _].
  pose proof (rel_exp_under_ctx_link Hτj Hl HB) as HBτ; cbn in HBτ.
  pose proof (rel_sub_under_ctx_q Hτj (rel_type_of_prop 0 HB)) as Hq.
  pose proof Hq as [_ _ S HS _].
  pose proof (per_ctx_env_of_typ_sub HΓ Hτj (rel_type_of_prop 0 HB)) as HΓB.
  pose proof (per_ctx_env_of_def_prop (M := M[τ]) HΓ HBτ) as HΓBd.
  apply (rel_sub_under_ctx_into_def_prop HB).
  exact (rel_sub_under_ctx_restrict HΓBd HΓB HS HS (fun _ _ H => H) (fun _ _ H => H) (fun _ _ _ _ Hp => Hp) Hq).
Qed.

(** The substitutions built from the identity by extensions with valid
    parts, liftings, equal substitutions and composites with ones that
    commute with further substitutions.  An assumption or a definition is
    of a type of a universe or of a proposition ([type_sort]), as in
    [rel_ctx_wf]; a definition with a module part is of a type of a
    universe. *)
Inductive gsub : ctx -> sub -> ctx -> Prop :=
(** The identity *)
| gsub_id : forall Γ, ⊨ Γ -> gsub Γ Id Γ
(** Extension by a valid term of the substituted type of an assumption *)
| gsub_ass : forall Γ τ Δ B Srt N,
    gsub Γ τ Δ -> type_sort Srt -> Δ ⊨ B : Srt -> Γ ⊨ N : B[τ] -> gsub Γ (τ ,, N) (Δ ▹ B)
(** Extension by the substituted body of a definition *)
| gsub_def : forall Γ τ Δ B Srt M,
    gsub Γ τ Δ -> type_sort Srt -> Δ ⊨ B : Srt -> Δ ⊨ M : B -> gsub Γ (τ ,, M[τ]) (Δ ▸ B ≔ M)
(** Extension by the substituted literal of a slot's unit *)
| gsub_mod : forall Γ τ Δ U,
    gsub Γ τ Δ -> Δ ⊨ᵘ U ≈ U -> gsub Γ (τ ,,ₘ me_lit U[τ]ᵘ) (Δ ▹ₘ U)
(** Extension by a definition with a module part: its term, and the
    literal of its unit *)
| gsub_dm : forall Γ τ Δ B i M U,
    gsub Γ τ Δ -> Δ ⊨ B : Typeω@i -> Δ ⊨ M : B -> Δ ⊨ᵘ U ≈ U ->
    gsub Γ (τ ,,ᵈ M[τ] ‖ me_lit U[τ]ᵘ) (Δ ▸ₘ B ≔ M ‖ U)
(** An equal substitution *)
| gsub_eq : forall Γ τ τ' Δ, gsub Γ τ Δ -> sb_eq τ τ' -> gsub Γ τ' Δ
(** Under an assumption *)
| gsub_q : forall Γ τ Δ B Srt,
    gsub Γ τ Δ -> type_sort Srt -> Δ ⊨ B : Srt -> gsub (Γ ▹ B[τ]) (q τ) (Δ ▹ B)
(** Under a definition *)
| gsub_q_def : forall Γ τ Δ B Srt M,
    gsub Γ τ Δ -> type_sort Srt -> Δ ⊨ B : Srt -> Δ ⊨ M : B -> gsub (Γ ▸ B[τ] ≔ M[τ]) (q τ) (Δ ▸ B ≔ M)
(** Under a slot *)
| gsub_q_mod : forall Γ τ Δ U,
    gsub Γ τ Δ -> Δ ⊨ᵘ U ≈ U -> Γ ⊨ᵘ U[τ]ᵘ ≈ U[τ]ᵘ -> gsub (Γ ▹ₘ U[τ]ᵘ) (q τ) (Δ ▹ₘ U)
(** Under a definition with a module part *)
| gsub_q_dm : forall Γ τ Δ B i M U,
    gsub Γ τ Δ -> Δ ⊨ B : Typeω@i -> Δ ⊨ M : B -> Δ ⊨ᵘ U ≈ U -> Γ ⊨ᵘ U[τ]ᵘ ≈ U[τ]ᵘ ->
    gsub (Γ ▸ₘ B[τ] ≔ M[τ] ‖ U[τ]ᵘ) (q τ) (Δ ▸ₘ B ≔ M ‖ U)
(** A composite with a semantic substitution that commutes with further
    ones *)
| gsub_comp : forall Γ Γ0 τ σ Δ,
    gsub Γ0 τ Δ -> ⊨ Γ -> Γ ⊨ˢ σ ≈ σ : Γ0 -> sub_link Γ Γ0 σ -> gsub Γ (τ ⨟ σ) Δ.

Lemma gsub_props : forall {Γ τ Δ}, gsub Γ τ Δ -> Γ ⊨ˢ τ ≈ τ : Δ /\ sub_link Γ Δ τ.
Proof.
  induction 1 as [? HΓ | ? ? ? ? ? ? ? [IH1 IH2] HS HB HN | ? ? ? ? ? ? ? [IH1 IH2] HS HB HM
                 | ? ? ? ? ? [IH1 IH2] HU | ? ? ? ? ? ? ? ? [IH1 IH2] HB HM HU | ? ? ? ? ? [IH1 IH2] Eq
                 | ? ? ? ? ? ? [IH1 IH2] HS HB
                 | ? ? ? ? ? ? ? [IH1 IH2] HS HB HM | ? ? ? ? ? [IH1 IH2] HU _
                 | ? ? ? ? ? ? ? ? [IH1 IH2] HB HM HU _ | ? ? ? ? ? ? [IH1 IH2] _ Hσ Hl ].
  - split; [ exact (rel_sub_id (rel_ctx_wf_per_ctx_env HΓ)) | exact sub_link_id ].
  - destruct (rel_type_of_sort HS HB) as [i HBt].
    split; [ exact (rel_sub_under_ctx_extend IH1 HBt HN) | exact (sub_link_ass IH1 IH2 HBt HN) ].
  - destruct HS as [i |].
    + split; [ eapply rel_sub_under_ctx_extend_sub_def; eassumption | eapply sub_link_def; eassumption ].
    + split; [| exact (sub_link_def_prop IH1 IH2 HB) ].
      apply (rel_sub_under_ctx_into_def_prop HB).
      exact (rel_sub_under_ctx_extend IH1 (rel_type_of_prop 0 HB) (rel_exp_under_ctx_link IH1 IH2 HM)).
  - destruct HU as [HU _ _].
    split; [ exact (rel_sub_under_ctx_extend_mod IH1 HU) | eapply sub_link_mod; eassumption ].
  - destruct HU as [HU _ _].
    split; [ eapply rel_sub_under_ctx_extend_dm; eassumption | eapply sub_link_dm; eassumption ].
  - split; [ exact (rel_sub_under_ctx_sb_eq IH1 Eq Eq) | exact (sub_link_sb_eq Eq IH2) ].
  - destruct (rel_type_of_sort HS HB) as [i HBt].
    split; [ exact (rel_sub_under_ctx_q IH1 HBt) | exact (sub_link_q IH1 IH2 HBt) ].
  - destruct HS as [i |].
    + split; [ exact (rel_sub_under_ctx_q_def IH1 HB HM) | exact (sub_link_q_def IH1 IH2 HB HM) ].
    + split; [ exact (rel_sub_under_ctx_q_def_prop_link IH1 IH2 HB) | exact (sub_link_q_def_prop IH1 IH2 HB) ].
  - destruct HU as [HU _ _].
    split; [ exact (rel_sub_under_ctx_q_mod IH1 HU) | exact (sub_link_q_mod IH1 IH2 HU) ].
  - destruct HU as [HU _ _].
    split; [ exact (rel_sub_under_ctx_q_dm IH1 HB HM HU) | exact (sub_link_q_dm IH1 IH2 HB HM HU) ].
  - split; [ exact (rel_sub_compose_of_link IH1 IH2 _ _ _ Hσ) | exact (sub_link_comp IH1 IH2 Hσ Hl) ].
Qed.

Corollary gsub_valid : forall {Γ τ Δ}, gsub Γ τ Δ -> Γ ⊨ˢ τ ≈ τ : Δ.
Proof. intros * H; exact (proj1 (gsub_props H)). Qed.

Corollary gsub_compose : forall {Γ τ Δ}, gsub Γ τ Δ ->
    forall Γ' σ σ', Γ' ⊨ˢ σ ≈ σ' : Γ -> Γ' ⊨ˢ τ ⨟ σ ≈ τ ⨟ σ' : Δ.
Proof. intros * H; destruct (gsub_props H); eapply rel_sub_compose_of_link; eassumption. Qed.

(** ** Instances

    Judgments move along the substitutions built from valid parts, as along
    any that commute with further ones ([rel_exp_under_ctx_link]). *)
Lemma rel_exp_under_ctx_gsub : forall {Γ τ Δ T M M'},
    gsub Γ τ Δ -> Δ ⊨ M ≈ M' : T -> Γ ⊨ M[τ] ≈ M'[τ] : T[τ].
Proof.
  intros * Hg HM; destruct (gsub_props Hg) as [Hτj Hl]; exact (rel_exp_under_ctx_link Hτj Hl HM).
Qed.

(** Module expressions likewise, the module PER having no types to move. *)
Lemma rel_modexp_under_ctx_gsub : forall {Γ τ Δ H H'},
    gsub Γ τ Δ -> Δ ⊨ᵐ H ≈ H' -> Γ ⊨ᵐ H[τ]ᵐ ≈ H'[τ]ᵐ.
Proof.
  intros * Hg HH; destruct (gsub_props Hg) as [Hτj Hl]; exact (rel_modexp_under_ctx_link Hτj Hl HH).
Qed.

End Fixed_GCtx.
