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
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases UniverseCases SubstitutionCases LetCases UnitCases.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma rel_sub_under_ctx_sb_eq : forall {Γ Δ σ1 σ2 τ1 τ2},
    Γ ⊨s σ1 ≈ σ2 : Δ -> sb_eq σ1 τ1 -> sb_eq σ2 τ2 -> Γ ⊨s τ1 ≈ τ2 : Δ.
Proof.
  intros * [R [HΓ [RΔ [HΔ Hσ]]]] E1 E2.
  exists R, HΓ, RΔ, HΔ.
  intros Γ' R' HΓ' φ Hφ ρ ρ' Hρ.
  destruct (Hσ _ _ HΓ' _ Hφ _ _ Hρ) as [x1 x2 x3 x4 H1 H2 H3 H4 Hc].
  econstructor; [ | | | | exact Hc ].
  - rewrite <- (sb_wk_cong _ _ φ φ E1 (reflexivity _)); exact H1.
  - rewrite <- E1; exact H2.
  - rewrite <- E2; exact H3.
  - rewrite <- (sb_wk_cong _ _ φ φ E2 (reflexivity _)); exact H4.
Qed.

(** ** Composition

    [τ ⨟ σ] evaluates, at an environment of [σ]'s domain, to an environment
    related to the value of [τ] at the value of [σ]. *)

Definition sub_link (Γ Δ : ctx) (τ : sub) : Prop :=
  forall Γ' R' (_ : EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R') σ σ',
    Γ' ⊨s σ ≈ σ' : Γ ->
    forall RΔ (_ : EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ) ρ ρσ,
      R' ρ ρ -> ⟦ σ ⟧s ρ ↘ ρσ ->
      exists e1, ⟦ τ ⨟ σ ⟧s ρ ↘ e1 /\ forall e2, ⟦ τ ⟧s ρσ ↘ e2 -> RΔ e1 e2.

Lemma rel_sub_compose_of_link : forall {Γ Δ τ},
    Γ ⊨s τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    forall Γ' σ σ', Γ' ⊨s σ ≈ σ' : Γ -> Γ' ⊨s τ ⨟ σ ≈ τ ⨟ σ' : Δ.
Proof.
  intros * Hτj Hl * Hσj.
  pose proof Hσj as [R' [HΓ' [RΓ [HΓ Hσ]]]].
  pose proof Hτj as [RΓ2 [HΓ2 [RΔ [HΔ _]]]].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (HPΓ : PER RΓ) by (eapply per_env_PER; exact HΓ).
  exists R', HΓ', RΔ, HΔ.
  intros Γ'' R'' HΓ'' φ Hφ ρ ρ' Hρ.
  assert (HP'' : PER R'') by (eapply per_env_PER; exact HΓ'').
  pose proof (rel_sub_under_ctx_wk Hσj (rel_wk_under_ctx_intro HΓ'' HΓ' Hφ)) as Hσφ.
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
  assert (T : forall a b x y, RΓ a b -> ⟦ τ ⟧s a ↘ x -> ⟦ τ ⟧s b ↘ y -> RΔ x y)
    by (intros; eapply (rel_sub_under_ctx_at' Hτj HΓ HΔ); eassumption).
  apply (mk_rel_sub e1 e2 e3 e4).
  - rewrite sb_wk_compose, sb_compose_assoc, <- sb_wk_compose; exact He1.
  - exact He2.
  - exact He3.
  - rewrite sb_wk_compose, sb_compose_assoc, <- sb_wk_compose; exact He4.
  - pose proof (L1 _ Ht1). pose proof (L2 _ Ht2). pose proof (L3 _ Ht3). pose proof (L4 _ Ht4).
    assert (RΔ t1 t2) by (eapply T; [ | exact Ht1 | exact Ht2 ]; pairwise).
    assert (RΔ t2 t3) by (eapply T; [ | exact Ht2 | exact Ht3 ]; pairwise).
    assert (RΔ t3 t4) by (eapply T; [ | exact Ht3 | exact Ht4 ]; pairwise).
    apply rel_chain_4.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
    + etransitivity; [ eassumption |]; etransitivity; [ eassumption |]; symmetry; eassumption.
Qed.

Lemma eval_sub_extend_inv : forall σ e ρ ρσ,
    ⟦ sb_extend σ e ⟧s ρ ↘ ρσ -> ⟦ σ ⟧s ρ ↘ ρσ↯ /\ eval_sentry gc_deps gc_stack e ρ (env_entry ρσ 0).
Proof.
  intros * H; split; [| exact (H 0) ].
  intros x; specialize (H (S x)); cbn in H.
  destruct ρσ; cbn in *; [ destruct (σ x); exact H | exact H ].
Qed.

Lemma sub_link_id : forall {Γ}, sub_link Γ Γ Id.
Proof.
  intros * Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  exists ρσ; split; [ rewrite sb_compose_id_left; exact Hev |].
  intros e2 He2.
  assert (Heq : env_eq e2 ρσ) by (eapply functional_eval_sub; [ exact He2 | apply eval_sub_id ]).
  rewrite Heq.
  eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΔ); eassumption.
Qed.

(** Extension by a term of the domain: its head commutes with [σ] since the
    term is valid, at a type that [τ] relates to the entry's own. *)
Lemma sub_link_ass : forall {Γ Δ τ B i N},
    Γ ⊨s τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ B : Type@i -> Γ ⊨ N : B[τ] ->
    sub_link Γ (Δ ▹ B) (τ ,, N).
Proof.
  intros * Hτj Hl HB HN Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ [HΓ [RΔ [HΔ _]]]].
  pose proof (per_ctx_env_of_typ HΔ HB) as HΔB'.
  assert (E : RΔB <~> per_env_extend B B RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  pose proof HN as [RΓ2 [HΓ2 [j HNgen]]].
  destruct (HNgen _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hσ) _ _ _ _ Hρ Hev Hev)
    as [R1 [[b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbc] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnc]]].
  exists (e1 ↦ n1); split.
  - rewrite sb_extend_compose; apply eval_sub_extend; assumption.
  - intros e2 He2.
    destruct (eval_sub_extend_inv _ _ _ _ He2) as [Ht2 [m2 [Hm2e Hm2]]].
    apply E.
    pose proof (L _ Ht2) as Ht.
    pose proof (rel_exp_of_typ_inversion HB) as [R0 [HΔ0 HBgen]].
    assert (Hm : m2 = n2) by (eapply functional_eval_exp; eassumption).
    subst m2.
    split; [ exact Ht |].
    destruct (HBgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ Ht2 Ht2) as [x1 c x3 x4 Hx1 Hc Hx3 Hx4 [[Rx Hxc] _]].
    destruct (HBgen _ _ HΔ _ _ (rel_sub_id (ex_intro _ _ HΔ)) _ _ _ _ Ht (eval_sub_id _) (eval_sub_id _))
      as [y1 a c' y4 Hy1 Ha Hc' Hy4 [_ [[Rac HRac] _]]].
    functional_eval_rewrite_clear.
    destruct Hbc as [_ [Hb23 _]].
    assert (Hn12 : R1 n1 n3) by (destruct Hnc as [? _]; assumption).
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hb23 Hxc) as E1.
    pose proof (per_univ_elem_left_irrel _ _ _ _ _ _ _ HRac Hxc) as E2.
    eapply per_head_of; [ exact Ha | exact Hc | exact HRac |].
    cbn; unfold env_var; rewrite Hm2e; apply E2, E1; exact Hn12.
Qed.

(** A valid term along a substitution, read at the substitution's value. *)
Lemma rel_exp_comm_head : forall {Γ' Δ τ τ' R' B M},
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    Γ' ⊨s τ ≈ τ' : Δ -> Δ ⊨ M : B ->
    forall ρ e m, R' ρ ρ -> ⟦ τ ⟧s ρ ↘ e -> ⟦ M[τ] ⟧ ρ ↘ m ->
      exists m', ⟦ M ⟧ e ↘ m' /\ per_head B B e e m m'.
Proof.
  intros * HΓ' Hτ HM * Hρ Hev Hm.
  pose proof HM as [R0 [HΔ0 [j HMgen]]].
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hτ) _ _ _ _ Hρ Hev Hev)
    as [E [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hac] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc]]].
  functional_eval_rewrite_clear.
  exists m2; split; [ exact Hm2 |].
  destruct Hac as [_ [Ha22 _]].
  eapply per_head_of; [ exact Ha2 | exact Ha2 | exact Ha22 |].
  destruct Hmc as [Hm12 _]; exact Hm12.
Qed.

(** Extension by a definition of the codomain, read along [τ]. *)
Lemma sub_link_def : forall {Γ Δ τ B i M},
    Γ ⊨s τ ≈ τ : Δ -> sub_link Γ Δ τ ->
    Δ ⊨ B : Type@i -> Δ ⊨ M : B ->
    sub_link Γ (Δ ▸ B ≔ M) (τ ,, M[τ]).
Proof.
  intros * Hτj Hl HB HM Γ' R' HΓ' σ σ' Hσ RΔB HΔB ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ [HΓ [RΔ [HΔ _]]]].
  pose proof (per_ctx_env_of_def HΔ HB HM) as HΔB'.
  assert (E : RΔB <~> per_env_extend_def B M RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  destruct (rel_exp_under_ctx_sub_simple HΓ' (rel_sub_under_ctx_refl_left Hτσ) HM _ _ Hρ)
    as [m1 [_ [Hm1 [_ _]]]].
  exists (e1 ↦ m1); split.
  - rewrite sb_extend_compose; apply eval_sub_extend; [ exact He1 | rewrite exp_sub_sub; exact Hm1 ].
  - intros e2 He2.
    destruct (eval_sub_extend_inv _ _ _ _ He2) as [Ht2 [m2 [Hm2e Hm2]]].
    apply E.
    pose proof (L _ Ht2) as Ht.
    assert (Heq : env_eq e2 (e2↯ ↦ m2)) by (intros [| x]; [ exact Hm2e | destruct e2; reflexivity ]).
    rewrite Heq.
    pose proof (rel_exp_of_typ_inversion_simple_at HΔ HB) as HS.
    pose proof (rel_exp_under_ctx_simple_at HΔ HM) as HMs.
    destruct (rel_exp_comm_head HΓ' Hτσ HM _ _ _ Hρ He1 Hm1) as [m1' [Hm1' H1]].
    destruct (rel_exp_comm_head HΓ (rel_sub_under_ctx_refl_left Hτj) HM _ _ _ Hρσ Ht2 Hm2)
      as [m2' [Hm2' H2]].
    destruct (HMs _ _ Ht) as [n1 [n2 [Hn1 [Hn2 H12]]]].
    functional_eval_rewrite_clear.
    assert (Hee : RΔ e1 e1) by (etransitivity; [ exact Ht | symmetry; exact Ht ]).
    assert (Hee' : RΔ e2↯ e2↯) by (etransitivity; [ symmetry; exact Ht | exact Ht ]).
    assert (Q1 : per_head B B e1 e1 <~> per_head B B e1 e2↯)
      by (eapply (per_head_of_typ_resp HΔ HB); apply rel_chain_4; assumption).
    assert (Q2 : per_head B B e2↯ e2↯ <~> per_head B B e1 e2↯)
      by (eapply (per_head_of_typ_resp HΔ HB); apply rel_chain_4; [ exact Hee' | symmetry; exact Ht | exact Ht ]).
    destruct (HS _ _ Ht) as [a [a' [Ha [Ha' [Rh HRh]]]]].
    pose proof (per_head_iff Ha Ha' HRh) as Qh.
    assert (PER Rh) by (eapply per_elem_PER; exact HRh).
    apply Q1, Qh in H1. apply Q2, Qh in H2. apply Qh in H12.
    eapply per_env_extend_def_intro; [ exact HPΔ | exact HS | exact HMs | exact Ht | | exact Hm1' | ].
    + apply Qh; etransitivity; [ exact H1 |]; etransitivity; [ exact H12 | symmetry; exact H2 ].
    + apply Qh; symmetry; exact H1.
Qed.

(** Extension by the literal of a unit of the codomain, read along [τ]. *)
Lemma sub_link_mod : forall {Γ Δ τ U},
    Γ ⊨s τ ≈ τ : Δ -> sub_link Γ Δ τ -> Δ ⊨ᵐ me_lit U ≈ me_lit U ->
    sub_link Γ (Δ ▹ₘ U) (τ ,,ₘ me_lit U[τ]ᵘ).
Proof.
  intros * Hτj Hl HU Γ' R' HΓ' σ σ' Hσ RΔU HΔU ρ ρσ Hρ Hev.
  pose proof Hτj as [RΓ [HΓ [RΔ [HΔ _]]]].
  pose proof (per_ctx_env_of_mod HΔ HU) as HΔU'.
  assert (E : RΔU <~> env_ext_mod U U RΔ) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (Hρσ : RΓ ρσ ρσ)
    by (eapply (rel_sub_under_ctx_at' (rel_sub_under_ctx_refl_left Hσ) HΓ' HΓ); eassumption).
  pose proof (rel_sub_compose_of_link Hτj Hl _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  destruct (unit_chain HU) as [R0 [HΔ0 Hch]].
  exists (e1 ↦ᵐ dm_local ρ U[τ ⨟ σ]ᵘ nil); split.
  - rewrite sb_extend_compose_gen; apply eval_sub_extend_mod; [ exact He1 |].
    cbn [sentry_sub modexp_sub]; rewrite gunit_sub_sub; constructor.
  - intros e2 He2.
    destruct (eval_sub_extend_inv _ _ _ _ He2) as [Ht2 [h2 [Hh2e Hh2]]].
    inversion Hh2; subst.
    apply E.
    pose proof (L _ Ht2) as Ht.
    assert (Heq : env_eq e2 (e2↯ ↦ᵐ dm_local ρσ U[τ]ᵘ nil))
      by (intros [| x]; [ exact Hh2e | destruct e2; reflexivity ]).
    rewrite Heq.
    pose proof (Hch _ _ HΓ' _ _ (rel_sub_under_ctx_refl_left Hτσ) _ _ _ _ Hρ He1 He1) as [C1 _].
    pose proof (Hch _ _ HΓ _ _ (rel_sub_under_ctx_refl_left Hτj) _ _ _ _ Hρσ Ht2 Ht2) as [C2 _].
    unfold env_ext_mod; cbn; repeat split; assumption.
Qed.

Lemma sub_link_sb_eq : forall {Γ Δ τ τ'}, sb_eq τ τ' -> sub_link Γ Δ τ -> sub_link Γ Δ τ'.
Proof.
  intros * Eq Hl Γ' R' HΓ' σ σ' Hσ RΔ HΔ ρ ρσ Hρ Hev.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρ Hev) as [e1 [He1 L]].
  exists e1; split.
  - assert (E2 : sb_eq (τ ⨟ σ) (τ' ⨟ σ)) by (intros x; cbn; rewrite (Eq x); reflexivity).
    rewrite <- E2; exact He1.
  - intros e2 He2; apply L; rewrite Eq; exact He2.
Qed.

(** ** Substitutions Built from Valid Parts *)

Inductive gsub (Γ : ctx) : sub -> ctx -> Prop :=
| gsub_id : ⊨ Γ -> gsub Γ Id Γ
| gsub_ass : forall τ Δ B i N,
    gsub Γ τ Δ -> Δ ⊨ B : Type@i -> Γ ⊨ N : B[τ] -> gsub Γ (τ ,, N) (Δ ▹ B)
| gsub_def : forall τ Δ B i M,
    gsub Γ τ Δ -> Δ ⊨ B : Type@i -> Δ ⊨ M : B -> gsub Γ (τ ,, M[τ]) (Δ ▸ B ≔ M)
| gsub_mod : forall τ Δ U,
    gsub Γ τ Δ -> Δ ⊨ᵘ U ≈ U -> gsub Γ (τ ,,ₘ me_lit U[τ]ᵘ) (Δ ▹ₘ U)
| gsub_eq : forall τ τ' Δ, gsub Γ τ Δ -> sb_eq τ τ' -> gsub Γ τ' Δ.

Lemma gsub_props : forall {Γ τ Δ}, gsub Γ τ Δ -> Γ ⊨s τ ≈ τ : Δ /\ sub_link Γ Δ τ.
Proof.
  induction 1 as [HΓ | ? ? ? ? ? ? [IH1 IH2] HB HN | ? ? ? ? ? ? [IH1 IH2] HB HM
                 | ? ? ? ? [IH1 IH2] HU | ? ? ? ? [IH1 IH2] Eq ].
  - split; [ exact (rel_sub_id (sem_ctx_per_ctx_env HΓ)) | exact sub_link_id ].
  - split; [ eapply rel_sub_under_ctx_extend; eassumption | eapply sub_link_ass; eassumption ].
  - split; [ eapply rel_sub_under_ctx_extend_sub_def; eassumption | eapply sub_link_def; eassumption ].
  - destruct HU as (HU & _ & _).
    split; [ exact (rel_sub_under_ctx_extend_mod IH1 HU) | eapply sub_link_mod; eassumption ].
  - split; [ exact (rel_sub_under_ctx_sb_eq IH1 Eq Eq) | exact (sub_link_sb_eq Eq IH2) ].
Qed.

Corollary gsub_valid : forall {Γ τ Δ}, gsub Γ τ Δ -> Γ ⊨s τ ≈ τ : Δ.
Proof. intros * H; exact (proj1 (gsub_props H)). Qed.

Corollary gsub_compose : forall {Γ τ Δ}, gsub Γ τ Δ ->
    forall Γ' σ σ', Γ' ⊨s σ ≈ σ' : Γ -> Γ' ⊨s τ ⨟ σ ≈ τ ⨟ σ' : Δ.
Proof. intros * H; destruct (gsub_props H); eapply rel_sub_compose_of_link; eassumption. Qed.

(** ** Instances

    Along [τ ⨟ σ] at [ρ] and along [τ] at the value of [σ]; the two inner
    environments are related by [sub_link], and a reflexive instance of the
    judgment at that pair bridges the two chains. *)
Lemma rel_exp_under_ctx_gsub : forall {Γ τ Δ T M M'},
    gsub Γ τ Δ -> Δ ⊨ M ≈ M' : T -> Γ ⊨ M[τ] ≈ M'[τ] : T[τ].
Proof.
  intros * Hg HM.
  destruct (gsub_props Hg) as [Hτj Hl].
  pose proof Hτj as [RΓ [HΓ [RΔ [HΔ _]]]].
  assert (HPΔ : PER RΔ) by (eapply per_env_PER; exact HΔ).
  pose proof (rel_exp_under_ctx_refl_left HM) as HMl.
  pose proof (rel_exp_under_ctx_refl_right HM) as HMr.
  destruct (rel_exp_under_ctx_simple_full_at HΔ HMl) as [kl HBl].
  destruct (rel_exp_under_ctx_simple_full_at HΔ HMr) as [kr HBr].
  pose proof HM as [R0 [HΔ0 [i HMgen]]].
  exists RΓ, HΓ, i.
  intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  assert (Hρσ : RΓ ρσ ρ'σ') by (exact (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev')).
  pose proof (gsub_compose Hg _ _ _ Hσ) as Hτσ.
  destruct (Hl _ _ HΓ' _ _ Hσ _ HΔ _ _ Hρρ Hev) as [e1 [He1 L1]].
  destruct (Hl _ _ HΓ' _ _ (rel_sub_under_ctx_sym Hσ) _ HΔ _ _ Hρ'ρ' Hev') as [e1' [He1' L1']].
  pose proof (rel_sub_under_ctx_simple Hτj) as [RΓ3 [HΓ3 [RΔ3 [HΔ3 Hτs]]]].
  assert (E3 : RΓ <~> RΓ3) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hτs _ _ (proj1 (E3 _ _) Hρσ)) as [e2 [e2' [He2 [He2' _]]]].
  pose proof (L1 _ He2) as Hl1. pose proof (L1' _ He2') as Hl1'.
  destruct (HMgen _ _ HΓ' _ _ Hτσ _ _ _ _ Hρ He1 He1')
    as [R1 [[c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcc] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmc]]].
  destruct (HMgen _ _ HΓ _ _ Hτj _ _ _ _ Hρσ He2 He2')
    as [R2 [[d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdc] [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnc]]].
  destruct (HBl _ _ Hl1) as [x1 [x2 [RB [Hx1 [Hx2 [HRB [y1 [y2 [Hy1 [Hy2 Hy]]]]]]]]]].
  destruct (HBr _ _ Hl1') as [x3 [x4 [RB' [Hx3 [Hx4 [HRB' [y3 [y4 [Hy3 [Hy4 Hy']]]]]]]]]].
  functional_eval_rewrite_clear.
  clear HBl HBr HMgen Hτs L1 L1' Hl.
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
  apply E2 in Hy. apply E3' in Hy'.
  destruct Hmc as (Hm12 & Hm23 & Hm34). destruct Hnc as (Hn12 & Hn23 & Hn34).
  apply F1 in Hm12, Hm23, Hm34.
  exists R2; split.
  - apply (mk_rel_exp c1 d1 d4 c4); try (rewrite exp_sub_sub; assumption); try assumption.
    apply rel_chain_4.
    + eapply per_univ_trans; [ eapply per_univ_trans; [ exact Hc12 | exact HRB ] | symmetry; exact Hd12 ].
    + eapply per_univ_trans; [ exact Hd12 |]; eapply per_univ_trans; [ exact Hd23 | exact Hd34 ].
    + eapply per_univ_trans; [ eapply per_univ_trans; [ symmetry; exact Hd34 | symmetry; exact HRB' ] | exact Hc34 ].
  - apply (mk_rel_exp m1 n1 n4 m4); try (rewrite exp_sub_sub; assumption); try assumption.
    apply rel_chain_4.
    + etransitivity; [ exact Hm12 |]; etransitivity; [ exact Hy | symmetry; exact Hn12 ].
    + etransitivity; [ exact Hn12 |]; etransitivity; [ exact Hn23 | exact Hn34 ].
    + etransitivity; [ symmetry; exact Hn34 |]; etransitivity; [ symmetry; exact Hy' | exact Hm34 ].
Qed.

End Fixed_GCtx.
