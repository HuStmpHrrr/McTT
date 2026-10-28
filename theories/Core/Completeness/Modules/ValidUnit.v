(** * Valid Units: Properties

    The valid units ([valid_unit]) and module expressions valid in what they
    denote ([valid_modexp]) are defined in [LogicalRelation/Definitions.v]; this file
    proves their properties.  A context has valid slots ([valid_ctx]) exactly
    when it is semantically well formed and each slot holds a unit valid in
    the context before it ([valid_ctx_iff]).  Descriptions are read at
    [Θm ⍮ Ξm], a global context the target one extends. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).

  #[local] Abbreviation valid_unit := (valid_unit Θm Ξm).
  #[local] Abbreviation valid_modexp := (valid_modexp Θm Ξm).

(** The slots of a context (its modules and the module parts of its
    definitions with one, [centry_unit]) hold valid units, each in the
    context before it. *)
Definition valid_slots (Γ : ctx) : Prop :=
  forall Γ1 e U Γ0, Γ = Γ1 ++ e :: Γ0 -> centry_unit e = Some U -> valid_unit Γ0 (me_lit U).

(** A context with valid slots is a semantically well-formed one whose
    slots hold valid units. *)
Lemma valid_ctx_iff : forall Γ, valid_ctx Θm Ξm Γ <-> ⊨ Γ /\ valid_slots Γ.
Proof.
  induction Γ as [| e Γ IH]; split.
  - intros _; split; [ constructor | intros Γ1 e U Γ0 H; destruct Γ1; discriminate ].
  - intros _; constructor.
  - intros H; inversion H; subst; (split; [ assumption |]);
      intros [| e1 Γ1] e0 U0 Γ0 Heq Hu; cbn in Heq; inversion Heq; subst; cbn in Hu;
      first [ discriminate | injection Hu as <-; assumption
            | eapply (proj2 (proj1 IH ltac:(assumption))); [ reflexivity | exact Hu ] ].
  - intros [H Hok]; destruct e as [A | A M | U | A M U]; inversion H; subst.
    + apply valid_ctx_ass; [ apply IH; split; [ assumption |] | assumption ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_ass A :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_def; [ apply IH; split; [ assumption |] | assumption ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_def A M :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_mod; [ apply IH; split; [ assumption |] | assumption | exact (Hok nil _ U Γ eq_refl eq_refl) ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_mod U :: Γ1) e0 U0 Γ0 eq_refl Hu).
    + apply valid_ctx_dm; [ apply IH; split; [ assumption |] | assumption | exact (Hok nil _ U Γ eq_refl eq_refl) ].
      intros Γ1 e0 U0 Γ0 -> Hu; exact (Hok (ce_dm A M U :: Γ1) e0 U0 Γ0 eq_refl Hu).
Qed.

Lemma valid_unit_ctx_wf : forall Γ K, valid_unit Γ K -> ⊨ Γ.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_unit_wf : forall Γ K, valid_unit Γ K -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ K ≈ K.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_modexp_wf : forall Γ H, valid_modexp Γ H -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * H; destruct H; assumption. Qed.

Lemma valid_modexp_rel : forall Γ H, valid_modexp Γ H -> Γ ⊨ᵐ H ≈ H.
Proof.
  intros * Hs; destruct Hs as [Γ H R Rm K RK _ _ _ HHK _ _ _].
  eapply rel_modexp_under_ctx_trans; [ exact HHK | apply rel_modexp_under_ctx_sym; exact HHK ].
Qed.

(** ** Instances of Valid Terms *)

Lemma valid_inst : forall Δ M A D τ RD, Δ ⊨ M : A -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ ⟧s ρ ↘ ρτ ->
    exists m1 m2 a i R, ⟦ M[τ] ⟧ ρ ↘ m1 /\ ⟦ M ⟧ ρτ ↘ m2 /\ ⟦ A ⟧ ρτ ↘ a /\ per_univ_elem i R a a /\ R m1 m2.
Proof.
  intros * [RΔ HΔ i Hgen] Hτ HD ρ ρτ Hρ Hev.
  destruct (Hgen _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [E [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & _)] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 (M12 & _)]]].
  exists m1, m2, a2, i, E; repeat split; try assumption.
  etransitivity; [ symmetry; exact T12 | exact T12 ].
Qed.

Lemma valid_at : forall Δ M A RΔ, Δ ⊨ M : A -> EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    forall ρ ρ', RΔ ρ ρ' ->
    exists m m' a i R, ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ ⟦ A ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m m'.
Proof.
  intros * [RΔ0 HΔ0 i Hgen] HΔ ρ ρ' Hρ.
  destruct (Hgen _ _ HΔ _ _ (rel_sub_id (ex_intro _ _ HΔ)) _ _ _ _ Hρ (eval_sub_id _) (eval_sub_id _))
    as [E [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & _)] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 (_ & M23 & _)]]].
  exists m2, m3, a2, i, E; repeat split; try assumption.
  etransitivity; [ exact T23 | symmetry; exact T23 ].
Qed.

Lemma valid_typ_inst : forall Δ A i D τ RD, Δ ⊨ A : Typeω@i -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ ⟧s ρ ↘ ρτ ->
    exists a1 a2, ⟦ A[τ] ⟧ ρ ↘ a1 /\ ⟦ A ⟧ ρτ ↘ a2 /\ Dom a1 ≈ a2 ∈ per_univ i.
Proof.
  intros * HA Hτ HD ρ ρτ Hρ Hev.
  pose proof (rel_exp_of_typ_inversion HA) as [R0 [HΔ0 HAgen]].
  destruct (HAgen _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & _)].
  exists a1, a2; repeat split; assumption.
Qed.

Lemma valid_mod_inst : forall Δ H D τ RD, Δ ⊨ᵐ H ≈ H -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ ⟧s ρ ↘ ρτ ->
    exists h1 h2, ⟦ H[τ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ h1 /\ ⟦ H ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρτ ↘ h2 /\ per_dmod h1 h2.
Proof.
  intros * [R0 HΔ0 HH] Hτ HD ρ ρτ Hρ Hev.
  destruct (HH _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & _)].
  exists h1, h2; repeat split; assumption.
Qed.

Lemma valid_exp_under_ctx_ctx_fn : forall Ψ D M X, tele_ass Ψ -> ⊨ Ψ ++ D -> Ψ ++ D ⊨ M : X ->
    D ⊨ ctx_fn Ψ M : ctx_pi Ψ X.
Proof.
  induction Ψ as [| e Ψ IH]; intros * HΨ HC HM; cbn in *; [ exact HM |].
  inversion HΨ as [| ? ? [B ->] HΨ']; subst.
  destruct (rel_ctx_wf_ass_inv HC) as [k HB].
  apply IH; [ exact HΨ' | exact (rel_ctx_wf_tail HC) |].
  eapply rel_exp_under_ctx_fn_cong; [ exact HB | exact HM ].
Qed.

(** ** A Body Filled in, Against its Environment

    The substitution filling in the entries of a body without opens is
    built from valid parts, and at an environment of the context it
    extends evaluates to one related to the environment the body makes
    there. *)

Lemma fill_gsub : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D ->
    gsub D σ (body_ctx Φ ++ D).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC; cbn in Hn, Hf; [| | discriminate ].
  - injection Hf as <-; constructor; exact HC.
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | ? ? ? ? | ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC.
    + destruct (rel_ctx_wf_def_inv HC) as [[i HA] HM].
      eapply gsub_def; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) ] | exact HA | exact HM ].
    + eapply gsub_mod; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) ] | exact (rel_ctx_wf_mod_inv HC) ].
    + destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HU).
      eapply gsub_dm; [ apply IH; [ exact Hn | reflexivity | exact (rel_ctx_wf_tail HC) ] | exact HA | exact HM | exact HU ].
Qed.

Lemma fill_rel : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ, RD ρ ρ -> exists ρσ ρ1, ⟦ σ ⟧s ρ ↘ ρσ /\ ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ R ρσ ρ1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC R RD HD HR ρ Hρ; cbn in Hn, Hf; [| | discriminate ].
  - injection Hf as <-.
    assert (E : R <~> RD) by (eapply per_ctx_env_right_irrel; eassumption).
    exists ρ, ρ; split; [ apply eval_sub_id | split; [ constructor | apply E, Hρ ] ].
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | pv A M [Δy Dy] | ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC, HR.
    + (* a definition: its filled-in body at the environment, against its value in the body's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_def_inv HC) as [[i HA] HM].
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0)) as Hτ.
      destruct (valid_inst _ _ _ _ _ _ HM Hτ HD _ _ Hρ Hσ0) as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (valid_at _ _ _ _ HM HR0 _ _ H0) as (m2' & m3 & a2' & j' & Ra' & Hm2' & Hm3 & Ha2' & HRa' & Hm23).
      functional_eval_rewrite_clear.
      pose proof (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ H0) as Htyp.
      destruct Htyp as (x & x' & Hx & Hx' & [Rx Hxx]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa Hxx) as E1.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa' Hxx) as E2.
      assert (HPx : PER Rx) by (eapply per_elem_PER; exact Hxx).
      apply E1 in Hm12; apply E2 in Hm23.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      pose proof (per_ctx_env_of_def HR0 HA HM) as HR'.
      assert (EQ : R <~> per_env_extend_def A M R0) by (eapply per_ctx_env_right_irrel; eassumption).
      exists (ρσ0 ↦ m1), (ρ10 ↦ m3); split; [ apply eval_sub_extend; assumption |].
      split; [ econstructor; eassumption |].
      apply EQ.
      eapply per_env_extend_def_intro; [ exact HP0 | | | exact H0 | | exact Hm2 | ].
      * intros r r' Hr; destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ Hr) as (z & z' & Hz & Hz' & Hzz); eauto.
      * intros r r' Hr; destruct (rel_exp_under_ctx_simple_at HR0 HM _ _ Hr) as (z & z' & Hz & Hz' & Hzz); eauto.
      * eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | etransitivity; eassumption ].
      * eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | symmetry; exact Hm12 ].
    + (* a submodule: the closure of its filled-in unit, against its closure in the body's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC)) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      pose proof (per_ctx_env_of_mod HR0 HU) as HR'.
      assert (EQ : R <~> env_ext_mod U U R0) by (eapply per_ctx_env_right_irrel; eassumption).
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Hρ Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      destruct (unit_chain_at HU HR0 _ _ H0) as [k2 k3 Hk2 Hk3 K23].
      pose proof (functional_eval_modexp _ _ _ _ Hg2 Hk2) as <-.
      destruct U as [Δy Dy].
      exists (ρσ0 ↦ᵐ g1), (ρ10 ↦ᵐ k3).
      split; [ apply eval_sub_extend_mod; [ exact Hσ0 | exact Hg1 ] |].
      split; [ econstructor; [ exact Hb0 | apply eval_me_lit_iff; exact Hk3 ] |].
      apply EQ.
      assert (K33 : per_dmod k3 k3) by (etransitivity; [ symmetry; exact K23 | exact K23 ]).
      unfold extend_env_mod, env_mod; cbn [drop_env tl nth_error env_entry hd].
      repeat split; try assumption;
        solve [ exists g2; split; [ exact Hg2 | exact G12 ] | exists k3; split; [ exact Hk3 | exact K33 ] ].
    + (* a definition with a module part: its term as a definition's, its
         unit as a submodule's *)
      pose proof (rel_ctx_wf_tail HC) as HC0.
      destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HUv).
      pose proof (rel_unit_under_ctx_lit _ _ _ HUv) as HU.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0)) as Hτ.
      destruct (valid_inst _ _ _ _ _ _ HM Hτ HD _ _ Hρ Hσ0) as (m1 & m2 & a2 & j & Ra & Hm1 & Hm2 & Ha2 & HRa & Hm12).
      destruct (valid_at _ _ _ _ HM HR0 _ _ H0) as (m2' & m3 & a2' & j' & Ra' & Hm2' & Hm3 & Ha2' & HRa' & Hm23).
      functional_eval_rewrite_clear.
      pose proof (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ H0) as Htyp.
      destruct Htyp as (x & x' & Hx & Hx' & [Rx Hxx]).
      functional_eval_rewrite_clear.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa Hxx) as E1.
      pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa' Hxx) as E2.
      assert (HPx : PER Rx) by (eapply per_elem_PER; exact Hxx).
      apply E1 in Hm12; apply E2 in Hm23.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      assert (Hdef : per_env_extend_def A M R0 (ρσ0 ↦ m1) (ρ10 ↦ m3)).
      { eapply per_env_extend_def_intro; [ exact HP0 | | | exact H0 | | exact Hm2 | ].
        - intros r r' Hr; destruct (rel_exp_of_typ_inversion_simple_at HR0 HA _ _ Hr) as (z & z' & Hz & Hz' & Hzz); eauto.
        - intros r r' Hr; destruct (rel_exp_under_ctx_simple_at HR0 HM _ _ Hr) as (z & z' & Hz & Hz' & Hzz); eauto.
        - eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | etransitivity; eassumption ].
        - eapply per_head_of; [ exact Ha2 | exact Hx' | exact Hxx | symmetry; exact Hm12 ]. }
      destruct (unit_sub_chain HD Hτ HU _ _ _ _ Hρ Hσ0 Hσ0) as ([g1 g2 Hg1 Hg2 G12] & _).
      destruct (unit_chain_at HU HR0 _ _ H0) as [k2 k3 Hk2 Hk3 K23].
      pose proof (functional_eval_modexp _ _ _ _ Hg2 Hk2) as <-.
      assert (EQ : R <~> per_env_extend_dm A M (gu_mk Δy Dy) R0)
        by (eapply per_ctx_env_right_irrel; [ exact HR | exact (per_ctx_env_of_dm HR0 HA HM HU) ]).
      exists (de_dm m1 g1 :: ρσ0), (de_dm m3 k3 :: ρ10).
      split; [ intros [| x0]; [ exists m1, g1; repeat split; assumption | exact (Hσ0 x0) ] |].
      split; [ econstructor; [ exact Hb0 | exact Hm3 | apply eval_me_lit_iff; exact Hk3 ] |].
      apply EQ.
      assert (K33 : per_dmod k3 k3) by (etransitivity; [ symmetry; exact K23 | exact K23 ]).
      destruct Hdef as [[Hd1 Hd2] Hd3 Hd4].
      constructor; [ constructor; [ split; assumption | exact Hd3 | exact Hd4 ] | |];
        unfold env_mod; cbn [drop_env tl env_entry hd];
        solve [ exists g2; split; [ exact Hg2 | exact G12 ] | exists k3; split; [ exact Hk3 | exact K33 ] ].
Qed.

(** A body without opens that can be filled in evaluates at every
    environment of its context, to one of the context it makes. *)
Lemma benv_exists : forall Φ D, gm_nopens Φ = 0 -> gm_fill Φ <> None -> ⊨ body_ctx Φ ++ D ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ, RD ρ ρ -> exists ρ1, ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ R ρ1 ρ1.
Proof.
  intros * Hn Hf HC R RD HD HR ρ Hρ.
  destruct (gm_fill Φ) as [σ |] eqn:Ef; [| congruence ].
  destruct (fill_rel _ _ _ Hn Ef HC _ _ HD HR _ Hρ) as (ρσ & ρ1 & _ & Hb & H1).
  assert (HP : PER R) by (eapply per_env_PER; exact HR).
  exists ρ1; split; [ exact Hb | etransitivity; [ symmetry; exact H1 | exact H1 ] ].
Qed.

(** An environment of a context extended by parameters, extending a given
    one of the context by arguments. *)
Lemma params_env : forall Δ Γ RΓ R, tele_ass Δ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EF Δ ++ Γ ≈ Δ ++ Γ ∈ per_ctx_env ↘ R ->
    forall ρ, RΓ ρ ρ -> exists args, List.length args = List.length Δ /\ R (env_args ρ args) (env_args ρ args).
Proof.
  induction Δ as [| e Δ IH] using rev_ind; intros * HΔ HΓ HR ρ Hρ; cbn [List.app] in *.
  - exists nil; split; [ reflexivity |].
    assert (E : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption); apply E, Hρ.
  - destruct (tele_ass_app_inv _ _ HΔ) as [HΔ0 He]; inversion He as [| ? ? [A ->] _]; subst.
    rewrite <- app_assoc in HR; cbn [List.app] in HR.
    destruct (per_ctx_env_app_tail Δ Δ _ _ _ eq_refl HR) as [R1 HR1].
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HE).
    destruct (Hhead _ _ Hρ) as [a a' Ha Ha' HRa].
    assert (Hρc : R1 (ρ ↦ ⇑! a 0) (ρ ↦ ⇑! a 0)).
    { apply HE; exists Hρ; cbn.
      pose proof (functional_eval_exp _ _ _ _ Ha Ha') as <-.
      exact (var_per_elem 0 HRa). }
    destruct (IH _ _ _ HΔ0 HR1 HR _ Hρc) as (args & Hl & Hargs).
    exists (⇑! a 0 :: args); split; [ rewrite length_app; cbn; lia | exact Hargs ].
Qed.

(** ** Kinds of Valid Module Values *)

Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

Lemma kshape_sym : forall ρ ρ', kshape gc_deps gc_stack ρ ρ' -> kshape gc_deps gc_stack ρ' ρ.
Proof. intros * [K S]; split; [ intros x; apply kinds_equiv_sym, K | intros x; symmetry; apply S ]. Qed.

Lemma kshape_trans : forall ρ1 ρ2 ρ3, kshape gc_deps gc_stack ρ1 ρ2 -> kshape gc_deps gc_stack ρ2 ρ3 ->
    kshape gc_deps gc_stack ρ1 ρ3.
Proof.
  intros * [K1 S1] [K2 S2]; split; [ intros x; eapply kinds_equiv_trans; [ apply K1 | apply K2 ] | intros x; rewrite S1; apply S2 ].
Qed.

(** A module value related to itself is a module. *)
Lemma per_dmod_nil_kind_all :
  (forall h h', per_dmod h h' -> dmod_member_kind gc_deps gc_stack h nil member_kind_mod) /\
  (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> True) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> True).
Proof.
  apply per_dmod_mut_ind_all; intros; try exact I.
  - apply dmod_member_kind_global_here_mod; unfold gc_loc in *; destruct (gc_frame _ _) eqn:Hfr;
      [ right; eauto | left; destruct (gc_body_module _ _ _ _ _ ltac:(eassumption)); eauto ].
  - apply dmod_member_kind_local, gunit_member_kind_self.
  - match goal with Hu : per_univ_elem _ _ _ _, E1 : forall c c', _ -> exists hc, eval_appm _ _ h c hc,
                    E2 : forall c c', _ -> exists hc', eval_appm _ _ h' c' hc',
                    IH : forall c c' hc hc', _ -> eval_appm _ _ h c hc -> eval_appm _ _ h' c' hc' -> dmod_member_kind _ _ hc _ _ |- _ =>
      destruct (E1 _ _ (var_per_elem 0 Hu)) as (hc & Hc); destruct (E2 _ _ (var_per_elem 0 Hu)) as (hc' & Hc');
      apply (kind_eval_appm _ _ _ _ _ Hc); exact (IH _ _ _ _ (var_per_elem 0 Hu) Hc Hc') end.
Qed.

Corollary per_dmod_nil_kind : forall h h', per_dmod h h' -> dmod_member_kind gc_deps gc_stack h nil member_kind_mod.
Proof. exact (proj1 per_dmod_nil_kind_all). Qed.

(** A valid module expression is a module, at every environment of its
    context. *)
Lemma valid_nil_kind : forall Γ E RΓ, Γ ⊨ᵐ E ≈ E -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ, RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ E nil member_kind_mod.
Proof.
  intros * HE HΓ ρ Hρ.
  destruct (rel_modexp_at _ _ _ _ _ HE HΓ _ _ Hρ) as (h & h' & Hh & _ & Hr).
  apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_nil_kind _ _ Hr).
Qed.

(** ** Bodies Read by Kinds

    Kinds read a body as its expansion, but for the types of the
    definitions an open generates, which they leave out ([body_eq_upto_types]). *)

(** The kind of what a description describes: a term, a module, or a
    member with a term part and a module part. *)
Definition mdesc_kind (R : mdesc) : member_kind :=
  match R with
  | mdesc_term _ _ => member_kind_term
  | mdesc_dm _ _ _ _ => member_kind_dm
  | _ => member_kind_mod
  end.

Lemma mdesc_kind_up : forall Θ' R, mdesc_kind (mdesc_up Θ' R) = mdesc_kind R.
Proof. intros Θ' R; induction R; cbn; auto. Qed.

Lemma mdesc_kind_sub : forall R σ, mdesc_kind (mdesc_sub R σ) = mdesc_kind R.
Proof. intros R σ; revert σ; induction R; intros; cbn; auto. Qed.

Lemma mdesc_kind_named : forall Θ' Ns M R, mdesc_kind (mdesc_named Θ' Ns M R) = mdesc_kind R.
Proof.
  intros; apply (mdesc_named_cases (fun R' => mdesc_kind R' = mdesc_kind R)); [ reflexivity |].
  destruct R as [? [] | | |]; reflexivity.
Qed.

(** Two definitions with a module part the same but for their types.  A
    variant rather than a record: its fields are data, which a [Prop]
    record cannot project. *)
Variant def_mod_eq_upto_type (Ek Ex : gentry) : Prop :=
| mk_def_mod_eq_upto_type :
    forall (pv : bool) (** the privacy of both *)
           (A : typ) (** the type of the first *)
           (A' : typ) (** the type of the second *)
           (M : exp) (** the term of both *)
           (U : gunit) (** the unit of both *),
    Ek = ge_def_mod pv A M U -> Ex = ge_def_mod pv A' M U -> def_mod_eq_upto_type Ek Ex.

(** Two entries the same but for the type of a definition, with or without
    a module part. *)
Definition entry_eq_upto_type (Ek Ex : gentry) : Prop :=
  Ek = Ex \/ (exists b pv A A' M, Ek = ge_def b pv A (Some M) /\ Ex = ge_def b pv A' (Some M)) \/
  def_mod_eq_upto_type Ek Ex.

Fixpoint body_eq_upto_types (Φk Φx : gmod) : Prop :=
  match Φk, Φx with
  | gm_nil, gm_nil => True
  | gm_ext Φk y Ek, gm_ext Φx y' Ex => body_eq_upto_types Φk Φx /\ y = y' /\ entry_eq_upto_type Ek Ex
  | _, _ => False
  end.

Lemma body_eq_upto_types_gens : forall gs Φk Φx k, body_eq_upto_types Φk Φx ->
    body_eq_upto_types (gens_append Φk k (List.map generated_item_erase gs)) (gens_append Φx k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ exact Hk |].
  destruct g; cbn [generated_item_erase generated_item_entry gentry_wk]; apply IH; cbn [body_eq_upto_types]; (split; [ exact Hk | split; [ reflexivity |] ]);
    first [ left; reflexivity | right; left; do 5 eexists; split; reflexivity
          | right; right; eapply mk_def_mod_eq_upto_type; reflexivity ].
Qed.

Lemma body_eq_upto_types_benv : forall Φk Φx, body_eq_upto_types Φk Φx -> forall ρ ρ1,
    ⟦ Φk ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 <-> ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk ρ ρ1; cbn [body_eq_upto_types] in Hk; try contradiction; [ reflexivity |].
  destruct Hk as (Hk & <- & [<- | [(b & pv & A & A' & M & -> & ->) | [pv A A' M U -> ->]]]).
  all: split; intros He; inversion He; subst; econstructor; try eassumption; apply (IH _ Hk); assumption.
Qed.

Lemma body_eq_upto_types_kinds_env : forall Φk Φx, body_eq_upto_types Φk Φx -> forall σ σ1,
    kinds_env gc_deps gc_stack σ Φk σ1 <-> kinds_env gc_deps gc_stack σ Φx σ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk σ σ1; cbn [body_eq_upto_types] in Hk; try contradiction; [ reflexivity |].
  destruct Hk as (Hk & <- & [<- | [(b & pv & A & A' & M & -> & ->) | [pv A A' M U -> ->]]]).
  - split; intros He; inversion He; subst; constructor; apply (IH _ Hk); assumption.
  - split; intros He; inversion He; subst;
      [ refine (kinds_env_ext _ _ _ _ _ _ (ge_def b pv A' (Some M)) _) | refine (kinds_env_ext _ _ _ _ _ _ (ge_def b pv A (Some M)) _) ];
      apply (IH _ Hk); assumption.
  - split; intros He; inversion He; subst;
      [ refine (kinds_env_ext _ _ _ _ _ _ (ge_def_mod pv A' M U) _) | refine (kinds_env_ext _ _ _ _ _ _ (ge_def_mod pv A M U) _) ];
      apply (IH _ Hk); assumption.
Qed.

Lemma body_eq_upto_types_kinds_env_exists : forall Φk Φx, body_eq_upto_types Φk Φx -> forall σ, exists σ1, kinds_env gc_deps gc_stack σ Φk σ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk σ; cbn [body_eq_upto_types] in Hk; try contradiction; [ eexists; constructor |].
  destruct (IH _ (proj1 Hk) σ) as (σ1 & H1); eexists; constructor; exact H1.
Qed.

Lemma body_eq_upto_types_prefix : forall Φk Φx, body_eq_upto_types Φk Φx -> forall y Φx' Ex,
    gm_prefix_upto Φx y = Some (gm_ext Φx' y Ex) ->
    exists Φk' Ek, gm_prefix_upto Φk y = Some (gm_ext Φk' y Ek) /\ body_eq_upto_types Φk' Φx' /\ entry_eq_upto_type Ek Ex.
Proof.
  induction Φk as [| Φk IH z Ek | ]; intros [| Φx z' Ex0 | ] Hk y Φx' Ex Hp; cbn [body_eq_upto_types] in Hk; try contradiction;
    cbn [gm_prefix_upto] in Hp |- *; [ discriminate |].
  destruct Hk as (Hk & <- & HE).
  destruct (String.eqb y z) eqn:Ey; [ injection Hp as -> -> -> | exact (IH _ Hk _ _ _ Hp) ].
  apply String.eqb_eq in Ey; subst; do 2 eexists; split; [ reflexivity | split; assumption ].
Qed.

Lemma entry_kind_read : forall T E, entry_kind (ge_read T E) = entry_kind E.
Proof. intros T [| ? [? [[|] ?|?]] | | |]; reflexivity. Qed.

Lemma mdesc_kind_edenote : forall Γ o E R, edenote Θm Ξm Γ o E R -> mdesc_kind R = entry_kind E.
Proof.
  intros * He; inversion He; subst; try reflexivity.
  all: match goal with Hu : udenote _ _ _ _ _ ?R0 |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm; destruct R0 end;
    cbn in *; first [ contradiction | reflexivity ].
Qed.

(** A description with a term part and a module part has no outside
    parameter left: an entry's ([edenote]) is one. *)
Definition mdesc_dm_closed (R : mdesc) : Prop :=
  match R with
  | mdesc_dm Θd _ _ _ => Θd = nil
  | _ => True
  end.

Lemma edenote_dm_closed : forall Γ o E R, edenote Θm Ξm Γ o E R -> mdesc_dm_closed R.
Proof.
  intros * He; inversion He; subst; cbn; try reflexivity; try exact I.
  match goal with Hu : udenote _ _ _ _ _ ?R0 |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm; destruct R0 end;
    cbn in *; first [ contradiction | exact I ].
Qed.

(** Not a description with a term part and a module part: one stays so at
    arguments, with its kind. *)
Definition mdesc_not_dm (R : mdesc) : Prop :=
  match R with
  | mdesc_dm _ _ _ _ => False
  | _ => True
  end.

Lemma mdesc_kind_at : forall R N R', mdesc_not_dm R -> mdesc_at R N = Some R' -> mdesc_not_dm R' /\ mdesc_kind R' = mdesc_kind R.
Proof.
  intros R N; destruct R as [| | | Θd A M Rm]; intros R' Hn E1; cbn in E1, Hn; [| | | contradiction ].
  all: repeat match type of E1 with
         | match ?s with _ => _ end = _ => destruct s; try discriminate
         end;
       injection E1 as <-; split; first [ exact I | reflexivity ].
Qed.

Lemma mdesc_kind_ats : forall Ns R R', mdesc_not_dm R -> mdesc_ats R Ns = Some R' -> mdesc_kind R' = mdesc_kind R.
Proof.
  induction Ns as [| N Ns IH]; intros * Hn Ha; cbn in Ha; [ injection Ha as <-; reflexivity |].
  destruct (mdesc_at R N) as [R1 |] eqn:E1; [| discriminate ].
  destruct (mdesc_kind_at _ _ _ Hn E1) as [Hn1 E].
  rewrite (IH _ _ Hn1 Ha); exact E.
Qed.

Lemma mdesc_kind_ats_read : forall Ns R R', mdesc_dm_closed R -> mdesc_ats_read R Ns = Some R' -> mdesc_kind R' = mdesc_kind R.
Proof.
  intros Ns [| | | Θd A M Rm] R' Hc Ha; cbn in Hc.
  4: { subst Θd; cbn in Ha; mdesc_dm_read_shape Ha; reflexivity. }
  all: apply (mdesc_kind_ats Ns); [ exact I | exact Ha ].
Qed.

Lemma mdesc_kind_read : forall rd R R', mdesc_dm_closed R -> mdesc_read rd R = Some R' -> mdesc_kind R' = mdesc_kind R.
Proof.
  intros [Δ Φ' | Θ' Ns M] * Hc Hr; cbn in Hr.
  - destruct (gm_fill Φ'); cbn in Hr; [ injection Hr as <- | discriminate ]; rewrite mdesc_kind_up, mdesc_kind_sub; reflexivity.
  - destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite mdesc_kind_up, mdesc_kind_named; exact (mdesc_kind_ats_read _ _ _ Hc Ha).
Qed.

(** What a member of a module expression denotes has the kind its value
    gives the name: an entry of the module part, or a unit or open frame
    the member names, of any kind. *)
Record kinds_ok (Γ : ctx) (H : modexp) : Prop := mk_kinds_ok
  { (** An entry of the module part has its entry's kind *)
    kinds_ok_entry : forall R Rm x Γy E rd, mdenote Θm Ξm Γ H R -> mdesc_mod R = Some Rm -> mdesc_entry Rm x = Some (Γy, E, rd) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) (entry_kind E)
    (** A unit the member names is a module *)
  ; kinds_ok_unit : forall x, (exists TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod
    (** The open frame of an inductive or a record type's module the member
        names is a member with a term part and a module part *)
  ; kinds_ok_frame : forall x, (exists p r, mod_qname (me_mem H x) = Some p /\ gs_find_ind Ξm p = Some r) \/
      (exists p Rr, mod_qname (me_mem H x) = Some p /\ gs_find_record Ξm p = Some Rr) ->
      forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm }.

Lemma kinds_ok_mem : forall Γ H x R, kinds_ok Γ H -> mdenote Θm Ξm Γ (me_mem H x) R ->
    forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> modexp_member_kind gc_deps gc_stack ρ H (x :: nil) (mdesc_kind R).
Proof.
  intros * [Ke Ku Kf] Hm RΓ ρ HΓ Hρ.
  inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr
                  | ? ? ? Rr ? ? Hq Hk]; subst.
  - exact (Ku _ (ex_intro _ _ Hu) _ _ HΓ Hρ).
  - exact (Kf _ (or_introl (ex_intro _ _ (ex_intro _ _ (conj Hq Hk)))) _ _ HΓ Hρ).
  - rewrite (mdesc_kind_read _ _ _ (edenote_dm_closed _ _ _ _ Hed) Hr), (mdesc_kind_edenote _ _ _ _ Hed);
      exact (Ke _ _ _ _ _ _ Hm0 Hmd He _ _ HΓ Hρ).
  - exact (Kf _ (or_intror (ex_intro _ _ (ex_intro _ _ (conj Hq Hk)))) _ _ HΓ Hρ).
Qed.

Lemma items_kinds_items_gen : forall Γ H its gs, items_gen Θm Ξm Γ H its gs -> kinds_ok Γ H ->
    forall RΓ ρ σ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> kshape gc_deps gc_stack ρ σ ->
    kinds_items_gen gc_deps gc_stack σ H its (List.map generated_item_erase gs).
Proof.
  intros * Hg Hk RΓ ρ σ HΓ Hρ Hs.
  induction Hg; cbn [List.map generated_item_erase].
  - constructor.
  - constructor; auto.
  - constructor; [| auto ].
    apply (modexp_member_kind_id _ _ _ _ (proj1 Hs)); exact (kinds_ok_mem _ _ _ _ Hk H0 _ _ HΓ Hρ).
  - constructor; [| auto ].
    apply (modexp_member_kind_id _ _ _ _ (proj1 Hs)).
    replace member_kind_mod with (mdesc_kind R) by (destruct R; cbn in H1 |- *; first [ contradiction | reflexivity ]).
    exact (kinds_ok_mem _ _ _ _ Hk H0 _ _ HΓ Hρ).
  - (* a member with a term part and a module part *)
    apply kinds_items_gen_dm; [| auto ].
    apply (modexp_member_kind_id _ _ _ _ (proj1 Hs)).
    replace member_kind_dm with (mdesc_kind R) by (destruct R; cbn in H1, H2 |- *; first [ discriminate | reflexivity ]).
    exact (kinds_ok_mem _ _ _ _ Hk H0 _ _ HΓ Hρ).
Qed.

(** A valid body with valid open targets is read by kinds, at an
    environment with the kinds of one of its context. *)
Lemma kinds_body_xp_exists : forall C Φ Φx, body_xp Θm Ξm C Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ C ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> kinds_ok (Ψ ++ C) H) ->
    forall RC ρ σ, EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρ ρ -> kshape gc_deps gc_stack ρ σ ->
    exists Φk, kinds_body_xp gc_deps gc_stack σ Φ Φk /\ body_eq_upto_types Φk Φx.
Proof.
  intros * Hx; induction Hx as [Γ | Γ Φ Φx x E Hx IH | Γ Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok];
    intros Hsh HC Ho RC ρ σ HRC Hρ Hs.
  - exists gm_nil; split; [ constructor | exact I ].
  - cbn [body_shape] in Hsh.
    destruct (IH (proj1 Hsh) ltac:(destruct E as [? ? ? [] | | | |]; exact (rel_ctx_wf_tail HC))
                ltac:(intros k Ψ H0 Hk; apply (Ho k); cbn [body_opens gm_dropn]; exact Hk) _ _ _ HRC Hρ Hs)
      as (Φk & Hb & Hk).
    exists (gm_ext Φk x E); split; [ constructor; exact Hb | split; [ exact Hk | split; [ reflexivity | left; reflexivity ] ] ].
  - pose proof (items_gen_length _ _ _ _ _ _ Hg) as Hl.
    assert (Eo : body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx).
    { cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. }
    rewrite Eo in Ho.
    pose proof (body_shape_gens_l _ _ _ Hsh) as Hsh0.
    rewrite gens_body_ctx_base, <- app_assoc in HC.
    pose proof (rel_ctx_wf_app_r _ _ HC) as HC0.
    destruct (IH Hsh0 HC0 (fun k => Ho (S k)) _ _ _ HRC Hρ Hs) as (Φk & Hb & Hk).
    destruct (body_eq_upto_types_kinds_env_exists _ _ Hk σ) as (σ1 & Hσ1).
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R1 HR1].
    destruct (benv_exists _ _ (body_xp_nopens _ _ _ _ _ Hx) (proj1 (body_shape_fill _ _ (body_xp_nopens _ _ _ _ _ Hx) Hsh0))
                HC0 _ _ HRC HR1 _ Hρ) as (ρ1 & Hb1 & Hρ1).
    destruct (kind_eval_benv _ _ _ _ _ Hb1 _ Hs) as (σ' & Hk' & Hs').
    apply (body_eq_upto_types_kinds_env _ _ Hk) in Hσ1.
    pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσ1 _ Hk') as <-.
    apply (body_eq_upto_types_kinds_env _ _ Hk) in Hσ1.
    exists (gens_append Φk 0 (List.map generated_item_erase gs)); split; [| exact (body_eq_upto_types_gens _ _ _ _ Hk) ].
    econstructor; [ exact Hb | exact Hσ1 |].
    exact (items_kinds_items_gen _ _ _ _ Hg (Ho 0 _ _ eq_refl) _ _ _ HR1 Hρ1 Hs').
Qed.

(** ** Valid Global Modules

    What the filed modules and open frames of [Θm ⍮ Ξm] are worth at the
    target ([valid_filed_mods], in [LogicalRelation/Definitions.v]). *)

Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
Hypothesis Hgf : valid_filed_mods Θm Ξm.
Hypothesis Hsb : gc_sub Θm Ξm gc_deps gc_stack.

Lemma modexp_member_kind_apps : forall Ns H ρ ch k, modexp_member_kind gc_deps gc_stack ρ (me_apps H Ns) ch k <-> modexp_member_kind gc_deps gc_stack ρ H ch k.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn [me_apps]; [ reflexivity |].
  rewrite IH; apply modexp_member_kind_app_iff.
Qed.

(** An open frame a member names is a module, unless it is the module of
    a member with a term part. *)
Lemma frame_kind : forall H x p TΦ, mod_qname (me_mem H x) = Some p -> gc_frame Ξm p = Some TΦ ->
    ~ dm_path gc_deps gc_stack p ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod.
Proof.
  intros * Hq Hf Hdm ρ.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hf.
  assert (Ht : exists U T0, gs_find_tele Ξm (qname_in mq x) = Some (U, nil, T0)).
  { unfold gc_frame in Hf; destruct (gs_find_tele Ξm (qname_in mq x)) as [[[U [| ? ?]] T0] |];
      try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
  destruct Ht as (U & T0 & Ht).
  destruct (frame_parent _ _ Hgm _ _ _ _ Ht) as (T1 & Φ1 & Hf1 & _).
  assert (Hgl0 : gc_loc Θm Ξm mq = Some (T1, Φ1)) by (unfold gc_loc; rewrite Hf1; reflexivity).
  assert (Hgl : gc_loc Θm Ξm (qname_in mq x) = Some TΦ) by (unfold gc_loc; rewrite Hf; reflexivity).
  destruct (Hgf _ _ _ Hgl0) as [_ Hp _ _ _ _ Hsub _ _ _ _].
  rewrite (mod_qname_inv _ _ Hq0).
  apply (kind_eval_modexp _ _ _ _ _ (Hp ρ)), (Hsub x TΦ); [ exact Hgl | exact Hdm ].
Qed.

(** A unit a member names is an open frame, so a module. *)
Lemma gunit_kind : forall H x TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_mod.
Proof.
  intros * Hu ρ; destruct TΦ as [T' Φ'].
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & Hc & _)]).
  - apply (frame_kind _ _ _ _ Hq Hf).
    exact (frame_not_dm_sub _ _ _ _ _ _ _ Hsb Hf (gc_unit_not_ind _ _ _ _ _ _ Hq Hu) (gc_unit_not_record _ _ _ _ _ _ Hq Hu)).
  - exfalso; cbn in Hq; destruct (mod_qname H) as [mq |]; [| discriminate ]; injection Hq as <-.
    cbn in Hc; destruct (q_chain mq); discriminate.
Qed.

(** An open frame a member names that is the module of a member with a
    term part is that member: one with a term part and a module part. *)
Lemma frame_dm_kind : forall H x p TΦ, mod_qname (me_mem H x) = Some p -> gc_frame Ξm p = Some TΦ ->
    dm_path gc_deps gc_stack p ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hf Hdm ρ.
  cbn in Hq; destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
  change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Hf, Hdm.
  assert (Ht : exists U T0, gs_find_tele Ξm (qname_in mq x) = Some (U, nil, T0)).
  { unfold gc_frame in Hf; destruct (gs_find_tele Ξm (qname_in mq x)) as [[[U [| ? ?]] T0] |];
      try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
  destruct Ht as (U & T0 & Ht).
  destruct (frame_parent _ _ Hgm _ _ _ _ Ht) as (T1 & Φ1 & Hf1 & _).
  assert (Hgl0 : gc_loc Θm Ξm mq = Some (T1, Φ1)) by (unfold gc_loc; rewrite Hf1; reflexivity).
  destruct TΦ as [T Φ].
  assert (Hgl : gc_loc Θm Ξm (qname_in mq x) = Some (T, Φ)) by (unfold gc_loc; rewrite Hf; reflexivity).
  destruct (gc_loc_grow _ _ _ _ Hgw Hsb _ _ _ Hgl) as (Φ2 & Hgl2 & _).
  destruct (Hgf _ _ _ Hgl0) as [_ Hp _ _ _ _ _ _ _ _ _].
  rewrite (mod_qname_inv _ _ Hq0).
  apply (kind_eval_modexp _ _ _ _ _ (Hp ρ)).
  eapply dmod_member_kind_global_here_dm; [ exact Hdm | exact Hgl2 ].
Qed.

(** The open frame of a member's module a member names is that member. *)
Lemma ind_frame_kind : forall H x p r, mod_qname (me_mem H x) = Some p -> gs_find_ind Ξm p = Some r ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hk ρ; destruct r as [[pq k] D].
  destruct (frame_ind_loc _ _ Hgm _ _ _ _ Hk) as (? & ? & T & Φ & ? & _ & Hf & _ & _).
  apply (frame_dm_kind _ _ _ _ Hq Hf).
  left; eexists; exact (gc_sub_frame_ind_field _ _ _ _ Hsb _ _ Hk).
Qed.

(** So is the open frame of a record type's module. *)
Lemma record_frame_kind : forall H x p Rr, mod_qname (me_mem H x) = Some p -> gs_find_record Ξm p = Some Rr ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * Hq Hk ρ.
  destruct (frame_record_loc _ _ Hgm _ _ Hk) as (? & ? & T & Φ & _ & Hf & _).
  apply (frame_dm_kind _ _ _ _ Hq Hf).
  right; left; eexists; exact (gc_sub_frame_record_field _ _ _ _ Hsb _ _ Hk).
Qed.

Lemma frame_member_kind : forall H x,
    (exists p r, mod_qname (me_mem H x) = Some p /\ gs_find_ind Ξm p = Some r) \/
    (exists p Rr, mod_qname (me_mem H x) = Some p /\ gs_find_record Ξm p = Some Rr) ->
    forall ρ, modexp_member_kind gc_deps gc_stack ρ H (x :: nil) member_kind_dm.
Proof.
  intros * [(p & r & Hq & Hk) | (p & Rr & Hq & Hk)] ρ;
    [ exact (ind_frame_kind _ _ _ _ Hq Hk ρ) | exact (record_frame_kind _ _ _ _ Hq Hk ρ) ].
Qed.

Lemma mdesc_entry_up_inv : forall Δ R y Γy E rd, mdesc_entry (mdesc_up Δ R) y = Some (Γy, E, rd) ->
    exists Γy' rd', mdesc_entry R y = Some (Γy', E, rd').
Proof.
  intros * He; destruct R; cbn in He |- *; try discriminate.
  - destruct (gm_prefix_upto _ y) as [[| ? ? [[|] ? ? [] | | | |] | ] |]; try discriminate;
      injection He as <- <- <-; eauto.
  - destruct (gm_prefix_upto _ y) as [[| ? ? E0 | ] |]; try discriminate; injection He as <- <- <-; eauto.
Qed.

Lemma mdesc_entry_open_inv : forall Δ Φ Φx y Γy E rd, mdesc_entry (mdesc_open Δ Φ Φx) y = Some (Γy, E, rd) ->
    exists Φ' E0, gm_prefix_upto Φx y = Some (gm_ext Φ' y E0) /\ entry_kind E = entry_kind E0 /\
      Γy = body_ctx Φ' ++ Δ /\ rd = reader_open Δ Φ'.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  exists Φ', E0; split; [ reflexivity |].
  destruct E0 as [[|] ? ? [] | | | |]; try discriminate; injection He as <- <- <-; repeat split.
Qed.

Lemma mdesc_entry_closed_inv : forall Θ p T Φ Ns y Γy E rd, mdesc_entry (mdesc_closed Θ p T Φ Ns) y = Some (Γy, E, rd) ->
    exists Φ0 E0, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E0) /\ E = ge_read T E0.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φ y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  injection He as _ <- _; eauto.
Qed.

(** A prefix of a body is a tail of its context. *)
Lemma prefix_body_ctx : forall Φ y Φp, gm_nopens Φ = 0 -> gm_prefix_upto Φ y = Some Φp ->
    exists X, body_ctx Φ = X ++ body_ctx Φp.
Proof.
  induction Φ as [| Φ IH z E | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; try discriminate.
  destruct (String.eqb y z); [ injection Hp as <-; exists nil; reflexivity |].
  destruct (IH _ _ Hn Hp) as (X & HX).
  destruct E as [? ? ? [] | | | |]; cbn [body_ctx]; rewrite HX; eexists (_ :: X); reflexivity.
Qed.

Lemma prefix_shape : forall Φ x Φ' E, body_shape Φ Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    body_shape Φ' Φ' /\ entry_shape E E.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its]; intros * Hs Hp; cbn in Hs, Hp; try discriminate.
  - destruct (String.eqb x z); [ injection Hp as <- _ <-; split; [ exact (proj1 Hs) | exact (proj2 (proj2 Hs)) ] |].
    exact (IH _ _ _ (proj1 Hs) Hp).
  - destruct (existsb _ _); [ discriminate | exact (IH _ _ _ (proj1 Hs) Hp) ].
Qed.

Lemma prefix_nopens : forall Φ x Φ', gm_nopens Φ = 0 -> gm_prefix_upto Φ x = Some Φ' -> gm_nopens Φ' = 0.
Proof.
  induction Φ as [| Φ IH z E0 | Φ IH H its]; intros * Hn Hp; cbn in Hn, Hp; try discriminate.
  destruct (String.eqb x z); [ injection Hp as <-; exact Hn | exact (IH _ _ Hn Hp) ].
Qed.

(** ** The Kinds of Valid Units *)

Lemma valid_unit_kinds_all :
  (forall Γ K, valid_unit Γ K -> kinds_ok Γ K) /\ (forall Γ H, valid_modexp Γ H -> kinds_ok Γ H).
Proof.
  apply valid_unit_modexp_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs;
      split; [| intros x [TΦ Hu] RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ)
              | intros x Hx RΓ ρ _ _; exact (frame_member_kind _ _ Hx ρ) ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_closed_inv _ _ _ _ _ _ _ _ _ He) as (Φ0 & E0 & Hp & ->).
    destruct (Hgf _ _ _ Hgl) as [_ Hpe _ _ _ Hk _ _ _ _ _].
    apply modexp_member_kind_apps, (kind_eval_modexp _ _ _ _ _ (Hpe ρ)); rewrite entry_kind_read; exact (Hk _ _ _ Hp).
  - (* a body *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hslots IHslots Hs Hsx HK Hopv Hops IHops.
    split; [| intros x (TΦ & Hu); cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate
            | intros x [(p & r & Hq & _) | (p & r & Hq & _)]; cbn in Hq; discriminate ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
    cbn in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_open_inv _ _ _ _ _ _ _ He) as (Φ' & E0 & Hp & Hek & _ & _).
    rewrite Hek.
    (* an environment of the parameters, and the kinds of the closure there *)
    destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HC)) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kshape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    destruct (kinds_body_xp_exists _ _ _ Hx Hsx HC (fun k Ψ H Hk => proj1 (conj (IHops k Ψ H Hk) I)) _ _ _ HRΔ Hρa Hsa) as (Φk & Hb & Hk).
    apply modexp_member_kind_lit, gunit_member_kind_pad, (gunit_member_kind_kinds_body_xp _ _ _ _ _ Hb).
    destruct (body_eq_upto_types_prefix _ _ Hk _ _ _ Hp) as (Φk' & Ek & Hpk & Hk' & HE).
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    destruct (prefix_shape _ _ _ _ Hsx Hp) as [Hsh' HshE].
    pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn [gm_nopens] in Hn'.
    destruct E0 as [b pv A0 oM | pm U | | pv A0 M0 U | ]; cbn in HshE; try contradiction;
      destruct HE as [-> | [(b' & pv' & A' & A'' & M' & -> & [= -> -> -> ->])
                            | [pv' A' A'' M' U' -> [= -> -> -> ->]]]]; cbn [entry_kind].
    1,2: eapply gunit_member_kind_def; exact Hpk.
    2,3: (* a definition with a module part: [dm_of] its unit's kind, a
            module's, at an environment of its context *)
      destruct (body_eq_upto_types_kinds_env_exists _ _ Hk' (kinds_placeholders (List.length Δ) ρ)) as (σ1 & Hσ1);
      change member_kind_dm with (dm_of member_kind_mod);
      eapply gunit_member_kind_dm_here; [ exact Hpk | exact Hσ1 |];
      destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX);
      rewrite HX, <- app_assoc in HC; pose proof (rel_ctx_wf_app_r _ _ HC) as HC1; cbn [body_ctx app] in HC1;
      pose proof (rel_ctx_wf_tail HC1) as HC0;
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0];
      destruct (benv_exists _ _ Hn' (proj1 (body_shape_fill _ _ Hn' Hsh')) HC0 _ _ HRΔ HR0 _ Hρa) as (ρ1 & Hb1 & Hρ1);
      destruct (kind_eval_benv _ _ _ _ _ Hb1 _ Hsa) as (σ' & Hk1 & Hs1);
      apply (body_eq_upto_types_kinds_env _ _ Hk') in Hσ1;
      pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσ1 _ Hk1) as <-;
      apply (gunit_member_kind_id _ _ _ _ (proj1 (kshape_sym _ _ Hs1))), modexp_member_kind_lit_iff;
      exact (valid_nil_kind _ _ _ (rel_unit_under_ctx_lit _ _ _ (proj2 (proj2 (rel_ctx_wf_dm_inv HC1)))) HR0 _ Hρ1).
    + (* a submodule: a module, at an environment of its context *)
      destruct (body_eq_upto_types_kinds_env_exists _ _ Hk' (kinds_placeholders (List.length Δ) ρ)) as (σ1 & Hσ1).
      eapply gunit_member_kind_mod; [ exact Hpk | exact Hσ1 |].
      destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX).
      rewrite HX, <- app_assoc in HC; pose proof (rel_ctx_wf_app_r _ _ HC) as HC1; cbn [body_ctx app] in HC1.
      pose proof (rel_ctx_wf_tail HC1) as HC0.
      destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0].
      destruct (benv_exists _ _ Hn' (proj1 (body_shape_fill _ _ Hn' Hsh')) HC0 _ _ HRΔ HR0 _ Hρa) as (ρ1 & Hb1 & Hρ1).
      destruct (kind_eval_benv _ _ _ _ _ Hb1 _ Hsa) as (σ' & Hk1 & Hs1).
      apply (body_eq_upto_types_kinds_env _ _ Hk') in Hσ1.
      pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσ1 _ Hk1) as <-.
      apply (gunit_member_kind_id _ _ _ _ (proj1 (kshape_sym _ _ Hs1))), modexp_member_kind_lit_iff.
      exact (valid_nil_kind _ _ _ (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC1)) HR0 _ Hρ1).
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HK HE Hsmt IHE.
    split; [| intros x (TΦ & Hu); cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate
            | intros x [(p & r & Hq & _) | (p & r & Hq & _)]; cbn in Hq; discriminate ].
    intros R Rm x Γy E' rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? E0 RE Rem HmE HmodE]; subst end.
    rewrite (mdesc_is_mod_mod _ (mdesc_is_mod_up _ _ (mdesc_mod_is_mod _ _ HmodE))) in Hmod; injection Hmod as <-.
    destruct (mdesc_entry_up_inv _ _ _ _ _ _ He) as (Γy' & rd' & He').
    destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kshape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    apply modexp_member_kind_lit, gunit_member_kind_alias, (modexp_member_kind_id _ _ _ _ (proj1 Hsa)).
    exact (kinds_ok_entry _ _ IHE _ _ _ _ _ _ HmE HmodE He' _ _ HRΔ Hρa).
  - (* a module expression equal to a valid unit: as the unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK.
    split; [| intros x [TΦ Hu] RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ)
            | intros x Hx RΓ ρ _ _; exact (frame_member_kind _ _ Hx ρ) ].
    intros R' Rm' x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH), HmodH in Hmod; injection Hmod as <-.
    pose proof (kinds_ok_entry _ _ IHK _ _ _ _ _ _ HmK HmodK He _ _ HRΓ Hρ) as Hk.
    destruct (rel_modexp_at _ _ _ _ _ HHK HRΓ _ _ Hρ) as (h & h' & Hh & Hh' & Hr).
    apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_kinds_equiv _ _ Hr), (kind_eval_modexp _ _ _ _ _ Hh'); exact Hk.
Qed.

Corollary valid_unit_kinds : forall Γ K, valid_unit Γ K -> kinds_ok Γ K.
Proof. exact (proj1 valid_unit_kinds_all). Qed.

Corollary valid_modexp_kinds : forall Γ H, valid_modexp Γ H -> kinds_ok Γ H.
Proof. exact (proj2 valid_unit_kinds_all). Qed.

End Fixed_GCtx.
