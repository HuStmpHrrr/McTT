(** * Valid Units

    A unit is semantically valid when its parts are ([semK]): a filed module
    at arguments valid against its telescope ([sargs]); a local body whose
    context, read as its expansion, is valid, whose submodules are valid
    units in the context the body before each makes, and whose opens'
    targets are valid; an alias whose target
    is.  A module expression is valid in what it denotes ([smt]) when it is
    equal, in the PER model, to a valid unit denoting the same module part:
    the semantic counterpart of lookup soundness.  Descriptions are read at
    [Θm ⍮ Ξm], a global context the target one extends. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping GlobalPaths MemberLemmas DescTyping LookupSound.
From Mctt.Core.Completeness Require Import
  LogicalRelation ContextCases FunctionCases UniverseCases SubstitutionCases LetCases UnitCases InstanceCases MemberReps
  ModuleVal ModuleSem.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Variables (Θm : gdeps) (Ξm : gstack).

(** ** Arguments of a Filed Module *)

(** [sargs Γ T Ns]: the arguments [Ns] fill, in order, the outermost
    parameters of the closed telescope [T], each valid in [Γ] at its
    parameter's type instantiated by the arguments before it, as
    [args_ok] says syntactically. *)
Definition sargs (Γ : ctx) (T : ctx) (Ns : list exp) : Prop :=
  exists T1 T2, T = T1 ++ T2 /\ List.length T2 = List.length Ns /\ tele_ass T2 /\ ctx_scoped 0 T2 /\
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts T2 Id Ns) k = Some A -> Γ ⊨ N : A).

(** ** Valid Units *)

Inductive semK : ctx -> modexp -> Prop :=
| sk_filed : forall Γ p T Φ Ns,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc Θm Ξm p = Some (T, Φ) -> ⊨ Γ -> sargs Γ T Ns ->
    semK Γ (me_apps (qname_mod p) Ns)
| sk_body : forall Γ Δ Φ Φx,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> tele_ass Δ -> ⊨ Γ -> ⊨ body_ctx Φx ++ Δ ++ Γ ->
    (forall y Φ0 pv U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y (ge_mod pv U)) ->
       semK (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U)) ->
    body_shape Φ Φ -> body_shape Φx Φx ->
    Γ ⊨ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ Φ) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Ψ ++ Δ ++ Γ ⊨ᵐ H ≈ H) ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> smt (Ψ ++ Δ ++ Γ) H) ->
    semK Γ (me_lit (gu_open Δ Φ))
| sk_alias : forall Γ Δ E,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    tele_ass Δ -> ⊨ Γ -> ⊨ Δ ++ Γ ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ (md_alias E)) ->
    Δ ++ Γ ⊨ᵐ E ≈ E -> smt (Δ ++ Γ) E ->
    semK Γ (me_lit (gu_mk Δ (md_alias E)))
(** [smt Γ H]: [H] is equal to a valid unit that denotes its module part. *)
with smt : ctx -> modexp -> Prop :=
| smt_intro : forall Γ H R Rm K RK,
    Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H ->
    mdenote Θm Ξm Γ H R -> ds_mod Θm Ξm R = Some Rm ->
    Γ ⊨ᵐ H ≈ K -> semK Γ K -> mdenote Θm Ξm Γ K RK -> ds_mod Θm Ξm RK = Some Rm ->
    smt Γ H.

Scheme semK_mut_ind := Induction for semK Sort Prop
with smt_mut_ind := Induction for smt Sort Prop.
Combined Scheme semK_smt_ind from semK_mut_ind, smt_mut_ind.

(** The slots of a context hold valid units, each in the context before it. *)
Definition ctx_ok (Γ : ctx) : Prop := forall Γ1 U Γ0, Γ = Γ1 ++ ce_mod U :: Γ0 -> semK Γ0 (me_lit U).

Lemma semK_ctx : forall Γ K, semK Γ K -> ⊨ Γ.
Proof. intros * H; destruct H; assumption. Qed.

Lemma semK_wf : forall Γ K, semK Γ K -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ K ≈ K.
Proof. intros * H; destruct H; assumption. Qed.

Lemma smt_wf : forall Γ H, smt Γ H -> Θm ⍮ Ξm ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * H; destruct H; assumption. Qed.

Lemma smt_valid : forall Γ H, smt Γ H -> Γ ⊨ᵐ H ≈ H.
Proof.
  intros * Hs; destruct Hs as [Γ H R Rm K RK _ _ _ HHK _ _ _].
  eapply rel_modexp_trans; [ exact HHK | apply rel_modexp_sym; exact HHK ].
Qed.

(** ** Instances of Valid Terms *)

Lemma valid_inst : forall Δ M A D τ RD, Δ ⊨ M : A -> D ⊨ˢ τ ≈ τ : Δ -> EF D ≈ D ∈ per_ctx_env ↘ RD ->
    forall ρ ρτ, RD ρ ρ -> ⟦ τ ⟧s ρ ↘ ρτ ->
    exists m1 m2 a i R, ⟦ M[τ] ⟧ ρ ↘ m1 /\ ⟦ M ⟧ ρτ ↘ m2 /\ ⟦ A ⟧ ρτ ↘ a /\ per_univ_elem i R a a /\ R m1 m2.
Proof.
  intros * [RΔ [HΔ [i Hgen]]] Hτ HD ρ ρτ Hρ Hev.
  destruct (Hgen _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [E [[a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 (T12 & T23 & _)] [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 (M12 & _)]]].
  exists m1, m2, a2, i, E; repeat split; try assumption.
  etransitivity; [ symmetry; exact T12 | exact T12 ].
Qed.

Lemma valid_at : forall Δ M A RΔ, Δ ⊨ M : A -> EF Δ ≈ Δ ∈ per_ctx_env ↘ RΔ ->
    forall ρ ρ', RΔ ρ ρ' ->
    exists m m' a i R, ⟦ M ⟧ ρ ↘ m /\ ⟦ M ⟧ ρ' ↘ m' /\ ⟦ A ⟧ ρ ↘ a /\ per_univ_elem i R a a /\ R m m'.
Proof.
  intros * [RΔ0 [HΔ0 [i Hgen]]] HΔ ρ ρ' Hρ.
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
  intros * [R0 [HΔ0 HH]] Hτ HD ρ ρτ Hρ Hev.
  destruct (HH _ _ HD _ _ Hτ _ _ _ _ Hρ Hev Hev) as [h1 h2 h3 h4 H1 H2 H3 H4 (C12 & _)].
  exists h1, h2; repeat split; assumption.
Qed.

Lemma valid_ctx_fn : forall Ψ D M X, tele_ass Ψ -> ⊨ Ψ ++ D -> Ψ ++ D ⊨ M : X -> D ⊨ ctx_fn Ψ M : ctx_pi Ψ X.
Proof.
  induction Ψ as [| e Ψ IH]; intros * HΨ HC HM; cbn in *; [ exact HM |].
  inversion HΨ as [| ? ? [B ->] HΨ']; subst.
  destruct (sem_ctx_ass_inv HC) as [k HB].
  apply IH; [ exact HΨ' | exact (sem_ctx_tail HC) |].
  eapply rel_exp_fn_cong; [ exact HB | exact HM ].
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
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC.
    + destruct (sem_ctx_def_inv HC) as [[i HA] HM].
      eapply gsub_def; [ apply IH; [ exact Hn | reflexivity | exact (sem_ctx_tail HC) ] | exact HA | exact HM ].
    + eapply gsub_mod; [ apply IH; [ exact Hn | reflexivity | exact (sem_ctx_tail HC) ] | exact (sem_ctx_mod_inv HC) ].
Qed.

Lemma fill_rel : forall Φ D σ, gm_nopens Φ = 0 -> gm_fill Φ = Some σ -> ⊨ body_ctx Φ ++ D ->
    forall R RD, EF D ≈ D ∈ per_ctx_env ↘ RD -> EF body_ctx Φ ++ D ≈ body_ctx Φ ++ D ∈ per_ctx_env ↘ R ->
    forall ρ, RD ρ ρ -> exists ρσ ρ1, ⟦ σ ⟧s ρ ↘ ρσ /\ ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 /\ R ρσ ρ1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hn Hf HC R RD HD HR ρ Hρ; cbn in Hn, Hf; [| | discriminate ].
  - injection Hf as <-.
    assert (E : R <~> RD) by (eapply per_ctx_env_right_irrel; eassumption).
    exists ρ, ρ; split; [ apply eval_sub_id | split; [ constructor | apply E, Hρ ] ].
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | ? ? ? ?]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx app] in HC, HR.
    + (* a definition: its filled-in body at the environment, against its value in the body's *)
      pose proof (sem_ctx_tail HC) as HC0.
      destruct (sem_ctx_def_inv HC) as [[i HA] HM].
      destruct (sem_ctx_per_ctx_env HC0) as [R0 HR0].
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
      pose proof (sem_ctx_tail HC) as HC0.
      pose proof (sem_ctx_mod_inv HC) as HU.
      destruct (sem_ctx_per_ctx_env HC0) as [R0 HR0].
      destruct (IH _ _ Hn eq_refl HC0 _ _ HD HR0 _ Hρ) as (ρσ0 & ρ10 & Hσ0 & Hb0 & H0).
      pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0)) as Hτ.
      assert (HP0 : PER R0) by (eapply per_env_PER; exact HR0).
      pose proof (per_ctx_env_of_mod HR0 (proj1 HU)) as HR'.
      assert (EQ : R <~> env_ext_mod U U R0) by (eapply per_ctx_env_right_irrel; eassumption).
      destruct (unit_sub_chain HD Hτ (proj1 HU) _ _ _ _ Hρ Hσ0 Hσ0) as ((g1 & g2 & Hg1 & Hg2 & G12) & _).
      destruct (unit_chain_at (proj1 HU) HR0 _ _ H0) as (k2 & k3 & Hk2 & Hk3 & K23).
      pose proof (functional_eval_modexp _ _ _ _ Hg2 Hk2) as <-.
      destruct U as [Δy Dy].
      exists (ρσ0 ↦ᵐ g1), (ρ10 ↦ᵐ k3).
      split; [ apply eval_sub_extend_mod; [ exact Hσ0 | exact Hg1 ] |].
      split; [ econstructor; [ exact Hb0 | apply eval_me_lit_iff; exact Hk3 ] |].
      apply EQ.
      assert (K33 : per_dmod k3 k3) by (etransitivity; [ symmetry; exact K23 | exact K23 ]).
      unfold env_ext_mod, extend_env_mod, env_mod; cbn [drop_env tl nth_error env_entry hd].
      repeat split; try assumption;
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
Proof. intros * [K S]; split; [ intros x; apply kequiv_sym, K | intros x; symmetry; apply S ]. Qed.

Lemma kshape_trans : forall ρ1 ρ2 ρ3, kshape gc_deps gc_stack ρ1 ρ2 -> kshape gc_deps gc_stack ρ2 ρ3 ->
    kshape gc_deps gc_stack ρ1 ρ3.
Proof.
  intros * [K1 S1] [K2 S2]; split; [ intros x; eapply kequiv_trans; [ apply K1 | apply K2 ] | intros x; rewrite S1; apply S2 ].
Qed.

(** A module value related to itself is a module. *)
Lemma per_dmod_nil_kind_all :
  (forall h h', per_dmod h h' -> dkind gc_deps gc_stack h nil mk_mod) /\
  (forall ts ρ ρ' args args', per_gargs ts ρ ρ' args args' -> True) /\
  (forall ρ Φ ρ' Φ', per_body ρ Φ ρ' Φ' -> True).
Proof.
  apply per_dmod_mut_ind_all; intros; try exact I.
  - apply dk_global_here_mod; unfold gc_loc in *; destruct (gc_frame _ _) eqn:Hfr;
      [ right; eauto | left; destruct (gc_body_module _ _ _ _ _ ltac:(eassumption)); eauto ].
  - apply dk_local, uk_self.
  - match goal with Hu : per_univ_elem _ _ _ _, E1 : forall c c', _ -> exists hc, eval_appm _ _ h c hc,
                    E2 : forall c c', _ -> exists hc', eval_appm _ _ h' c' hc',
                    IH : forall c c' hc hc', _ -> eval_appm _ _ h c hc -> eval_appm _ _ h' c' hc' -> dkind _ _ hc _ _ |- _ =>
      destruct (E1 _ _ (var_per_elem 0 Hu)) as (hc & Hc); destruct (E2 _ _ (var_per_elem 0 Hu)) as (hc' & Hc');
      apply (kind_eval_appm _ _ _ _ _ Hc); exact (IH _ _ _ _ (var_per_elem 0 Hu) Hc Hc') end.
Qed.

Corollary per_dmod_nil_kind : forall h h', per_dmod h h' -> dkind gc_deps gc_stack h nil mk_mod.
Proof. exact (proj1 per_dmod_nil_kind_all). Qed.

(** A valid module expression is a module, at every environment of its
    context. *)
Lemma valid_nil_kind : forall Γ E RΓ, Γ ⊨ᵐ E ≈ E -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ, RΓ ρ ρ -> skind gc_deps gc_stack ρ E nil mk_mod.
Proof.
  intros * HE HΓ ρ Hρ.
  destruct (rel_modexp_at _ _ _ _ _ HE HΓ _ _ Hρ) as (h & h' & Hh & _ & Hr).
  apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_nil_kind _ _ Hr).
Qed.

(** ** Bodies Read by Kinds

    Kinds read a body as its expansion, but for the types of the
    definitions an open generates, which they leave out ([kx]). *)

Definition kindOf (R : mdesc) : mkind :=
  match R with
  | ds_term _ _ => mk_term
  | _ => mk_mod
  end.

Definition kx_entry (Ek Ex : gentry) : Prop :=
  Ek = Ex \/ exists b pv A A' M, Ek = ge_def b pv A (Some M) /\ Ex = ge_def b pv A' (Some M).

Fixpoint kx (Φk Φx : gmod) : Prop :=
  match Φk, Φx with
  | gm_nil, gm_nil => True
  | gm_ext Φk y Ek, gm_ext Φx y' Ex => kx Φk Φx /\ y = y' /\ kx_entry Ek Ex
  | _, _ => False
  end.

Lemma kx_gens : forall gs Φk Φx k, kx Φk Φx ->
    kx (gens_append Φk k (List.map ig_erase gs)) (gens_append Φx k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ exact Hk |].
  destruct g; cbn [ig_erase ig_entry gentry_wk]; apply IH; cbn [kx]; (split; [ exact Hk | split; [ reflexivity |] ]);
    first [ left; reflexivity | right; do 5 eexists; split; reflexivity ].
Qed.

Lemma kx_benv : forall Φk Φx, kx Φk Φx -> forall ρ ρ1,
    ⟦ Φk ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1 <-> ⟦ Φx ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρ ↘ ρ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk ρ ρ1; cbn [kx] in Hk; try contradiction; [ reflexivity |].
  destruct Hk as (Hk & <- & [<- | (b & pv & A & A' & M & -> & ->)]).
  - split; intros He; inversion He; subst; econstructor; try eassumption; apply (IH _ Hk); assumption.
  - split; intros He; inversion He; subst; econstructor; try eassumption; apply (IH _ Hk); assumption.
Qed.

Lemma kx_kenv : forall Φk Φx, kx Φk Φx -> forall σ σ1,
    kenv gc_deps gc_stack σ Φk σ1 <-> kenv gc_deps gc_stack σ Φx σ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk σ σ1; cbn [kx] in Hk; try contradiction; [ reflexivity |].
  destruct Hk as (Hk & <- & [<- | (b & pv & A & A' & M & -> & ->)]).
  - split; intros He; inversion He; subst; constructor; apply (IH _ Hk); assumption.
  - split; intros He; inversion He; subst;
      [ refine (ke_ext _ _ _ _ _ _ (ge_def b pv A' (Some M)) _) | refine (ke_ext _ _ _ _ _ _ (ge_def b pv A (Some M)) _) ];
      apply (IH _ Hk); assumption.
Qed.

Lemma kx_kenv_exists : forall Φk Φx, kx Φk Φx -> forall σ, exists σ1, kenv gc_deps gc_stack σ Φk σ1.
Proof.
  induction Φk as [| Φk IH y Ek | ]; intros [| Φx y' Ex | ] Hk σ; cbn [kx] in Hk; try contradiction; [ eexists; constructor |].
  destruct (IH _ (proj1 Hk) σ) as (σ1 & H1); eexists; constructor; exact H1.
Qed.

Lemma kx_prefix : forall Φk Φx, kx Φk Φx -> forall y Φx' Ex,
    gm_prefix_upto Φx y = Some (gm_ext Φx' y Ex) ->
    exists Φk' Ek, gm_prefix_upto Φk y = Some (gm_ext Φk' y Ek) /\ kx Φk' Φx' /\ kx_entry Ek Ex.
Proof.
  induction Φk as [| Φk IH z Ek | ]; intros [| Φx z' Ex0 | ] Hk y Φx' Ex Hp; cbn [kx] in Hk; try contradiction;
    cbn [gm_prefix_upto] in Hp |- *; [ discriminate |].
  destruct Hk as (Hk & <- & HE).
  destruct (String.eqb y z) eqn:Ey; [ injection Hp as -> -> -> | exact (IH _ Hk _ _ _ Hp) ].
  apply String.eqb_eq in Ey; subst; do 2 eexists; split; [ reflexivity | split; assumption ].
Qed.

(** The kind of an entry. *)
Definition ent_kind (E : gentry) : mkind :=
  match E with
  | ge_def _ _ _ _ => mk_term
  | _ => mk_mod
  end.

Lemma ent_kind_read : forall T E, ent_kind (ge_read T E) = ent_kind E.
Proof. intros T [| ? [? [[|] ?|?]] | |]; reflexivity. Qed.

Lemma kindOf_edenote : forall Γ o E R, edenote Θm Ξm Γ o E R -> kindOf R = ent_kind E.
Proof.
  intros * He; inversion He; subst; try reflexivity.
  match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm end.
  destruct R; cbn in *; first [ contradiction | reflexivity ].
Qed.

Lemma kindOf_ats : forall Ns R R', ds_ats R Ns = Some R' -> kindOf R' = kindOf R.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha; [ injection Ha as <-; reflexivity |].
  destruct (ds_at R N) as [R1 |] eqn:E1; [| discriminate ].
  rewrite (IH _ _ Ha).
  destruct R; cbn in E1;
    repeat match type of E1 with
           | match ?s with _ => _ end = _ => destruct s; try discriminate
           end;
    injection E1 as <-; reflexivity.
Qed.

Lemma kindOf_read : forall rd R R', ds_read rd R = Some R' -> kindOf R' = kindOf R.
Proof.
  intros [Δ Φ' | Θ' Ns M] * Hr; cbn in Hr.
  - destruct (gm_fill Φ'); cbn in Hr; [ injection Hr as <- | discriminate ]; destruct R; reflexivity.
  - destruct (ds_ats R Ns) as [R1 |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
    rewrite <- (kindOf_ats _ _ _ Ha); destruct Θ', Ns; destruct R1 as [? [] | | |]; reflexivity.
Qed.

(** What a member of a module expression denotes has the kind its value
    gives the name: an entry of the module part, or a unit or open frame
    the member names. *)
Definition kinds_ok (Γ : ctx) (H : modexp) : Prop :=
  (forall R Rm x Γy E rd, mdenote Θm Ξm Γ H R -> ds_mod Θm Ξm R = Some Rm -> ds_entry Rm x = Some (Γy, E, rd) ->
     forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> skind gc_deps gc_stack ρ H (x :: nil) (ent_kind E)) /\
  (forall x TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ ->
     forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> skind gc_deps gc_stack ρ H (x :: nil) mk_mod).

Lemma kinds_ok_mem : forall Γ H x R, kinds_ok Γ H -> mdenote Θm Ξm Γ (me_mem H x) R ->
    forall RΓ ρ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> skind gc_deps gc_stack ρ H (x :: nil) (kindOf R).
Proof.
  intros * [Ke Ku] Hm RΓ ρ HΓ Hρ.
  inversion Hm as [? ? ? ? ? Hq Hu | | | | ? ? ? R0 R0m Γy E rd Re ? Hm0 Hmd He Hed Hr]; subst.
  - exact (Ku _ _ Hu _ _ HΓ Hρ).
  - rewrite (kindOf_read _ _ _ Hr), (kindOf_edenote _ _ _ _ Hed); exact (Ke _ _ _ _ _ _ Hm0 Hmd He _ _ HΓ Hρ).
Qed.

Lemma items_kgens : forall Γ H its gs, items_gen Θm Ξm false Γ H its gs -> kinds_ok Γ H ->
    forall RΓ ρ σ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ -> kshape gc_deps gc_stack ρ σ ->
    kgens gc_deps gc_stack σ H its (List.map ig_erase gs).
Proof.
  intros * Hg Hk RΓ ρ σ HΓ Hρ Hs.
  remember false as io eqn:Eio; induction Hg; subst; try discriminate; cbn [List.map ig_erase].
  - constructor.
  - constructor; auto.
  - constructor; [| auto ].
    apply (skind_id _ _ _ _ (proj1 Hs)); exact (kinds_ok_mem _ _ _ _ Hk H0 _ _ HΓ Hρ).
  - constructor; [| auto ].
    apply (skind_id _ _ _ _ (proj1 Hs)).
    replace mk_mod with (kindOf R) by (destruct R; cbn in H1 |- *; first [ contradiction | reflexivity ]).
    exact (kinds_ok_mem _ _ _ _ Hk H0 _ _ HΓ Hρ).
Qed.

(** A valid body with valid open targets is read by kinds, at an
    environment with the kinds of one of its context. *)
Lemma kbody_exists : forall C Φ Φx, body_xp Θm Ξm C Φ Φx -> body_shape Φx Φx -> ⊨ body_ctx Φx ++ C ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> kinds_ok (Ψ ++ C) H) ->
    forall RC ρ σ, EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρ ρ -> kshape gc_deps gc_stack ρ σ ->
    exists Φk, kbody gc_deps gc_stack σ Φ Φk /\ kx Φk Φx.
Proof.
  intros * Hx; induction Hx as [Γ | Γ Φ Φx x E Hx IH | Γ Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok];
    intros Hsh HC Ho RC ρ σ HRC Hρ Hs.
  - exists gm_nil; split; [ constructor | exact I ].
  - cbn [body_shape] in Hsh.
    destruct (IH (proj1 Hsh) ltac:(destruct E as [? ? ? [] | | |]; exact (sem_ctx_tail HC))
                ltac:(intros k Ψ H0 Hk; apply (Ho k); cbn [body_opens gm_dropn]; exact Hk) _ _ _ HRC Hρ Hs)
      as (Φk & Hb & Hk).
    exists (gm_ext Φk x E); split; [ constructor; exact Hb | split; [ exact Hk | split; [ reflexivity | left; reflexivity ] ] ].
  - pose proof (items_gen_length _ _ _ _ _ _ _ Hg) as Hl.
    assert (Eo : body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx).
    { cbn [body_opens]; rewrite <- Hl, gm_dropn_gens_append; reflexivity. }
    rewrite Eo in Ho.
    pose proof (body_shape_gens_l _ _ _ Hsh) as Hsh0.
    rewrite gens_body_ctx_base, <- app_assoc in HC.
    pose proof (sem_ctx_app_r _ _ HC) as HC0.
    destruct (IH Hsh0 HC0 (fun k => Ho (S k)) _ _ _ HRC Hρ Hs) as (Φk & Hb & Hk).
    destruct (kx_kenv_exists _ _ Hk σ) as (σ1 & Hσ1).
    destruct (sem_ctx_per_ctx_env HC0) as [R1 HR1].
    destruct (benv_exists _ _ (body_xp_nopens _ _ _ _ _ Hx) (proj1 (body_shape_fill _ _ (body_xp_nopens _ _ _ _ _ Hx) Hsh0))
                HC0 _ _ HRC HR1 _ Hρ) as (ρ1 & Hb1 & Hρ1).
    destruct (kind_eval_benv _ _ _ _ _ Hb1 _ Hs) as (σ' & Hk' & Hs').
    apply (kx_kenv _ _ Hk) in Hσ1.
    pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσ1 _ Hk') as <-.
    apply (kx_kenv _ _ Hk) in Hσ1.
    exists (gens_append Φk 0 (List.map ig_erase gs)); split; [| exact (kx_gens _ _ _ _ Hk) ].
    econstructor; [ exact Hb | exact Hσ1 |].
    exact (items_kgens _ _ _ _ Hg (Ho 0 _ _ eq_refl) _ _ _ HR1 Hρ1 Hs').
Qed.

(** ** Valid Global Modules

    What the filed modules and open frames of [Θm ⍮ Ξm] are worth, at the
    target: each is a stored body there, its path evaluates to it,
    and its telescope is valid; each of its entries has the kind of its
    entry there, and so has each module stored under it; each of its term
    entries is the member of a type over its telescope, of a value related
    to itself there, with its δ-reduct at arguments for the outer part of
    the telescope, if it has one, a term over that part instantiated, valid
    there, whose value at arguments is the member's value applied to them
    (an inductive type's reduct, its type former at the arguments, is not
    a [λ]); each alias entry is a valid
    unit in any valid context. *)
Definition gfiled_ok : Prop :=
  forall p T Φ, gc_loc Θm Ξm p = Some (T, Φ) ->
    (exists Φ', gc_loc gc_deps gc_stack p = Some (T, Φ')) /\
    (forall ρ, ⟦ qname_mod p ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρ ↘ dm_global p nil) /\
    ⊨ T /\ tele_ass T /\ ctx_scoped 0 T /\
    (forall x Φ0 E, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) ->
       dkind gc_deps gc_stack (dm_global p nil) (x :: nil) (ent_kind E)) /\
    (forall x TΦ, gc_loc Θm Ξm (qname_app p (x :: nil)) = Some TΦ ->
       dkind gc_deps gc_stack (dm_global p nil) (x :: nil) mk_mod) /\
    (forall x Φ0 E R0, gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_term E = Some R0 ->
       exists A0 i g, T ⊨ A0 : Typeω@i /\
         (forall Ns R1 T1 T2, T = T1 ++ T2 -> List.length T2 = List.length Ns -> ds_ats R0 Ns = Some R1 ->
            ds_ty Θm Ξm R1 = Some (ctx_pi T1 A0)[sb_of_list Id Ns] /\
            (ds_red R1 = None \/
             exists M1, ds_red R1 = Some M1[sb_of_list Id Ns] /\ T2 ⊨ M1 : ctx_pi T1 A0 /\
               forall ns m, List.length ns = List.length T2 -> ⟦ M1 ⟧ env_args nil ns ↘ m ->
                 $*| g & ns | gc_deps ⍮ gc_stack ↘ m)) /\
         dm_global p nil ·ₜ x gc_deps ⍮ gc_stack ↘ g /\
         (exists j E0 e, ⟦ ctx_pi T A0 ⟧ nil ↘ e /\ per_univ_elem j E0 e e /\ E0 g g)) /\
    (forall y Φ0 E Ua, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua ->
       gc_module gc_deps gc_stack (qname_in p y) = Some (mr_alias Ua) /\
       forall Γ, ⊨ Γ -> wf_ctx Θm Ξm Γ -> semK Γ (me_lit Ua)).

Hypothesis Hgm : ⊢ᵍ Θm ⍮ Ξm.
Hypothesis Hgf : gfiled_ok.

Lemma skind_apps : forall Ns H ρ ch k, skind gc_deps gc_stack ρ (me_apps H Ns) ch k <-> skind gc_deps gc_stack ρ H ch k.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn [me_apps]; [ reflexivity |].
  rewrite IH; apply skind_app_iff.
Qed.

(** A unit or open frame a member names is a module. *)
Lemma gunit_kind : forall H x TΦ, gc_unit Θm Ξm (me_mem H x) = Some TΦ ->
    forall ρ, skind gc_deps gc_stack ρ H (x :: nil) mk_mod.
Proof.
  intros * Hu ρ.
  destruct TΦ as [T' Φ'].
  destruct (gc_unit_mem_parent _ _ Hgm _ _ _ _ Hu) as (T0 & Φ0 & Hu0 & _).
  destruct (gc_unit_loc _ _ _ _ _ Hu0) as (mq & Hq & Hl0).
  destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hqp & Hl).
  cbn [mod_qname] in Hqp; rewrite Hq in Hqp; injection Hqp as <-.
  pose proof (gc_loc_of_loc _ _ Hgm _ _ _ Hl0) as Hgl0.
  pose proof (gc_loc_of_loc _ _ Hgm _ _ _ Hl) as Hgl.
  destruct (Hgf _ _ _ Hgl0) as (_ & Hp & _ & _ & _ & _ & Hsub & _).
  rewrite (mod_qname_inv _ _ Hq).
  apply (kind_eval_modexp _ _ _ _ _ (Hp ρ)), (Hsub x (T', Φ')); exact Hgl.
Qed.

Lemma ds_entry_up_inv : forall Δ R y Γy E rd, ds_entry (ds_up Δ R) y = Some (Γy, E, rd) ->
    exists Γy' rd', ds_entry R y = Some (Γy', E, rd').
Proof.
  intros * He; destruct R; cbn in He |- *; try discriminate.
  - destruct (gm_prefix_upto _ y) as [[| ? ? [[|] ? ? [] | | |] | ] |]; try discriminate;
      injection He as <- <- <-; eauto.
  - destruct (gm_prefix_upto _ y) as [[| ? ? E0 | ] |]; try discriminate; injection He as <- <- <-; eauto.
Qed.

Lemma ds_entry_open_inv : forall Δ Φ Φx y Γy E rd, ds_entry (ds_open Δ Φ Φx) y = Some (Γy, E, rd) ->
    exists Φ' E0, gm_prefix_upto Φx y = Some (gm_ext Φ' y E0) /\ ent_kind E = ent_kind E0 /\
      Γy = body_ctx Φ' ++ Δ /\ rd = rd_open Δ Φ'.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φx y) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  pose proof (gm_prefix_name _ _ _ _ _ Hp) as ->.
  exists Φ', E0; split; [ reflexivity |].
  destruct E0 as [[|] ? ? [] | | |]; try discriminate; injection He as <- <- <-; repeat split.
Qed.

Lemma ds_entry_closed_inv : forall Θ p T Φ Ns y Γy E rd, ds_entry (ds_closed Θ p T Φ Ns) y = Some (Γy, E, rd) ->
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
  destruct E as [? ? ? [] | | |]; cbn [body_ctx]; rewrite HX; eexists (_ :: X); reflexivity.
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

Lemma semK_kinds_all :
  (forall Γ K, semK Γ K -> kinds_ok Γ K) /\ (forall Γ H, smt Γ H -> kinds_ok Γ H).
Proof.
  apply semK_smt_ind.
  - (* a filed module at arguments *)
    intros Γ p T Φ Ns Hw Hgl HΓ Hs; split; [| intros x TΦ Hu RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ) ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    destruct (filed_denote _ _ Hgm _ _ _ Γ Ns Hgl) as (R1 & Hm1 & Hmod1).
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ Hm1), Hmod1 in Hmod; injection Hmod as <-.
    destruct (ds_entry_closed_inv _ _ _ _ _ _ _ _ _ He) as (Φ0 & E0 & Hp & ->).
    destruct (Hgf _ _ _ Hgl) as (_ & Hpe & _ & _ & _ & Hk & _).
    apply skind_apps, (kind_eval_modexp _ _ _ _ _ (Hpe ρ)); rewrite ent_kind_read; exact (Hk _ _ _ Hp).
  - (* a body *)
    intros Γ Δ Φ Φx Hw Hx HΔ HΓ HC Hslots IHslots Hs Hsx HK Hopv Hops IHops.
    split; [| intros x TΦ Hu; cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate ].
    intros R Rm x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; [ match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end |].
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hb : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end.
    match goal with Hx' : body_xp _ _ _ Φ ?Φx1 |- _ =>
      pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hgm)))) _ _ _ Hx _ Hx') as <- end.
    cbn in Hmod; injection Hmod as <-.
    destruct (ds_entry_open_inv _ _ _ _ _ _ _ He) as (Φ' & E0 & Hp & Hek & _ & _).
    rewrite Hek.
    (* an environment of the parameters, and the kinds of the closure there *)
    destruct (sem_ctx_per_ctx_env (sem_ctx_app_r _ _ HC)) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kshape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    destruct (kbody_exists _ _ _ Hx Hsx HC (fun k Ψ H Hk => proj1 (conj (IHops k Ψ H Hk) I)) _ _ _ HRΔ Hρa Hsa) as (Φk & Hb & Hk).
    apply sk_lit, ukind_pad, (ukind_kbody _ _ _ _ _ Hb).
    destruct (kx_prefix _ _ Hk _ _ _ Hp) as (Φk' & Ek & Hpk & Hk' & HE).
    pose proof (body_xp_nopens _ _ _ _ _ Hx) as Hn.
    destruct (prefix_shape _ _ _ _ Hsx Hp) as [Hsh' HshE].
    pose proof (prefix_nopens _ _ _ Hn Hp) as Hn'; cbn [gm_nopens] in Hn'.
    destruct E0 as [b pv A0 oM | pm U | | ]; cbn in HshE; try contradiction;
      destruct HE as [-> | (b' & pv' & A' & A'' & M' & -> & [= -> -> -> ->])]; cbn [ent_kind].
    1,2: eapply uk_def; exact Hpk.
    + (* a submodule: a module, at an environment of its context *)
      destruct (kx_kenv_exists _ _ Hk' (kpad (List.length Δ) ρ)) as (σ1 & Hσ1).
      eapply uk_mod; [ exact Hpk | exact Hσ1 |].
      destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX).
      rewrite HX, <- app_assoc in HC; pose proof (sem_ctx_app_r _ _ HC) as HC1; cbn [body_ctx app] in HC1.
      pose proof (sem_ctx_tail HC1) as HC0.
      destruct (sem_ctx_per_ctx_env HC0) as [R0 HR0].
      destruct (benv_exists _ _ Hn' (proj1 (body_shape_fill _ _ Hn' Hsh')) HC0 _ _ HRΔ HR0 _ Hρa) as (ρ1 & Hb1 & Hρ1).
      destruct (kind_eval_benv _ _ _ _ _ Hb1 _ Hsa) as (σ' & Hk1 & Hs1).
      apply (kx_kenv _ _ Hk') in Hσ1.
      pose proof (proj1 (proj2 (proj2 (proj2 (@functional_kind gc_deps gc_stack)))) _ _ _ Hσ1 _ Hk1) as <-.
      apply (ukind_id _ _ _ _ (proj1 (kshape_sym _ _ Hs1))), skind_lit_iff.
      exact (valid_nil_kind _ _ _ (proj1 (sem_ctx_mod_inv HC1)) HR0 _ Hρ1).
  - (* an alias *)
    intros Γ Δ E Hw HΔ HΓ HΔΓ HK HE Hsmt IHE.
    split; [| intros x TΦ Hu; cbn in Hu; unfold gc_unit in Hu; cbn in Hu; discriminate ].
    intros R Rm x Γy E' rd Hm Hmod He RΓ ρ HRΓ Hρ.
    inversion Hm; subst; [ match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end |].
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? E0 RE Rem HmE HmodE]; subst end.
    rewrite (ds_is_mod_mod _ _ _ (ds_is_mod_up _ _ (ds_mod_is_mod _ _ _ _ HmodE))) in Hmod; injection Hmod as <-.
    destruct (ds_entry_up_inv _ _ _ _ _ _ He) as (Γy' & rd' & He').
    destruct (sem_ctx_per_ctx_env HΔΓ) as [RΔ HRΔ].
    destruct (params_env _ _ _ _ HΔ HRΓ HRΔ _ Hρ) as (args & Hl & Hρa).
    pose proof (kshape_args_pad gc_deps gc_stack ρ _ _ Hl) as Hsa.
    apply sk_lit, uk_alias, (skind_id _ _ _ _ (proj1 Hsa)).
    exact (proj1 IHE _ _ _ _ _ _ HmE HmodE He' _ _ HRΔ Hρa).
  - (* a module expression equal to a valid unit: as the unit *)
    intros Γ H R Rm K RK HwH HmH HmodH HHK HK IHK HmK HmodK.
    split; [| intros x TΦ Hu RΓ ρ _ _; exact (gunit_kind _ _ _ Hu ρ) ].
    intros R' Rm' x Γy E rd Hm Hmod He RΓ ρ HRΓ Hρ.
    rewrite (proj1 (mdenote_functional_all _ _ Hgm) _ _ _ Hm _ HmH), HmodH in Hmod; injection Hmod as <-.
    pose proof (proj1 IHK _ _ _ _ _ _ HmK HmodK He _ _ HRΓ Hρ) as Hk.
    destruct (rel_modexp_at _ _ _ _ _ HHK HRΓ _ _ Hρ) as (h & h' & Hh & Hh' & Hr).
    apply (kind_eval_modexp _ _ _ _ _ Hh), (per_dmod_kequiv _ _ Hr), (kind_eval_modexp _ _ _ _ _ Hh'); exact Hk.
Qed.

Corollary semK_kinds : forall Γ K, semK Γ K -> kinds_ok Γ K.
Proof. exact (proj1 semK_kinds_all). Qed.

Corollary smt_kinds : forall Γ H, smt Γ H -> kinds_ok Γ H.
Proof. exact (proj2 semK_kinds_all). Qed.

End Fixed_GCtx.
