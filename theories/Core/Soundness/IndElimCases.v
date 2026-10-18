(** * The Eliminator in the Gluing Model

    The soundness counterpart of [Core/Completeness/ElimCases.v]: an
    elimination is glued at the motive's instance, by induction on the
    gluing of the scrutinee.  On a constructor, the branch is glued at the
    substitution of the constructor's non-uniform parameters, its arguments
    and the recursive results; on a neutral, the eliminator reads back as
    the stuck one, through the motive and the branches at fresh variables.
    The values the gluings are at are related to those the evaluation
    reaches through the PER model, as [Core/Completeness/ElimCases.v] and
    [Core/Semantic/IndElim.v] relate them. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness Require IndCases IndSem ElimCases TeleSem SubstitutionCases InstanceCases UnitCases MemberReps GlobalArgs.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability IndCanon IndElim Evaluation.Modules.
From Mctt.Core.Syntactic Require Import Substitution IndCong.
From Mctt.Core.Syntactic.System Require Import MemberLemmas.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  TermStructureCases
  UniverseCases.
Require Import Mctt.Core.Soundness.IndCases.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Values Related through a Substitution *)

(** A term glued at a type of one of two related values is glued at that
    type of the other, at some universe. *)
Lemma glu_transfer_per' : forall (j : uidx) (i : nat) a b P El Γ T M m, DG a ∈ glu_univ_elem j ↘ P ↘ El ->
    Dom a ≈ b ∈ per_univ i -> Γ ⊢ T ® P -> Γ ⊢ M : T ® m ∈ El ->
    exists (k : uidx) P' El', DG b ∈ glu_univ_elem k ↘ P' ↘ El' /\ Γ ⊢ T ® P' /\ Γ ⊢ M : T ® m ∈ El'.
Proof.
  intros * Hg Hab HT HM.
  destruct (glu_univ_elem_cumu_ge_uidx (i := j) (j := ul (Nat.max (ulvl j) i)) ltac:(apply uidx_le_max) Hg) as (P1 & El1 & Hg1).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx (uidx_le_max _ _) Hg Hg1 HT) as HT1.
  pose proof (glu_univ_elem_exp_cumu_ge_uidx (uidx_le_max _ _) Hg Hg1 HM) as HM1.
  destruct (glu_transfer_per (Nat.max (ulvl j) i) i a b P1 El1 Γ T M m Hg1 Hab HT1 HM1) as (k & P' & El' & H1 & H2 & H3).
  exists k, P', El'; auto.
Qed.

(** ** Fresh Variables, Glued

    The substitution [q^n σ] past a telescope [C], at variables related to
    the fresh ones of the types of [C], is glued at the extension. *)
Lemma glu_sub_qn : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a (i : uidx) R, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       DF a ≈ a ∈ per_univ_elem i ↘ R -> exists x, List.nth_error xs k = Some x /\ R (⇑! a (List.length Δ + k)) x) ->
    tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
Proof.
  induction C as [| e C IH]; intros * Hass HΓb Sb HC * Hσ Hl Hx.
  - destruct xs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env HΓb HC); exact Hσ.
  - inversion Hass as [| ? ? [A ->] Hass']; subst.
    destruct (List.exists_last (l := xs)) as (xs' & x & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hl; cbn in Hl.
    cbn [List.app] in HC.
    assert (HC' : exists TSb, EG C ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eauto).
    destruct HC' as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (i & HA & HT & HSb).
    assert (Hx' : forall k A0 a (i0 : uidx) R, List.nth_error (List.rev C) k = Some (ce_ass A0) ->
              ⟦ A0 ⟧ env_args ρ (List.firstn k xs') ↘ a -> DF a ≈ a ∈ per_univ_elem i0 ↘ R ->
              exists x0, List.nth_error xs' k = Some x0 /\ R (⇑! a (List.length Δ + k)) x0).
    { intros * HA0 Ea HR.
      assert (Hk : k < List.length C) by (rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
      assert (HA1 : List.nth_error (List.rev (C ▹ A)) k = Some (ce_ass A0))
        by (cbn [List.rev]; rewrite List.nth_error_app1 by (rewrite List.length_rev; lia); exact HA0).
      assert (Ea1 : ⟦ A0 ⟧ env_args ρ (List.firstn k (xs' ++ x :: nil)) ↘ a)
        by (rewrite List.firstn_app, (proj2 (Nat.sub_0_le k (List.length xs'))) by lia; cbn; rewrite List.app_nil_r; exact Ea).
      destruct (Hx k A0 a i0 R HA1 Ea1 HR) as (x0 & Hx0 & HRx).
      exists x0; split; [ rewrite List.nth_error_app1 in Hx0 by lia; exact Hx0 | exact HRx ]. }
    pose proof (IH _ _ Hass' HΓb _ HTSb Δ σ ρ xs' Hσ ltac:(lia) Hx') as Hτ.
    cbn [tele_sub List.length sb_qn List.app centry_sub].
    rewrite env_args_app; cbn [env_args List.fold_left].
    apply HSb.
    destruct (HT _ _ _ Hτ) as [a P El Ea Hg HTP].
    assert (Hxk : List.nth_error (List.rev (C ▹ A)) (List.length C) = Some (ce_ass A))
      by (cbn [List.rev]; rewrite List.nth_error_app2 by (rewrite List.length_rev; lia); rewrite List.length_rev, Nat.sub_diag; reflexivity).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hg) as [Ra HRa].
    assert (Ea' : ⟦ A ⟧ env_args ρ (List.firstn (List.length C) (xs' ++ x :: nil)) ↘ a)
      by (rewrite firstn_app_exact by lia; exact Ea).
    destruct (Hx _ _ _ _ _ Hxk Ea' HRa) as (x0 & Hx0 & Hrx).
    rewrite List.nth_error_app2 in Hx0 by lia; replace (List.length C - List.length xs') with 0 in Hx0 by lia; cbn in Hx0; injection Hx0 as <-.
    assert (HΔC : ⊢ tele_sub C σ ++ Δ) by (pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ); gen_presups; assumption).
    assert (HAτ : tele_sub C σ ++ Δ ⊢ A[sb_qn (List.length C) σ] : Typeω@i)
      by (pose proof (glu_ctx_env_sub_escape HTSb _ _ _ Hτ); mauto 3).
    assert (HΔA : ⊢ (tele_sub C σ ++ Δ) ▹ A[sb_qn (List.length C) σ]) by mauto 3.
    unfold sb_q; eapply cons_glu_sub_pred_helper_gen; [ exact HTSb | | exact HA | exact Ea | exact Hg | ].
    + eapply glu_ctx_env_sub_monotone; [ exact HTSb | exact Hτ | mauto 3 ].
    + cbn [sentry_exp]; rewrite <- exp_wk_sub.
      pose proof (var0_glu_elem Hg HTP) as Hv.
      eapply glu_univ_elem_trm_resp_per_elem; [ exact Hg | exact HRa | exact Hv |].
      rewrite List.length_app, length_tele_sub, Nat.add_comm; exact Hrx.
Qed.

(** A substitution glued to an environment extended by values is glued to
    it extended by values related to them at the telescope. *)
Lemma glu_sub_resp_args : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ τ ρ ys xs, List.length ys = List.length C -> per_gargs (List.rev C) ρ ρ ys xs ->
      Δ ⊢ˢ τ ® env_args ρ ys ∈ Sb -> Δ ⊢ˢ τ ® env_args ρ xs ∈ Sb.
Proof.
  induction C as [| e C IH]; intros * Hass HΓb Sb HC * Hl Hg Hτ.
  - destruct ys; [| discriminate ]; inversion Hg; subst; exact Hτ.
  - inversion Hass as [| ? ? [A ->] Hass']; subst.
    destruct (List.exists_last (l := ys)) as (ys' & y & ->); [ intros ->; discriminate |].
    rewrite List.length_app in Hl; cbn in Hl.
    pose proof (IndSem.per_gargs_length _ _ _ _ _ Hg) as [Lyx _].
    destruct (List.exists_last (l := xs)) as (xs' & x & ->); [ intros ->; rewrite List.length_app in Lyx; cbn in Lyx; lia |].
    rewrite !List.length_app in Lyx; cbn in Lyx.
    cbn [List.rev] in Hg.
    destruct (IndSem.per_gargs_app (List.rev C) (ce_ass A :: nil) _ _ ys' xs' (y :: nil) (x :: nil) ltac:(rewrite List.length_rev; lia) Hg ltac:(rewrite List.length_rev; lia)) as [Hg1 Hg2].
    inversion Hg2 as [| ? ? ? ? ? ? ? ? ? ? HA Hyx _]; subst.
    destruct HA as [a1 a1' Ea1 Ea1' HR1].
    cbn [List.app] in HC.
    assert (HC' : exists TSb, EG C ++ Γb ∈ glu_ctx_env ↘ TSb) by (inversion HC; subst; eauto).
    destruct HC' as [TSb HTSb].
    destruct (glu_ctx_env_cons_clean_inversion HTSb HC) as (ic & _ & _ & HSb).
    rewrite env_args_app in Hτ |- *; cbn [env_args List.fold_left] in Hτ |- *.
    apply HSb in Hτ; apply HSb.
    inversion Hτ as [? ? ? a P El Hτt Ea Hga HEl Htail]; subst.
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [Ra HRa].
    destruct (InstanceCases.per_univ_elem_trans_any _ _ _ _ _ _ _ HRa HR1) as (R2 & HR2 & _).
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R2 HR2) Hga) as Hga'.
    econstructor; [ exact Hτt | exact Ea1' | exact Hga' | | exact (IH _ _ Hass' HΓb _ HTSb _ _ _ ys' xs' ltac:(lia) Hg1 Htail) ].
    cbn.
    eapply glu_univ_elem_trm_resp_per_elem; [ exact Hga | exact HRa | exact HEl |].
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HRa); exact Hyx.
Qed.

(** The substitution [q^n σ] past a telescope [C], at variables of types
    related to those of [C], is glued at the extension. *)
Lemma glu_sub_fresh : forall C Γb Sb_b, tele_ass C -> EG Γb ∈ glu_ctx_env ↘ Sb_b ->
    forall Sb, EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall Δ σ ρ xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       exists b (j : nat), List.nth_error xs k = Some (⇑! b (List.length Δ + k)) /\ Dom a ≈ b ∈ per_univ j) ->
    tele_sub C σ ++ Δ ⊢ˢ sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
Proof.
  intros * Hass HΓb Sb HC * Hσ Hl Hx.
  eapply glu_sub_qn; [ exact Hass | exact HΓb | exact HC | exact Hσ | exact Hl |].
  intros k A a i R HA Ea HR.
  destruct (Hx k A a HA Ea) as (b & j & Hxk & [R' HR']).
  exists (⇑! b (List.length Δ + k)); split; [ exact Hxk |].
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR' HR); exact (var_per_elem _ HR').
Qed.

(** ** Glued Arguments along Related Types *)

Lemma tele_insts_base_agree : forall Δ k σ σ' Ms, tele_ass Δ -> ctx_scoped k Δ ->
    (forall x, x < k -> σ x = σ' x) -> tele_insts Δ σ Ms = tele_insts Δ σ' Ms.
Proof.
  intros * Hass Hs Hσ.
  pose proof (tele_insts_sub Δ k σ σ' Id Ms Hass Hs ltac:(intros x Hx; rewrite sentry_sub_id; apply Hσ; exact Hx)) as H.
  rewrite (List.map_ext _ (fun T => T) (fun T => exp_sub_id T)), List.map_id in H.
  rewrite (List.map_ext _ (fun M => M) (fun M => exp_sub_id M)), List.map_id in H.
  exact H.
Qed.

Lemma ctx_rev_split : forall (C : ctx) k e, List.nth_error (List.rev C) k = Some e ->
    exists C1 Pre, C = C1 ++ e :: Pre /\ List.length Pre = k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & E & Hl).
  exists (List.rev l2), (List.rev l1); split; [| rewrite List.length_rev; exact Hl ].
  rewrite <- (List.rev_involutive C), E, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma nth_rev_tele_sub : forall C1 e Pre σ,
    List.nth_error (List.rev (tele_sub (C1 ++ e :: Pre) σ)) (List.length Pre) = Some (centry_sub e (sb_qn (List.length Pre) σ)).
Proof.
  intros; rewrite tele_sub_app; cbn [tele_sub]; rewrite !List.rev_app_distr; cbn [List.rev].
  rewrite <- List.app_assoc; rewrite List.nth_error_app2 by (rewrite List.length_rev, length_tele_sub; lia).
  rewrite List.length_rev, length_tele_sub, Nat.sub_diag; reflexivity.
Qed.

(** Glued arguments of a telescope are glued arguments of another one
    whose types, at the same arguments, have values related to its own. *)
Lemma glu_args_link : forall Δ C C' τ τ' ρ1 ρ2 Ms vs, List.length C = List.length C' ->
    tele_insts C τ Ms = tele_insts C' τ' Ms -> glu_args Δ C τ ρ1 Ms vs ->
    (forall k A A' a, List.nth_error (List.rev C) k = Some (ce_ass A) -> List.nth_error (List.rev C') k = Some (ce_ass A') ->
       k < List.length vs -> ⟦ A ⟧ env_args ρ1 (List.firstn k vs) ↘ a ->
       exists a' (i : nat), ⟦ A' ⟧ env_args ρ2 (List.firstn k vs) ↘ a' /\ Dom a' ≈ a ∈ per_univ i) ->
    (forall k e', List.nth_error (List.rev C') k = Some e' -> exists A, List.nth_error (List.rev C) k = Some (ce_ass A) /\ exists A', e' = ce_ass A') ->
    glu_args Δ C' τ' ρ2 Ms vs.
Proof.
  intros * HlC HT [L1 L2 H] Hlink Hass.
  constructor; [ congruence | congruence |].
  intros k M T v A' HM HT' Hv HA'.
  destruct (Hass _ _ HA') as (A & HA & A'' & E); injection E as <-.
  rewrite <- HT in HT'.
  destruct (H _ _ _ _ _ HM HT' Hv HA) as [j a P El Ea Hg HP HMg].
  assert (Hk : k < List.length vs) by (apply List.nth_error_Some; congruence).
  destruct (Hlink _ _ _ _ HA HA' Hk Ea) as (a' & i & Ea' & Hr).
  destruct (glu_transfer_per' j i a a' P El Δ T M v Hg (per_univ_sym' _ _ _ Hr) HP HMg) as (k' & P' & El' & Hg' & HP' & HM').
  exact (mk_glu_arg _ _ _ _ _ _ k' a' P' El' Ea' Hg' HP' HM').
Qed.

(** ** Arguments of a Closed Telescope, Glued *)

Lemma per_gargs_nth : forall ts ρ ρ' xs xs' k A, per_gargs ts ρ ρ' xs xs' ->
    List.nth_error ts k = Some (ce_ass A) -> k < List.length xs ->
    exists (i : nat) R a a', ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a /\ ⟦ A ⟧ env_args ρ' (List.firstn k xs') ↘ a' /\
      DF a ≈ a' ∈ per_univ_elem i ↘ R.
Proof.
  intros * H; revert k; induction H as [| ? ? ? ? ? ? ? ? ? ? HA Ha Hr IH]; intros k Hk Hl; [ cbn in Hl; lia |].
  destruct k as [| k]; cbn in Hk, Hl |- *.
  - injection Hk as <-; destruct HA as [a0 a0' E E' HR]; eauto 10.
  - exact (IH k Hk ltac:(lia)).
Qed.

Lemma tele_typed_prefix : forall C1 Pre Γ Ms, tele_ass Pre -> List.length Pre <= List.length Ms ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts (C1 ++ Pre) Id Ms) k = Some T -> Γ ⊨ N : T) ->
    forall k N T, List.nth_error (List.firstn (List.length Pre) Ms) k = Some N ->
      List.nth_error (tele_insts Pre Id (List.firstn (List.length Pre) Ms)) k = Some T -> Γ ⊨ N : T.
Proof.
  intros * Hass Hle HMs k N T HN HT.
  assert (Hk : k < List.length (List.firstn (List.length Pre) Ms)) by (apply List.nth_error_Some; congruence).
  rewrite List.length_firstn in Hk.
  apply (HMs k).
  - rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec k (List.length Pre)); [ exact HN | discriminate ].
  - rewrite <- (List.firstn_skipn (List.length Pre) Ms), tele_insts_app by (try exact Hass; rewrite List.length_firstn; lia).
    rewrite List.nth_error_app1; [ exact HT |].
    rewrite length_tele_insts by exact Hass; rewrite List.length_firstn; lia.
Qed.

(** Terms valid at a closed telescope have values related at it to
    themselves over [ρ] and over the empty environment. *)
Lemma closed_args_gargs : forall C Γ RΓ ρ Ms vs, tele_ass C -> ⊨ C -> ⊨ Γ -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> RΓ ρ ρ ->
    List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> per_gargs (List.rev C) ρ nil vs vs.
Proof.
  intros * Hass HC HΓ HRΓ Hρ Hl HMs Hv.
  pose proof (TeleSem.gsub_closed_inst C Γ Ms Hass HC HΓ Hl HMs) as Hg.
  destruct (TeleSem.closed_app_sem C Γ Hass HC HΓ) as [HCΓ Hres].
  destruct (sem_ctx_per_ctx_env HCΓ) as [RCΓ HRCΓ]; destruct (sem_ctx_per_ctx_env HC) as [RC HRC].
  pose proof (IndSem.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hv) as Hev.
  pose proof (rel_sub_under_ctx_at' (InstanceCases.gsub_valid Hg) HRΓ HRCΓ _ _ _ _ Hρ Hev Hev) as H1.
  apply (Hres _ _ HRC HRCΓ) in H1.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (IndCases.eval_exps_length _ _ _ Hv)).
  pose proof (TeleSem.closed_env_base C RC vs vs ρ ρ ρ nil Hass HC HRC Lv Lv H1) as H2.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  assert (L' : List.length vs = List.length (List.rev C)) by (rewrite List.length_rev; exact Lv).
  destruct (IndSem.rel_gargs (List.rev C) ⋅ _ RC GlobalArgs.per_ctx_env_nil_true HC' (List.Forall_rev Hass) HRC' ρ nil vs vs L' L' H2)
    as [_ Hgg]; exact Hgg.
Qed.

(** Terms glued at the instances of a closed telescope are glued
    arguments of it, at their values. *)
Lemma params_glu_args : forall C Γ RΓ Sb Δ σ ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢ˢ σ ® ρ ∈ Sb -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊩ N : T) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HRΓ HSb Hσ Hl HMs HMg Hv.
  pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
  pose proof (closed_args_gargs _ _ _ _ _ _ Hass HC HΓ HRΓ Hρ Hl HMs Hv) as Hpg.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (IndCases.eval_exps_length _ _ _ Hv)).
  constructor; [ rewrite List.length_map; exact Hl | exact Lv |].
  intros k M T v A HM HT Hv' HA.
  apply nth_error_map_inv in HM as (N & HN & ->).
  rewrite <- (tele_insts_sub C 0 Id Id σ Ms Hass Hs ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  destruct (glu_rel_exp_clean_inversion1 HSb (HMg k N T0 HN HT0)) as [i Hi].
  destruct (Hi _ _ _ Hσ) as [a m P El Ea Em Hgl HNg].
  destruct (IndCases.eval_exps_nth _ _ _ _ _ Hv HN) as (v0 & Hv0 & Ev0).
  rewrite Hv0 in Hv'; injection Hv' as <-.
  assert (m = v0) as -> by (eapply functional_eval_exp; eassumption).
  destruct (tele_insts_nth _ _ _ _ _ HT0) as (A0 & HA0 & ET0).
  rewrite HA in HA0; injection HA0 as <-.
  assert (Hk : k < List.length vs) by (apply List.nth_error_Some; congruence).
  destruct (per_gargs_nth _ _ _ _ _ _ _ Hpg HA Hk) as (i' & R & a1 & a2 & Ea1 & Ea2 & HR).
  (** The value of the instance, against the type at the values before it. *)
  destruct (ctx_rev_split C k _ HA) as (C1 & Pre & EC & HPl).
  assert (HPa : tele_ass Pre) by (rewrite EC in Hass; unfold tele_ass in Hass; apply List.Forall_app in Hass as [_ H']; inversion H'; assumption).
  pose proof HC as HC1; rewrite EC in HC1; pose proof (UnitCases.sem_ctx_app_r _ _ HC1) as HC2.
  destruct (MemberReps.sem_ctx_ass_inv HC2) as [j HAj].
  pose proof (sem_ctx_tail HC2) as HPre.
  pose proof (TeleSem.closed_app_valid Pre Γ _ A A HPa HPre HΓ HAj) as HAj'.
  assert (Hle : List.length Pre <= List.length Ms) by (rewrite Hl, EC, List.length_app; cbn; lia).
  rewrite EC in HMs; replace (C1 ++ ce_ass A :: Pre) with ((C1 ++ ce_ass A :: nil) ++ Pre) in HMs by (rewrite <- List.app_assoc; reflexivity).
  pose proof (tele_typed_prefix _ _ _ _ HPa Hle HMs) as HMs'.
  assert (Lf : List.length (List.firstn (List.length Pre) Ms) = List.length Pre) by (rewrite List.length_firstn; lia).
  pose proof (TeleSem.gsub_closed_inst Pre Γ _ HPa HPre HΓ Lf HMs') as Hgs.
  pose proof (IndSem.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) (eval_exps_firstn _ _ _ (List.length Pre) Hv)) as Hevτ.
  destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAj' HRΓ (InstanceCases.gsub_valid Hgs) Hρ Hevτ) as (a' & b' & Ea' & Eb' & Hab).
  rewrite HPl in Ea', Eb'; rewrite <- ET0 in Ea'.
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (b' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hlink : Dom a ≈ a2 ∈ per_univ j) by (eapply per_univ_trans'; [ exact Hab | exists R; exact HR ]).
  destruct (glu_transfer_per' i j a a2 P El Δ T0[σ] N[σ] v0 Hgl Hlink ltac:(eapply glu_univ_elem_trm_typ; eassumption) HNg)
    as (k' & P' & El' & Hg' & HP' & HM').
  apply (mk_glu_arg _ _ _ _ _ _ k' a2 P' El'); assumption.
Qed.

(** ** Lists of Parameters *)

Lemma eval_exps_skipn : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.skipn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.skipn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn; try constructor; try assumption; auto.
Qed.

Lemma params_split_gen : forall D (Pr : exp -> typ -> Prop) Ms, decl_closed D -> List.length Ms = ind_np D ->
    (forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T -> Pr M T) ->
    (forall k U T, List.nth_error (List.firstn (ind_nu D) Ms) k = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ms)) k = Some T -> Pr U T) /\
    (forall k N T, List.nth_error (List.skipn (ind_nu D) Ms) k = Some N ->
       List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ms)) (List.skipn (ind_nu D) Ms)) k = Some T ->
       Pr N T).
Proof.
  intros * Hc HMl HMs.
  pose proof (decl_closed_nu D Hc) as Hle.
  assert (L1 : List.length (List.firstn (ind_nu D) Ms) = List.length (ind_uparams D))
    by (rewrite List.length_firstn, length_ind_uparams by exact Hle; unfold ind_np in *; lia).
  assert (E : tele_insts (ind_params D) Id Ms
              = tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ms)
                ++ tele_insts (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Ms)) (List.skipn (ind_nu D) Ms))
    by (rewrite <- (List.firstn_skipn (ind_nu D) Ms) at 1; rewrite params_split, tele_insts_app by (try exact (decl_uparams_ass D Hc); exact L1); reflexivity).
  assert (L2 : List.length (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ms)) = ind_nu D)
    by (rewrite length_tele_insts by exact (decl_uparams_ass D Hc); rewrite L1, Nat.min_id, length_ind_uparams by exact Hle; reflexivity).
  split.
  - intros k U T HU HT.
    assert (Hk : k < ind_nu D) by (rewrite <- L2; apply List.nth_error_Some; congruence).
    apply (HMs k); [ rewrite <- (List.firstn_skipn (ind_nu D) Ms), List.nth_error_app1 by (rewrite List.length_firstn; lia); exact HU |].
    rewrite E, List.nth_error_app1 by lia; exact HT.
  - intros k N T HN HT.
    apply (HMs (ind_nu D + k)).
    + rewrite <- (List.firstn_skipn (ind_nu D) Ms), List.nth_error_app2 by (rewrite List.length_firstn; lia).
      rewrite List.length_firstn; replace (ind_nu D + k - Nat.min (ind_nu D) (List.length Ms)) with k by (unfold ind_np in *; lia); exact HN.
    + rewrite E, List.nth_error_app2 by lia; rewrite L2; replace (ind_nu D + k - ind_nu D) with k by lia; exact HT.
Qed.

Lemma exps_eq_at_params_trans : forall p D Δ Xs Ys Zs, ind_lookup gc_deps gc_stack p = Some D -> ⊢ Δ ->
    List.length Xs = ind_np D -> exps_eq_at Δ (ind_params D) Xs Ys -> exps_eq_at Δ (ind_params D) Ys Zs ->
    exps_eq_at Δ (ind_params D) Xs Zs.
Proof.
  intros * Hl HΔ HXl [L1 H1] [L2 H2]; split; [ congruence |].
  eapply (params_eq_trans _ p D Xs Ys Zs Hl HΔ); [ exact HXl | congruence | congruence | exact H1 | exact H2 ].
Qed.

Lemma ind_rel_con_inv : forall p D ups ns c gs bs vs, ind_con D c = Some gs -> List.length bs = ind_np D ->
    ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)) ->
    tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns /\
    tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns (List.skipn (ind_nu D) bs) /\
    tele_full (ind_ar D ups ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) /\
    ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns gs vs vs.
Proof.
  intros * Hcn Hbl H.
  inversion H as [? ? gs0 bs0 bs0' vs0 vs0' Hn Hc0 Hb0 Hb0' Hs Hs' Hav Hia | ]; subst.
  match goal with E : bs0 ++ vs0 = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ E ltac:(congruence)) as [-> ->] end.
  match goal with E : bs0' ++ vs0' = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ E ltac:(congruence)) as [-> ->] end.
  rewrite Hcn in Hc0; injection Hc0 as <-.
  auto.
Qed.

(** ** The Recursive Results, Position by Position *)

Lemma ihs_rev_nth : forall D A Us na gs k e,
    List.nth_error (List.rev (ihs_ctx_aux D A Us na nil 0 gs)) k = Some e ->
    exists gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 /\ cargs_nrec gs1 = k /\
      e = ce_ass (ptyp_ihty A (sb_of_wk (wk_shiftn (k + na + ind_nn D))) (ihs_sub D Us na (cargs_pat gs1) k)
                    (a_var (k + na - 1 - List.length (cargs_pat gs1))) t).
Proof.
  intros D A Us na gs; induction gs as [| g gs IH] using List.rev_ind; intros k e H; [ cbn in H; destruct k; discriminate |].
  pose proof (ElimCases.ihs_ctx_aux_app D A Us na gs (g :: nil) nil 0) as E.
  rewrite List.app_nil_r in E; cbn [Nat.add] in E; rewrite E in H; clear E.
  destruct g as [B | t]; cbn [ihs_ctx_aux List.app] in H.
  - destruct (IH k e H) as (gs1 & t & gs2 & -> & Hk & ->).
    exists gs1, t, (gs2 ++ ca_arg B :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
  - cbn [List.rev] in H.
    destruct (Nat.lt_ge_cases k (List.length (ihs_ctx_aux D A Us na nil 0 gs))) as [Hlt | Hge].
    + rewrite List.nth_error_app1 in H by (rewrite List.length_rev; exact Hlt).
      destruct (IH k e H) as (gs1 & t' & gs2 & -> & Hk & ->).
      exists gs1, t', (gs2 ++ ca_rec t :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
    + rewrite List.nth_error_app2 in H by (rewrite List.length_rev; exact Hge).
      rewrite List.length_rev in H; rewrite length_ihs_ctx_aux in H, Hge.
      destruct (k - cargs_nrec gs) as [| k'] eqn:Ek; cbn in H; [| destruct k'; discriminate ].
      injection H as <-.
      assert (k = cargs_nrec gs) as -> by (pose proof (proj1 (Nat.sub_0_le k (cargs_nrec gs)) Ek); lia).
      exists gs, t, nil; split; [ reflexivity | split; [ reflexivity |] ].
      try rewrite List.app_nil_r; reflexivity.
Qed.

Lemma elim_ihs_nth : forall nm A Bs gs1 σ gs t gs2 As N, gs = gs1 ++ ca_rec t :: gs2 -> List.length As = List.length gs ->
    List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (elim_ihs nm A Bs σ gs As) (cargs_nrec gs1) = Some (ptyp_ih nm A Bs (cargs_sub σ gs1 As) N t).
Proof.
  intros nm A Bs gs1; induction gs1 as [| g gs1 IH]; intros σ gs t gs2 As N -> Hl HN;
    destruct As as [| N0 As]; cbn in *; try discriminate; [ injection HN as ->; reflexivity |].
  destruct g; cbn; [ apply (IH _ _ t gs2); auto | apply (IH _ _ t gs2); auto ].
Qed.

Lemma eval_ihs_nth : forall ρ nm A Bs gs1 gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
    forall t gs2 v, gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
    exists r, List.nth_error ihs (cargs_nrec gs1) = Some r /\ eval_ih gc_deps gc_stack ρ nm A Bs t v r.
Proof.
  intros ρ nm A Bs gs1; induction gs1 as [| g gs1 IH]; intros gs vs ihs H t gs2 v -> Hv; inversion H; subst; cbn in *.
  - injection Hv as ->; eauto.
  - eapply IH; eauto.
  - edestruct (IH _ _ _ ltac:(eassumption) _ _ _ eq_refl Hv) as (r & Hr & Er); exists r; split; [ exact Hr | exact Er ].
Qed.

(** ** Fresh Variables of Readback *)

Lemma fresh_tele_nth : forall E T s vs, fresh_tele gc_deps gc_stack E T s vs ->
    forall k A, List.nth_error T k = Some (ce_ass A) ->
      exists b, ⟦ A ⟧ env_args E (List.firstn k vs) ↘ b /\ List.nth_error vs k = Some (⇑! b (s + k)).
Proof.
  induction 1 as [| ? ? ? ? ? ? Ea Hr IH]; intros k A0 Hk; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in Hk |- *.
  - injection Hk as <-; exists a; rewrite Nat.add_0_r; split; [ exact Ea | reflexivity ].
  - destruct (IH k A0 Hk) as (b & Eb & Hb); exists b; split; [ exact Eb |].
    rewrite Hb; do 3 f_equal; lia.
Qed.

Lemma fresh_tele_length : forall E T s vs, fresh_tele gc_deps gc_stack E T s vs -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

Lemma functional_fresh_cargs : forall p ups E gs s vs, fresh_cargs gc_deps gc_stack p ups E gs s vs ->
    forall vs', fresh_cargs gc_deps gc_stack p ups E gs s vs' -> vs = vs'.
Proof.
  induction 1; intros vs' H'; inversion H'; subst; [ reflexivity | |].
  - functional_eval_rewrite_clear.
    match goal with H : fresh_cargs _ _ _ _ _ _ _ _ |- _ => rewrite (IHfresh_cargs _ H) end; reflexivity.
  - match goal with H1 : eval_shty _ _ _ _ ?E ?t ?a1, H2 : eval_shty _ _ _ _ ?E ?t ?a2 |- _ =>
      pose proof (functional_eval_shty _ _ _ _ _ _ H1 H2) as <- end.
    match goal with H : fresh_cargs _ _ _ _ _ _ _ _ |- _ => rewrite (IHfresh_cargs _ H) end; reflexivity.
Qed.

Lemma functional_fresh_ihs : forall ρ A ρa gs vs s ihs, fresh_ihs gc_deps gc_stack ρ A ρa gs vs s ihs ->
    forall ihs', fresh_ihs gc_deps gc_stack ρ A ρa gs vs s ihs' -> ihs = ihs'.
Proof.
  induction 1; intros ihs' H'; inversion H'; subst; [ reflexivity | auto |].
  match goal with H1 : eval_ihty _ _ ?r ?A ?E ?t ?v ?a1, H2 : eval_ihty _ _ ?r ?A ?E ?t ?v ?a2 |- _ =>
    pose proof (functional_eval_ihty _ _ _ _ _ _ _ H1 H2) as <- end.
  f_equal; auto.
Qed.

Lemma fresh_cargs_nth : forall p ups E gs s vs, fresh_cargs gc_deps gc_stack p ups E gs s vs ->
    forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    (forall A, g = ca_arg A -> exists a, ⟦ A ⟧ env_args E (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
       List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))) /\
    (forall t, g = ca_rec t -> exists a, eval_shty gc_deps gc_stack p ups (env_args E (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) t a /\
       List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))).
Proof.
  intros p ups E gs s vs H gs1; revert E gs s vs H; induction gs1 as [| g1 gs1 IH]; intros * H g gs2 Heq; cbn in Heq.
  - subst; split; intros * ->; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_cargs _ _ _ _ _ (gs1 ++ _) _ _ |- _ => destruct (IH _ _ _ _ Hr1 g gs2 eq_refl) as [IHa IHr] end.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros t0 ->; destruct (IHr t0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
Qed.

Lemma fresh_ihs_nth : forall ρ A ρa gs vs s ihs, fresh_ihs gc_deps gc_stack ρ A ρa gs vs s ihs ->
    forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists v a, List.nth_error vs (List.length gs1) = Some v /\
      eval_ihty gc_deps gc_stack ρ A (env_args ρa (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) t v a /\
      List.nth_error ihs (cargs_nrec gs1) = Some (⇑! a (s + cargs_nrec gs1)).
Proof.
  intros ρ A ρa gs vs s ihs H gs1; revert ρa gs vs s ihs H; induction gs1 as [| g1 gs1 IH]; intros * H t gs2 Heq; cbn in Heq.
  - subst; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto 10.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_ihs _ _ _ _ _ (gs1 ++ _) _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ Hr1 t gs2 eq_refl) as (v0 & a0 & Hv & Ea & Hi) end.
    + exists v0, a0; cbn; auto.
    + exists v0, a0; cbn.
      split; [ exact Hv | split; [ exact Ea |] ].
      rewrite Hi; do 3 f_equal; lia.
Qed.

(** ** The Readback of a Stuck Eliminator *)

Lemma read_ne_elim_inv : forall s ρ0 nm A0 Bs0 p D as0 m0 M0, ind_lookup gc_deps gc_stack p = Some D ->
    Rne d_elim ρ0 nm A0 Bs0 p as0 m0 in gc_deps ⍮ gc_stack ⍮ s ↘ M0 ->
    exists ns a A'' Bs'' Mr, M0 = ne_elim nm A'' Bs'' Mr /\ List.length as0 = ind_np D /\ nm = S (ind_nn D) /\
      fresh_tele gc_deps gc_stack (env_args nil (List.firstn (ind_nu D) as0)) (List.rev (ind_nparams D)) s ns /\
      ⟦ A0 ⟧ env_args ρ0 (ns ++ ⇑! (d_ind p (List.firstn (ind_nu D) as0 ++ ns)) (s + ind_nn D) :: nil) ↘ a /\
      Rtyp a in gc_deps ⍮ gc_stack ⍮ S (s + ind_nn D) ↘ A'' /\
      read_brs gc_deps gc_stack s ρ0 A0 p D (List.firstn (ind_nu D) as0) (ind_cons D) Bs0 Bs'' /\
      Rne m0 in gc_deps ⍮ gc_stack ⍮ s ↘ Mr.
Proof.
  intros * Hl H; inversion H; subst.
  match goal with H' : ind_lookup _ _ p = Some ?D0 |- _ => assert (D0 = D) as -> by congruence end.
  eexists _, _, _, _, _; split; [ reflexivity |]; eauto 10.
Qed.

Lemma read_brs_fst : forall s ρ0 A0 p D ua cs Bs Bs'', read_brs gc_deps gc_stack s ρ0 A0 p D ua cs Bs Bs'' ->
    List.map fst (nbrs_to_brs Bs'') = List.map fst Bs.
Proof. induction 1; cbn; congruence. Qed.

Lemma read_brs_nth : forall s ρ0 A0 p D ua cs Bs Bs'', read_brs gc_deps gc_stack s ρ0 A0 p D ua cs Bs Bs'' ->
    forall k c n B, List.nth_error Bs k = Some (c, n, B) ->
    exists gs ns vs ihs b t Bn, List.nth_error cs k = Some (c, gs) /\
      List.nth_error (nbrs_to_brs Bs'') k = Some (c, n, nf_to_exp Bn) /\
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) s ns /\
      fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns)) gs (s + ind_nn D) vs /\
      fresh_ihs gc_deps gc_stack ρ0 A0 (env_args nil (ua ++ ns)) gs vs (s + ind_nn D + List.length gs) ihs /\
      ⟦ B ⟧ env_args ρ0 (ns ++ vs ++ ihs) ↘ b /\
      ⟦ A0 ⟧ env_args ρ0 (ns ++ d_con p c (ua ++ ns ++ vs) :: nil) ↘ t /\
      Rnf ⇓ t b in gc_deps ⍮ gc_stack ⍮ (s + n) ↘ Bn.
Proof.
  induction 1; intros k c0 n0 B0 Hk; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in Hk |- *.
  - injection Hk as <- <- <-; eexists _, _, _, _, _, _, _.
    refine (conj eq_refl (conj eq_refl _)); subst; repeat split; eassumption.
  - exact (IHread_brs k c0 n0 B0 Hk).
Qed.

(** ** Function Shapes: Syntax and Values *)

(** [β] after a Kripke weakening. *)
Lemma fn_wk_beta : forall Δ' Δ IT OT M b φ (i : nat),
    Δ' ⊢ IT : Typeω@i -> Δ' ▹ IT ⊢ OT : Typeω@i -> Δ' ▹ IT ⊢ M : OT -> Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ->
    Δ ⊢ (λ IT M)[φ]ʷ $ b ≈ M[(ι φ),,b] : OT[(ι φ),,b].
Proof.
  intros * HIT HOT HM Hφ Hb; cbn [exp_wk].
  rewrite <- (exp_sub_wk_q_extend M), <- (exp_sub_wk_q_extend OT).
  eapply wf_exp_eq_pi_beta;
    [ exact (kripke_preserves_typ _ _ _ _ _ HIT Hφ) | exact (kripke_preserves_typ_q _ _ _ _ _ _ _ HOT HIT Hφ)
    | exact (kripke_preserves_exp_q _ _ _ _ _ _ _ HM HIT Hφ) | exact Hb ].
Qed.

Lemma app_wk_typed : forall Δ' Δ IT OT N b φ, Δ' ⊢ N : Π IT OT -> Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ->
    Δ ⊢ N[φ]ʷ $ b : OT[(ι φ),,b].
Proof.
  intros * HN Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  eapply wf_app'; [ exact (kripke_preserves_exp _ _ _ _ _ HN Hφ) | exact Hb ].
Qed.

Lemma eval_fam_cod_ihfam_inv : forall ρm A0 ρ0 t f x a,
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm A0 ρ0 t f ↦ x ↘ a ->
    exists fx, $| f & x | gc_deps ⍮ gc_stack ↘ fx /\ eval_ihty gc_deps gc_stack ρm A0 (ρ0 ↦ x) t fx a.
Proof.
  intros * H; unfold fam_cod in H; inversion H; subst.
  match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end.
  match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
  match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; eauto end.
Qed.


Lemma sb_wk_shift_extend : forall σ φ e, sb_eq (sb_wk σ ↑ ⨟ sb_extend (ι φ) e) (sb_wk σ φ).
Proof.
  intros σ φ e x; unfold sb_wk; cbn [sb_compose].
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  apply sentry_sub_of_wk.
Qed.

Lemma exp_qn_step : forall M n σ φ e, M[sb_qn n σ][wk_qn n ↑]ʷ[sb_qn n (sb_extend (ι φ) e)] = M[sb_qn n (sb_wk σ φ)].
Proof.
  intros; rewrite (exp_wk_sub_ext _ _ _ (sb_qn n (sb_wk σ ↑))) by (apply sb_qn_wk_ext; intros x; reflexivity).
  apply exp_sub_sub_ext, sb_qn_compose_ext, sb_wk_shift_extend.
Qed.

Lemma brs_step : forall Bs σ φ e, brs_sub (brs_wk (brs_sub Bs σ) ↑) (sb_extend (ι φ) e) = brs_sub Bs (sb_wk σ φ).
Proof.
  intros; unfold brs_sub, brs_wk; rewrite !List.map_map; apply List.map_ext; intros [[c n] B]; cbn; f_equal.
  apply exp_qn_step.
Qed.

Lemma exp_qn_wk : forall M n σ φ, M[sb_qn n σ][sb_qn n (ι φ)] = M[sb_qn n (sb_wk σ φ)].
Proof. intros; apply exp_sub_sub_ext, sb_qn_compose_ext; symmetry; apply sb_wk_compose. Qed.

Lemma ihs_ctx_nth : forall D A Us na gs gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    List.nth_error (List.rev (ihs_ctx_aux D A Us na nil 0 gs)) (cargs_nrec gs1)
    = Some (ce_ass (ptyp_ihty A (sb_of_wk (wk_shiftn (cargs_nrec gs1 + na + ind_nn D))) (ihs_sub D Us na (cargs_pat gs1) (cargs_nrec gs1))
                      (a_var (cargs_nrec gs1 + na - 1 - List.length (cargs_pat gs1))) t)).
Proof.
  intros * ->.
  rewrite ElimCases.ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux Nat.add].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_ihs_ctx_aux; lia).
  rewrite List.length_rev, length_ihs_ctx_aux, Nat.sub_diag; reflexivity.
Qed.


Lemma exp_shift_extend_wk_e : forall U φ e, U[↑]ʷ[sb_extend (ι φ) e] = U[φ]ʷ.
Proof. intros; rewrite exp_sub_shift; apply exp_sub_of_wk_ext; intros [|?]; reflexivity. Qed.

(** Substitutions with the same terms at every variable act alike on the
    terms of a shape, which have no free module variable. *)
Definition sb_exp_agree (σ τ : sub) : Prop := forall x, sentry_exp (σ x) = sentry_exp (τ x).

Lemma sb_exp_agree_q : forall σ τ, sb_exp_agree σ τ -> sb_exp_agree (q σ) (q τ).
Proof.
  intros σ τ H [| x]; [ reflexivity |].
  change (sentry_exp (sentry_wk (σ x) ↑) = sentry_exp (sentry_wk (τ x) ↑)).
  rewrite <- !sentry_exp_wk, H; reflexivity.
Qed.

Lemma ptyp_ih_agree_exp : forall nm t A Bs σ σ' M, List.Forall (exp_mvc 0) (ptyp_doms t) -> sb_exp_agree σ σ' ->
    ptyp_ih nm A Bs σ M t = ptyp_ih nm A Bs σ' M t.
Proof.
  intros nm t; induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hm Hσ; cbn in *; [ reflexivity | reflexivity |].
  inversion Hm; subst; f_equal; [ apply exp_mvc_sub_agree; assumption | apply IH; [ assumption | apply sb_exp_agree_q; exact Hσ ] ].
Qed.

Lemma ptyp_ihty_agree_exp : forall t A β β' σ σ' x, List.Forall (exp_mvc 0) (ptyp_doms t) -> List.Forall (exp_mvc 0) (ptyp_ps t) ->
    sb_eq β β' -> sb_exp_agree σ σ' -> ptyp_ihty A β σ x t = ptyp_ihty A β' σ' x t.
Proof.
  induction t as [k0 Ps | k0 Ps | B t IH]; intros * Hd Hp Hβ Hσ; cbn in *.
  1, 2: apply exp_sub_sb_eq; etransitivity; [ apply sb_of_list_cong, Hβ |];
    rewrite (List.map_ext_in (fun P => P[σ]) (fun P => P[σ']));
    [ reflexivity | intros P HP; apply exp_mvc_sub_agree; [ exact (proj1 (List.Forall_forall _ _) Hp P HP) | exact Hσ ] ].
  inversion Hd; subst; f_equal; [ apply exp_mvc_sub_agree; assumption |].
  apply IH; [ assumption | exact Hp | | apply sb_exp_agree_q; exact Hσ ].
  intros z; cbn [sb_compose]; rewrite (Hβ z); reflexivity.
Qed.

Lemma sb_exp_agree_var0 : forall σ, sb_exp_agree (q σ ⨟ ((ι ↑),,#0)) (q σ ⨟ sb_extend (ι ↑) (se_var 0)).
Proof.
  intros σ [| y]; cbn [sb_compose]; [ reflexivity |].
  f_equal; change ((q σ) (S y)) with (sentry_wk (σ y) ↑).
  rewrite !sentry_sub_wk; apply sentry_sub_sb_eq; intros z; reflexivity.
Qed.


Lemma sub_typ_extend : forall Δ' Δ IT OT φ b (j : nat), Δ' ⊢ IT : Typeω@j -> Δ' ▹ IT ⊢ OT : Typeω@j -> Δ ⊢ᵏ φ : Δ' ->
    Δ ⊢ b : IT[φ]ʷ -> Δ ⊢ OT[(ι φ),,b] : Typeω@j.
Proof.
  intros * HIT HOT Hφ Hb; rewrite <- exp_sub_wk_q_extend.
  pose proof (kripke_preserves_typ_q _ _ _ _ _ _ _ HOT HIT Hφ) as H.
  pose proof (kripke_preserves_typ _ _ _ _ _ HIT Hφ) as HIT'.
  assert (Hs : Δ ⊢ˢ Id,,b : Δ ▹ IT[φ]ʷ) by mauto 3.
  exact (sub_preserves_exp _ _ _ _ _ _ _ H Hs).
Qed.

Lemma eval_ih_pi_inv : forall ρ0 nm0 A0 Bs0 B t v r, eval_ih gc_deps gc_stack ρ0 nm0 A0 Bs0 (pt_pi B t) v r -> r = d_ihfn ρ0 nm0 A0 Bs0 t v.
Proof. intros * H; inversion H; reflexivity. Qed.

Lemma eval_ihty_pi_inv : forall ρm A0 ρ0 B t v a, eval_ihty gc_deps gc_stack ρm A0 ρ0 (pt_pi B t) v a ->
    exists b, ⟦ B ⟧ ρ0 ↘ b /\ a = Πᵈ b (nil ↦ d_ihfam ρm A0 ρ0 t v) fam_cod.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma eval_app_ihfn_inv : forall ρ0 nm0 A0 Bs0 t f c r, $| d_ihfn ρ0 nm0 A0 Bs0 t f & c | gc_deps ⍮ gc_stack ↘ r ->
    exists fc, $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ eval_ih gc_deps gc_stack ρ0 nm0 A0 Bs0 t fc r.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma per_gargs_nth_el : forall ts ρ ρ' xs xs' k A, per_gargs ts ρ ρ' xs xs' ->
    List.nth_error ts k = Some (ce_ass A) -> k < List.length xs ->
    exists (i : nat) R a a' x x', ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a /\ ⟦ A ⟧ env_args ρ' (List.firstn k xs') ↘ a' /\
      DF a ≈ a' ∈ per_univ_elem i ↘ R /\ List.nth_error xs k = Some x /\ List.nth_error xs' k = Some x' /\ R x x'.
Proof.
  intros * H; revert k; induction H as [| ? ? ? ? ? ? ? ? ? ? HA Ha Hr IH]; intros k Hk Hl; [ cbn in Hl; lia |].
  destruct k as [| k]; cbn in Hk, Hl |- *.
  - injection Hk as <-; destruct HA as [a0 a0' E E' HR]; eauto 15.
  - exact (IH k Hk ltac:(lia)).
Qed.

Section ElimSyn.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hc : decl_closed D).
  Variable (Γ : ctx) (Us : list exp) (nm : nat) (A : exp) (i : nat) (Bs : list (String.string * nat * exp)).
  Hypothesis (HUl : List.length Us = ind_nu D) (Hnm : nm = S (ind_nn D))
    (HAt : elim_mctx p D Us ++ Γ ⊢ A : Typeω@i)
    (HMx : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us)
    (Hn : brs_names (ind_cons D) Bs)
    (HBx : forall c gs, ind_con D c = Some gs -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us)
    (Hk : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
    (HBt : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
             elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us).

  (** The premises of the eliminator's rules, at the instance by a
      substitution. *)
  Lemma elim_prems_at : forall Δ σ, Δ ⊢ˢ σ : Γ ->
      elim_mctx p D (List.map (fun U => U[σ]) Us) ++ Δ ⊢ A[sb_qn nm σ] : Typeω@i /\
      gc_deps ⍮ gc_stack ⍮ Δ ⊢ˣ elim_mctx p D (List.map (fun U => U[σ]) Us) ≈ elim_mctx p D (List.map (fun U => U[σ]) Us) /\
      brs_names (ind_cons D) (brs_sub Bs σ) /\
      (forall c gs, ind_con D c = Some gs ->
         gc_deps ⍮ gc_stack ⍮ Δ ⊢ˣ elim_bctx p D gs A[sb_qn nm σ] (List.map (fun U => U[σ]) Us)
           ≈ elim_bctx p D gs A[sb_qn nm σ] (List.map (fun U => U[σ]) Us)) /\
      (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_sub Bs σ) ->
         n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) /\
      (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) (brs_sub Bs σ) ->
         elim_bctx p D gs A[sb_qn nm σ] (List.map (fun U => U[σ]) Us) ++ Δ
           ⊢ B : elim_bty p D c gs A[sb_qn nm σ] (List.map (fun U => U[σ]) Us)).
  Proof.
    intros Δ σ Hσ; subst nm.
    pose proof (sub_preserves_ext _ _ _ _ _ _ _ HMx Hσ) as HΨσ.
    pose proof (sub_elim_motive_ctx _ _ _ _ _ _ _ _ Hc HUl Hσ HMx HΨσ) as Hq.
    split; [ exact (sub_preserves_exp _ _ _ _ _ _ _ HAt Hq) |].
    split; [ rewrite <- elim_mctx_sub by assumption; exact HΨσ |].
    split; [ apply brs_names_map; exact Hn |].
    split; [ intros c gs Hcn; rewrite <- (elim_bctx_sub p D c gs A _ σ Hc (cons_lookup_in _ _ _ Hcn) HUl);
             exact (sub_preserves_ext _ _ _ _ _ _ _ (HBx c gs Hcn) Hσ) |].
    split; [ intros c gs n B' Hcn Hin; apply brs_in_map in Hin as (B & Hin & ->); eapply Hk; eassumption |].
    intros c gs n B' Hcn Hin; apply brs_in_map in Hin as (B & Hin & ->); cbn [fst snd].
    rewrite <- elim_bty_sub, (Hk _ _ _ _ Hcn Hin).
    apply (sub_preserves_exp _ _ _ _ _ _ _ (HBt c gs n B Hcn Hin)).
    apply (sub_elim_branch_ctx _ _ _ _ _ _ _ c); [ exact Hc | exact (cons_lookup_in _ _ _ Hcn) | exact HUl | exact Hσ | exact (HBx c gs Hcn) |].
    exact (sub_preserves_ext _ _ _ _ _ _ _ (HBx c gs Hcn) Hσ).
  Qed.
End ElimSyn.

(** ** The Eliminator's Contexts at an Environment

    The links between the types of the eliminator's contexts at an
    environment glued to a substitution, and the declaration's types at
    the values of the uniform parameters there. *)
Section ElimSem.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_core D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (HDc : IndCases.sem_core D).
  Let HD : IndCases.sem_decl D := ElimCases.sem_decl_of_core D HDc Hc Hsu Hdt.
  Let Ua : tele_ass (ind_uparams D) := decl_uparams_ass D Hc.
  Let Usem : ⊨ ind_uparams D := IndCases.uparams_sem D HDc.
  Let Hsimp := IndCases.sd_simple D HDc.
  Let Hplen := IndCases.sd_plen D HDc.
  (** An element of the inductive type at glued parameters, related to
      itself, and an element at every weakening and instance of the
      parameters, at the gluings of the clause at [ups], is glued at the
      type. *)
  Lemma ind_elem_glue : forall (u : uidx) R ups0 ns bu NP NEl AP AEl DP DEl Δ Q M m,
      List.length ups0 = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups0 ↘ bu -> uidx_le (IndSem.univ_idx bu) u ->
      (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups0) k vs vs -> ⟦ A ⟧ env_args nil (ups0 ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs) ->
      (forall ms c gs k A vs b, tele_full (ind_nr D ups0) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
         tele_pre (ind_ar D ups0 ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups0 ++ ms ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs) ->
      (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups0) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups0 ms c) (List.length (cargs_nonrec gs1)) ws ws ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups0) ms ws (ptyp_doms t)) k ys ys ->
         ⟦ B ⟧ env_args nil (ups0 ++ ms ++ ws ++ ys) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B) ->
      DF d_ind p (ups0 ++ ns) ≈ d_ind p (ups0 ++ ns) ∈ per_univ_elem u ↘ R ->
      ⊢ Δ -> glu_args Δ (ind_params D) Id nil Q (ups0 ++ ns) -> Δ ⊢ M : apps (a_ind p) Q -> R m m ->
      (forall Δ' φ Q', Δ' ⊢ᵏ φ : Δ -> exps_eq_at Δ' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups0 NEl AEl DP DEl Δ' Q' M[φ]ʷ m) ->
      exists P El, DG d_ind p (ups0 ++ ns) ∈ glu_univ_elem u ↘ P ↘ El /\ Δ ⊢ apps (a_ind p) Q ® P /\
        Δ ⊢ M : apps (a_ind p) Q ® m ∈ El.
  Proof.
    intros * Hu Hbu Hule HNP HAP HDP HR HΔ Hg HM Hm HK.
    destruct (glu_ind_of_per p D Hl u R ups0 ns HR Hu)
      as (NP' & NEl' & AP' & AEl' & DP' & DEl' & P & El & R' & Hg' & HP & HEl & HRR & HeN' & HNP' & HeA' & HAP' & HeD' & HDP').
    pose proof (decl_closed_params D Hc) as Hass.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR Hl Hu Hu) as (_ & _ & Hcp & _).
    pose proof (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Δ Q ups0 ns bu u NP' NEl' AP' AEl' DP' DEl' HΔ Hg Hu Hbu Hule
                  HeN' HNP' HeA' HAP' HeD' HDP') as HT.
    exists P, El; split; [ exact Hg' | split ].
    - apply HP; exists Q; exact HT.
    - apply HEl; refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _ Q HT _); [ apply HRR; exact Hm |].
      intros Δ' φ Q' Hφ HQ'.
      apply (glu_ind_mono p D ups0 NEl AEl DP DEl Hass Hcp NEl' AEl' DP' DEl'); [ | | | exact (HK _ _ _ Hφ HQ') ].
      + intros k vs Hk Hp Γ0 A0 N n HN.
        destruct (nparams_lt_ass D k Hass ltac:(rewrite List.length_rev, length_nparams; exact Hk)) as [S HS].
        destruct (HeN' _ _ _ HS Hp) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HNP _ _ _ _ HS Hp Eb) (HNP' _ _ _ _ HS Hp Eb)) as [_ E].
        apply E; exact HN.
      + intros ms c gs k vs Hms Hcon Hk Hp Γ0 A0 N n HN.
        destruct (nth_error_lt_some' _ _ Hk) as [S HS].
        destruct (HeA' _ _ _ _ _ _ Hms Hcon HS Hp) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HAP _ _ _ _ _ _ _ Hms Hcon HS Hp Eb) (HAP' _ _ _ _ _ _ _ Hms Hcon HS Hp Eb)) as [_ E].
        apply E; exact HN.
      + intros ms c gs gs1 t gs2 ws k B ys Hms Hcon Heq Hws HB Hys.
        destruct (HeD' _ _ _ _ _ _ _ _ _ _ Hms Hcon Heq Hws HB Hys) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HDP _ _ _ _ _ _ _ _ _ _ _ Hms Hcon Heq Hws HB Hys Eb)
                    (HDP' _ _ _ _ _ _ _ _ _ _ _ Hms Hcon Heq Hws HB Hys Eb)) as [EP EE].
        split; [ intros Γ0 A0 H; apply EP; exact H | intros Γ0 A0 N n _ H; apply EE; exact H ].
  Qed.

  Variable (Γ : ctx) (RΓ : relation env).
  Hypothesis (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypothesis (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Let τU := sb_of_list Id Us.
  Variable (ρ : env) (ups : list domain).
  Hypothesis (Hρ : RΓ ρ ρ) (HUv : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ups).

  Lemma ups_len : List.length ups = ind_nu D.
  Proof. rewrite <- HUl; exact (IndCases.eval_exps_length _ _ _ HUv). Qed.

  Lemma ups_RU : RU (env_args nil ups) (env_args nil ups).
  Proof.
    destruct (ElimCases.us_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ρ ρ Hρ) as (u1 & u2 & E1 & E2 & H).
    pose proof (functional_eval_exps' _ _ _ _ E1 HUv) as ->; pose proof (functional_eval_exps' _ _ _ _ E2 HUv) as ->; exact H.
  Qed.

  Lemma ups_gargs : per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof. exact (ElimCases.U_gargs D HD Hc RU HRU _ _ ups_RU ups_len ups_len). Qed.

  Lemma τU_eval : ⟦ τU ⟧s ρ ↘ env_args ρ ups.
  Proof. exact (IndSem.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) HUv). Qed.

  (** An instance of a closed telescope's type at [τU], at an environment
      extended by values related at the telescope at [ups], against the
      type at [ups] and those values. *)
  Lemma inst_link : forall Pre X (j : nat) zs, tele_ass (Pre ++ ind_uparams D) -> ⊨ Pre ++ ind_uparams D ->
      ⊨ tele_sub Pre τU ++ Γ -> Pre ++ ind_uparams D ⊨ X : Typeω@j ->
      per_gargs (List.rev Pre) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length Pre ->
      exists a b, ⟦ X[sb_qn (List.length Pre) τU] ⟧ env_args ρ zs ↘ a /\ ⟦ X ⟧ env_args nil (ups ++ zs) ↘ b /\
        Dom a ≈ b ∈ per_univ j.
  Proof.
    intros * HKa HK HS HX Hg Hlz.
    pose proof (ElimCases.cv_gen D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups ups_gargs ups_len Pre HKa HK HS
                  ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU zs zs Hg Hlz) as Hg'.
    destruct (sem_ctx_per_ctx_env HS) as [RS HRS].
    pose proof (TeleSem.gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS HS Hρ ltac:(rewrite length_tele_sub; exact Hlz) Hg') as HE.
    destruct (sem_ctx_per_ctx_env HK) as [RK HRK].
    pose proof (ElimCases.closed_pre_base D HD Hc RU HRU Us HUl ups ups_gargs ups_len Pre RK HKa HK HRK ρ ups zs
                  ups_RU ups_len Hg Hlz) as HF.
    exact (TeleSem.closed_typ_inst Pre (ind_uparams D) Γ X j τU RΓ RK RS ρ zs (env_args ρ ups) (env_args nil (ups ++ zs))
             HKa HK Ua Usem HΓ HRΓ HRK HRS HX
             (InstanceCases.gsub_valid (ElimCases.gsub_U D HD Hc Γ HΓ Us HUl HUs)) HE Hlz τU_eval HF).
  Qed.
  (** Glued arguments of a closed telescope over the uniform parameters,
      at the declaration's types at [ups], are glued arguments of its
      instance at [τU], over a substitution glued to [ρ]. *)
  Lemma tele_inst_args : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D ->
      ⊨ tele_sub C τU ++ Γ -> ctx_scoped (ind_nu D) C ->
      forall Δ' σ' Ms zs, glu_args Δ' C (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ms zs ->
        per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs ->
        glu_args Δ' (tele_sub C τU) σ' ρ Ms zs.
  Proof.
    intros C HCa HCs HCS HCsc Δ' σ' Ms zs Hg Hpg.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [LM Lz].
    apply (glu_args_link Δ' C (tele_sub C τU) (sb_of_list Id (List.map (fun U => U[σ']) Us)) σ' (env_args nil ups) ρ Ms zs); [ rewrite length_tele_sub; reflexivity | | exact Hg | |].
    - rewrite tele_insts_tele_sub; symmetry; apply (tele_insts_base_agree _ (ind_nu D)); [ exact HCa' | exact HCsc |].
      intros x Hx; cbn [sb_compose]; unfold τU; apply sb_of_list_lt_compose; lia.
    - intros k A A' a HA HA' Hk Ea.
      destruct (ctx_rev_split C k _ HA) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <-.
      rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
      assert (HKa : tele_ass (Pre ++ ind_uparams D))
        by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
      pose proof (UnitCases.sem_ctx_app_r _ _ HCs) as HK1.
      destruct (MemberReps.sem_ctx_ass_inv HK1) as [j HX].
      pose proof (sem_ctx_tail HK1) as HK.
      rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (UnitCases.sem_ctx_app_r _ _ HCS) as HS1.
      cbn [tele_sub List.app] in HS1; pose proof (sem_ctx_tail HS1) as HS.
      rewrite List.rev_app_distr in Hpg; cbn [List.rev] in Hpg; rewrite <- List.app_assoc in Hpg.
      rewrite <- (List.firstn_skipn k zs) in Hpg.
      assert (Lk : List.length (List.firstn k zs) = k) by (rewrite List.length_firstn; lia).
      assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_rev; lia).
      destruct (IndSem.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
        as [Hg1 _].
      destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(lia)) as (a1 & b & Ea1 & Eb & Hab).
      rewrite <- env_args_app in Ea.
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a1, j; split; assumption.
    - intros k e' He'.
      assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
      assert (HeA : exists A, e = ce_ass A).
      { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
        unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
      destruct HeA as [A ->].
      destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
      rewrite <- HPl in He'; rewrite nth_rev_tele_sub in He'; injection He' as <-.
      exists A; split; [ exact He | eexists; reflexivity ].
  Qed.
  (** The type of an entry of the instance at [τU] of a closed telescope,
      against the entry's type at [ups]. *)
  Lemma inst_entry_link : forall C, tele_ass (C ++ ind_uparams D) -> ⊨ C ++ ind_uparams D -> ⊨ tele_sub C τU ++ Γ ->
      forall zs, per_gargs (List.rev C) (env_args nil ups) (env_args nil ups) zs zs -> List.length zs = List.length C ->
      forall k A' a, List.nth_error (List.rev (tele_sub C τU)) k = Some (ce_ass A') -> ⟦ A' ⟧ env_args ρ (List.firstn k zs) ↘ a ->
        exists A b (j : nat), List.nth_error (List.rev C) k = Some (ce_ass A) /\
          ⟦ A ⟧ env_args nil (ups ++ List.firstn k zs) ↘ b /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros C HCa HCs HCS zs Hpg Hlz k A' a HA' Ea.
    assert (HCa' : tele_ass C) by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [H _]; exact H).
    assert (Hk : k < List.length C) by (rewrite <- (length_tele_sub C τU), <- List.length_rev; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    assert (HeA : exists A, e = ce_ass A).
    { pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
      unfold tele_ass in HCa'; rewrite List.Forall_forall in HCa'; exact (HCa' _ Hin). }
    destruct HeA as [A ->].
    pose proof He as He0.
    destruct (ctx_rev_split C k _ He) as (C1 & Pre & -> & HPl).
    rewrite <- HPl in HA'; rewrite nth_rev_tele_sub in HA'; injection HA' as <-.
    rewrite <- List.app_assoc in HCa, HCs; cbn [List.app] in HCa, HCs.
    assert (HKa : tele_ass (Pre ++ ind_uparams D))
      by (unfold tele_ass in HCa; apply List.Forall_app in HCa as [_ H]; inversion H; assumption).
    pose proof (UnitCases.sem_ctx_app_r _ _ HCs) as HK1.
    destruct (MemberReps.sem_ctx_ass_inv HK1) as [j HX].
    pose proof (sem_ctx_tail HK1) as HK.
    rewrite tele_sub_app, <- List.app_assoc in HCS; pose proof (UnitCases.sem_ctx_app_r _ _ HCS) as HS1.
    cbn [tele_sub List.app] in HS1; pose proof (sem_ctx_tail HS1) as HS.
    rewrite List.rev_app_distr in Hpg; cbn [List.rev] in Hpg; rewrite <- List.app_assoc in Hpg.
    rewrite <- (List.firstn_skipn k zs) in Hpg.
    rewrite !List.length_app in Hlz; cbn in Hlz.
    assert (L1 : List.length (List.firstn k zs) = List.length (List.rev Pre)) by (rewrite List.length_firstn, List.length_rev; lia).
    destruct (IndSem.per_gargs_app (List.rev Pre) _ _ _ (List.firstn k zs) (List.firstn k zs) (List.skipn k zs) (List.skipn k zs) L1 Hpg L1)
      as [Hg1 _].
    destruct (inst_link Pre A j (List.firstn k zs) HKa HK HS HX Hg1 ltac:(rewrite List.length_firstn; lia)) as (a1 & b & Ea1 & Eb & Hab).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    exists A, b, j; split; [ exact He0 | split; [ exact Eb | exact Hab ] ].
  Qed.

  Variable (bu : domain).
  Hypothesis (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu).

  Lemma ns_gargs : forall ns ns', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns' ->
      per_gargs (List.rev (ind_nparams D)) (env_args nil ups) (env_args nil ups) ns ns'.
  Proof.
    intros * H; pose proof (tele_full_pre _ _ _ _ H) as Hp.
    rewrite List.length_rev, length_nparams in Hp.
    pose proof (IndCases.nr_gargs D HDc Hc Hsu ups ups bu ups_gargs ups_len Hbu (ind_nn D) ns ns' (le_n _) Hp) as Hg.
    rewrite List.firstn_all2 in Hg by (rewrite List.length_rev, length_nparams; lia); exact Hg.
  Qed.

  Lemma it_inst : forall σ Ns, List.length Ns = ind_nn D ->
      (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))[sb_of_list σ Ns]
      = apps (a_ind p) (List.map (fun U => U[σ]) Us ++ Ns).
  Proof.
    intros * HNl.
    rewrite apps_exp_sub, List.map_app, List.map_map; cbn [exp_sub].
    rewrite <- HNl, map_shift_sb_of_list, vars_from_sb_of_list; reflexivity.
  Qed.

  Hypothesis (HNt : ⊨ tele_sub (ind_nparams D) τU ++ Γ).
  Variable (SbΓ : glu_sub_pred).
  Hypothesis (HSbΓ : EG Γ ∈ glu_ctx_env ↘ SbΓ).

  (** The non-uniform parameters glued at their declaration's types at
      [ups], at the instance at [τU]. *)
  Lemma nparams_inst_args : forall Δ' σ' Ns ns,
      glu_args Δ' (ind_nparams D) (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ns ns ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      glu_args Δ' (tele_sub (ind_nparams D) τU) σ' ρ Ns ns.
  Proof.
    intros * Hg Hns.
    apply tele_inst_args; [ rewrite <- params_split; exact (decl_closed_params D Hc)
                          | rewrite <- params_split; exact (IndCases.sd_params D HDc) | exact HNt
                          | exact (decl_closed_nparams_scoped D Hc) | exact Hg | exact (ns_gargs _ _ Hns) ].
  Qed.

  (** The fresh variables at [ups] of the motive's context, against its
      instance's types. *)
  Lemma mctx_entry_link : forall s ns_u, fresh_tele gc_deps gc_stack (env_args nil ups) (List.rev (ind_nparams D)) s ns_u ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns_u ns_u ->
      forall k X a, List.nth_error (List.rev (elim_mctx p D Us)) k = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn k (ns_u ++ ⇑! (d_ind p (ups ++ ns_u)) (s + ind_nn D) :: nil)) ↘ a ->
        exists b (j : nat), List.nth_error (ns_u ++ ⇑! (d_ind p (ups ++ ns_u)) (s + ind_nn D) :: nil) k = Some (⇑! b (s + k)) /\
          Dom a ≈ b ∈ per_univ j.
  Proof.
    intros s ns_u Hf Hns k X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Hf) as Ln; rewrite List.length_rev, length_nparams in Ln.
    pose proof (ns_gargs _ _ Hns) as Hg.
    assert (HKa : tele_ass (ind_nparams D ++ ind_uparams D)) by (rewrite <- params_split; exact (decl_closed_params D Hc)).
    assert (HK : ⊨ ind_nparams D ++ ind_uparams D) by (rewrite <- params_split; exact (IndCases.sd_params D HDc)).
    unfold elim_mctx in HX; cbn [List.rev] in HX.
    destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HX by (rewrite List.length_rev, length_ind_nparams_sub; lia).
      rewrite firstn_app_le in Ea by lia.
      destruct (inst_entry_link (ind_nparams D) HKa HK HNt ns_u Hg ltac:(rewrite length_nparams; exact Ln) k X a HX Ea)
        as (A0 & b & j & HA & Eb & Hab).
      destruct (fresh_tele_nth _ _ _ _ Hf k A0 HA) as (b' & Eb' & Hb').
      rewrite <- env_args_app in Eb'.
      assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
      exists b, j; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
    - assert (k = ind_nn D) as ->.
      { match type of HX with List.nth_error ?l _ = _ =>
          assert (Hlt : k < List.length l) by (apply List.nth_error_Some; rewrite HX; discriminate) end.
        rewrite List.length_app, List.length_rev, length_ind_nparams_sub in Hlt; cbn in Hlt; lia. }
      rewrite List.nth_error_app2 in HX by (rewrite List.length_rev, length_ind_nparams_sub; lia).
      rewrite List.length_rev, length_ind_nparams_sub, Nat.sub_diag in HX; cbn in HX; injection HX as <-.
      rewrite firstn_app_le, List.firstn_all2 in Ea by lia.
      pose proof (ElimCases.cv_gen D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups ups_gargs ups_len (ind_nparams D) HKa HK HNt
                    ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU ns_u ns_u Hg ltac:(rewrite length_nparams; exact Ln)) as Hg'.
      destruct (sem_ctx_per_ctx_env HNt) as [RS HRS].
      pose proof (TeleSem.gargs_env_rel_gen _ _ _ _ _ _ _ _ HRΓ HRS HNt Hρ
                    ltac:(rewrite length_tele_sub, length_nparams; exact Ln) Hg') as HE.
      destruct (ElimCases.us_wk_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs _ RS ρ ns_u HRS HNt HE
                  ltac:(rewrite length_ind_nparams_sub; exact Ln)) as (w & u' & Hw & Hu' & Hwu).
      pose proof (functional_eval_exps' _ _ _ _ Hu' HUv) as ->.
      rewrite length_ind_nparams_sub in Hw.
      pose proof (ElimCases.eval_IT D Hc p Hl Us HUl ups ups_len ρ ns_u w Ln Hw) as Ew.
      assert (a = d_ind p (w ++ ns_u)) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (IndCases.eval_exps_length _ _ _ Hw) as Lw; rewrite List.length_map, HUl in Lw.
      pose proof (IndCases.ind_relate D HDc Hc Hsu p Hl ups w ns_u ns_u bu
                    (ElimCases.U_gargs D HD Hc RU HRU _ _ (symmetry Hwu) ups_len Lw) ups_len Hbu Hns) as Hrl.
      destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hrl) as [n Hn].
      exists (d_ind p (ups ++ ns_u)), n; split.
      + rewrite List.nth_error_app2, Ln, Nat.sub_diag by lia; reflexivity.
      + apply per_univ_sym'; eexists; exact Hn.
  Qed.

  (** The substitution of the motive's context at glued non-uniform
      parameters and a scrutinee glued at the type at them. *)
  Lemma mctx_glu_sub : forall SbM, EG elim_mctx p D Us ++ Γ ∈ glu_ctx_env ↘ SbM ->
      forall Δ' σ' Ns ns M m (j : uidx) P El, Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
        glu_args Δ' (ind_nparams D) (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ns ns ->
        tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        DG d_ind p (ups ++ ns) ∈ glu_univ_elem j ↘ P ↘ El ->
        Δ' ⊢ apps (a_ind p) (List.map (fun U => U[σ']) Us ++ Ns) ® P ->
        Δ' ⊢ M : apps (a_ind p) (List.map (fun U => U[σ']) Us ++ Ns) ® m ∈ El ->
        Δ' ⊢ˢ sb_of_list σ' (Ns ++ M :: nil) ® env_args ρ (ns ++ m :: nil) ∈ SbM.
  Proof.
    intros SbM HSbM Δ' σ' Ns ns M m j P El Hσ' Hg Hns Hgj HP HMg.
    pose proof (nparams_inst_args _ _ _ _ Hg Hns) as Hg1.
    destruct (glu_args_length _ _ _ _ _ _ Hg1) as [LN Ln]; rewrite length_ind_nparams_sub in LN, Ln.
    assert (HassN : tele_ass (tele_sub (ind_nparams D) τU)) by (apply tele_ass_sub, decl_closed_nparams_ass, Hc).
    eapply glu_sub_of_list; [ apply elim_mctx_ass, Hc | exact HSbM | exact HSbΓ | exact Hσ' |].
    unfold elim_mctx; change (ce_ass ?H0 :: ?R) with ((ce_ass H0 :: nil) ++ R).
    apply glu_args_app; [ exact HassN | rewrite length_ind_nparams_sub; exact LN | rewrite length_ind_nparams_sub; exact Ln |].
    split; [ exact Hg1 |].
    change (ce_ass ?H0 :: nil) with (nil ++ ce_ass H0 :: nil).
    apply glu_args_snoc; split; [| apply glu_args_nil ].
    (** The scrutinee's type at the environment. *)
    assert (HSbN : exists SbN, EG tele_sub (ind_nparams D) τU ++ Γ ∈ glu_ctx_env ↘ SbN)
      by (unfold elim_mctx in HSbM; cbn [List.app] in HSbM; inversion HSbM; subst; eauto).
    destruct HSbN as [SbN HSbN].
    pose proof (glu_sub_of_list _ _ _ _ _ _ _ _ _ HassN HSbN HSbΓ Hσ' Hg1) as Hσ1.
    destruct (sem_ctx_per_ctx_env HNt) as [RS HRS].
    pose proof (glu_ctx_env_per_env HSbN HRS Hσ1) as HE.
    destruct (ElimCases.us_wk_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs _ RS ρ ns HRS HNt HE
                ltac:(rewrite length_ind_nparams_sub; exact Ln)) as (w & u' & Hw & Hu' & Hwu).
    pose proof (functional_eval_exps' _ _ _ _ Hu' HUv) as ->.
    rewrite length_ind_nparams_sub in Hw.
    pose proof (ElimCases.eval_IT D Hc p Hl Us HUl ups ups_len ρ ns w Ln Hw) as Ew.
    pose proof (IndCases.eval_exps_length _ _ _ Hw) as Lw; rewrite List.length_map, HUl in Lw.
    pose proof (IndCases.ind_relate D HDc Hc Hsu p Hl ups w ns ns bu
                  (ElimCases.U_gargs D HD Hc RU HRU _ _ (symmetry Hwu) ups_len Lw) ups_len Hbu Hns) as Hrel.
    destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hrel) as [n Hn].
    assert (Hpu : Dom d_ind p (ups ++ ns) ≈ d_ind p (w ++ ns) ∈ per_univ n) by (eexists; exact Hn).
    destruct (glu_transfer_per' j n _ _ P El Δ' _ M m Hgj Hpu HP HMg) as (k' & P' & El' & Hg' & HP' & HM').
    rewrite it_inst by exact LN.
    exact (mk_glu_arg _ _ _ _ _ _ k' (d_ind p (w ++ ns)) P' El' Ew Hg' HP' HM').
  Qed.

  (** ** The Eliminator, by Induction on the Gluing of the Scrutinee *)
  Variable (nm : nat) (A : exp) (iA : nat) (Bs : list (String.string * nat * exp)).
  Hypothesis (Hnm : nm = S (ind_nn D))
    (HAt : elim_mctx p D Us ++ Γ ⊢ A : Typeω@iA)
    (HMx : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D Us ≈ elim_mctx p D Us)
    (HBn : brs_names (ind_cons D) Bs)
    (HBx : forall c gs, ind_con D c = Some gs -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx p D gs A Us ≈ elim_bctx p D gs A Us)
    (HBa : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat)
    (HBt : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
             elim_bctx p D gs A Us ++ Γ ⊢ B : elim_bty p D c gs A Us)
    (HAg : elim_mctx p D Us ++ Γ ⊩ A : Typeω@iA)
    (HBg : forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
             elim_bctx p D gs A Us ++ Γ ⊩ B : elim_bty p D c gs A Us)
    (HUg : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊩ N : T).
  Variable (u : nat) (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred).
  Hypothesis (Hule : uidx_le (IndSem.univ_idx bu) (ul u))
    (HeN : forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b)
    (HNP : forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem (ul u) ↘ NP k vs ↘ NEl k vs)
    (HeA : forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b)
    (HAP : forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem (ul u) ↘ AP ms c k vs ↘ AEl ms c k vs)
    (HeD : forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
       exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b)
    (HDP : forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
       ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
       DG b ∈ glu_univ_elem (ul u) ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B).
  Variable (R0 : relation domain) (ns0 : list domain).
  Hypothesis (HR0 : DF d_ind p (ups ++ ns0) ≈ d_ind p (ups ++ ns0) ∈ per_univ_elem (ul u) ↘ R0).

  Lemma us_glu_args : forall Δ'' σ'', Δ'' ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      glu_args Δ'' (ind_uparams D) Id nil (List.map (fun U => U[σ'']) Us) ups.
  Proof.
    intros * Hσ''.
    eapply params_glu_args; [ exact Ua | exact (decl_uparams_closed D Hc) | exact Usem | exact HΓ | exact HRΓ | exact HSbΓ | exact Hσ''
                            | rewrite length_ind_uparams by exact (decl_closed_nu D Hc); exact HUl | exact HUs | exact HUg | exact HUv ].
  Qed.

  Let HM : ⊨ elim_mctx p D Us ++ Γ := completeness_fundamental_ctx _ (proj1 (presup_exp HAt)).
  Let HAv : elim_mctx p D Us ++ Γ ⊨ A : Typeω@iA := completeness_fundamental_exp _ _ _ HAt.
  Let Hcan := ElimCases.u0_canon D HD Hc Hsu ups bu ups_gargs ups_len Hbu.
  Let HnP := proj1 Hcan.
  Let HnI := proj1 (proj2 Hcan).
  Let HaP := proj1 (proj2 (proj2 Hcan)).
  Let HaI := proj1 (proj2 (proj2 (proj2 Hcan))).
  Let HdP := proj1 (proj2 (proj2 (proj2 (proj2 Hcan)))).
  Let HdI := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hcan))))).
  Let Had := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hcan))))).
  Let Hass : tele_ass (ind_params D) := decl_closed_params D Hc.
  Let Hle : ind_nu D <= ind_np D := decl_closed_nu D Hc.
  Let imv := IndElim.ind_rel_mv p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen.
  Let tsym := tnr_sym p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI.
  Let ttrans := tnr_trans p D ups _ _ _ Hass HnP HnI HaP HaI HdP HdI.
  Let mmid := ElimCases.mot_mid D HD Hc Hsu p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM A A iA HAv ρ ρ Hρ HUv.

  Let Rel := fun ns m ns' m' => per_head A A (env_args ρ (ns ++ m :: nil)) (env_args ρ (ns' ++ m' :: nil)).

  Lemma bctx_sem : forall c gs, ind_con D c = Some gs -> ⊨ elim_bctx p D gs A Us ++ Γ.
  Proof.
    intros c gs Hcn.
    destruct (IndElim.brs_names_lookup _ _ _ _ HBn Hcn) as (n & B & _ & Hin).
    exact (completeness_fundamental_ctx _ (proj1 (presup_exp (HBt c gs n B Hcn Hin)))).
  Qed.

  Lemma brs_rel : forall c gs n B B', ind_con D c = Some gs -> brs_lookup Bs c = Some (n, B) -> brs_lookup Bs c = Some (n, B') ->
      elim_bctx p D gs A Us ++ Γ ⊨ B ≈ B' : elim_bty p D c gs A Us.
  Proof.
    intros * Hcn H1 H2; rewrite H1 in H2; injection H2 as <-.
    exact (completeness_fundamental_exp _ _ _ (HBt c gs n B Hcn (brs_lookup_in _ _ _ _ H1))).
  Qed.

  Let Hbrm := ElimCases.br_mid D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
               A A iA HAv ρ ρ Hρ HUv bctx_sem Bs Bs brs_rel.
  Let pelim := IndElim.per_ind_elim_all p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                 (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.
  Let fnp2 := IndElim.fresh_np2 p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.
  Let frargs := IndElim.fresh_args p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.
  Let irvar := IndElim.ind_rel_var p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.
  Let shex := IndElim.shty_exists p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.
  Let pbelim := IndElim.per_bot_elim p D ups _ _ _ Hl Hass HnP HnI HaP HaI HdP HdI Had Hle Hsimp Hplen iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.

  (** The substitution of the motive's context at the fresh variables a
      stuck eliminator's readback makes, at admissible uniform parameters. *)
  Lemma mctx_fresh_glu : forall SbM, EG elim_mctx p D Us ++ Γ ∈ glu_ctx_env ↘ SbM ->
      forall Δ σ'' ua ns_x, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ -> ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ua -> List.length ua = ind_nu D ->
        fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
        elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ˢ sb_qn nm σ''
          ® env_args ρ (ns_x ++ ⇑! (d_ind p (ua ++ ns_x)) (List.length Δ + ind_nn D) :: nil) ∈ SbM.
  Proof.
    intros SbM HSbM Δ σ'' ua ns_x Hσ'' Hadm Lua Hfx.
    destruct (fnp2 ups ua (List.length Δ) Had Hadm) as (ns_u & ns_x' & Fu & Fx & Hux).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ Fx Hfx) as ->; clear Fx.
    pose proof (ttrans _ _ _ Hux (tsym _ _ Hux)) as Huu.
    pose proof (fresh_tele_length _ _ _ _ Fu) as Lu; rewrite List.length_rev, length_nparams in Lu.
    pose proof (fresh_tele_length _ _ _ _ Hfx) as Lx; rewrite List.length_rev, length_nparams in Lx.
    assert (HMlen : List.length (elim_mctx p D Us) = nm) by (rewrite length_elim_mctx; symmetry; exact Hnm).
    rewrite <- (elim_mctx_sub p D Us σ'' Hc HUl), <- HMlen.
    assert (Hws : tele_sub (elim_mctx p D Us) σ'' ++ Δ ⊢ˢ sb_qn (List.length (elim_mctx p D Us)) σ''
                    ® env_args ρ (ns_u ++ ⇑! (d_ind p (ups ++ ns_u)) (List.length Δ + ind_nn D) :: nil) ∈ SbM).
    { apply (glu_sub_fresh _ Γ SbΓ (elim_mctx_ass p D Us Hc) HSbΓ SbM HSbM Δ σ'' ρ _ Hσ'');
        [ rewrite List.length_app, length_elim_mctx; cbn; lia |].
      intros k X a HX Ea; exact (mctx_entry_link _ _ Fu Huu k X a HX Ea). }
    destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
    pose proof (irvar ns_u ups ua ns_u ns_x (List.length Δ + ind_nn D) Had Hadm ups_len Lua Huu Hux) as Hv.
    pose proof (ElimCases.cv_mctx D HD Hc Hsu p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  ρ ρ ups ups Hρ HUv HUv ups_RU ups_RU RM HRM _ _ _ _ Hux Hv) as HE.
    assert (HMr : ⊨ List.rev (List.rev (elim_mctx p D Us)) ++ Γ) by (rewrite List.rev_involutive; exact HM).
    assert (HRMr : EF List.rev (List.rev (elim_mctx p D Us)) ++ Γ ≈ List.rev (List.rev (elim_mctx p D Us)) ++ Γ ∈ per_ctx_env ↘ RM)
      by (rewrite List.rev_involutive; exact HRM).
    assert (Ll : forall Y (y : domain), List.length Y = ind_nn D -> List.length (Y ++ y :: nil) = List.length (List.rev (elim_mctx p D Us)))
      by (intros; rewrite List.length_rev, length_elim_mctx, List.length_app; cbn; lia).
    pose proof (proj2 (IndSem.rel_gargs _ _ _ _ HRΓ HMr (List.Forall_rev (elim_mctx_ass p D Us Hc)) HRMr _ _ _ _
                         (Ll _ _ Lu) (Ll _ _ Lx) HE)) as Hg.
    eapply (glu_sub_resp_args _ Γ SbΓ (elim_mctx_ass p D Us Hc) HSbΓ SbM HSbM); [| exact Hg | exact Hws ].
    rewrite List.length_app, length_elim_mctx; cbn; lia.
  Qed.

  (** The fresh variables at [ups] of a branch's context, against its
      instance's types. *)
  Lemma bctx_entry_link : forall c gs, ind_con D c = Some gs ->
      forall s ns_u vs_u ihs_u,
      fresh_tele gc_deps gc_stack (env_args nil ups) (List.rev (ind_nparams D)) s ns_u ->
      fresh_cargs gc_deps gc_stack p ups (env_args nil (ups ++ ns_u)) gs (s + ind_nn D) vs_u ->
      fresh_ihs gc_deps gc_stack ρ A (env_args nil (ups ++ ns_u)) gs vs_u (s + ind_nn D + List.length gs) ihs_u ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns_u ns_u ->
      tele_full (ind_ar D ups ns_u c) (cargs_nonrec gs) (nonrec_vals gs vs_u) (nonrec_vals gs vs_u) ->
      ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns_u gs vs_u vs_u ->
      ihs_rel ups (ind_dr ups) Rel ns_u gs vs_u vs_u ihs_u ihs_u ->
      forall k X a, List.nth_error (List.rev (elim_bctx p D gs A Us)) k = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn k (ns_u ++ vs_u ++ ihs_u)) ↘ a ->
        exists b (j : nat), List.nth_error (ns_u ++ vs_u ++ ihs_u) k = Some (⇑! b (s + k)) /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros c gs Hcon s ns_u vs_u ihs_u Fn Fc Fi Hns Har Hia Hir k X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_nparams in Ln.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    pose proof (bctx_sem c gs Hcon) as HBs.
    assert (Hbe : elim_bctx p D gs A Us = ihs_ctx_aux D A Us (List.length gs) nil 0 gs ++ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU)
      by (unfold elim_bctx; rewrite tele_sub_app, length_nparams; reflexivity).
    rewrite Hbe, List.rev_app_distr in HX.
    assert (LC : List.length (List.rev (tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU)) = ind_nn D + List.length gs)
      by (rewrite List.length_rev, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia).
    destruct (Nat.lt_ge_cases k (ind_nn D + List.length gs)) as [Hk | Hk].
    - (** The parameters and the arguments. *)
      rewrite List.nth_error_app1 in HX by lia.
      assert (Hfk : List.firstn k (ns_u ++ vs_u ++ ihs_u) = List.firstn k (ns_u ++ vs_u))
        by (rewrite List.app_assoc, firstn_app_le by (rewrite List.length_app; lia); reflexivity).
      rewrite Hfk in Ea.
      pose proof (ElimCases.closed_args_gargs D HD Hc Hsu p Hl Us HUl ups bu ups_gargs ups_len Hbu c gs Hcon ns_u ns_u ns_u vs_u vs_u
                    Hns Hns Har Hia (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      assert (HCa : tele_ass ((cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D))
        by (rewrite <- List.app_assoc, <- params_split; unfold tele_ass; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]).
      assert (HCs : ⊨ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact (IndCases.sd_cargs D HD p c gs Hl Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU ++ Γ).
      { pose proof (ElimCases.ihs_pre_sem D p Γ Us A gs HBs nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_nparams, <- List.app_assoc; exact H. }
      destruct (inst_entry_link _ HCa HCs HCS (ns_u ++ vs_u) Hpg
                  ltac:(rewrite !List.length_app, length_cargs_ctx, length_nparams; lia) k X a HX Ea) as (A0 & b & j & HA0 & Eb & Hab).
      rewrite List.rev_app_distr in HA0.
      destruct (Nat.lt_ge_cases k (ind_nn D)) as [Hk1 | Hk1].
      + rewrite List.nth_error_app1 in HA0 by (rewrite List.length_rev, length_nparams; lia).
        destruct (fresh_tele_nth _ _ _ _ Fn k A0 HA0) as (b' & Eb' & Hb').
        rewrite <- env_args_app in Eb'.
        rewrite firstn_app_le in Eb by lia.
        assert (b' = b) as -> by (eapply functional_eval_exp; eassumption).
        exists b, j; split; [ rewrite List.nth_error_app1 by lia; exact Hb' | exact Hab ].
      + rewrite List.nth_error_app2 in HA0 by (rewrite List.length_rev, length_nparams; lia).
        rewrite List.length_rev, length_nparams in HA0.
        destruct (nth_error_lt_some gs (k - ind_nn D) ltac:(lia)) as [g Hg].
        destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & Heq & Hl1).
        rewrite <- Hl1 in HA0.
        rewrite firstn_app_ge in Eb by lia; rewrite Ln in Eb; rewrite <- Hl1 in Eb.
        assert (Hnthw : forall x, List.nth_error vs_u (List.length gs1) = Some x -> List.nth_error (ns_u ++ vs_u ++ ihs_u) k = Some x).
        { intros x Hx; rewrite List.nth_error_app2 by lia; rewrite Ln, <- Hl1; rewrite List.nth_error_app1 by lia; exact Hx. }
        destruct (fresh_cargs_nth _ _ _ _ _ _ Fc gs1 g gs2 Heq) as [Fa Fr].
        (** The environment of the argument's context. *)
        pose proof (proj1 (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon gs1 (g :: gs2) Heq)) as HC1.
        destruct (sem_ctx_per_ctx_env HC1) as [R HR].
        pose proof (ElimCases.closed_args_gargs D HD Hc Hsu p Hl Us HUl ups bu ups_gargs ups_len Hbu c gs Hcon ns_u ns_u ns_u vs_u vs_u
                      Hns Hns Har Hia (List.length gs1) ltac:(lia)) as Hpg1.
        replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
        assert (HE : R (env_args nil (ups ++ ns_u ++ List.firstn (List.length gs1) vs_u))
                       (env_args nil (ups ++ ns_u ++ List.firstn (List.length gs1) vs_u))).
        { rewrite params_split, List.app_assoc in HR, HC1.
          assert (Lz : List.length (ns_u ++ List.firstn (List.length gs1) vs_u) = List.length (cargs_ctx p D gs1 ++ ind_nparams D))
            by (rewrite !List.length_app, length_cargs_ctx, length_nparams, List.length_firstn; lia).
          pose proof (TeleSem.gargs_env_rel_gen (cargs_ctx p D gs1 ++ ind_nparams D) (ind_uparams D) RU R (env_args nil ups) (env_args nil ups)
                        (ns_u ++ List.firstn (List.length gs1) vs_u) (ns_u ++ List.firstn (List.length gs1) vs_u) HRU HR HC1 ups_RU Lz Hpg1) as H.
          rewrite <- !env_args_app in H; exact H. }
        assert (Hbb : Dom b ≈ b ∈ per_univ j) by (eapply per_univ_trans'; [ apply per_univ_sym'; exact Hab | exact Hab ]).
        destruct g as [B0 | Pr].
        * pose proof (cargs_rev_nth_arg p D gs gs1 B0 gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fa B0 eq_refl) as (a' & Ea' & Hv).
          assert (Ea2 : ⟦ B0 ⟧ ⟪wk_pat (cargs_pat gs1)⟫ (env_args nil (ups ++ ns_u ++ List.firstn (List.length gs1) vs_u)) ↘ a')
            by (rewrite List.app_assoc, env_args_app, IndSem.eval_wk_pat_args by (rewrite List.length_firstn; lia);
                exact Ea').
          destruct (cargs_arg_val_rel p D Hl Hc Hdt Hsu HDc c gs Hcon gs1 B0 gs2 Heq R _ b a' HR HE Eb Ea2) as [k0 [Rl Hlk]].
          destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hlk) as [n Hn].
          destruct Hab as [R1 HR1].
          destruct (InstanceCases.per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 Hn) as (R2 & HR2 & _).
          exists a', j; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia | eexists; exact HR2 ].
        * pose proof (cargs_rev_nth_rec p D gs gs1 Pr gs2 Heq) as HB'; rewrite HA0 in HB'; injection HB' as ->.
          destruct (Fr Pr eq_refl) as (a' & Ea' & Hv).
          pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Lv Heq) as Hpk.
          destruct Hbb as [Rb HRb].
          rewrite <- env_args_app, <- List.app_assoc in Ea'.
          pose proof (IndCases.shty_link D HDc Hc Hsu p Hl c gs Hcon (IndCases.sd_cargs D HD p c gs Hl Hcon) gs1 Pr gs2 Heq
                        ups ns_u (List.firstn (List.length gs1) vs_u) bu ups_len Ln ltac:(rewrite List.length_firstn; lia)
                        ups_gargs Hbu Hns Hpk
                        ltac:(intros R' HR'; apply (per_ctx_env_right_irrel _ _ _ _ _ HR HR'); exact HE)
                        (List.length (ptyp_doms Pr)) 0 nil b j Rb a' ltac:(lia) (tele_pre_nil _) ltac:(cbn; apply per_gargs_nil)
                        ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Eb) HRb
                        ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Ea')) as Hba.
          exists a', j; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia |].
          eapply per_univ_trans'; [ exact Hab | exact Hba ].
    - (** The recursive results. *)
      rewrite List.nth_error_app2 in HX by lia; rewrite LC in HX.
      destruct (ihs_rev_nth D A Us (List.length gs) gs (k - (ind_nn D + List.length gs)) _ HX) as (gs1 & t & gs2 & Heq & Hi' & HXe).
      rewrite <- Hi' in HXe; injection HXe as ->.
      set (j := cargs_nrec gs1) in *.
      assert (Hfk : List.firstn k (ns_u ++ vs_u ++ ihs_u) = (ns_u ++ vs_u) ++ List.firstn j ihs_u)
        by (rewrite List.app_assoc, firstn_app_ge by (rewrite List.length_app; lia); rewrite List.length_app, Ln, Lv, Hi'; reflexivity).
      rewrite Hfk in Ea.
      destruct (ElimCases.ind_args_rel_at D p ups _ gs vs_u vs_u Hia gs1 t gs2 Heq) as (v & v' & Hv1 & Hv1' & Hsh).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      destruct (fresh_ihs_nth _ _ _ _ _ _ _ Fi gs1 t gs2 Heq) as (v0 & a' & Hv0 & Ea' & Hih).
      rewrite Hv1' in Hv0; injection Hv0 as <-.
      set (fa := List.firstn (List.length gs1) vs_u) in *.
      set (aft := List.skipn (S (List.length gs1)) vs_u).
      assert (Evs : vs_u = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      assert (Lj : j <= List.length ihs_u) by (rewrite Li; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; lia).
      set (ihp := List.firstn j ihs_u) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Lv, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Lv, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn; lia).
      (** The environment of the context before the result. *)
      pose proof (ElimCases.e_HCtxT D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                    A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq) as HCtxT.
      destruct (MemberReps.sem_ctx_ass_inv HCtxT) as [jT HT].
      pose proof (sem_ctx_tail HCtxT) as HCtx.
      destruct (sem_ctx_per_ctx_env HCtx) as [RS HRS].
      destruct (sem_ctx_per_ctx_env HBs) as [RB HRB].
      pose proof (ElimCases.cv_bctx D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                    A iA HAv ρ ρ Hρ HUv c gs Hcon HBs ρ ρ Hρ Hρ ns_u ns_u ns_u vs_u vs_u ihs_u ihs_u Hns Hns Har Hia Hir RB HRB) as HZ.
      assert (HEE : RS (env_args ρ (ns_u ++ vs_u ++ ihp)) (env_args ρ (ns_u ++ vs_u ++ ihp))).
      { assert (Esp : ihs_ctx_aux D A Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2) ++ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite ElimCases.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite ElimCases.bctx_split, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))) in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs_u) = List.length (List.rev (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Li; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; lia).
        assert (HZ' : RB (env_args (env_args ρ (ns_u ++ vs_u ++ ihp)) (List.skipn j ihs_u)) (env_args (env_args ρ (ns_u ++ vs_u ++ ihp)) (List.skipn j ihs_u)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (IndSem.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      rewrite Evs, <- !List.app_assoc in Ea; cbn [List.app] in Ea.
      destruct (rel_exp_of_typ_inversion_simple_at HRS HT _ _ HEE) as (ty & ty' & Et & Et' & [R HR]).
      assert (ty = a) as -> by (eapply functional_eval_exp; eassumption).
      assert (ty' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (ElimCases.side_w D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq RS HRS ρ ns_u fa v' aft ihp Hρ Ln Lfa Laft Lihp HEE)
        as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Lv Heq) as Hpk; fold fa in Hpk.
      destruct (ElimCases.ihty_link D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq RS HRS (List.length (ptyp_doms t)) 0 ρ ns_u fa v' aft ihp w nil v' a jT R
                  ltac:(lia) Ln Lfa Laft Lihp eq_refl Hρ HEE Hw HwU Lw Hns Hpk (tele_pre_nil _) ltac:(apply eval_apps_nil)
                  ltac:(rewrite List.app_nil_r; exact Hsh) Ea HR) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
      rewrite <- env_args_app, <- List.app_assoc in Ea'.
      pose proof (functional_eval_ihty _ _ _ _ _ _ _ Eb Ea') as <-.
      exists b, jT; split; [| exact Hab ].
      rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
      rewrite List.length_app, Ln, Lv.
      replace (k - (ind_nn D + List.length gs)) with j by (unfold j; lia).
      unfold j in *; rewrite Hih; do 3 f_equal; lia.
  Qed.

  (** The substitution of a branch's context at the fresh variables a stuck
      eliminator's readback makes, at admissible uniform parameters. *)
  Lemma br_fresh_glu : forall c gs, ind_con D c = Some gs ->
      forall SbB, EG elim_bctx p D gs A Us ++ Γ ∈ glu_ctx_env ↘ SbB ->
      forall Δ σ'' ua ns_x vs_x ihs_x, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
        ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ua -> List.length ua = ind_nu D ->
        fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
        fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns_x)) gs (List.length Δ + ind_nn D) vs_x ->
        fresh_ihs gc_deps gc_stack ρ A (env_args nil (ua ++ ns_x)) gs vs_x (List.length Δ + ind_nn D + List.length gs) ihs_x ->
        tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ ⊢ˢ sb_qn (List.length (elim_bctx p D gs A Us)) σ''
          ® env_args ρ (ns_x ++ vs_x ++ ihs_x) ∈ SbB.
  Proof.
    intros c gs Hcon SbB HSbB Δ σ'' ua ns_x vs_x ihs_x Hσ'' Hadm Lua Fx Cx Ix.
    pose proof (bctx_sem c gs Hcon) as HBs.
    set (s := List.length Δ) in *.
    destruct (fnp2 ups ua s Had Hadm) as (ns_u & ns_x' & Fu & Fx' & Hux).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ Fx' Fx) as ->; clear Fx'.
    pose proof (ttrans _ _ _ Hux (tsym _ _ Hux)) as Huu.
    destruct (frargs ups ua ns_u ns_x c gs Had Hadm ups_len Lua Hux Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1 & vs2 & ihs1 & ihs2 & C1 & C2 & I1 & I2 & P & Hia & Hir).
    rewrite !List.app_nil_r in C1, C2, I1, I2, Hia, Hir; cbn in P.
    pose proof (functional_fresh_cargs _ _ _ _ _ _ C2 _ Cx) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I2 _ Ix) as ->.
    destruct (frargs ups ups ns_u ns_u c gs Had Had ups_len ups_len Huu Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1' & vs1'' & ihs1' & ihs1'' & C1' & C1'' & I1' & I1'' & P' & Hia' & Hir').
    rewrite !List.app_nil_r in C1', C1'', I1', I1'', Hia', Hir'; cbn in P'.
    pose proof (functional_fresh_cargs _ _ _ _ _ _ C1' _ C1) as ->.
    pose proof (functional_fresh_cargs _ _ _ _ _ _ C1'' _ C1) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1' _ I1) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1'' _ I1) as ->.
    pose proof (tele_full_of_pre _ _ _ _ P) as Har.
    pose proof (tele_full_of_pre _ _ _ _ P') as Har'.
    pose proof (fresh_tele_length _ _ _ _ Fu) as Lu; rewrite List.length_rev, length_nparams in Lu.
    pose proof (fresh_tele_length _ _ _ _ Fx) as Lx; rewrite List.length_rev, length_nparams in Lx.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv1 Lv2].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li1 Li2].
    assert (Lb : List.length (elim_bctx p D gs A Us) = ind_nn D + List.length gs + cargs_nrec gs) by (rewrite length_elim_bctx; lia).
    (** Glued at the variables at [ups]. *)
    assert (Hws : tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ ⊢ˢ sb_qn (List.length (elim_bctx p D gs A Us)) σ''
                    ® env_args ρ (ns_u ++ vs1 ++ ihs1) ∈ SbB).
    { apply (glu_sub_fresh _ Γ SbΓ (elim_bctx_ass p D gs A Us Hc) HSbΓ SbB HSbB Δ σ'' ρ _ Hσ'');
        [ rewrite Lb, !List.length_app; lia |].
      intros k X a HX Ea.
      exact (bctx_entry_link c gs Hcon s ns_u vs1 ihs1 Fu C1 I1 Huu Har' Hia' Hir' k X a HX Ea). }
    (** Related to those at [ua]. *)
    destruct (sem_ctx_per_ctx_env HBs) as [RB HRB].
    pose proof (ElimCases.cv_bctx D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs ρ ρ Hρ Hρ ns_u ns_u ns_x vs1 vs_x ihs1 ihs_x Huu Hux Har Hia Hir RB HRB) as HE.
    assert (HBr : ⊨ List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ) by (rewrite List.rev_involutive; exact HBs).
    assert (HRBr : EF List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ ≈ List.rev (List.rev (elim_bctx p D gs A Us)) ++ Γ ∈ per_ctx_env ↘ RB)
      by (rewrite List.rev_involutive; exact HRB).
    pose proof (proj2 (IndSem.rel_gargs _ _ _ _ HRΓ HBr (List.Forall_rev (elim_bctx_ass p D gs A Us Hc)) HRBr ρ ρ
                         (ns_u ++ vs1 ++ ihs1) (ns_x ++ vs_x ++ ihs_x)
                         ltac:(rewrite List.length_rev, Lb, !List.length_app; lia)
                         ltac:(rewrite List.length_rev, Lb, !List.length_app; lia) HE)) as Hg.
    eapply (glu_sub_resp_args _ Γ SbΓ (elim_bctx_ass p D gs A Us Hc) HSbΓ SbB HSbB); [| exact Hg | exact Hws ].
    rewrite Lb, !List.length_app; lia.
  Qed.

  (** The readback of the motive of a stuck eliminator, against its
      instance. *)
  Lemma motive_rb : forall Δ σ'' ua ns_x af A'', Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ua -> List.length ua = ind_nu D ->
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
      ⟦ A ⟧ env_args ρ (ns_x ++ ⇑! (d_ind p (ua ++ ns_x)) (List.length Δ + ind_nn D) :: nil) ↘ af ->
      Rtyp af in gc_deps ⍮ gc_stack ⍮ S (List.length Δ + ind_nn D) ↘ A'' ->
      elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ A[sb_qn nm σ''] ≈ A'' : Typeω@iA.
  Proof.
    intros * Hσ'' Hadm Lua Fx Eaf HRA.
    pose proof HAg as [SbM HSbM _ _].
    pose proof (mctx_fresh_glu SbM HSbM Δ σ'' ua ns_x Hσ'' Hadm Lua Fx) as Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM HAg Hτ) as (HAτ & a & Ea & Hpa & HPa).
    assert (a = af) as -> by (eapply functional_eval_exp; eassumption).
    destruct (per_univ_glu_univ_elem _ _ Hpa) as (P & El & Hg).
    pose proof (HPa P El Hg) as HP.
    destruct (realize_glu_typ_top _ _ _ _ Hg _ _ HP) as [_ _ Hrbt].
    assert (HΔm : ⊢ elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ) by (gen_presups; assumption).
    assert (Hlen : List.length (elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ) = S (List.length Δ + ind_nn D))
      by (rewrite List.length_app, length_elim_mctx; lia).
    rewrite <- Hlen in HRA.
    pose proof (Hrbt _ wk_id _ (kripke_id _ HΔm) HRA) as H.
    rewrite exp_wk_id in H; exact H.
  Qed.

  (** The readback of a branch of a stuck eliminator, against its
      instance. *)
  Lemma br_rb : forall Δ σ'' ua c gs n B ns_x vs_x ihs_x b t Bn, Δ ⊢ˢ σ'' ® ρ ∈ SbΓ ->
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ua -> List.length ua = ind_nu D ->
      ind_con D c = Some gs -> In (c, n, B) Bs ->
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
      fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns_x)) gs (List.length Δ + ind_nn D) vs_x ->
      fresh_ihs gc_deps gc_stack ρ A (env_args nil (ua ++ ns_x)) gs vs_x (List.length Δ + ind_nn D + List.length gs) ihs_x ->
      ⟦ B ⟧ env_args ρ (ns_x ++ vs_x ++ ihs_x) ↘ b ->
      ⟦ A ⟧ env_args ρ (ns_x ++ d_con p c (ua ++ ns_x ++ vs_x) :: nil) ↘ t ->
      Rnf ⇓ t b in gc_deps ⍮ gc_stack ⍮ (List.length Δ + n) ↘ Bn ->
      elim_bctx p D gs A[sb_qn nm σ''] (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ B[sb_qn n σ''] ≈ Bn
        : elim_bty p D c gs A[sb_qn nm σ''] (List.map (fun U => U[σ'']) Us).
  Proof.
    intros * Hσ'' Hadm Lua Hcon Hin Fx Cx Ix Eb Et HRn.
    pose proof (HBa c gs n B Hcon Hin) as Hn.
    pose proof (HBg c gs n B Hcon Hin) as HBgl; destruct HBgl as [SbB HSbB _ _].
    pose proof (br_fresh_glu c gs Hcon SbB HSbB Δ σ'' ua ns_x vs_x ihs_x Hσ'' Hadm Lua Fx Cx Ix) as Hτ.
    destruct (glu_rel_exp_clean_inversion1 HSbB (HBg c gs n B Hcon Hin)) as [iB HiB].
    destruct (HiB _ _ _ Hτ) as [eb rb Pb Elb Eeb Erb Hgb HBglue]; clear HiB.
    assert (rb = b) as -> by (eapply functional_eval_exp; eassumption).
    set (s := List.length Δ) in *.
    pose proof (bctx_sem c gs Hcon) as HBs.
    (** The relations of the variables at [ua] to themselves. *)
    destruct (fnp2 ua ua s Hadm Hadm) as (ns1 & ns2 & F1 & F2 & Hxx).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F1 Fx) as ->; pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F2 Fx) as ->.
    clear F1 F2.
    destruct (frargs ua ua ns_x ns_x c gs Hadm Hadm Lua Lua Hxx Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1 & vs2 & ihs1 & ihs2 & C1 & C2 & I1 & I2 & P & Hia & Hir).
    rewrite !List.app_nil_r in C1, C2, I1, I2, Hia, Hir; cbn in P.
    pose proof (functional_fresh_cargs _ _ _ _ _ _ C1 _ Cx) as ->.
    pose proof (functional_fresh_cargs _ _ _ _ _ _ C2 _ Cx) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1 _ Ix) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I2 _ Ix) as ->.
    pose proof (tele_full_of_pre _ _ _ _ P) as Har.
    pose proof (fresh_tele_length _ _ _ _ Fx) as LX; rewrite List.length_rev, length_nparams in LX.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ _ _ Hir) as [Li _].
    destruct (sem_ctx_per_ctx_env HBs) as [RB HRB].
    pose proof (ElimCases.cv_bctx D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs ρ ρ Hρ Hρ ns_x ns_x ns_x vs_x vs_x ihs_x ihs_x Hxx Hxx Har Hia Hir RB HRB) as HE.
    (** The branch type's value, against the motive at the constructor. *)
    assert (Lb : List.length (elim_bctx p D gs A Us) = ind_nn D + List.length gs + cargs_nrec gs) by (rewrite length_elim_bctx; lia).
    destruct (ElimCases.us_wk_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs _ RB ρ (ns_x ++ vs_x ++ ihs_x) HRB HBs HE
                ltac:(rewrite Lb, !List.length_app; lia)) as (w & u' & Hw & _ & _).
    rewrite Lb in Hw.
    pose proof (ElimCases.eval_bty D Hc p Hl Us HUl ups ups_len c gs Hcon ρ ns_x vs_x ihs_x w LX Lv Li Hw) as Hev.
    pose proof (ElimCases.gsub_bty D HD Hc Hsu Hdt p Hl Γ HΓ Us HUl HUs ups ups_len HM A c gs Hcon HBs) as Hgb'.
    destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRB (InstanceCases.gsub_valid Hgb') HE Hev) as (eb' & b0 & Eeb' & Eb0 & Heb0).
    rewrite <- ElimCases.elim_bty_args in Eeb'.
    assert (eb' = eb) as -> by (eapply functional_eval_exp; eassumption).
    assert (Lw : List.length w = ind_nu D) by (rewrite (IndCases.eval_exps_length _ _ _ Hw), List.length_map; exact HUl).
    assert (Hm1 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns_x (d_con p c ((w ++ ns_x) ++ vs_x)) (d_con p c ((ua ++ ns_x) ++ vs_x))).
    { eapply ind_rel_con; [ exact Hxx | exact Hcon | rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia
                          | rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia
                          | rewrite skipn_app_exact by exact Lw; exact Hxx | rewrite skipn_app_exact by exact Lua; exact Hxx
                          | exact Har | exact Hia ]. }
    destruct (mmid _ _ _ _ Hxx Hm1) as (a1 & a2 & Ea1 & Ea2 & Haa).
    rewrite <- List.app_assoc in Ea1, Ea2.
    assert (a1 = b0) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = t) as -> by (eapply functional_eval_exp; eassumption).
    assert (Hebt : Dom eb ≈ t ∈ per_univ iA) by (eapply per_univ_trans'; [ exact Heb0 | eexists; exact Haa ]).
    (** The branch glued at [t], read back. *)
    pose proof (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HBglue) as HTP.
    destruct (glu_transfer_per iB iA eb t Pb Elb _ _ _ b Hgb Hebt HTP HBglue) as (k' & P' & El' & Hg' & HP' & HM').
    destruct (realize_glu_elem_top _ _ _ _ Hg' _ _ _ _ HM') as [? ? _ _ _ _ Hrbs].
    assert (HΔb : ⊢ tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ) by (pose proof (glu_ctx_env_sub_escape HSbB _ _ _ Hτ); gen_presups; assumption).
    assert (Hlen : List.length (tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ) = s + n)
      by (rewrite List.length_app, length_tele_sub, Lb, Hn; unfold s; lia).
    rewrite <- Hlen in HRn.
    pose proof (Hrbs _ wk_id _ (kripke_id _ HΔb) HRn) as H.
    rewrite !exp_wk_id in H.
    rewrite (elim_bctx_sub p D c gs A Us σ'' Hc (cons_lookup_in _ _ _ Hcon) HUl) in H.
    replace (List.length (elim_bctx p D gs A Us)) with (ind_nn D + List.length gs + cargs_nrec gs) in H by (symmetry; exact Lb).
    rewrite elim_bty_sub in H.
    rewrite Hn, Hnm; exact H.
  Qed.


  (** The motive at glued non-uniform parameters and scrutinee. *)
  Lemma motive_glu : forall Δ' σ' Q M' m' ns, Δ' ⊢ˢ σ' ® ρ ∈ SbΓ ->
      List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us -> List.length Q = ind_np D -> Δ' ⊢ M' : apps (a_ind p) Q ->
      (forall Δ'' φ Q', Δ'' ⊢ᵏ φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl DP DEl Δ'' Q' M'[φ]ʷ m') ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns m' m' ->
      glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns ->
      exists a, ⟦ A ⟧ env_args ρ (ns ++ m' :: nil) ↘ a /\ Dom a ≈ a ∈ per_univ iA /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® P.
  Proof.
    intros * Hσ' HQU HQl HMt HK Hns Hrel Hgn.
    pose proof HAg as [SbM HSbM _ _].
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ HR0 Hl ups_len ups_len ns ns Hns) as [R HR].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR Hl ups_len ups_len) as (_ & _ & _ & _ & _ & _ & _ & HRi).
    pose proof (us_glu_args Δ' σ' Hσ') as HUga.
    rewrite <- HQU in HUga.
    pose proof (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hgn Hns) as HgN.
    assert (HfQ : List.length (List.firstn (ind_nu D) Q) = ind_nu D) by (rewrite List.length_firstn; lia).
    assert (Hga : glu_args Δ' (ind_params D) Id nil Q (ups ++ ns)).
    { rewrite <- (List.firstn_skipn (ind_nu D) Q), params_split.
      apply glu_args_app; [ exact Ua | rewrite HfQ, length_ind_uparams by exact Hle; reflexivity
                          | rewrite ups_len, length_ind_uparams by exact Hle; reflexivity |].
      split; [ exact HUga | exact HgN ]. }
    destruct (ind_elem_glue u R ups ns bu NP NEl AP AEl DP DEl Δ' Q M' m' ups_len Hbu Hule HNP HAP HDP HR HΔ' Hga HMt
                ltac:(apply HRi; exact Hrel) HK) as (P1 & El1 & Hg1 & HP1 & HM1).
    rewrite <- (List.firstn_skipn (ind_nu D) Q), HQU in HP1, HM1.
    rewrite HQU in HgN.
    pose proof (mctx_glu_sub SbM HSbM Δ' σ' _ ns M' m' u P1 El1 Hσ' HgN Hns Hg1 HP1 HM1) as Hτ.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbM HAg Hτ) as (_ & a & Ea & Hpa & HPa).
    exists a; split; [ exact Ea | split; [ exact Hpa |] ].
    intros P El Hg; pose proof (HPa P El Hg) as H.
    rewrite <- exp_sub_qn_of_list in H.
    replace (List.length (List.skipn (ind_nu D) Q ++ M' :: nil)) with nm in H
      by (rewrite List.length_app, List.length_skipn, Hnm; cbn; unfold ind_nn in *; lia).
    exact H.
  Qed.

  (** What the eliminator does with an element: at any substitution glued
      to [ρ] instantiating the uniform parameters, and any values of the
      non-uniform ones glued to the element's, its result is glued at the
      motive. *)
  #[warnings="-cannot-define-projection"]
  Record elim_out (Δ' : ctx) (Q : list exp) (M' : exp) (m' : domain) (σ' : sub) (ns : list domain) : Prop :=
    mk_elim_out
    { eli_val : domain
    ; eli_motive : domain
    ; eli_eval : ⟦elim m' under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ eli_val
    ; eli_eval_motive : ⟦ A ⟧ env_args ρ (ns ++ m' :: nil) ↘ eli_motive
    ; eli_per : Dom eli_motive ≈ eli_motive ∈ per_univ iA
    ; eli_glu : forall P El, DG eli_motive ∈ glu_univ_elem iA ↘ P ↘ El ->
        Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M'
           : A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® eli_val ∈ El }.

  Definition elim_prop (Δ' : ctx) (Q : list exp) (M' : exp) (m' : domain) : Prop :=
    forall σ', Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us ->
      List.length Q = ind_np D -> Δ' ⊢ M' : apps (a_ind p) Q ->
      (forall Δ'' φ Q', Δ'' ⊢ᵏ φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl DP DEl Δ'' Q' M'[φ]ʷ m') ->
      forall ns, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns m' m' ->
        glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns ->
        elim_out Δ' Q M' m' σ' ns.


  Lemma rec_mvc : forall c0 gs1 t0 gs2 k, ind_con D c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
      List.Forall (exp_mvc 0) (ptyp_doms (ptyp_skip k t0)) /\ List.Forall (exp_mvc 0) (ptyp_ps (ptyp_skip k t0)).
  Proof.
    intros * Hc0.
    pose proof (dmv_cons _ (dt_mvc _ _ _ Hdt)) as Hcm.
    pose proof (Hcm _ _ (cons_lookup_in _ _ _ Hc0)) as Hf.
    apply List.Forall_app in Hf as [_ Hf]; inversion Hf as [| ? ? Hct _]; subst; cbn in Hct; destruct Hct as [Hd Hp].
    rewrite ptyp_doms_skip, ptyp_ps_skip; split; [| exact Hp ].
    rewrite <- (List.firstn_skipn k (ptyp_doms t0)) in Hd; apply List.Forall_app in Hd as [_ Hd]; exact Hd.
  Qed.

  (** A domain value's relation is the canonical family's at it. *)
  Lemma rel_dr : forall pre B b (j : nat) R c, ⟦ B ⟧ env_args nil (ups ++ pre) ↘ b ->
      DF b ≈ b ∈ per_univ_elem j ↘ R -> R c c -> ind_dr ups pre B c c.
  Proof.
    intros * Eb HR Hcc; unfold ind_dr; intros i2 R1 b2 b2' Eb2 Eb2' HR1.
    assert (b2 = b) as -> by (eapply functional_eval_exp; eassumption).
    assert (b2' = b) as -> by (eapply functional_eval_exp; eassumption).
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR1); exact Hcc.
  Qed.

  (** A recursive argument, glued by [glu_rec] after [k] domains of its
      shape, is an element of the type of the rest of the shape. *)
  Lemma rec_el : forall n t0 k Δ' ms c0 gs1 gs2 ws ys Ty N v σ' σs a (j : nat) R P El,
      k + n = List.length (ptyp_doms t0) ->
      glu_rec p D ups NEl AEl DP DEl Δ' (ms ++ ws ++ ys) (ptyp_skip k t0) Ty N v ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms -> ind_con D c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
      tele_pre (ind_ar D ups ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t0)) k ys ys ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Ty = ptyp_ty_at p (List.map (fun U => U[σ']) Us) σs (ptyp_skip k t0) -> Δ' ⊢ N : Ty ->
      Δ' ⊢ Ty : Typeω@j -> eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ ms ++ ws ++ ys)) (ptyp_skip k t0) a ->
      DF a ≈ a ∈ per_univ_elem j ↘ R -> R v v -> u <= j -> DG a ∈ glu_univ_elem j ↘ P ↘ El ->
      Δ' ⊢ N : Ty ® v ∈ El.
  Proof.
    induction n as [| n IH]; intros * Hkn Hgr Hms Hc0 Hws Hys Hσ' HTy HN HTyt Ea HR Hv Huj Hg.
    all: assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    all: pose proof (Hsimp _ _ _ _ _ Hc0 eq_refl) as Hst.
    - assert (Hk : k = List.length (ptyp_doms t0)) by lia; rewrite Hk, (ptyp_skip_end t0 Hst) in Hgr, HTy, Ea.
      subst Ty; inversion Hgr; subst.
      match goal with H : forall bsr Q, _ -> _ -> List.length Q = ind_np D /\ _ |- _ => rename H into Hs1 end.
      match goal with H : forall bsr Q, _ -> _ -> forall Δ φ Q', _ -> _ -> glu_ind _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hs2 end.
      inversion Ea; subst.
      match goal with H : ⟦ ptyp_ps t0 ⟧* _ ⍮ _ ⍮ _ ↘ ?b0 |- _ => rename H into Ebs; rename b0 into bs end.
      cbn [ptyp_ty_at ptyp_ps] in HN |- *.
      set (Q := List.map (fun U => U[σ']) Us ++ List.map (fun P => P[σs]) (ptyp_ps t0)) in *.
      destruct (Hs1 _ Q Ebs eq_refl) as (HQl & Hbs & Hgn).
      destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ HR0 Hl ups_len ups_len bs bs Hbs) as [R' HR'].
      assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
      assert (Hga : glu_args Δ' (ind_params D) Id nil Q (ups ++ bs)).
      { unfold Q; rewrite params_split; apply glu_args_app; [ exact (decl_uparams_ass D Hc) | rewrite HUl', length_ind_uparams by exact Hle; reflexivity
                                                           | rewrite ups_len, length_ind_uparams by exact Hle; reflexivity |].
        split; [ exact (us_glu_args Δ' σ' Hσ') |].
        destruct (Hgn bs Hbs) as [Hgn' _].
        unfold Q in Hgn'; rewrite firstn_app_len, skipn_app_len in Hgn' by exact HUl'.
        exact (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hgn' Hbs). }
      assert (HRv : R' v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HR'); exact Hv).
      destruct (ind_elem_glue u R' ups bs bu NP NEl AP AEl DP DEl Δ' Q N v ups_len Hbu Hule HNP HAP HDP HR' HΔ' Hga HN HRv
                  (Hs2 _ Q Ebs eq_refl)) as (P1 & El1 & Hg1 & HP1 & HM1).
      eapply glu_elem_retype; [ exact Hg1 | exact Hg | exact HP1 | exact HM1 |].
      eapply (glu_typ_transfer (ul u) (ul j) (ul j)); [ cbn; lia | cbn; lia | eexists; exact HR | exact Hg1 | exact Hg | exact HP1 ].
    - assert (Hk : k < List.length (ptyp_doms t0)) by lia.
      destruct (ptyp_skip_lt k t0 Hk) as (B & HB & Hs).
      rewrite Hs in Hgr, HTy, Ea.
      set (t' := ptyp_skip (S k) t0) in *.
      subst Ty; inversion Hgr; subst.
      match goal with H : forall IT OT, _ = a_pi IT OT -> forall Δ φ, _ -> DP _ _ _ _ |- _ => rename H into Hq1 end.
      match goal with H : forall IT OT, _ = a_pi IT OT -> forall Δ φ b c, _ -> _ -> _ -> exists fc, _ |- _ => rename H into Hq2 end.
      match goal with H : forall IT OT, _ = a_pi IT OT -> forall Δ φ b c fc, _ -> _ -> _ -> _ -> glu_rec _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hq3 end.
      cbn [ptyp_ty_at] in HN, HTyt, Hq1, Hq2, Hq3 |- *.
      set (IT := B[σs]) in *.
      set (OTy := ptyp_ty_at p (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (q σs) t') in *.
      specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (Hq3 _ _ eq_refl).
      inversion Ea; subst.
      match goal with E : ⟦ B ⟧ _ ↘ ?x |- _ => rename x into b1; rename E into Eb1' end.
      pose proof HR as HRsave.
      basic_invert_per_univ_elem HR.
      match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
      match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
      destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
      pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ Hms Hc0 eq_refl Hws HB Hys Eb1') as HgD.
      destruct (wf_pi_inversion' HTyt) as [HITt HOTt].
      assert (HIT : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® IP).
      { intros Δ φ Hφ.
        eapply (glu_typ_transfer (ul u) (ul j) (ul j)); [ cbn; lia | cbn; lia | eexists; exact equiv_a_a' | exact HgD | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
      assert (HDEl : forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                       Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl (ms ++ ws ++ ys) B).
      { intros * Hφ Hb.
        eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ Hb) | exact Hb | exact (Hq1 _ _ Hφ) ]. }
      assert (Happ : forall Δ φ b c (equiv_c : in_rel c c), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                       exists fc a2, $| v & c | gc_deps ⍮ gc_stack ↘ fc /\
                         ⟦ fam_cod ⟧ (nil ↦ d_shfam p ups (env_args nil (ups ++ ms ++ ws ++ ys)) t') ↦ c ↘ a2 /\
                         Δ ⊢ N[φ]ʷ $ b : OTy[(ι φ),,b] ® fc ∈ OEl c equiv_c).
      { intros * Hφ Hb.
        pose proof (rel_dr _ _ _ _ _ c Eb1' equiv_a_a' equiv_c) as Hdc.
        pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
        destruct (Hq2 _ _ _ _ Hφ Hdc HbD) as [fc Efc].
        pose proof (Hq3 _ _ _ _ _ Hφ Hdc HbD Efc) as Hgr'.
        destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
        assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
        destruct (proj1 (HRE v v) Hv _ _ equiv_c) as [fc1 fc2 Efc1 Efc2 Hfc].
        assert (fc1 = fc) as -> by (eapply functional_eval_app; eassumption).
        assert (fc2 = fc) as -> by (eapply functional_eval_app; eassumption).
        pose proof (eval_fam_cod_shfam_inv _ _ _ _ _ _ Ea2) as Ea2s.
        exists fc, a2; split; [ exact Efc | split; [ exact Ea2 |] ].
        assert (Hys' : tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t0)) (S k) (ys ++ c :: nil) (ys ++ c :: nil))
          by (apply tele_pre_snoc; [ exact Hys |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hdc).
        assert (HTy' : OTy[(ι φ),,b] = ptyp_ty_at p (List.map (fun U => U[sb_wk σ' φ]) Us) (q σs ⨟ ((ι φ),,b)) t').
        { unfold OTy; rewrite ptyp_ty_at_sub, !List.map_map; f_equal.
          apply List.map_ext; intros U; rewrite exp_shift_extend_wk, exp_wk_sub; reflexivity. }
        pose proof (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb) as Hbt.
        pose proof (app_wk_typed _ _ _ _ _ _ _ HN Hφ Hbt) as HNt'.
        pose proof (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ Hbt) as HTyt'.
        assert (Ea2s' : eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ ms ++ ws ++ ys ++ c :: nil)) (ptyp_skip (S k) t0) a2).
        { replace (ups ++ ms ++ ws ++ ys ++ c :: nil) with ((ups ++ ms ++ ws ++ ys) ++ c :: nil) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite env_args_snoc; exact Ea2s. }
        rewrite <- !List.app_assoc in Hgr'; cbn [List.app] in Hgr'.
        exact (IH t0 (S k) Δ ms c0 gs1 gs2 ws (ys ++ c :: nil) _ _ fc (sb_wk σ' φ) (q σs ⨟ ((ι φ),,b)) a2 j _ _ _ ltac:(lia)
                 Hgr' Hms Hc0 Hws Hys' (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) HTy' HNt' HTyt' Ea2s' Ha22 Hfc Huj
                 (Hcodg _ equiv_c _ Ea2)). }
      apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTy);
        [ exact HN | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hv
        | apply wf_exp_eq_refl; exact HTyt | exact HITt | exact HOTt | exact HIT |].
      intros Δ φ N0 n0 Hφ HN0 equiv_n.
      destruct (Happ _ _ _ _ equiv_n Hφ HN0) as (fc & a2 & Efc & _ & Hgl).
      exists fc; split; [ exact Efc | exact Hgl ].
  Qed.

  (** What the recursive result of a recursive argument does: at any
      substitution glued to [ρ] and any position of the argument in a
      shape, the recursive result of the argument is glued at the type of
      its recursive result, at the value the eliminator gives. *)
  Definition rec_prop (Δ' : ctx) (pre : list domain) (t : ptyp) (Ty : typ) (N : exp) (v : domain) : Prop :=
    forall ms c0 gs1 t0 gs2 ws k ys σ' σs r a (j : nat) R P El,
      pre = ms ++ ws ++ ys -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
      ind_con D c0 = Some (gs1 ++ ca_rec t0 :: gs2) ->
      tele_pre (ind_ar D ups ms c0) (List.length (cargs_nonrec gs1)) ws ws ->
      ptyp_skip k t0 = t -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t0)) k ys ys ->
      Δ' ⊢ˢ σ' ® ρ ∈ SbΓ -> Ty = ptyp_ty_at p (List.map (fun U => U[σ']) Us) σs t -> Δ' ⊢ N : Ty ->
      ind_shape_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) pre t v v ->
      eval_ih gc_deps gc_stack ρ nm A Bs t v r ->
      eval_ihty gc_deps gc_stack ρ A (env_args nil (ups ++ pre)) t v a ->
      DF a ≈ a ∈ per_univ_elem j ↘ R -> R r r -> u <= j -> iA <= j ->
      DG a ∈ glu_univ_elem j ↘ P ↘ El ->
      Δ' ⊢ ptyp_ihty A[sb_qn nm σ'] Id σs N t : Typeω@j ->
      Δ' ⊢ ptyp_ih nm A[sb_qn nm σ'] (brs_sub Bs σ') σs N t : ptyp_ihty A[sb_qn nm σ'] Id σs N t ® r ∈ El.

  Lemma rec_self_case : forall Δ' pre k0 Ps Ty N v,
      (forall bsr Q, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bsr -> Ty = apps (a_ind p) Q ->
         List.length Q = ind_np D /\ tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr /\
         (forall bsr', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr' ->
            glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) bsr' /\
            forall Δ φ, Δ ⊢ᵏ φ : Δ' -> glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Q) (ups ++ bsr'))) ->
      (forall bsr Q, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bsr -> Ty = apps (a_ind p) Q ->
         forall Δ φ Q', Δ ⊢ᵏ φ : Δ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
           glu_ind p D ups NEl AEl DP DEl Δ Q' N[φ]ʷ v) ->
      (forall bsr Q, eval_exps gc_deps gc_stack Ps (env_args nil (ups ++ pre)) bsr -> Ty = apps (a_ind p) Q ->
         forall Δ φ Q', Δ ⊢ᵏ φ : Δ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
           elim_prop Δ Q' N[φ]ʷ v) ->
      rec_prop Δ' pre (pt_self k0 Ps) Ty N v.
  Proof.
    intros * Hs1 Hs2 IH; unfold rec_prop; intros * Hpre Hms Hc0 Hws Hsk Hys Hσ' HTy HN Hsh Er Ea HR Hr Huj HiAj Hg HIT.
    subst Ty; cbn [ptyp_ih ptyp_ihty ptyp_ty_at ptyp_ps] in *.
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    destruct (ind_shape_self_inv _ _ _ _ _ _ _ _ _ _ _ Hsh) as (bs & Ebs & Hir).
    inversion Er; subst.
    match goal with H : ⟦elim v under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => rename H into Er' end.
    inversion Ea; subst.
    match goal with H : ⟦ A ⟧ env_args ρ (?b0 ++ v :: nil) ↘ a |- _ => rename H into Ea'; rename b0 into bs' end.
    match goal with H : ⟦ Ps ⟧* _ ⍮ _ ⍮ _ ↘ bs' |- _ => pose proof (functional_eval_exps' _ _ _ _ H Ebs) as -> end.
    set (Q := List.map (fun U => U[σ']) Us ++ List.map (fun P => P[σs]) Ps) in *.
    assert (HUl' : List.length (List.map (fun U => U[σ']) Us) = ind_nu D) by (rewrite List.length_map; exact HUl).
    destruct (Hs1 _ Q Ebs eq_refl) as (HQl & Hbs & Hgn).
    assert (Hid : Δ' ⊢ᵏ wk_id : Δ') by mauto 3.
    pose proof (proj2 (Hgn bs Hbs) Δ' wk_id Hid) as Htop.
    pose proof (IH _ Q Ebs eq_refl Δ' wk_id _ Hid (glu_params_top_refl _ _ _ _ Htop)) as HE.
    rewrite map_wk_id, exp_wk_id in HE.
    destruct (HE σ' Hσ' ltac:(unfold Q; apply firstn_app_len; exact HUl') HQl HN) with (ns := bs) as [r' a' Er'' Ea'' Haa Hgl].
    - intros Δ'' φ Q'' Hφ HQ''; exact (Hs2 _ Q Ebs eq_refl Δ'' φ Q'' Hφ HQ'').
    - exact Hbs.
    - exact Hir.
    - exact (proj1 (Hgn bs Hbs)).
    - pose proof (functional_eval_elim _ _ _ _ _ _ _ Er'' Er') as ->.
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_glu_univ_elem _ _ Haa) as (P0 & El0 & Hg0).
      pose proof (Hgl P0 El0 Hg0) as HE0.
      unfold Q in HE0; rewrite skipn_app_len in HE0 by exact HUl'.
      eapply glu_univ_elem_exp_cumu_ge; [ exact HiAj | exact Hg0 | exact Hg | exact HE0 ].
  Qed.

  (** The body of the recursive result of a function shape, at an
      argument, moved by a weakening. *)
  Lemma ih_body_inst : forall σ' σs N t φ e,
      (ptyp_ih nm A[sb_qn nm σ'][wk_qn nm ↑]ʷ (brs_wk (brs_sub Bs σ') ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ih nm A[sb_qn nm (sb_wk σ' φ)] (brs_sub Bs (sb_wk σ' φ)) (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros; rewrite ptyp_ih_sub, exp_qn_step, brs_step; cbn [exp_sub].
    rewrite exp_shift_extend_wk_e; reflexivity.
  Qed.

  Lemma ih_cod_inst : forall σ' σs N t φ e, List.length (ptyp_ps t) = ind_nn D ->
      (ptyp_ihty A[sb_qn nm σ'] (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t)[sb_extend (ι φ) e]
      = ptyp_ihty A[sb_qn nm (sb_wk σ' φ)] Id (q σs ⨟ sb_extend (ι φ) e) (a_app N[φ]ʷ (sentry_exp e)) t.
  Proof.
    intros * HPl; rewrite ptyp_ihty_sub; cbn [exp_sub]; rewrite exp_shift_extend_wk_e.
    rewrite (ptyp_ihty_sb_eq _ _ _ (ι φ ⨟ Id) _ _ _ (fun z => eq_refl) (fun z => eq_refl)).
    rewrite (ptyp_ihty_base _ _ _ _ _ _ _ HPl), <- Hnm, exp_qn_wk; reflexivity.
  Qed.

  Lemma rec_pi_case : forall Δ' pre B t Ty N v,
      (forall IT OT, Ty = a_pi IT OT -> forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® DP pre B) ->
      (forall IT OT, Ty = a_pi IT OT -> forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> ind_dr ups pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B -> exists fc, $| v & c | gc_deps ⍮ gc_stack ↘ fc) ->
      (forall IT OT, Ty = a_pi IT OT -> forall Δ φ b c fc, Δ ⊢ᵏ φ : Δ' -> ind_dr ups pre B c c ->
         Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl pre B -> $| v & c | gc_deps ⍮ gc_stack ↘ fc ->
         rec_prop Δ (pre ++ c :: nil) t OT[(ι φ),,b] (a_app N[φ]ʷ b) fc) ->
      rec_prop Δ' pre (pt_pi B t) Ty N v.
  Proof.
    intros * Hq1 Hq2 IH3; unfold rec_prop; intros * Hpre Hms Hc0 Hws Hsk Hys Hσ' HTy HN Hsh Er Ea HR Hr Huj HiAj Hg HIT.
    subst Ty pre.
    assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hsk'].
    assert (Hk : S k <= List.length (ptyp_doms t0)) by (pose proof (proj1 (List.nth_error_Some (ptyp_doms t0) k) ltac:(congruence)); lia).
    assert (HPl : List.length (ptyp_ps t) = ind_nn D)
      by (rewrite <- Hsk', ptyp_ps_skip; exact (IndCases.length_rec_ps D Hc c0 _ gs1 t0 gs2 Hc0 eq_refl)).
    cbn [ptyp_ty_at ptyp_ih ptyp_ihty] in HN, HIT, Hq1, Hq2, IH3 |- *.
    set (IT := B[σs]) in *.
    set (OTy := ptyp_ty_at p (List.map (fun U => U[↑]ʷ) (List.map (fun U => U[σ']) Us)) (q σs) t) in *.
    specialize (Hq1 _ _ eq_refl); specialize (Hq2 _ _ eq_refl); specialize (IH3 _ _ eq_refl).
    pose proof (eval_ih_pi_inv _ _ _ _ _ _ _ _ Er) as ->.
    destruct (eval_ihty_pi_inv _ _ _ _ _ _ _ Ea) as (b1 & Eb1 & ->).
    pose proof HR as HRsave.
    basic_invert_per_univ_elem HR.
    match goal with H : forall (c c' : domain) (_ : ?ir c c'), rel_mod_eval _ _ _ _ _ _ |- _ => rename H into Hcod end.
    match goal with H : _ <~> (fun _ _ => forall _ _ _, rel_mod_app _ _ _ _ _) |- _ => rename H into HRE end.
    destruct (glu_univ_elem_pi_clean_inversion1 equiv_a_a' Hg) as (IP & IEl & OP & OEl & erel & Hgb1 & Hcodg & Hper & HPeq & HEleq).
    pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ Hms Hc0 eq_refl Hws HB Hys Eb1) as HgD.
    destruct (wf_pi_inversion' HIT) as [HITt HOTt].
    destruct (rec_mvc _ _ _ _ (S k) Hc0) as [Hmd Hmp]; rewrite Hsk' in Hmd, Hmp.
    set (body := ptyp_ih nm A[sb_qn nm σ'][wk_qn nm ↑]ʷ (brs_wk (brs_sub Bs σ') ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    set (OTi := ptyp_ihty A[sb_qn nm σ'] (Id ⨟ sb_of_wk ↑) (q σs) (a_app N[↑]ʷ (a_var 0)) t).
    assert (HIT' : forall Δ φ, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ IT[φ]ʷ ® IP).
    { intros Δ φ Hφ.
      eapply (glu_typ_transfer (ul u) (ul j) (ul j)); [ cbn; lia | cbn; lia | eexists; exact equiv_a_a' | exact HgD | exact Hgb1 | exact (Hq1 _ _ Hφ) ]. }
    assert (HDEl : forall Δ φ b c, Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     Δ ⊢ b : IT[φ]ʷ ® c ∈ DEl (ms ++ ws ++ ys) B).
    { intros * Hφ Hb.
      eapply glu_elem_retype; [ exact Hgb1 | exact HgD | exact (glu_univ_elem_trm_typ _ _ _ _ Hgb1 _ _ _ _ Hb) | exact Hb | exact (Hq1 _ _ Hφ) ]. }
    assert (Happ : forall Δ φ b c (equiv_c : in_rel c c), Δ ⊢ᵏ φ : Δ' -> Δ ⊢ b : IT[φ]ʷ ® c ∈ IEl ->
                     exists rc a2, $| d_ihfn ρ nm A Bs t v & c | gc_deps ⍮ gc_stack ↘ rc /\
                       ⟦ fam_cod ⟧ (nil ↦ d_ihfam ρ A (env_args nil (ups ++ ms ++ ws ++ ys)) t v) ↦ c ↘ a2 /\
                       Δ ⊢ body[(ι φ),,b] : OTi[(ι φ),,b] ® rc ∈ OEl c equiv_c).
    { intros * Hφ Hb.
      pose proof (rel_dr _ _ _ _ _ c Eb1 equiv_a_a' equiv_c) as Hdc.
      pose proof (HDEl _ _ _ _ Hφ Hb) as HbD.
      destruct (Hq2 _ _ _ _ Hφ Hdc HbD) as [fc Efc].
      pose proof (IH3 _ _ _ _ _ Hφ Hdc HbD Efc) as IH'.
      destruct (Hcod _ _ equiv_c) as [a2 a2' Ea2 Ea2' Ha22].
      assert (a2' = a2) as -> by (eapply functional_eval_exp; eassumption).
      destruct (proj1 (HRE _ _) Hr _ _ equiv_c) as [rc rc' Erc Erc' Hrc].
      assert (rc' = rc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_fam_cod_ihfam_inv _ _ _ _ _ _ _ Ea2) as (fx & Efx & Ea2i).
      assert (fx = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (eval_app_ihfn_inv _ _ _ _ _ _ _ _ Erc) as (y & Ey & Erc0).
      assert (y = fc) as -> by (eapply functional_eval_app; eassumption).
      destruct (ind_shape_pi_inv _ _ _ _ _ _ _ _ _ _ _ Hsh c c Hdc) as (r0 & r0' & Er0 & Er0' & Hsh').
      assert (r0 = fc) as -> by (eapply functional_eval_app; eassumption).
      assert (r0' = fc) as -> by (eapply functional_eval_app; eassumption).
      exists rc, a2; split; [ exact Erc | split; [ exact Ea2 |] ].
      unfold body, OTi; rewrite ih_body_inst, ih_cod_inst by exact HPl.
      eapply (IH' ms c0 gs1 t0 gs2 ws (S k) (ys ++ c :: nil) (sb_wk σ' φ) (q σs ⨟ ((ι φ),,b)) rc a2 j _ _ _);
        [ rewrite <- !List.app_assoc; reflexivity | exact Hms | exact Hc0 | exact Hws | exact Hsk'
        | | exact (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) | | | exact Hsh' | exact Erc0 | | exact Ha22 | exact Hrc
        | exact Huj | exact HiAj | exact (Hcodg _ equiv_c _ Ea2) |].
      - apply tele_pre_snoc; [ exact Hys |]; unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hdc.
      - unfold OTy; rewrite ptyp_ty_at_sub, !List.map_map; f_equal.
        apply List.map_ext; intros U; rewrite exp_shift_extend_wk, exp_wk_sub; reflexivity.
      - exact (app_wk_typed _ _ _ _ _ _ _ HN Hφ (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb)).
      - replace (ups ++ (ms ++ ws ++ ys) ++ c :: nil) with ((ups ++ ms ++ ws ++ ys) ++ c :: nil) by (rewrite <- !List.app_assoc; reflexivity).
        rewrite env_args_snoc; exact Ea2i.
      - pose proof (ih_cod_inst σ' σs N t φ (se_exp b) HPl) as E; cbn [sentry_exp] in E; rewrite <- E; fold OTi.
        exact (sub_typ_extend _ _ _ _ _ _ _ HITt HOTt Hφ (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ Hb)). }
    (** The typing of the body, at the generic variable. *)
    assert (HITid : Δ' ⊢ IT ® IP) by (pose proof (HIT' Δ' wk_id (kripke_id _ HΔ')) as Hx0; rewrite exp_wk_id in Hx0; exact Hx0).
    assert (HΔIT : ⊢ Δ' ▹ IT) by mauto 3.
    pose proof (var0_glu_elem Hgb1 HITid) as Hvar.
    pose proof (var_per_elem (length Δ') equiv_a_a') as Heqv.
    destruct (Happ _ _ _ _ Heqv (kripke_shift _ _ HΔIT) Hvar) as (rc0 & a0 & _ & Ea0 & Hg0).
    pose proof (glu_univ_elem_trm_escape _ _ _ _ (Hcodg _ Heqv _ Ea0) _ _ _ _ Hg0) as Hbodyt.
    assert (Ebv : body[(ι ↑),,#0] = body).
    { transitivity (body[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold body; rewrite !ih_body_inst; cbn [sentry_exp].
      apply ptyp_ih_agree_exp; [ exact Hmd | apply sb_exp_agree_var0 ]. }
    assert (Eov : OTi[(ι ↑),,#0] = OTi).
    { transitivity (OTi[sb_extend (ι ↑) (se_var 0)]); [| apply exp_sub_of_shift_extend_zero ].
      unfold OTi; rewrite !(ih_cod_inst σ' σs N t ↑ _ HPl); cbn [sentry_exp].
      apply ptyp_ihty_agree_exp; [ exact Hmd | exact Hmp | reflexivity | apply sb_exp_agree_var0 ]. }
    rewrite Ebv, Eov in Hbodyt.
    apply HEleq; eapply mk_pi_glu_exp_pred with (IT := IT) (OT := OTi);
      [ apply wf_fn with (i := j); [ exact HITt | exact Hbodyt ]
      | apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRsave Hper); exact Hr
      | apply wf_exp_eq_refl; exact HIT | exact HITt | exact HOTt | exact HIT' |].
    intros Δ φ N0 n0 Hφ HN0 equiv_n.
    destruct (Happ _ _ _ _ equiv_n Hφ HN0) as (rc & a2 & Erc & Ea2 & Hgl).
    exists rc; split; [ exact Erc |].
    pose proof (Hcodg _ equiv_n _ Ea2) as Hga2.
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hga2 | exact Hgl |].
    apply wf_exp_eq_sym; eapply fn_wk_beta; [ exact HITt | exact HOTt | exact Hbodyt | exact Hφ | exact (glu_univ_elem_trm_escape _ _ _ _ Hgb1 _ _ _ _ HN0) ].
  Qed.

  Section ConCase.
    Variable (c : String.string) (gs : list carg) (Q : list exp) (bs vs : list domain) (As : list exp) (Δ' : ctx) (M' : exp).
    Hypothesis (Hcon : ind_con D c = Some gs) (HQl : List.length Q = ind_np D) (Hbl : List.length bs = ind_np D)
      (Hvl : List.length vs = List.length gs) (HAl : List.length As = List.length gs)
      (HMeq : Δ' ⊢ M' ≈ apps (a_con p c) (Q ++ As) : apps (a_ind p) Q)
      (Hb : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs))
      (Hv : tele_full (ind_ar D ups (List.skipn (ind_nu D) bs) c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs))
      (Hnp : glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) (List.skipn (ind_nu D) bs))
      (HAs : forall k N A, List.nth_error As k = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) k = Some A -> Δ' ⊢ N : A)
      (Harg : forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Δ' ⊢ N : A ® v ∈ AEl (List.skipn (ind_nu D) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_vals gs1 (List.firstn (List.length gs1) vs)))
      (Hrec : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec p D ups NEl AEl DP DEl Δ' (List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t A N v)
      (IH : forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          rec_prop Δ' (List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t A N v).
    Variable (σ' : sub).
    Hypothesis (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : apps (a_ind p) Q).
    Variable (ns : list domain).
    Hypothesis (Hns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns)
      (Hrel : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)))
      (HKm : forall Δ'' φ Q', Δ'' ⊢ᵏ φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl DP DEl Δ'' Q' M'[φ]ʷ (d_con p c (bs ++ vs)))
      (Hgnm : glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns).
    Let X := List.skipn (ind_nu D) bs.

    Lemma con_rel : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns X /\
        ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) X (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)) /\
        ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) X gs vs vs.
    Proof.
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl Hrel) as (_ & HnX & _ & _).
      pose proof (imv _ _ _ _ Hrel HnX) as HrX.
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl HrX) as (_ & _ & _ & Hia).
      auto.
    Qed.

    (** The non-uniform parameters and the arguments, glued at the
        declaration's telescope at [ups]. *)
    Lemma con_canon_args : glu_args Δ' (cargs_ctx p D gs ++ ind_nparams D) (sb_of_list Id (List.map (fun U => U[σ']) Us))
        (env_args nil ups) (List.skipn (ind_nu D) Q ++ As) (X ++ vs).
    Proof.
      destruct con_rel as (HnsX & HrelX & HiaX).
      pose proof (fun k Hk => ElimCases.closed_args_gargs D HD Hc Hsu p Hl Us HUl ups bu ups_gargs ups_len Hbu c gs Hcon X X X vs vs Hb Hb Hv HiaX k Hk) as Hpg.
      pose proof (fun gs1 gs2 Heq => proj1 (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon gs1 gs2 Heq)) as Hcs.
      pose proof ups_RU as HuRU.
      pose proof ups_gargs as Hug.
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      rewrite <- HQU.
      apply glu_args_app; [ exact (decl_closed_nparams_ass D Hc) | rewrite length_nparams; exact LXs | rewrite length_nparams; exact LX |].
      split; [ exact (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hnp Hb) |].
      rewrite <- sb_of_list_app, List.firstn_skipn, <- env_args_app.
      constructor; [ rewrite length_cargs_ctx; exact HAl | rewrite length_cargs_ctx; exact Hvl |].
      intros k N T v B HN HT Hv' HB.
      assert (Hk : k < List.length gs) by (rewrite <- Hvl; apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some gs k Hk) as [g Hg].
      destruct (List.nth_error_split _ _ Hg) as (gs1 & gs2 & Heq & <-).
      pose proof (Hpg (List.length gs1) ltac:(lia)) as Hpg1.
      replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
      pose proof (Hcs gs1 (g :: gs2) Heq) as HC1.
      destruct (sem_ctx_per_ctx_env HC1) as [R HR].
      assert (HE : R (env_args nil (ups ++ X ++ List.firstn (List.length gs1) vs)) (env_args nil (ups ++ X ++ List.firstn (List.length gs1) vs))).
      { rewrite params_split, List.app_assoc in HR, HC1.
        assert (Lz : List.length (X ++ List.firstn (List.length gs1) vs) = List.length (cargs_ctx p D gs1 ++ ind_nparams D))
          by (rewrite !List.length_app, length_cargs_ctx, length_nparams, List.length_firstn; lia).
        pose proof (TeleSem.gargs_env_rel_gen (cargs_ctx p D gs1 ++ ind_nparams D) (ind_uparams D) RU R (env_args nil ups) (env_args nil ups)
                      (X ++ List.firstn (List.length gs1) vs) (X ++ List.firstn (List.length gs1) vs) HRU HR HC1 HuRU Lz Hpg1) as H.
        rewrite <- !env_args_app in H; exact H. }
      pose proof (Hpg (List.length gs) (le_n _)) as Hpgf.
      rewrite List.firstn_all2, List.firstn_all2 in Hpgf by lia.
      assert (HBf : List.nth_error (List.rev (cargs_ctx p D gs ++ ind_nparams D)) (ind_nn D + List.length gs1) = Some (ce_ass B))
        by (rewrite List.rev_app_distr, List.nth_error_app2 by (rewrite List.length_rev, length_nparams; lia);
            rewrite List.length_rev, length_nparams; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia; exact HB).
      destruct (per_gargs_nth _ _ _ _ _ _ _ Hpgf HBf ltac:(rewrite List.length_app; lia)) as (i0 & Ra & a1 & a2 & Ea1 & Ea2x & HRa).
      assert (a2 = a1) as -> by (eapply functional_eval_exp; eassumption).
      rewrite firstn_app_ge in Ea1 by lia; rewrite LX in Ea1; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) in Ea1 by lia.
      rewrite !env_args_app in Ea1 |- *.
      clear Hpg Hpgf HBf Hcs Hpg1 HC1 Hg.
      destruct g as [B0 | Pr].
      - pose proof (cargs_rev_nth_arg p D gs gs1 B0 gs2 Heq) as HB'; rewrite HB in HB'; injection HB' as ->.
        pose proof (Harg gs1 B0 gs2 N T v Heq HN HT Hv') as HNg.
        assert (HB0 : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some B0)
          by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk.
        destruct (HeA _ _ _ _ _ _ Hb Hcon HB0 Hpk) as [b Eb].
        pose proof (HAP _ _ _ _ _ _ _ Hb Hcon HB0 Hpk Eb) as Hgb.
        assert (Ea2 : ⟦ B0 ⟧ ⟪wk_pat (cargs_pat gs1)⟫ (env_args nil (ups ++ X ++ List.firstn (List.length gs1) vs)) ↘ b)
          by (rewrite List.app_assoc, env_args_app, IndSem.eval_wk_pat_args by (rewrite List.length_firstn; lia);
              rewrite <- env_args_app, <- List.app_assoc; exact Eb).
        pose proof Ea1 as Ea1c; rewrite <- !env_args_app in Ea1c.
        destruct (cargs_arg_val_rel p D Hl Hc Hdt Hsu HDc c gs Hcon gs1 B0 gs2 Heq R _ a1 b HR HE Ea1c Ea2) as [k0 [Rl Hlk]].
        destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hlk) as [n Hn].
        assert (Hba : Dom b ≈ a1 ∈ per_univ n) by (apply per_univ_sym'; eexists; exact Hn).
        destruct (glu_transfer_per' u n b a1 _ _ Δ' T N v Hgb Hba (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HNg) HNg) as (k' & P' & El' & Hg' & HP' & HM').
        apply (mk_glu_arg _ _ _ _ _ _ k' a1 P' El'); assumption.
      - pose proof (cargs_rev_nth_rec p D gs gs1 Pr gs2 Heq) as HB'; rewrite HB in HB'; injection HB' as ->.
        pose proof (Hrec gs1 Pr gs2 N T v Heq HN HT Hv') as Hgr.
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk.
        pose proof Ea1 as Ea1c; rewrite <- !env_args_app in Ea1c.
        assert (Hcon' : ind_con D c = Some (gs1 ++ ca_rec Pr :: gs2)) by (rewrite <- Heq; exact Hcon).
        assert (Lfa : List.length (List.firstn (List.length gs1) vs) = List.length gs1) by (rewrite List.length_firstn; lia).
        assert (HPre : forall R', EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R' ->
                         R' (env_args nil (ups ++ X ++ List.firstn (List.length gs1) vs)) (env_args nil (ups ++ X ++ List.firstn (List.length gs1) vs)))
          by (intros R' HR'; apply (per_ctx_env_right_irrel _ _ _ _ _ HR HR'); exact HE).
        destruct (shex ups Had X X c gs1 Pr gs2 _ _ Hb Hcon' Hpk 0 nil nil ltac:(lia) (tele_pre_nil _)) as [b Eb].
        cbn [ptyp_skip] in Eb; rewrite List.app_nil_r in Eb.
        pose proof (IndCases.sd_cargs D HD p c gs Hl Hcon) as HΨ.
        pose proof (IndCases.shty_link D HDc Hc Hsu p Hl c gs Hcon HΨ gs1 Pr gs2 Heq ups X _ bu ups_len LX Lfa ups_gargs Hbu Hb Hpk HPre
                      (List.length (ptyp_doms Pr)) 0 nil a1 i0 Ra b ltac:(lia) (tele_pre_nil _) ltac:(cbn; apply per_gargs_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Ea1c) HRa
                      ltac:(cbn [ptyp_skip]; rewrite List.app_nil_r; exact Eb)) as Hab.
        pose proof (IndCases.shape_char D HDc Hc Hsu p Hl c gs Hcon HΨ gs1 Pr gs2 Heq ups X _ bu ups_len LX Lfa ups_gargs Hbu Hb Hpk HPre
                      (List.length (ptyp_doms Pr)) 0 nil a1 i0 Ra ltac:(lia) (tele_pre_nil _) ltac:(cbn; apply per_gargs_nil)
                      ltac:(cbn [List.repeat List.app ptyp_skip]; rewrite List.app_nil_r; exact Ea1c) HRa) as Hsr.
        destruct (ElimCases.ind_args_rel_at D p ups _ gs vs vs HiaX gs1 Pr gs2 Heq) as (x & x' & Hx & Hx' & Hsh).
        rewrite Hv' in Hx; injection Hx as <-; rewrite Hv' in Hx'; injection Hx' as <-.
        assert (HRav : Ra v v) by (apply Hsr; cbn [ptyp_skip]; rewrite List.app_nil_r; exact Hsh).
        destruct Hab as [Rab HRab].
        destruct (presup_exp (HAs _ _ _ HN HT)) as [_ [jT HjT]].
        set (j := Nat.max (Nat.max u i0) jT).
        pose proof (per_univ_elem_cumu_ge i0 j _ _ _ ltac:(unfold j; lia) (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRab) HRab)) as HRbb.
        pose proof (per_univ_elem_cumu_ge i0 j _ _ _ ltac:(unfold j; lia) (per_univ_sym _ _ _ _ HRab)) as HRba.
        assert (HRbv : Rab v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRa HRab); exact HRav).
        destruct (per_univ_glu_univ_elem j _ (ex_intro _ Rab HRbb)) as (P & El & Hgb).
        set (σs := cargs_sub (sb_of_list Id Q) gs1 As).
        assert (HTeq : T = ptyp_ty_at p (List.map (fun U => U[σ']) Us) σs Pr).
        { rewrite (cargs_rec_type_at p D gs gs1 Pr gs2 Q As T Heq Hle HQl HT), HQU.
          apply ptyp_ty_at_sb_eq; rewrite sb_of_list_app; unfold σs; rewrite <- (cargs_sub_firstn gs1 (sb_of_list Id Q) As).
          apply cargs_sub_pat; rewrite List.length_firstn; lia. }
        pose proof (rec_el (List.length (ptyp_doms Pr)) Pr 0 Δ' X c gs1 gs2 _ nil T N v σ' σs b j Rab P El ltac:(lia)
                      ltac:(rewrite List.app_nil_r; exact Hgr) Hb Hcon' Hpk (tele_pre_nil _) Hσ' HTeq (HAs _ _ _ HN HT)
                      (lift_exp_ge _ _ _ _ jT j ltac:(unfold j; lia) HjT)
                      ltac:(rewrite List.app_nil_r; exact Eb) HRbb HRbv ltac:(unfold j; lia) Hgb) as HMr.
        pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ Rab HRba) Hgb) as Hga1.
        exact (mk_glu_arg _ _ _ _ _ _ (ul j) a1 P El Ea1 Hga1 (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMr) HMr).
    Qed.
    Lemma con_Q_typed : forall k P T, List.nth_error Q k = Some P ->
        List.nth_error (tele_insts (ind_params D) Id Q) k = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUga.
      rewrite <- HQU in HUga.
      pose proof (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hnp Hb) as HgN.
      assert (HfQ : List.length (List.firstn (ind_nu D) Q) = ind_nu D) by (rewrite List.length_firstn; lia).
      assert (Hga : glu_args Δ' (ind_params D) Id nil Q (ups ++ X)).
      { rewrite <- (List.firstn_skipn (ind_nu D) Q), params_split.
        apply glu_args_app; [ exact Ua | rewrite HfQ, length_ind_uparams by exact Hle; reflexivity
                            | rewrite ups_len, length_ind_uparams by exact Hle; reflexivity |].
        split; [ exact HUga | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ Hass Hga).
    Qed.

    (** The recursive results, glued at their types in the branch's
        context. *)
    Lemma con_ihs_args : forall ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)) ->
        glu_args Δ' (ihs_ctx_aux D A Us (List.length gs) nil 0 gs) (sb_of_list σ' (List.skipn (ind_nu D) Q ++ As))
          (env_args ρ (X ++ vs)) (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As) ihs.
    Proof.
      intros ihs Ei RB HRB HZ.
      pose proof (bctx_sem c gs Hcon) as HBs.
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      destruct con_rel as (HnsX & HrelX & HiaX).
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      (** The recursive results, related at the telescope of their types. *)
      assert (Hpgi : per_gargs (List.rev (ihs_ctx_aux D A Us (List.length gs) nil 0 gs)) (env_args ρ (X ++ vs)) (env_args ρ (X ++ vs)) ihs ihs).
      { pose proof (ElimCases.ihs_pre_sem D p Γ Us A gs HBs nil gs eq_refl) as HC0.
        cbn [ihs_ctx_aux List.app] in HC0.
        destruct (sem_ctx_per_ctx_env HC0) as [RC HRC].
        pose proof HRB as HRB'; pose proof HBs as HBs'; rewrite ElimCases.bctx_split in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux D A Us (List.length gs) nil 0 gs)) in HRB', HBs'.
        assert (Lr : List.length ihs = List.length (List.rev (ihs_ctx_aux D A Us (List.length gs) nil 0 gs)))
          by (rewrite List.length_rev, length_ihs_ctx_aux; exact Lih).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs)) ihs) (env_args (env_args ρ (X ++ vs)) ihs))
          by (rewrite <- env_args_app, <- List.app_assoc; exact HZ).
        destruct (IndSem.rel_gargs _ _ _ _ HRC HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [_ H].
        exact H. }
      constructor; [ rewrite length_elim_ihs, length_ihs_ctx_aux by exact HAl; reflexivity | rewrite length_ihs_ctx_aux; exact Lih |].
      intros k M T r B0 HMk HT Hr HB0.
      destruct (ihs_rev_nth D A Us (List.length gs) gs k _ HB0) as (gs1 & t & gs2 & Heq & Hk & EB).
      injection EB as ->; subst k.
      set (j := cargs_nrec gs1) in *.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [N HN].
      rewrite (elim_ihs_nth _ _ _ gs1 _ gs t gs2 As N Heq HAl HN) in HMk; injection HMk as <-.
      destruct (ElimCases.ind_args_rel_at D p ups _ gs vs vs HiaX gs1 t gs2 Heq) as (v & v' & Hv1 & Hv1' & Hsh).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      destruct (eval_ihs_nth _ _ _ _ gs1 _ _ _ Ei t gs2 v' Heq Hv1') as (r' & Hr' & Er').
      fold j in Hr'; rewrite Hr in Hr'; injection Hr' as <-.
      set (σg := cargs_sub (sb_of_list Id Q) gs1 As).
      assert (Lj : j <= List.length ihs) by (rewrite Lih; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; lia).
      (** The instance of the result's type. *)
      rewrite (tele_insts_sb_eq _ _ (sb_qn (0 + List.length gs + ind_nn D) σ' ⨟ sb_of_list Id (List.skipn (ind_nu D) Q ++ As))) in HT.
      2:{ replace (0 + List.length gs + ind_nn D) with (List.length (List.skipn (ind_nu D) Q ++ As)) by (rewrite List.length_app; lia).
            symmetry; etransitivity; [ apply sb_qn_of_list | apply sb_of_list_cong, sb_compose_id_right ]. }
      rewrite <- tele_insts_tele_sub in HT.
      rewrite (ihs_ctx_aux_sub D A Us (List.length gs) σ' gs nil 0 Hc HUl eq_refl) in HT.
      2:{ intros * Heq'; pose proof Hc as [_ _ _ _ _ HPs HPl].
            split; [ exact (HPs _ _ _ _ _ Hin Heq') | exact (HPl _ _ _ _ _ Hin Heq') ]. }
      assert (ET : T = ptyp_ihty A[sb_qn nm σ'] Id σg N t).
      { pose proof HT as HT0.
        destruct (tele_insts_nth _ _ _ _ _ HT0) as (B'' & HB'' & ET).
        rewrite (ihs_ctx_nth D _ _ _ gs gs1 t gs2 Heq) in HB''; fold j in HB''; injection HB'' as <-.
        subst T; rewrite <- sb_of_list_app, <- List.app_assoc.
        set (L' := List.firstn j (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)).
        assert (LL' : List.length L' = j)
          by (unfold L'; rewrite List.length_firstn, length_elim_ihs by exact HAl; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; lia).
        set (δ := sb_of_list Id (List.skipn (ind_nu D) Q ++ As ++ L')).
        assert (Hθδ : sb_eq (ihs_sub D (List.map (fun U => U[σ']) Us) (List.length gs) (cargs_pat gs1) j ⨟ δ) σg).
        { unfold δ, σg; rewrite <- HQU, <- LL'.
          apply ihs_sub_iota; [ exact Hc | exact HQl | exact HAl | rewrite Heq, List.length_app; lia ]. }
        assert (Hbδ : sb_eq (sb_of_wk (wk_shiftn (j + List.length gs + ind_nn D)) ⨟ δ) Id).
        { intros z; unfold δ; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
          replace (z + (j + List.length gs + ind_nn D)) with (List.length (List.skipn (ind_nu D) Q ++ As ++ L') + z)
            by (rewrite !List.length_app, LXs, HAl, LL'; lia).
          rewrite sb_of_list_ge; reflexivity. }
        assert (Hidx : (a_var (j + List.length gs - 1 - List.length (cargs_pat gs1)))[δ] = N).
        { change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)); unfold δ.
          rewrite (sb_of_list_nth _ _ _ N) by (rewrite !List.length_app, LXs, HAl, LL', Heq, List.length_app, length_cargs_pat; cbn; lia).
          rewrite !List.length_app, LXs, HAl, LL', length_cargs_pat.
          replace (ind_nn D + (List.length gs + j) - 1 - (j + List.length gs - 1 - List.length gs1))
            with (ind_nn D + List.length gs1) by (rewrite Heq, List.length_app; cbn; lia).
          cbn [sentry_exp]; rewrite List.app_nth2 by lia; rewrite LXs; replace (ind_nn D + List.length gs1 - ind_nn D) with (List.length gs1) by lia.
          rewrite List.app_nth1 by exact Hlt; apply List.nth_error_nth; exact HN. }
        rewrite ptyp_ihty_sub, Hidx.
        rewrite (ptyp_ihty_sb_eq t _ _ Id _ σg N Hbδ Hθδ), Hnm; reflexivity. }
      (** The result is of its type. *)
      assert (HMt' : Δ' ⊢ ptyp_ih nm A[sb_qn nm σ'] (brs_sub Bs σ') σg N t : T).
      { assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
        assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
        destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ' σ' Hσt)
          as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
        rewrite <- HQU in HAt', HMx', HBx', HBt'.
        pose proof (wf_iota_sub _ _ _ p D c gs Q As nm _ iA _ Hl Hcon HΔ' HQl con_Q_typed HAl HAs Hnm HAt' HMx' HBn' HBx' HBa' HBt')
          as Hιs.
        assert (Lei : List.length (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As) = cargs_nrec gs)
          by (apply length_elim_ihs; exact HAl).
        set (Rst := tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id (List.firstn (ind_nu D) Q)))
                    ++ tele_sub (ind_nparams D) (sb_of_list Id (List.firstn (ind_nu D) Q))).
        assert (LRst : List.length Rst = List.length (List.skipn (ind_nu D) Q ++ As))
          by (unfold Rst; rewrite !List.length_app, !length_tele_sub, length_cargs_ctx, length_nparams, LXs, HAl; lia).
        assert (Hlen : List.length (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)
                       = List.length (elim_bctx p D gs A[sb_qn nm σ'] (List.firstn (ind_nu D) Q)))
          by (rewrite length_elim_bctx, !List.length_app, LXs, HAl, Lei; lia).
        apply (wf_sub_of_list_inv _ _ _ (elim_bctx p D gs A[sb_qn nm σ'] (List.firstn (ind_nu D) Q)) Δ' Id
                  (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)
                  (elim_bctx_ass _ _ _ _ _ Hc) Hlen Hιs (ind_nn D + List.length gs + j)).
        - rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
          rewrite List.length_app, LXs, HAl.
          replace (ind_nn D + List.length gs + j - (ind_nn D + List.length gs)) with j by lia.
          exact (elim_ihs_nth _ _ _ gs1 _ gs t gs2 As N Heq HAl HN).
        - unfold elim_bctx; fold Rst.
          assert (HRa : tele_ass Rst)
            by (unfold Rst; apply List.Forall_app; split; apply tele_ass_sub; [ apply cargs_ctx_aux_ass | apply decl_closed_nparams_ass, Hc ]).
          assert (LRi : List.length (tele_insts Rst Id (List.skipn (ind_nu D) Q ++ As)) = ind_nn D + List.length gs)
            by (rewrite length_tele_insts by exact HRa; rewrite LRst, Nat.min_id, List.length_app, LXs, HAl; reflexivity).
          rewrite List.app_assoc, tele_insts_app by (first [ exact HRa | exact (eq_sym LRst) ]).
          rewrite List.nth_error_app2 by lia; rewrite LRi.
          replace (ind_nn D + List.length gs + j - (ind_nn D + List.length gs)) with j by lia.
          rewrite HQU; rewrite <- Hnm in HT; exact HT. }
      destruct (presup_exp HMt') as [_ [jT HjT]].
      rewrite ET in HjT.
      (** The argument and the type of the argument. *)
      destruct (nth_error_lt_some (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1)) as [TN HTN].
      { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
      assert (HTNeq : TN = ptyp_ty_at p (List.map (fun U => U[σ']) Us) σg t).
      { rewrite (cargs_rec_type_at p D gs gs1 t gs2 Q As TN Heq Hle HQl HTN), HQU.
        apply ptyp_ty_at_sb_eq; rewrite sb_of_list_app; unfold σg; rewrite <- (cargs_sub_firstn gs1 (sb_of_list Id Q) As).
        apply cargs_sub_pat; rewrite List.length_firstn; lia. }
      pose proof (IH gs1 t gs2 N TN v' Heq HN HTN Hv1') as IHr.
      (** The value of the result's type, against its canonical value. *)
      destruct (per_gargs_nth_el _ _ _ _ _ j _ Hpgi HB0 ltac:(rewrite Lih; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; cbn; lia)) as (i0 & Rae & ae & ae' & x & x' & Eae & Eae' & HRae & Hx & Hx' & Hrr).
      assert (ae' = ae) as -> by (eapply functional_eval_exp; eassumption).
      fold j in Hx, Hx', Eae, Eae'; rewrite Hr in Hx; injection Hx as <-; rewrite Hr in Hx'; injection Hx' as <-.
      set (fa := List.firstn (List.length gs1) vs) in *.
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v' :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons _ _ _ Hv1'), List.firstn_skipn; reflexivity).
      set (ihp := List.firstn j ihs) in *.
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Laft : List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn, Hvl, Heq, List.length_app; cbn; lia).
      assert (Lihp : List.length ihp = j) by (unfold ihp; rewrite List.length_firstn; lia).
      pose proof (ElimCases.e_HCtxT D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                    A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq) as HCtxT.
      pose proof (sem_ctx_tail HCtxT) as HCtx.
      destruct (sem_ctx_per_ctx_env HCtx) as [RS HRS].
      assert (HEE : RS (env_args ρ (X ++ vs ++ ihp)) (env_args ρ (X ++ vs ++ ihp))).
      { assert (Esp : ihs_ctx_aux D A Us (List.length gs) nil 0 gs
                     = ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2) ++ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1)
          by (rewrite Heq at 2; rewrite ElimCases.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
        pose proof HRB as HRB'; pose proof HBs as HBs'.
        rewrite ElimCases.bctx_split, Esp, <- List.app_assoc in HRB', HBs'.
        rewrite <- (List.rev_involutive (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))) in HRB', HBs'.
        assert (Lr : List.length (List.skipn j ihs) = List.length (List.rev (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) j (ca_rec t :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Lih; unfold j; rewrite Heq, ElimCases.cargs_nrec_app; lia).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)) (env_args (env_args ρ (X ++ vs ++ ihp)) (List.skipn j ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold ihp; rewrite List.firstn_skipn; exact HZ).
        destruct (IndSem.rel_gargs _ _ _ _ HRS HBs' (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB' _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      rewrite Evs, <- !List.app_assoc in HEE; cbn [List.app] in HEE.
      pose proof Eae as Eae0; rewrite <- env_args_app in Eae0; fold ihp in Eae0.
      rewrite Evs, <- !List.app_assoc in Eae0; cbn [List.app] in Eae0.
      destruct (ElimCases.side_w D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq RS HRS ρ X fa v' aft ihp Hρ LX Lfa Laft Lihp HEE)
        as (w & Hw & HwU & Lw).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk; fold fa in Hpk.
      destruct (ElimCases.ihty_link D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs gs1 t gs2 Heq RS HRS (List.length (ptyp_doms t)) 0 ρ X fa v' aft ihp w nil v' ae i0 Rae
                  ltac:(lia) LX Lfa Laft Lihp eq_refl Hρ HEE Hw HwU Lw Hb Hpk (tele_pre_nil _) ltac:(apply eval_apps_nil)
                  ltac:(rewrite List.app_nil_r; exact Hsh) Eae0 HRae) as (b & Eb & Hab).
      rewrite List.app_nil_r in Eb; cbn [ptyp_skip] in Eb.
      (** The canonical gluing. *)
      destruct Hab as [Rab HRab].
      set (J := Nat.max (Nat.max u iA) (Nat.max i0 jT)).
      pose proof (per_univ_elem_cumu_ge i0 J _ _ _ ltac:(unfold J; lia) (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRab) HRab)) as HRbb.
      pose proof (per_univ_elem_cumu_ge i0 J _ _ _ ltac:(unfold J; lia) (per_univ_sym _ _ _ _ HRab)) as HRba.
      assert (HRr : Rab r r) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRae HRab); exact Hrr).
      destruct (per_univ_glu_univ_elem J _ (ex_intro _ Rab HRbb)) as (P & El & Hgb).
      assert (Hcon' : ind_con D c = Some (gs1 ++ ca_rec t :: gs2)) by (rewrite <- Heq; exact Hcon).
      pose proof (IHr X c gs1 t gs2 (nonrec_vals gs1 fa) 0 nil σ' σg r b J Rab P El ltac:(rewrite List.app_nil_r; reflexivity) Hb Hcon' Hpk eq_refl
                    (tele_pre_nil _) Hσ' HTNeq (HAs _ _ _ HN HTN) Hsh Er' Eb HRbb HRr ltac:(unfold J; lia) ltac:(unfold J; lia) Hgb
                    (lift_exp_ge _ _ _ _ jT J ltac:(unfold J; lia) HjT)) as HMg.
      pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ Rab HRba) Hgb) as Hgae.
      rewrite ET; exact (mk_glu_arg _ _ _ _ _ _ (ul J) ae P El Eae Hgae (glu_univ_elem_trm_typ _ _ _ _ Hgb _ _ _ _ HMg) HMg).
    Qed.
    Lemma con_bctx : exists ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
        (forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
           RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs))) /\
        forall SbB, EG elim_bctx p D gs A Us ++ Γ ∈ glu_ctx_env ↘ SbB ->
          Δ' ⊢ˢ sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)
            ® env_args ρ (X ++ vs ++ ihs) ∈ SbB.
    Proof.
      destruct con_rel as (HnsX & HrelX & HiaX).
      destruct (proj1 (proj2 pelim) _ _ _ _ HiaX) as (ihs & ihs' & Ei & Ei' & Hir).
      pose proof (functional_eval_ihs _ _ _ _ _ _ _ _ Ei Ei') as <-; clear Ei'.
      pose proof (bctx_sem c gs Hcon) as HBs.
      assert (HZ : forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
                RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)))
        by (intros RB HRB; exact (ElimCases.cv_bctx D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs ρ ρ Hρ Hρ X X X vs vs ihs ihs Hb Hb Hv HiaX Hir RB HRB)).
      exists ihs; split; [ exact Ei | split; [ exact HZ |] ].
      intros SbB HSbB.
      destruct (sem_ctx_per_ctx_env HBs) as [RB HRB].
      pose proof (con_ihs_args ihs Ei RB HRB (HZ RB HRB)) as Hg2.
      pose proof con_canon_args as Hg1.
      pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      assert (HCa : tele_ass ((cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D))
        by (rewrite <- List.app_assoc, <- params_split; unfold tele_ass; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]).
      assert (HCs : ⊨ (cargs_ctx p D gs ++ ind_nparams D) ++ ind_uparams D)
        by (rewrite <- List.app_assoc, <- params_split; exact (IndCases.sd_cargs D HD p c gs Hl Hcon)).
      assert (HCS : ⊨ tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU ++ Γ).
      { pose proof (ElimCases.ihs_pre_sem D p Γ Us A gs HBs nil gs eq_refl) as H.
        cbn [ihs_ctx_aux List.app] in H; unfold cinst in H.
        rewrite tele_sub_app, length_nparams, <- List.app_assoc; exact H. }
      assert (HCsc : ctx_scoped (ind_nu D) (cargs_ctx p D gs ++ ind_nparams D)).
      { apply ctx_scoped_app; split; [ rewrite length_nparams; replace (ind_nn D + ind_nu D) with (ind_np D) by (unfold ind_nn; lia);
                                       exact (decl_closed_cargs_scoped D Hc p c gs Hin) | exact (decl_closed_nparams_scoped D Hc) ]. }
      pose proof (ElimCases.closed_args_gargs D HD Hc Hsu p Hl Us HUl ups bu ups_gargs ups_len Hbu c gs Hcon X X X vs vs Hb Hb Hv HiaX
                    (List.length gs) (le_n _)) as Hpg.
      rewrite List.firstn_all2, List.firstn_all2 in Hpg by lia.
      pose proof (tele_inst_args _ HCa HCs HCS HCsc Δ' σ' _ _ Hg1 Hpg) as Hg1'.
      eapply glu_sub_of_list; [ exact (elim_bctx_ass p D gs A Us Hc) | exact HSbB | exact HSbΓ | exact Hσ' |].
      unfold elim_bctx.
      replace (tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)) ++ tele_sub (ind_nparams D) (sb_of_list Id Us))
        with (tele_sub (cargs_ctx p D gs ++ ind_nparams D) τU) by (rewrite tele_sub_app, length_nparams; reflexivity).
      rewrite List.app_assoc, (List.app_assoc X).
      apply glu_args_app; [ apply tele_ass_sub; unfold tele_ass in HCa |- *; apply List.Forall_app in HCa as [H _]; exact H
                          | rewrite List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia
                          | rewrite List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_nparams; lia |].
      split; [ exact Hg1' | exact Hg2 ].
    Qed.
    Lemma con_main : elim_out Δ' Q M' (d_con p c (bs ++ vs)) σ' ns.
    Proof.
      destruct con_bctx as (ihs & Ei & HZ & Hgs).
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl Hrel) as (_ & HnX & Hvn & Hian).
      destruct (IndElim.brs_names_lookup _ _ _ _ HBn Hcon) as (n & B & HBl & HBin).
      pose proof (HBa c gs n B Hcon HBin) as Hn.
      pose proof (HBg c gs n B Hcon HBin) as HBgl.
      destruct HBgl as [SbB HSbB _ _].
      destruct (glu_rel_exp_clean_inversion1 HSbB (HBg c gs n B Hcon HBin)) as [iB HiB].
      destruct (HiB _ _ _ (Hgs SbB HSbB)) as [eb rb Pb Elb Eeb Erb Hgb HBglue].
      clear HiB.
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (Er : ⟦elim d_con p c (bs ++ vs) under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rb).
      { eapply eval_elim_con; [ exact Hl | exact Hcon | rewrite List.length_app; lia | exact HBl | exact Hn | |].
        - rewrite skipn_app_len by exact Hbl; exact Ei.
        - rewrite firstn_app_len, skipn_app_len by exact Hbl; exact Erb. }
      pose proof (bctx_sem c gs Hcon) as HBs.
      destruct (sem_ctx_per_ctx_env HBs) as [RB HRB].
      pose proof (HZ RB HRB) as HE.
      assert (Lb : List.length (elim_bctx p D gs A Us) = ind_nn D + List.length gs + cargs_nrec gs) by (rewrite length_elim_bctx; lia).
      destruct (ElimCases.us_wk_vals D HD Hc Γ RΓ HRΓ HΓ RU HRU Us HUl HUs _ RB ρ (X ++ vs ++ ihs) HRB HBs HE
                  ltac:(rewrite Lb, !List.length_app; lia)) as (w & u' & Hw & _ & _).
      rewrite Lb in Hw.
      pose proof (ElimCases.eval_bty D Hc p Hl Us HUl ups ups_len c gs Hcon ρ X vs ihs w LX Hvl Lih Hw) as Hev.
      pose proof (ElimCases.gsub_bty D HD Hc Hsu Hdt p Hl Γ HΓ Us HUl HUs ups ups_len HM A c gs Hcon HBs) as Hgb'.
      destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRB (InstanceCases.gsub_valid Hgb') HE Hev) as (eb' & b & Eeb' & Eb & Hebb).
      rewrite <- ElimCases.elim_bty_args in Eeb'.
      assert (eb' = eb) as -> by (eapply functional_eval_exp; eassumption).
      assert (Lw : List.length w = ind_nu D) by (rewrite (IndCases.eval_exps_length _ _ _ Hw), List.length_map; exact HUl).
      assert (Hm1 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns (d_con p c (bs ++ vs)) (d_con p c ((w ++ X) ++ vs))).
      { eapply ind_rel_con; [ exact Hns | exact Hcon | exact Hbl | rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia
                            | exact HnX | rewrite skipn_app_exact by exact Lw; exact HnX | exact Hvn | exact Hian ]. }
      destruct (mmid _ _ _ _ HnX Hm1) as (a & a' & Ea & Ea' & Haa).
      rewrite <- List.app_assoc in Ea'.
      assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (Hpe : Dom eb ≈ a ∈ per_univ iA).
      { eapply per_univ_trans'; [ exact Hebb | apply per_univ_sym'; eexists; exact Haa ]. }
      apply (mk_elim_out _ _ _ _ _ _ rb a Er Ea); [ eapply per_univ_trans'; [ apply per_univ_sym'; exact Hpe | exact Hpe ] |].
      intros P El HgP.
      pose proof con_Q_typed as HQt.
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
      destruct (motive_glu Δ' σ' Q M' _ ns Hσ' HQU HQl HMt HKm Hns Hrel Hgnm) as (a0 & Ea0 & _ & HTP).
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (HTP P El HgP) as HTg; clear HTP.
      destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ' σ' Hσt)
        as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
      rewrite <- HQU in HAt', HMx', HBx', HBt'.
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      assert (Lei : List.length (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As) = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
      assert (LZ : List.length (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As) = n)
        by (rewrite !List.length_app, LXs, HAl, Lei, Hn; lia).
      pose proof (brs_lookup_map (fun b => (snd b)[sb_qn (snd (fst b)) σ']) Bs c n B HBl) as HBl'.
      change (List.map _ Bs) with (brs_sub Bs σ') in HBl'; cbn [fst snd] in HBl'.
      pose proof (wf_exp_eq_elim_iota _ _ _ p D c gs Q As nm iA _ _ n _ HΔ' Hl Hcon HQl HQt HAl HAs Hnm HAt' HMx' HBn' HBx' HBa' HBt' HBl')
        as Hiota.
      pose proof (presup_exp_eq HMeq) as (_ & HM't & Hcont & _).
      pose proof (proj1 (presup_exp HAt')) as HMctx.
      pose proof (wf_elim_inst_sub_eq _ _ _ p D Q M' (apps (a_con p c) (Q ++ As)) Hl HΔ' HQl HQt HM't Hcont HMeq HMctx) as Hseq.
      pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HAt' Hseq) as HTeq.
      assert (Hcong : Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M' ≈ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') (apps (a_con p c) (Q ++ As))
                       : A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)]).
      { eapply wf_exp_eq_elim_cong; try eassumption; [ apply wf_exp_eq_refl; exact HAt' | reflexivity |].
        intros k c0 gs0 n0 B0 B0' H1 H2 Hc0; rewrite H1 in H2; injection H2 as <-.
        apply wf_exp_eq_refl; exact (HBt' c0 gs0 n0 B0 Hc0 (List.nth_error_In _ _ H1)). }
      assert (EB : B[sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)]
                   = B[sb_qn n σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)])
        by (rewrite <- LZ; symmetry; apply exp_sub_qn_of_list).
      assert (ET : (elim_bty p D c gs A Us)[sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') (sb_of_list Id Q) gs As)]
                   = A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ apps (a_con p c) (Q ++ As) :: nil)]).
      { rewrite <- (exp_sub_qn_of_list (elim_bty p D c gs A Us)), LZ, Hn, elim_bty_sub.
        rewrite elim_bty_iota by first [ exact LXs | exact HAl | exact Lei ].
        rewrite <- HQU, List.app_assoc, List.firstn_skipn, Hnm; reflexivity. }
      rewrite EB, ET in HBglue.
      pose proof (glu_univ_elem_typ_resp_exp_eq _ _ _ _ HgP _ _ _ HTg HTeq) as HTgb.
      pose proof (glu_univ_elem_exp_conv Hpe Hgb HgP HBglue HTgb) as HE1.
      pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ HgP _ _ _ _ _ HE1 (wf_exp_eq_sym _ _ _ _ _ _ HTeq)) as HE2.
      pose proof (wf_exp_eq_conv' _ _ _ _ _ _ _ _ Hiota (wf_exp_eq_sym _ _ _ _ _ _ HTeq)) as Hiota'.
      eapply glu_univ_elem_trm_resp_exp_eq; [ exact HgP | exact HE2 |].
      eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym; exact Hiota' | apply wf_exp_eq_sym; exact Hcong ].
    Qed.
  End ConCase.

  (** *** A Neutral *)
  Section NeutCase.
    Variable (m : domain_ne) (Q : list exp) (as' : list domain) (Δ' : ctx) (M' : exp).
    Hypothesis (Hm : per_bot m m)
      (Hrb : forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (apps (a_ind p) Q)[φ]ʷ).
    Variable (σ' : sub).
    Hypothesis (Hσ' : Δ' ⊢ˢ σ' ® ρ ∈ SbΓ) (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us)
      (HQl : List.length Q = ind_np D) (HMt : Δ' ⊢ M' : apps (a_ind p) Q).
    Variable (ns : list domain).
    Hypothesis (Hns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns)
      (Hrel : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns (⇑ (d_ind p as') m) (⇑ (d_ind p as') m))
      (HKm : forall Δ'' φ Q', Δ'' ⊢ᵏ φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl DP DEl Δ'' Q' M'[φ]ʷ (⇑ (d_ind p as') m))
      (Hgnm : glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns).

    Lemma neut_inv : List.length as' = ind_np D /\ ind_adm D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) (List.firstn (ind_nu D) as') /\
        tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns (List.skipn (ind_nu D) as').
    Proof. inversion Hrel; subst; auto. Qed.

    Lemma neut_Q_typed : forall k P T, List.nth_error Q k = Some P ->
        List.nth_error (tele_insts (ind_params D) Id Q) k = Some T -> Δ' ⊢ P : T.
    Proof.
      pose proof (us_glu_args Δ' σ' Hσ') as HUga.
      rewrite <- HQU in HUga.
      pose proof (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hgnm Hns) as HgN.
      assert (HfQ : List.length (List.firstn (ind_nu D) Q) = ind_nu D) by (rewrite List.length_firstn; lia).
      assert (Hga : glu_args Δ' (ind_params D) Id nil Q (ups ++ ns)).
      { rewrite <- (List.firstn_skipn (ind_nu D) Q), params_split.
        apply glu_args_app; [ exact Ua | rewrite HfQ, length_ind_uparams by exact Hle; reflexivity
                            | rewrite ups_len, length_ind_uparams by exact Hle; reflexivity |].
        split; [ exact HUga | exact HgN ]. }
      exact (glu_args_typed _ _ _ _ _ _ Hass Hga).
    Qed.

    Lemma neut_rb : forall Δ φ M0, Δ ⊢ᵏ φ : Δ' -> Rne d_elim ρ nm A Bs p as' m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
        Δ ⊢ (a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M')[φ]ʷ ≈ M0
          : (A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)])[φ]ʷ.
    Proof.
      intros Δ φ M0 Hφ HR.
      destruct neut_inv as (Lan & Hadm & Hsn).
      destruct (read_ne_elim_inv _ _ _ _ _ _ _ _ _ _ Hl HR) as (nsx & af & A'' & Bs'' & Mr & -> & _ & _ & Fx & Eaf & HRA & HRB & HRM).
      set (ua := List.firstn (ind_nu D) as') in *.
      assert (Lua : List.length ua = ind_nu D) by (unfold ua; rewrite List.length_firstn; lia).
      pose proof (glu_ctx_env_sub_monotone _ _ HSbΓ _ _ _ _ _ Hσ' Hφ) as Hσ''.
      set (σ'' := sb_wk σ' φ) in *.
      assert (Hσt : Δ ⊢ˢ σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
      assert (HΔ : ⊢ Δ) by (gen_presups; assumption).
      assert (EA : A[sb_qn nm σ'][wk_qn nm φ]ʷ = A[sb_qn nm σ''])
        by (apply exp_wk_sub_ext, sb_qn_wk_ext; intro; reflexivity).
      assert (EBs : List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) (brs_sub Bs σ') = brs_sub Bs σ'').
      { unfold brs_sub; rewrite List.map_map; apply List.map_ext; intros [[c0 n0] B0]; cbn; f_equal.
        apply exp_wk_sub_ext, sb_qn_wk_ext; intro; reflexivity. }
      assert (Ew : (a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M')[φ]ʷ = a_elim nm A[sb_qn nm σ''] (brs_sub Bs σ'') M'[φ]ʷ)
        by (rewrite <- EA, <- EBs; reflexivity).
      rewrite Ew, (wk_elim_type D Q A[sb_qn nm σ'] M' nm φ HQl Hnm), EA.
      set (Q' := List.map (fun P => P[φ]ʷ) Q).
      assert (HQU' : List.firstn (ind_nu D) Q' = List.map (fun U => U[σ'']) Us)
        by (unfold Q'; rewrite List.firstn_map, HQU, List.map_map; apply List.map_ext; intros; apply exp_wk_sub).
      destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ σ'' Hσt)
        as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
      rewrite <- HQU' in HAt', HMx', HBx', HBt'.
      change (ne_to_exp (ne_elim nm A'' Bs'' Mr)) with (a_elim nm (nf_to_exp A'') (nbrs_to_brs Bs'') (ne_to_exp Mr)).
      eapply wf_exp_eq_elim_cong; [ exact Hl | unfold Q'; rewrite List.length_map; exact HQl | | | exact Hnm | exact HAt' | exact HMx'
                                  | | exact HBn' | exact HBx' | | exact HBa' | ].
      - intros k P' T' HP HT; unfold Q' in HP, HT.
        apply nth_error_map_inv in HP as (P0 & HP0 & ->).
        rewrite <- params_insts_wk in HT by exact Hc.
        apply nth_error_map_inv in HT as (T0 & HT0 & ->).
        exact (kripke_preserves_exp _ _ _ _ _ (neut_Q_typed _ _ _ HP0 HT0) Hφ).
      - unfold Q'; rewrite <- wk_apps_ind; exact (Hrb Δ φ Mr Hφ HRM).
      - rewrite HQU'; exact (motive_rb Δ σ'' ua nsx af A'' Hσ'' Hadm Lua Fx Eaf HRA).
      - transitivity (List.map fst Bs); [ unfold brs_sub; rewrite List.map_map; reflexivity |].
        symmetry; exact (read_brs_fst _ _ _ _ _ _ _ _ _ HRB).
      - intros k c0 gs0 n0 Bw B'' H1 H2 Hc0.
        unfold brs_sub in H1; apply nth_error_map_inv in H1 as ([[c1 n1] B1] & H1 & E1); cbn in E1; injection E1 as -> -> ->.
        destruct (read_brs_nth _ _ _ _ _ _ _ _ _ HRB k c1 n1 B1 H1)
          as (gs & ns1 & vs1 & ihs1 & b1 & t1 & Bn & Hcs & HBk & F1 & C1 & I1 & Eb1 & Et1 & HRn).
        rewrite HBk in H2; injection H2 as <-.
        pose proof (IndElim.cons_lookup_nodup_in _ _ _ (IndCases.sd_nodup D HDc) (List.nth_error_In _ _ Hcs)) as Hc1.
        assert (gs = gs0) as <- by (unfold ind_con in Hc0; congruence).
        pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F1 Fx) as ->.
        rewrite HQU'.
        exact (br_rb Δ σ'' ua c1 gs n1 B1 nsx vs1 ihs1 b1 t1 Bn Hσ'' Hadm Lua Hc0 (List.nth_error_In _ _ H1) Fx C1 I1 Eb1 Et1 HRn).
    Qed.

    Lemma neut_main : elim_out Δ' Q M' (⇑ (d_ind p as') m) σ' ns.
    Proof.
      destruct neut_inv as (Lan & Hadm & Hsn).
      destruct (mmid _ _ _ _ Hsn Hrel) as (a & a1 & Ea & Ea1 & Haa).
      assert (Er : ⟦elim ⇑ (d_ind p as') m under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ⇑ a1 (d_elim ρ nm A Bs p as' m))
        by (eapply eval_elim_neut; eassumption).
      apply (mk_elim_out _ _ _ _ _ _ (⇑ a1 (d_elim ρ nm A Bs p as' m)) a Er Ea);
        [ eapply per_univ_trans'; [ eexists; exact Haa | apply per_univ_sym'; eexists; exact Haa ] |].
      intros P El HgP.
      destruct (motive_glu Δ' σ' Q M' _ ns Hσ' HQU HQl HMt HKm Hns Hrel Hgnm) as (a0 & Ea0 & _ & HTP).
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (HTP P El HgP) as HTg.
      pose proof (glu_univ_elem_resp_per_univ _ a a1 _ _ (ltac:(eexists; exact Haa) : Dom a ≈ a1 ∈ per_univ iA) HgP) as HgP1.
      eapply realize_glu_elem_bot; [ exact HgP1 |].
      assert (Hσt : Δ' ⊢ˢ σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ' σ' Hσt)
        as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
      rewrite <- HQU in HAt', HMx', HBx', HBt'.
      econstructor; [ | exact HgP1 | exact HTg | |].
      - eapply wf_elim; [ exact Hl | exact HQl | exact neut_Q_typed | exact HMt | exact Hnm | exact HAt' | exact HMx'
                        | exact HBn' | exact HBx' | exact HBa' | exact HBt' ].
      - exact (pbelim ns as' as' m m Lan Lan Hadm Hadm Hsn Hsn Hm).
      - intros Δ φ M0 Hφ HR; exact (neut_rb Δ φ M0 Hφ HR).
    Qed.
  End NeutCase.

  Lemma elim_con_case : forall c gs Ps bs vs As Γ' M,
       ind_con D c = Some gs ->
       List.length Ps = ind_np D ->
       List.length bs = ind_np D ->
       List.length vs = List.length gs ->
       List.length As = List.length gs ->
       Γ' ⊢ M ≈ apps (a_con p c) (Ps ++ As) : apps (a_ind p) Ps ->
       tele_full (ind_nr D ups) (List.rev (ind_nparams D)) (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs) ->
       tele_full (ind_ar D ups (List.skipn (ind_nu D) bs) c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) ->
       glu_nparams D NEl Γ' (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) (List.skipn (ind_nu D) bs) ->
       (forall k N A, List.nth_error As k = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some A -> Γ' ⊢ N : A) ->
       (forall gs1 A0 gs2 N A v, gs = gs1 ++ ca_arg A0 :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          Γ' ⊢ N : A ® v ∈ AEl (List.skipn (ind_nu D) bs) c (List.length (cargs_nonrec gs1))
                             (nonrec_vals gs1 (List.firstn (List.length gs1) vs))) ->
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          glu_rec p D ups NEl AEl DP DEl Γ' (List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t A N v) ->
       (forall gs1 t gs2 N A v, gs = gs1 ++ ca_rec t :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          rec_prop Γ' (List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs)) t A N v) ->
       elim_prop Γ' Ps M (d_con p c (bs ++ vs)).
  Proof.
    intros * Hcon HPl Hbl Hvl HAl HMeq Hb Hv Hnp HAs Harg Hrec IH.
    unfold elim_prop; intros σ' Hσ' HQU HQl HMt HK ns Hns Hrel Hgn.
    eapply con_main; eassumption.
  Qed.

  Lemma elim_neut_case : forall m Γ' Ps M as',
      per_bot m m ->
      (forall Δ φ M', Δ ⊢ᵏ φ : Γ' -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
         Δ ⊢ M[φ]ʷ ≈ M' : (apps (a_ind p) Ps)[φ]ʷ) ->
      elim_prop Γ' Ps M (⇑ (d_ind p as') m).
  Proof.
    intros * Hm Hrb; unfold elim_prop; intros σ' Hσ' HQU HQl HMt HK ns Hns Hrel Hgn.
    eapply neut_main; eassumption.
  Qed.

  Theorem elim_glu : (forall Δ' Q M' m', glu_ind p D ups NEl AEl DP DEl Δ' Q M' m' -> elim_prop Δ' Q M' m') /\
      (forall Δ' pre t T N v, glu_rec p D ups NEl AEl DP DEl Δ' pre t T N v -> rec_prop Δ' pre t T N v).
  Proof.
    apply (glu_ind_mut_ind_all p D ups NEl AEl DP DEl (fun Δ Q M m _ => elim_prop Δ Q M m) (fun Δ pre t T N v _ => rec_prop Δ pre t T N v)).
    - intros; eapply elim_con_case; eassumption.
    - intros; eapply elim_neut_case; eassumption.
    - intros; eapply rec_self_case; eassumption.
    - intros; eapply rec_pi_case; eassumption.
  Qed.
End ElimSem.

(** ** The Eliminator Is Glued *)

Lemma glu_rel_exp_elim : forall Γ p D Ps M nm A (i : nat) Bs,
    ind_lookup gc_deps gc_stack p = Some D -> glu_core D -> IndCases.sem_core D ->
    List.length Ps = ind_np D ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Γ ⊢ P : T) ->
    (forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (ind_params D) Id Ps) k = Some T -> Γ ⊩ P : T) ->
    Γ ⊢ M : apps (a_ind p) Ps -> Γ ⊩ M : apps (a_ind p) Ps ->
    nm = S (ind_nn D) ->
    elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊢ A : Typeω@i ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_mctx p D (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D (List.firstn (ind_nu D) Ps) ->
    elim_mctx p D (List.firstn (ind_nu D) Ps) ++ Γ ⊩ A : Typeω@i ->
    brs_names (ind_cons D) Bs ->
    (forall c gs, ind_con D c = Some gs ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ≈ elim_bctx p D gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs ->
       elim_bctx p D gs A (List.firstn (ind_nu D) Ps) ++ Γ ⊩ B : elim_bty p D c gs A (List.firstn (ind_nu D) Ps)) ->
    Γ ⊩ a_elim nm A Bs M : A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl HG HDc HPl HPt HPg HMt HMg Hnm HAt HMx HAg Hn HBx Hk HBt HBg.
  destruct (presup_exp HMt) as [HΓw _].
  destruct (decl_of_lookup _ _ _ _ _ HΓw Hl) as [Hdt Hc].
  pose proof (dt_sort_univ _ _ _ Hdt) as Hsu.
  pose proof (decl_closed_nu D Hc) as Hle.
  pose proof (decl_closed_params D Hc) as Hass.
  pose proof (dc_params _ Hc) as Hs0.
  pose proof (completeness_fundamental_ctx _ HΓw) as HΓs.
  destruct (sem_ctx_per_ctx_env HΓs) as [RΓ HRΓ].
  destruct (sem_ctx_per_ctx_env (IndCases.uparams_sem D HDc)) as [RU HRU].
  set (Us := List.firstn (ind_nu D) Ps) in *.
  set (Ns := List.skipn (ind_nu D) Ps) in *.
  pose proof (wk_firstn_length D Ps Hc HPl) as HUl; fold Us in HUl.
  destruct (params_split_gen D (fun N T => Γ ⊢ N : T) Ps Hc HPl HPt) as [_ HNt'].
  destruct (params_split_gen D (fun N T => Γ ⊩ N : T) Ps Hc HPl HPg) as [HUg _].
  destruct (params_split_gen D (fun N T => Γ ⊨ N : T) Ps Hc HPl ltac:(intros; eapply completeness_fundamental_exp; eauto)) as [HUs HNs].
  fold Us Ns in HNt', HUg, HUs, HNs.
  pose proof (completeness_fundamental_ctx _ (proj1 (presup_exp HAt))) as HMs.
  assert (HNt : ⊨ tele_sub (ind_nparams D) (sb_of_list Id Us) ++ Γ) by (unfold elim_mctx in HMs; cbn [List.app] in HMs; eapply sem_ctx_tail; exact HMs).
  pose proof HMg as [SbΓ HSbΓ _ _].
  eapply mk_glu_rel_exp with (gre_lvl := i); [ exact HSbΓ |]; intros Δ σ ρ Hσ.
  pose proof (glu_ctx_env_per_env HSbΓ HRΓ Hσ) as Hρ.
  assert (HΔ : ⊢ Δ) by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ); gen_presups; assumption).
  assert (HPv : forall k P, List.nth_error Ps k = Some P -> exists v, ⟦ P ⟧ ρ ↘ v).
  { intros k P HP.
    destruct (nth_error_lt_some' (tele_insts (ind_params D) Id Ps) k) as [T HT].
    { rewrite length_tele_insts by exact Hass; assert (k < List.length Ps) by (apply List.nth_error_Some; congruence); unfold ind_np in *; lia. }
    assert (HPs : Γ ⊨ P : T) by (eapply completeness_fundamental_exp; eapply HPt; eassumption).
    destruct (rel_exp_under_ctx_simple_at HRΓ HPs _ _ Hρ) as (v1 & v2 & E1 & _); eauto. }
  destruct (IndCases.eval_exps_each Ps ρ HPv) as [vs Hvs].
  pose proof (eval_exps_firstn _ _ _ (ind_nu D) Hvs) as HUv; fold Us in HUv.
  pose proof (eval_exps_skipn _ _ _ (ind_nu D) Hvs) as HNv; fold Ns in HNv.
  set (ups := List.firstn (ind_nu D) vs) in *; set (ns0 := List.skipn (ind_nu D) vs) in *.
  pose proof (params_glu_args _ _ _ _ _ _ _ _ _ Hass Hs0 (IndCases.sd_params D HDc) HΓs HRΓ HSbΓ Hσ HPl
                ltac:(intros; eapply completeness_fundamental_exp; eauto) HPg Hvs) as HPga.
  clear HPv HNt' HPg.
  assert (Hvl : List.length vs = ind_np D) by (rewrite <- HPl; exact (IndCases.eval_exps_length _ _ _ Hvs)).
  assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; lia).
  assert (Evs : vs = ups ++ ns0) by (symmetry; apply List.firstn_skipn).
  pose proof (glu_args_uparams_of_params D Hc _ _ _ HPga) as HUga.
  rewrite List.firstn_map in HUga; fold Us ups in HUga.
  pose proof HPga as HPga'.
  rewrite <- (List.firstn_skipn (ind_nu D) (List.map (fun M0 => M0[σ]) Ps)), Evs, params_split in HPga'.
  apply glu_args_app in HPga' as [_ HNga];
    [| exact (decl_uparams_ass D Hc) | rewrite List.length_firstn, List.length_map, length_ind_uparams by exact Hle; unfold ind_np in *; lia
     | rewrite Hu, length_ind_uparams by exact Hle; reflexivity ].
  rewrite List.firstn_map, List.skipn_map in HNga; fold Us Ns in HNga.
  destruct (sort_eval D HG Hc Hsu Δ _ ups HΔ HUga) as [bu Hbu].
  destruct (sort_bound D Hsu) as [n0 Hn0].
  destruct (glu_rel_exp_clean_inversion1 HSbΓ HMg) as [iM HiM].
  destruct (HiM _ _ _ Hσ) as [aM m PM ElM EaM Em HgM HMσ].
  assert (EaM' : ⟦ apps (a_ind p) Ps ⟧ ρ ↘ d_ind p vs).
  { apply Modules.eval_apps_exp; exists (d_ind p nil), vs; split; [ constructor | split; [ exact Hvs |] ].
    change (d_ind p vs) with (d_ind p (nil ++ vs)); apply (IndCases.eval_apps_ind D p Hl); cbn; lia. }
  assert (aM = d_ind p vs) as -> by (eapply functional_eval_exp; eassumption).
  clear EaM HiM.
  destruct (glu_univ_elem_cumu_ge (i := iM) (j := Nat.max iM n0) (Nat.le_max_l _ _) HgM) as (P1 & El1 & Hg1).
  assert (HMσ1 : El1 Δ (apps (a_ind p) Ps)[σ] M[σ] m)
    by (eapply glu_univ_elem_exp_cumu_ge; [ apply Nat.le_max_l | exact HgM | exact Hg1 | exact HMσ ]).
  set (u := Nat.max iM n0) in *.
  assert (Hule : uidx_le (IndSem.univ_idx bu) (ul u)) by (apply (Hn0 _ _ Hbu); unfold u; lia).
  rewrite Evs in Hg1.
  destruct (glu_univ_elem_per_univ _ _ _ _ Hg1) as [R0 HR0].
  destruct (glu_ind_of_per p D Hl (ul u) R0 ups ns0 HR0 Hu)
    as (NP & NEl & AP & AEl & DP & DEl & P2 & El2 & R' & Hg2 & HP2 & HEl2 & HRR & HeN & HNP & HeA & HAP & HeD & HDP).
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg1 Hg2) as [_ EE].
  apply EE, HEl2 in HMσ1; destruct HMσ1 as [HMt' Hmm Ps0 HT0 HK0].
  clear EE HgM HMσ HP2 HEl2 Hg2 P1 El1 Hg1 PM ElM.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (_ & _ & Hcp & _ & _ & Hadm & Hns0 & HRi).
  assert (Hrel0 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns0 m m) by (apply HRi, HRR; exact Hmm).
  clear HMg Hmm HRR R'.
  (** The scrutinee at the instance of the parameters. *)
  set (Q := List.map (fun P => P[σ]) Ps) in *.
  assert (HQl : List.length Q = ind_np D) by (unfold Q; rewrite List.length_map; exact HPl).
  assert (HQeq : forall Δ0 φ, Δ0 ⊢ᵏ φ : Δ -> exps_eq_at Δ0 (ind_params D) (List.map (fun P => P[φ]ʷ) Ps0) (List.map (fun P => P[φ]ʷ) Q)).
  { intros Δ0 φ Hφ.
    destruct HT0 as (_ & HT0); destruct (HT0 _ _ Hφ) as (Hpt0 & _ & _).
    eapply glu_params_top_eq; [ exact Hl | eapply kripke_dom; exact Hφ | exact (ind_rps_of_per _ _ _ _ _ _ HR0 Hl _) | exact Hpt0 |].
    rewrite <- Evs; apply glu_args_params_top; [ exact Hass | exact Hs0 |].
    exact (glu_args_wk _ _ _ _ _ _ _ Hass Hs0 Hφ HPga). }
  assert (HKQ : forall Δ0 φ Q', Δ0 ⊢ᵏ φ : Δ -> exps_eq_at Δ0 (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
                  glu_ind p D ups NEl AEl DP DEl Δ0 Q' M[σ][φ]ʷ m).
  { intros Δ0 φ Q' Hφ HQ'; apply (HK0 _ _ _ Hφ).
    eapply exps_eq_at_params_trans; [ exact Hl | eapply kripke_dom; exact Hφ | | exact (HQeq _ _ Hφ) | exact HQ' ].
    destruct (HQeq _ _ Hφ) as [L _]; rewrite !List.length_map in *; congruence. }
  clear HK0 HQeq HT0 Ps0.
  assert (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ]) Us) by (unfold Q, Us; apply List.firstn_map).
  assert (HQN : List.skipn (ind_nu D) Q = List.map (fun U => U[σ]) Ns) by (unfold Q, Ns; apply List.skipn_map).
  pose proof (comps_of_uparams p D HG Hc Hdt Hsu ups bu (ul u) NP NEl AP AEl DP DEl Hu Hbu Hule HeN HNP HeA HAP HeD HDP Δ _ HΔ HUga) as Hcomps.
  pose proof (nparams_of_glu_args p D Hc ups (ul u) NP NEl AP AEl DP DEl Hu HNP Δ _ _ _ Hcomps HNga Hns0) as Hgn.
  rewrite <- HQU, <- HQN in Hgn.
  assert (HMQ : Δ ⊢ M[σ] : apps (a_ind p) Q) by (unfold Q; rewrite <- sub_apps_ind; exact HMt').
  assert (HM0 : glu_ind p D ups NEl AEl DP DEl Δ Q M[σ] m).
  { pose proof (HKQ Δ wk_id Q ltac:(mauto 3)) as H; rewrite map_wk_id, exp_wk_id in H; apply H.
    eapply glu_params_top_refl; apply glu_args_params_top; [ exact Hass | exact Hs0 | exact HPga ]. }
  destruct (proj1 (elim_glu p D Hl HG Hc Hdt Hsu HDc Γ RΓ HRΓ HΓs RU HRU Us HUl HUs ρ ups Hρ HUv bu Hbu HNt SbΓ HSbΓ nm A i Bs
              Hnm HAt HMx Hn HBx Hk HBt HAg HBg HUg u NP NEl AP AEl DP DEl Hule HeN HNP HeA HAP HDP R0 ns0 HR0) Δ Q M[σ] m HM0
              σ Hσ HQU HQl HMQ HKQ ns0 Hns0 Hrel0 Hgn) as [r a Er Ea _ Hglr].
  clear HM0 HKQ Hgn Hcomps HNga HUga HPga.
  (** The type at the instance, against the motive at the values. *)
  assert (HNl : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
  assert (HMv : Γ ⊨ M : apps (a_ind p) (Us ++ Ns)) by (unfold Us, Ns; rewrite List.firstn_skipn; eapply completeness_fundamental_exp; exact HMt).
  pose proof (ElimCases.gsub_tau D Hc p Γ HΓs Us HUl HMs Ns M HNl HNs HMv) as Hgτ.
  assert (Hevl : ⟦ Ns ++ M :: nil ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ns0 ++ m :: nil)
    by (apply Modules.eval_exps_app; [ exact HNv | econstructor; [ exact Em | constructor ] ]).
  pose proof (IndSem.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hevl) as Hevτ.
  pose proof (completeness_fundamental_exp _ _ _ HAt) as HAv.
  destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HRΓ (InstanceCases.gsub_valid Hgτ) Hρ Hevτ) as (ares & b & Eares & Eb & Hab).
  assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hrr : Dom ares ≈ ares ∈ per_univ i) by (eapply per_univ_trans'; [ exact Hab | apply per_univ_sym'; exact Hab ]).
  destruct (per_univ_glu_univ_elem _ _ Hrr) as (P & El & Hgres).
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ Hab Hgres) as Hga.
  pose proof (Hglr P El Hga) as HE.
  econstructor; [ exact Eares | eapply eval_exp_elim; [ exact Em | exact Er ] | exact Hgres |].
  unfold Ns; rewrite (sub_elim_type D Ps A M nm σ HPl Hnm); exact HE.
Qed.

End Fixed_GCtx.
