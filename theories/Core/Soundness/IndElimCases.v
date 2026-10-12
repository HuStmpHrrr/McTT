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
From Mctt.Core.Completeness Require IndCases IndSem ElimCases TeleSem SubstitutionCases InstanceCases UnitCases MemberReps.
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

(** The value of an instance [X[τ]] is related to the value of [X] at an
    environment related to the substitution's value. *)
Lemma val_link : forall Δ0 Γ' X (i : nat) τ RΓ' E' Eτ RΔ0 E1,
    Δ0 ⊨ X : Typeω@i -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨s τ ≈ τ : Δ0 -> RΓ' E' E' -> ⟦ τ ⟧s E' ↘ Eτ ->
    EF Δ0 ≈ Δ0 ∈ per_ctx_env ↘ RΔ0 -> RΔ0 Eτ E1 ->
    exists a b, ⟦ X[τ] ⟧ E' ↘ a /\ ⟦ X ⟧ E1 ↘ b /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * HX HΓ' Hτ HE Hev HΔ0 HE1.
  destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HX HΓ' Hτ HE Hev) as (a & b0 & Ea & Eb0 & [R1 HR1]).
  destruct (rel_exp_of_typ_inversion_simple_at HΔ0 HX _ _ HE1) as (b1 & b & Eb1 & Eb & [R2 HR2]).
  assert (b1 = b0) as -> by (eapply functional_eval_exp; eassumption).
  destruct (InstanceCases.per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 HR2) as (R3 & HR3 & _).
  exists a, b; split; [ exact Ea | split; [ exact Eb | exists R3; exact HR3 ] ].
Qed.

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
    forall Δ σ ρ xs, Δ ⊢s σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a (i : uidx) R, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       DF a ≈ a ∈ per_univ_elem i ↘ R -> exists x, List.nth_error xs k = Some x /\ R (⇑! a (List.length Δ + k)) x) ->
    tele_sub C σ ++ Δ ⊢s sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
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
      Δ ⊢s τ ® env_args ρ ys ∈ Sb -> Δ ⊢s τ ® env_args ρ xs ∈ Sb.
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
    forall Δ σ ρ xs, Δ ⊢s σ ® ρ ∈ Sb_b -> List.length xs = List.length C ->
    (forall k A a, List.nth_error (List.rev C) k = Some (ce_ass A) -> ⟦ A ⟧ env_args ρ (List.firstn k xs) ↘ a ->
       exists b (j : nat), List.nth_error xs k = Some (⇑! b (List.length Δ + k)) /\ Dom a ≈ b ∈ per_univ j) ->
    tele_sub C σ ++ Δ ⊢s sb_qn (List.length C) σ ® env_args ρ xs ∈ Sb.
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
  intros * HlC HT (L1 & L2 & H) Hlink Hass.
  split; [ congruence | split; [ congruence |] ].
  intros k M T v A' HM HT' Hv HA'.
  destruct (Hass _ _ HA') as (A & HA & A'' & E); injection E as <-.
  rewrite <- HT in HT'.
  destruct (H _ _ _ _ _ HM HT' Hv HA) as (j & a & P & El & Ea & Hg & HP & HMg).
  assert (Hk : k < List.length vs) by (apply List.nth_error_Some; congruence).
  destruct (Hlink _ _ _ _ HA HA' Hk Ea) as (a' & i & Ea' & Hr).
  destruct (glu_transfer_per' j i a a' P El Δ T M v Hg (per_univ_sym' _ _ _ Hr) HP HMg) as (k' & P' & El' & Hg' & HP' & HM').
  exists k', a', P', El'; auto.
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
  destruct (IndSem.rel_gargs (List.rev C) ⋅ _ RC GlobalSem.per_ctx_env_nil_true HC' (List.Forall_rev Hass) HRC' ρ nil vs vs L' L' H2)
    as [_ Hgg]; exact Hgg.
Qed.

(** Terms glued at the instances of a closed telescope are glued
    arguments of it, at their values. *)
Lemma params_glu_args : forall C Γ RΓ Sb Δ σ ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> ⊨ C -> ⊨ Γ ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ -> EG Γ ∈ glu_ctx_env ↘ Sb -> Δ ⊢s σ ® ρ ∈ Sb -> List.length Ms = List.length C ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊨ N : T) ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts C Id Ms) k = Some T -> Γ ⊩ N : T) ->
    ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> glu_args Δ C Id nil (List.map (fun M => M[σ]) Ms) vs.
Proof.
  intros * Hass Hs HC HΓ HRΓ HSb Hσ Hl HMs HMg Hv.
  pose proof (glu_ctx_env_per_env HSb HRΓ Hσ) as Hρ.
  pose proof (closed_args_gargs _ _ _ _ _ _ Hass HC HΓ HRΓ Hρ Hl HMs Hv) as Hpg.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (IndCases.eval_exps_length _ _ _ Hv)).
  split; [ rewrite List.length_map; exact Hl | split; [ exact Lv |] ].
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
  exists k', a2, P', El'; auto.
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
    ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)) ->
    tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns /\
    tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns (List.skipn (ind_nu D) bs) /\
    tele_full (ind_ar D ups ns c) (cargs_nonrec gs) (nonrec_vals gs vs) (nonrec_vals gs vs) /\
    ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (env_args nil (ups ++ ns)) gs vs vs.
Proof.
  intros * Hcn Hbl H.
  inversion H as [? ? gs0 bs0 bs0' vs0 vs0' Hn Hc0 Hb0 Hb0' Hs Hs' Hav Hia | ]; subst.
  match goal with E : bs0 ++ vs0 = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ E ltac:(congruence)) as [-> ->] end.
  match goal with E : bs0' ++ vs0' = bs ++ vs |- _ => destruct (app_split_eq _ _ _ _ E ltac:(congruence)) as [-> ->] end.
  rewrite Hcn in Hc0; injection Hc0 as <-.
  auto.
Qed.

(** ** The Recursive Results' Types at the Instance of [ι] *)

Lemma length_cargs_strat_nonrec : forall gs, List.length (cargs_strat gs) = List.length (cargs_nonrec gs).
Proof. induction gs as [| [] gs IH]; cbn; rewrite ?List.length_app; cbn; lia. Qed.

Lemma sb_of_list_compose_base : forall Ms σ0 σ,
    sb_eq (sb_of_list σ0 Ms ⨟ σ) (sb_of_list (σ0 ⨟ σ) (List.map (fun M => M[σ]) Ms)).
Proof.
  induction Ms as [| M Ms IH]; intros σ0 σ x; cbn [sb_of_list List.map]; [ reflexivity |].
  rewrite (IH (σ0,,M) σ x); apply sb_of_list_cong, sb_extend_compose.
Qed.

Lemma sb_of_list_base_lt : forall Ms σ τ x, x < List.length Ms -> sb_of_list σ Ms x = sb_of_list τ Ms x.
Proof. intros * Hx; rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; reflexivity. Qed.

Lemma sb_shift_past : forall Ms Ns σ, sb_eq (ι (wk_shiftn (List.length Ns)) ⨟ sb_of_list σ (Ms ++ Ns)) (sb_of_list σ Ms).
Proof.
  intros * x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; rewrite sb_of_list_app, Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

Lemma sb_of_list_shift_compose_gen : forall Ms L σ,
    sb_eq (sb_of_list (ι (wk_shiftn (List.length L))) Ms ⨟ sb_of_list σ L)
          (sb_of_list σ (List.map (fun M => M[sb_of_list σ L]) Ms)).
Proof.
  intros; etransitivity; [ apply sb_of_list_compose_base |].
  apply sb_of_list_cong; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  rewrite Nat.add_comm, sb_of_list_ge; reflexivity.
Qed.

(** A recursive result's type in the branch's context, at the instance of
    the branch's context by the iota rule, is the motive at the instance of
    the recursive argument's type and the argument. *)
Lemma ih_entry_inst : forall D A Us σ gs1 Pr Xs As L, ind_nu D <= ind_np D ->
    List.length Us = ind_nu D -> List.length Xs = ind_nn D -> List.length gs1 < List.length As ->
    List.length Pr = ind_nn D -> List.Forall (exp_scoped (List.length (cargs_strat gs1) + ind_np D)) Pr ->
    (A[sb_of_list (ι (wk_shiftn (List.length L + List.length As + ind_nn D)))
         (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                [wk_shiftn (List.length As - List.length (cargs_pat gs1) + List.length L)]ʷ) Pr
          ++ a_var (List.length L + List.length As - 1 - List.length (cargs_pat gs1)) :: nil)])[sb_of_list σ (Xs ++ As ++ L)]
    = A[sb_qn (S (ind_nn D)) σ][sb_of_list Id (List.map (fun P => P[sb_of_list Id ((List.map (fun U => U[σ]) Us ++ Xs)
                                                                 ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))]) Pr
                                              ++ List.nth (List.length gs1) As (a_var 0) :: nil)].
Proof.
  intros * Hle HUl HXl Hlt HPl HPs.
  rewrite length_cargs_pat.
  set (i := List.length gs1) in *.
  rewrite exp_sub_sub.
  replace (List.length L + List.length As + ind_nn D) with (List.length (Xs ++ As ++ L)) by (rewrite !List.length_app; lia).
  rewrite (exp_sub_sb_eq _ _ _ (sb_of_list_shift_compose_gen _ _ σ)).
  replace (S (ind_nn D)) with (List.length (List.map (fun P => P[sb_of_list Id ((List.map (fun U => U[σ]) Us ++ Xs)
                                                              ++ nonrec_exps gs1 (List.firstn i As))]) Pr ++ List.nth i As (a_var 0) :: nil))
    by (rewrite List.length_app, List.length_map, HPl; cbn; lia).
  rewrite exp_sub_qn_of_list.
  f_equal; f_equal; rewrite List.map_app, List.map_map; f_equal.
  - apply List.map_ext_in; intros P HP.
    pose proof (proj1 (List.Forall_forall _ _) HPs P HP) as HPsc.
    assert (EZ : Xs ++ As ++ L = (Xs ++ List.firstn i As) ++ (List.skipn i As ++ L))
      by (rewrite <- (List.firstn_skipn i As) at 1; rewrite !List.app_assoc; reflexivity).
    rewrite EZ.
    replace (List.length As - i + List.length L) with (List.length (List.skipn i As ++ L)) by (rewrite List.length_app, List.length_skipn; lia).
    rewrite exp_sub_wk, (exp_sub_sb_eq _ _ _ (sb_shift_past _ _ σ)).
    rewrite exp_sub_sub.
    replace (i + ind_nn D) with (List.length (Xs ++ List.firstn i As)) by (rewrite List.length_app, List.length_firstn; lia).
    rewrite (exp_sub_sb_eq _ _ _ (sb_qn_of_list _ _ _)).
    rewrite (exp_sub_sb_eq _ _ (sb_of_list (sb_of_list σ (List.map (fun U => U[σ]) Us)) (Xs ++ List.firstn i As)))
      by (apply sb_of_list_cong; etransitivity; [ apply sb_of_list_compose_base | apply sb_of_list_cong, sb_compose_id_left ]).
    rewrite sb_of_list_app, exp_wk_pat_sb_of_list by (rewrite List.length_firstn; lia).
    rewrite <- !sb_of_list_app, <- List.app_assoc.
    eapply exp_scoped_sub_agree; [ exact HPsc |].
    intros x Hx; apply sb_of_list_base_lt.
    rewrite !List.length_app, List.length_map, length_nonrec_exps by (rewrite List.length_firstn; lia).
    pose proof (length_cargs_strat_nonrec gs1) as E; rewrite HUl, HXl, <- E; unfold ind_nn; lia.
  - cbn [List.map]; f_equal; change (exp_sub (a_var ?x) ?s) with (sentry_exp (s x)).
    rewrite (sb_of_list_nth _ _ _ (a_var 0)) by (rewrite !List.length_app; lia).
    rewrite !List.length_app.
    replace (List.length Xs + (List.length As + List.length L) - 1 - (List.length L + List.length As - 1 - i)) with (List.length Xs + i) by lia.
    cbn [sentry_exp]; rewrite List.app_nth2 by lia; replace (List.length Xs + i - List.length Xs) with i by lia.
    rewrite List.app_nth1 by lia; reflexivity.
Qed.

(** ** The Recursive Results, Position by Position *)

Lemma ihs_rev_nth : forall D A Us na gs k e,
    List.nth_error (List.rev (ihs_ctx_aux D A Us na nil 0 gs)) k = Some e ->
    exists gs1 Pr gs2, gs = gs1 ++ ca_rec Pr :: gs2 /\ cargs_nrec gs1 = k /\
      e = ce_ass A[sb_of_list (ι (wk_shiftn (k + na + ind_nn D)))
                     (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                          [wk_shiftn (na - List.length (cargs_pat gs1) + k)]ʷ) Pr
                      ++ a_var (k + na - 1 - List.length (cargs_pat gs1)) :: nil)].
Proof.
  intros D A Us na gs; induction gs as [| g gs IH] using List.rev_ind; intros k e H; [ cbn in H; destruct k; discriminate |].
  pose proof (ElimCases.ihs_ctx_aux_app D A Us na gs (g :: nil) nil 0) as E.
  rewrite List.app_nil_r in E; cbn [Nat.add] in E; rewrite E in H; clear E.
  destruct g as [B | Pr]; cbn [ihs_ctx_aux List.app] in H.
  - destruct (IH k e H) as (gs1 & Pr & gs2 & -> & Hk & ->).
    exists gs1, Pr, (gs2 ++ ca_arg B :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
  - cbn [List.rev] in H.
    destruct (Nat.lt_ge_cases k (List.length (ihs_ctx_aux D A Us na nil 0 gs))) as [Hlt | Hge].
    + rewrite List.nth_error_app1 in H by (rewrite List.length_rev; exact Hlt).
      destruct (IH k e H) as (gs1 & Pr' & gs2 & -> & Hk & ->).
      exists gs1, Pr', (gs2 ++ ca_rec Pr :: nil); split; [ rewrite <- List.app_assoc; reflexivity | split; [ exact Hk | reflexivity ] ].
    + rewrite List.nth_error_app2 in H by (rewrite List.length_rev; exact Hge).
      rewrite List.length_rev in H; rewrite length_ihs_ctx_aux in H, Hge.
      destruct (k - cargs_nrec gs) as [| k'] eqn:Ek; cbn in H; [| destruct k'; discriminate ].
      injection H as <-.
      assert (k = cargs_nrec gs) as -> by (pose proof (proj1 (Nat.sub_0_le k (cargs_nrec gs)) Ek); lia).
      exists gs, Pr, nil; split; [ reflexivity | split; [ reflexivity |] ].
      try rewrite List.app_nil_r; reflexivity.
Qed.

Lemma elim_ihs_nth : forall nm A Bs gs gs1 Pr gs2 As N, gs = gs1 ++ ca_rec Pr :: gs2 -> List.length As = List.length gs ->
    List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (elim_ihs nm A Bs gs As) (cargs_nrec gs1) = Some (a_elim nm A Bs N).
Proof.
  intros nm A Bs gs gs1; revert gs; induction gs1 as [| g gs1 IH]; intros gs Pr gs2 As N -> Hl HN;
    destruct As as [| N0 As]; cbn in *; try discriminate; [ injection HN as ->; reflexivity |].
  destruct g; cbn; [ apply (IH _ Pr gs2); auto | apply (IH _ Pr gs2); auto ].
Qed.

Lemma eval_ihs_nth : forall ρ nm A Bs gs1 gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
    forall Pr gs2 v, gs = gs1 ++ ca_rec Pr :: gs2 -> List.nth_error vs (List.length gs1) = Some v ->
    exists r, List.nth_error ihs (cargs_nrec gs1) = Some r /\ ⟦elim v under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r.
Proof.
  intros ρ nm A Bs gs1; induction gs1 as [| g gs1 IH]; intros gs vs ihs H Pr gs2 v -> Hv; inversion H; subst; cbn in *.
  - injection Hv as ->; eauto.
  - eapply IH; eauto.
  - edestruct (IH _ _ _ ltac:(eassumption) _ _ _ eq_refl Hv) as (r & Hr & Er); exists r; split; [ exact Hr | exact Er ].
Qed.

(** ** The Eliminator's Premises at a Substitution *)

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

Lemma functional_fresh_cargs : forall p ups E gs s vs bss, fresh_cargs gc_deps gc_stack p ups E gs s vs bss ->
    forall vs' bss', fresh_cargs gc_deps gc_stack p ups E gs s vs' bss' -> vs = vs' /\ bss = bss'.
Proof.
  induction 1; intros vs' bss' H'; inversion H'; subst; [ auto | |].
  - functional_eval_rewrite_clear.
    match goal with H : fresh_cargs _ _ _ _ _ _ _ _ _ |- _ => destruct (IHfresh_cargs _ _ H) as [-> ->] end; auto.
  - match goal with H1 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?E ↘ ?b1, H2 : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ ?E ↘ ?b2 |- _ =>
      pose proof (functional_eval_exps' _ _ _ _ H1 H2) as <- end.
    match goal with H : fresh_cargs _ _ _ _ _ _ _ _ _ |- _ => destruct (IHfresh_cargs _ _ H) as [-> ->] end; auto.
Qed.

Lemma functional_fresh_ihs : forall ρ A gs vs bss s ihs, fresh_ihs gc_deps gc_stack ρ A gs vs bss s ihs ->
    forall ihs', fresh_ihs gc_deps gc_stack ρ A gs vs bss s ihs' -> ihs = ihs'.
Proof.
  induction 1; intros ihs' H'; inversion H'; subst; [ reflexivity | auto |].
  functional_eval_rewrite_clear; f_equal; auto.
Qed.

Lemma fresh_cargs_nth : forall p ups E gs s vs bss, fresh_cargs gc_deps gc_stack p ups E gs s vs bss ->
    forall gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    (forall A, g = ca_arg A -> exists a, ⟦ A ⟧ env_args E (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ a /\
       List.nth_error vs (List.length gs1) = Some (⇑! a (s + List.length gs1))) /\
    (forall Ps, g = ca_rec Ps -> exists bs, ⟦ (ptyp_ps Ps) ⟧* gc_deps ⍮ gc_stack ⍮ env_args E (nonrec_vals gs1 (List.firstn (List.length gs1) vs)) ↘ bs /\
       List.nth_error vs (List.length gs1) = Some (⇑! (d_ind p (ups ++ bs)) (s + List.length gs1)) /\
       List.nth_error bss (cargs_nrec gs1) = Some bs).
Proof.
  intros p ups E gs s vs bss H gs1; revert E gs s vs bss H; induction gs1 as [| g1 gs1 IH]; intros * H g gs2 Heq; cbn in Heq.
  - subst; split; intros * ->; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_cargs _ _ _ _ _ (gs1 ++ _) _ _ _ |- _ => destruct (IH _ _ _ _ _ Hr1 g gs2 eq_refl) as [IHa IHr] end.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros Ps0 ->; destruct (IHr Ps0 eq_refl) as (bs0 & Ebs & Hv & Hb); exists bs0; cbn; split; [ exact Ebs | split; [| exact Hb ] ].
        rewrite Hv; do 3 f_equal; lia.
    + split.
      * intros A0 ->; destruct (IHa A0 eq_refl) as (a0 & Ea & Hv); exists a0; cbn; split; [ exact Ea |].
        rewrite Hv; do 3 f_equal; lia.
      * intros Ps0 ->; destruct (IHr Ps0 eq_refl) as (bs0 & Ebs & Hv & Hb); exists bs0; cbn; split; [ exact Ebs | split; [| exact Hb ] ].
        rewrite Hv; do 3 f_equal; lia.
Qed.

Lemma fresh_ihs_nth : forall ρ A gs vs bss s ihs, fresh_ihs gc_deps gc_stack ρ A gs vs bss s ihs ->
    forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
    exists v bs t, List.nth_error vs (List.length gs1) = Some v /\ List.nth_error bss (cargs_nrec gs1) = Some bs /\
      ⟦ A ⟧ env_args ρ (bs ++ v :: nil) ↘ t /\ List.nth_error ihs (cargs_nrec gs1) = Some (⇑! t (s + cargs_nrec gs1)).
Proof.
  intros ρ A gs vs bss s ihs H gs1; revert gs vs bss s ihs H; induction gs1 as [| g1 gs1 IH]; intros * H Ps gs2 Heq; cbn in Heq.
  - subst; inversion H; subst; cbn; rewrite Nat.add_0_r; eauto 10.
  - subst; inversion H; subst;
      lazymatch goal with Hr1 : fresh_ihs _ _ _ _ (gs1 ++ _) _ _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ Hr1 Ps gs2 eq_refl) as (v0 & bs0 & t0 & Hv & Hb & Et & Hi) end.
    + exists v0, bs0, t0; cbn; auto.
    + exists v0, bs0, t0; cbn.
      split; [ exact Hv | split; [ exact Hb | split; [ exact Et |] ] ].
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
    exists gs ns vs bss ihs b t Bn, List.nth_error cs k = Some (c, gs) /\
      List.nth_error (nbrs_to_brs Bs'') k = Some (c, n, nf_to_exp Bn) /\
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) s ns /\
      fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns)) gs (s + ind_nn D) vs bss /\
      fresh_ihs gc_deps gc_stack ρ0 A0 gs vs bss (s + ind_nn D + List.length gs) ihs /\
      ⟦ B ⟧ env_args ρ0 (ns ++ vs ++ ihs) ↘ b /\
      ⟦ A0 ⟧ env_args ρ0 (ns ++ d_con p c (ua ++ ns ++ vs) :: nil) ↘ t /\
      Rnf ⇓ t b in gc_deps ⍮ gc_stack ⍮ (s + n) ↘ Bn.
Proof.
  induction 1 as [| * ? ? ? ? ? ? ? ? ? IH]; intros k c0 n0 B0 Hk; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in Hk |- *.
  - injection Hk as <- <- <-; eexists _, _, _, _, _, _, _, _.
    refine (conj eq_refl (conj eq_refl _)); subst; repeat split; eassumption.
  - exact (IH k c0 n0 B0 Hk).
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
  Lemma elim_prems_at : forall Δ σ, Δ ⊢s σ : Γ ->
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
  (** An element of the inductive type at glued parameters, related to
      itself, and an element at every weakening and instance of the
      parameters, at the gluings of the clause at [ups], is glued at the
      type. *)
  Lemma ind_elem_glue : forall (u : uidx) R ups0 ns bu NP NEl AP AEl Δ Q M m,
      List.length ups0 = ind_nu D -> ⟦ ind_sort D ⟧ env_args nil ups0 ↘ bu -> uidx_le (IndSem.univ_idx bu) u ->
      (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups0) k vs vs -> ⟦ A ⟧ env_args nil (ups0 ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs) ->
      (forall ms c gs k A vs b, tele_full (ind_nr D ups0) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
         tele_pre (ind_ar D ups0 ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups0 ++ ms ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs) ->
      DF d_ind p (ups0 ++ ns) ≈ d_ind p (ups0 ++ ns) ∈ per_univ_elem u ↘ R ->
      ⊢ Δ -> glu_args Δ (ind_params D) Id nil Q (ups0 ++ ns) -> Δ ⊢ M : apps (a_ind p) Q -> R m m ->
      (forall Δ' φ Q', Δ' ⊢k φ : Δ -> exps_eq_at Δ' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups0 NEl AEl Δ' Q' M[φ]ʷ m) ->
      exists P El, DG d_ind p (ups0 ++ ns) ∈ glu_univ_elem u ↘ P ↘ El /\ Δ ⊢ apps (a_ind p) Q ® P /\
        Δ ⊢ M : apps (a_ind p) Q ® m ∈ El.
  Proof.
    intros * Hu Hbu Hule HNP HAP HR HΔ Hg HM Hm HK.
    destruct (glu_ind_of_per p D Hl u R ups0 ns HR Hu)
      as (NP' & NEl' & AP' & AEl' & P & El & R' & Hg' & HP & HEl & HRR & HeN' & HNP' & HeA' & HAP').
    pose proof (decl_closed_params D Hc) as Hass.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR Hl Hu Hu) as (_ & _ & Hcp & _).
    pose proof (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Δ Q ups0 ns bu u NP' NEl' AP' AEl' HΔ Hg Hu Hbu Hule HeN' HNP' HeA' HAP') as HT.
    exists P, El; split; [ exact Hg' | split ].
    - apply HP; exists Q; exact HT.
    - apply HEl; split; [ exact HM | split; [ apply HRR; exact Hm | exists Q; split; [ exact HT |] ] ].
      intros Δ' φ Q' Hφ HQ'.
      apply (glu_ind_mono p D ups0 NEl AEl Hass Hcp NEl' AEl'); [ | | exact (HK _ _ _ Hφ HQ') ].
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
      forall Δ' σ' Ns ns M m (j : uidx) P El, Δ' ⊢s σ' ® ρ ∈ SbΓ ->
        glu_args Δ' (ind_nparams D) (sb_of_list Id (List.map (fun U => U[σ']) Us)) (env_args nil ups) Ns ns ->
        tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        DG d_ind p (ups ++ ns) ∈ glu_univ_elem j ↘ P ↘ El ->
        Δ' ⊢ apps (a_ind p) (List.map (fun U => U[σ']) Us ++ Ns) ® P ->
        Δ' ⊢ M : apps (a_ind p) (List.map (fun U => U[σ']) Us ++ Ns) ® m ∈ El ->
        Δ' ⊢s sb_of_list σ' (Ns ++ M :: nil) ® env_args ρ (ns ++ m :: nil) ∈ SbM.
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
    exists k', (d_ind p (w ++ ns)), P', El'; split; [ exact Ew | split; [ exact Hg' | split; assumption ] ].
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
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred).
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
       DG b ∈ glu_univ_elem (ul u) ↘ AP ms c k vs ↘ AEl ms c k vs).
  Variable (R0 : relation domain) (ns0 : list domain).
  Hypothesis (HR0 : DF d_ind p (ups ++ ns0) ≈ d_ind p (ups ++ ns0) ∈ per_univ_elem (ul u) ↘ R0).

  Lemma us_glu_args : forall Δ'' σ'', Δ'' ⊢s σ'' ® ρ ∈ SbΓ ->
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
  Let Had := proj2 (proj2 (proj2 (proj2 Hcan))).
  Let Hass : tele_ass (ind_params D) := decl_closed_params D Hc.
  Let Hle : ind_nu D <= ind_np D := decl_closed_nu D Hc.
  Let imv := IndElim.ind_rel_mv p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle.
  Let tsym := tnr_sym p D ups _ _ Hass HnP HnI HaP HaI.
  Let ttrans := tnr_trans p D ups _ _ Hass HnP HnI HaP HaI.
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
  Let pelim := IndElim.per_ind_elim_all p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                 (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm.

  (** The substitution of the motive's context at the fresh variables a
      stuck eliminator's readback makes, at admissible uniform parameters. *)
  Lemma mctx_fresh_glu : forall SbM, EG elim_mctx p D Us ++ Γ ∈ glu_ctx_env ↘ SbM ->
      forall Δ σ'' ua ns_x, Δ ⊢s σ'' ® ρ ∈ SbΓ -> ind_adm D ups (ind_nr D ups) (ind_ar D ups) ua -> List.length ua = ind_nu D ->
        fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
        elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ ⊢s sb_qn nm σ''
          ® env_args ρ (ns_x ++ ⇑! (d_ind p (ua ++ ns_x)) (List.length Δ + ind_nn D) :: nil) ∈ SbM.
  Proof.
    intros SbM HSbM Δ σ'' ua ns_x Hσ'' Hadm Lua Hfx.
    destruct (IndElim.fresh_np2 p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ups ua (List.length Δ) Had Hadm) as (ns_u & ns_x' & Fu & Fx & Hux).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ Fx Hfx) as ->; clear Fx.
    pose proof (ttrans _ _ _ Hux (tsym _ _ Hux)) as Huu.
    pose proof (fresh_tele_length _ _ _ _ Fu) as Lu; rewrite List.length_rev, length_nparams in Lu.
    pose proof (fresh_tele_length _ _ _ _ Hfx) as Lx; rewrite List.length_rev, length_nparams in Lx.
    assert (HMlen : List.length (elim_mctx p D Us) = nm) by (rewrite length_elim_mctx; symmetry; exact Hnm).
    rewrite <- (elim_mctx_sub p D Us σ'' Hc HUl), <- HMlen.
    assert (Hws : tele_sub (elim_mctx p D Us) σ'' ++ Δ ⊢s sb_qn (List.length (elim_mctx p D Us)) σ''
                    ® env_args ρ (ns_u ++ ⇑! (d_ind p (ups ++ ns_u)) (List.length Δ + ind_nn D) :: nil) ∈ SbM).
    { apply (glu_sub_fresh _ Γ SbΓ (elim_mctx_ass p D Us Hc) HSbΓ SbM HSbM Δ σ'' ρ _ Hσ'');
        [ rewrite List.length_app, length_elim_mctx; cbn; lia |].
      intros k X a HX Ea; exact (mctx_entry_link _ _ Fu Huu k X a HX Ea). }
    destruct (sem_ctx_per_ctx_env HM) as [RM HRM].
    pose proof (IndElim.ind_rel_var p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                  (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ns_u ups ua ns_u ns_x (List.length Δ + ind_nn D)
                  Had Hadm ups_len Lua Huu Hux) as Hv.
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
      forall s ns_u vs_u bss_u ihs_u,
      fresh_tele gc_deps gc_stack (env_args nil ups) (List.rev (ind_nparams D)) s ns_u ->
      fresh_cargs gc_deps gc_stack p ups (env_args nil (ups ++ ns_u)) gs (s + ind_nn D) vs_u bss_u ->
      fresh_ihs gc_deps gc_stack ρ A gs vs_u bss_u (s + ind_nn D + List.length gs) ihs_u ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns_u ns_u ->
      tele_full (ind_ar D ups ns_u c) (cargs_nonrec gs) (nonrec_vals gs vs_u) (nonrec_vals gs vs_u) ->
      ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (env_args nil (ups ++ ns_u)) gs vs_u vs_u ->
      ihs_rel Rel (env_args nil (ups ++ ns_u)) gs vs_u vs_u ihs_u ihs_u ->
      forall k X a, List.nth_error (List.rev (elim_bctx p D gs A Us)) k = Some (ce_ass X) ->
        ⟦ X ⟧ env_args ρ (List.firstn k (ns_u ++ vs_u ++ ihs_u)) ↘ a ->
        exists b (j : nat), List.nth_error (ns_u ++ vs_u ++ ihs_u) k = Some (⇑! b (s + k)) /\ Dom a ≈ b ∈ per_univ j.
  Proof.
    intros c gs Hcon s ns_u vs_u bss_u ihs_u Fn Fc Fi Hns Har Hia Hir k X a HX Ea.
    pose proof (fresh_tele_length _ _ _ _ Fn) as Ln; rewrite List.length_rev, length_nparams in Ln.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li _].
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
        destruct (fresh_cargs_nth _ _ _ _ _ _ _ Fc gs1 g gs2 Heq) as [Fa Fr].
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
          destruct (Fr Pr eq_refl) as (bs' & Ebs' & Hv & _).
          pose proof (nonrec_prefix_pre _ _ _ _ _ _ Har Lv Heq) as Hpk.
          destruct Hbb as [Rb HRb].
          destruct (ElimCases.rec_entry_char D HD Hc Hsu p Hl Us HUl c gs Hcon gs1 Pr gs2 Heq ups ns_u (List.firstn (List.length gs1) vs_u) bu
                      ups_len Ln ltac:(rewrite List.length_firstn; lia) ups_gargs Hbu Hns Hpk
                      ltac:(intros R' HR'; apply (per_ctx_env_right_irrel _ _ _ _ _ HR HR'); exact HE) _ _ _ _ Eb HRb)
            as (bs0 & bs1 & Ebs0 & Ebs1 & Hb01 & -> & _).
          rewrite <- env_args_app, <- List.app_assoc in Ebs'.
          pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebs') as <-.
          pose proof (IndCases.ind_relate D HDc Hc Hsu p Hl ups ups bs0 bs1 bu ups_gargs ups_len Hbu Hb01) as Hrel1.
          destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hrel1) as [n Hn].
          destruct Hab as [R1 HR1].
          destruct (InstanceCases.per_univ_elem_trans_any _ _ _ _ _ _ _ HR1 (per_univ_sym _ _ _ _ Hn)) as (R2 & HR2 & _).
          exists (d_ind p (ups ++ bs0)), j; split; [ apply Hnthw; rewrite Hv; do 3 f_equal; lia | eexists; exact HR2 ].
    - (** The recursive results. *)
      rewrite List.nth_error_app2 in HX by lia; rewrite LC in HX.
      remember (k - (ind_nn D + List.length gs)) as i eqn:Hi.
      destruct (ihs_rev_nth D A Us (List.length gs) gs i _ HX) as (gs1 & Pr & gs2 & Heq & Hi' & HXe).
      injection HXe as ->.
      subst i.
      assert (Hfk : List.firstn k (ns_u ++ vs_u ++ ihs_u) = (ns_u ++ vs_u) ++ List.firstn (cargs_nrec gs1) ihs_u)
        by (rewrite List.app_assoc, firstn_app_ge by (rewrite List.length_app; lia); rewrite List.length_app, Ln, Lv, Hi'; reflexivity).
      rewrite Hfk in Ea.
      rewrite <- Hi' in Ea.
      assert (Ea' : ⟦ A[sb_of_list (sb_of_wk (wk_shiftn (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs + ind_nn D)))
                     (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                  [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1))]ʷ) Pr
                      ++ a_var (List.length (ihs_ctx_aux D A Us (List.length gs) nil 0 gs1) + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil)] ⟧
                    env_args ρ ((ns_u ++ vs_u) ++ List.firstn (cargs_nrec gs1) ihs_u) ↘ a)
        by (rewrite length_ihs_ctx_aux; exact Ea).
      destruct (ElimCases.ih_entry_link D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM
                  A iA HAv ρ ρ Hρ HUv c gs Hcon HBs ns_u vs_u ihs_u Hns Har Hia Hir gs1 Pr gs2 Heq a Ea')
        as (v & bs & t & j & Hv & Ebs & Et & Hat).
      destruct (fresh_ihs_nth _ _ _ _ _ _ _ Fi gs1 Pr gs2 Heq) as (v' & bs' & t' & Hv' & Hbss & Et' & Hih).
      rewrite Hv in Hv'; injection Hv' as <-.
      destruct (fresh_cargs_nth _ _ _ _ _ _ _ Fc gs1 (ca_rec Pr) gs2 Heq) as [_ Fr].
      destruct (Fr Pr eq_refl) as (bs'' & Ebs'' & _ & Hbss').
      rewrite Hbss in Hbss'; injection Hbss' as <-.
      rewrite <- env_args_app, <- List.app_assoc in Ebs''.
      pose proof (functional_eval_exps' _ _ _ _ Ebs Ebs'') as <-.
      assert (t' = t) as -> by (eapply functional_eval_exp; eassumption).
      exists t, j; split; [| exact Hat ].
      rewrite List.app_assoc, List.nth_error_app2 by (rewrite List.length_app; lia).
      rewrite List.length_app, Ln, Lv.
      replace (k - (ind_nn D + List.length gs)) with (cargs_nrec gs1) by lia.
      rewrite Hih; do 3 f_equal; lia.
  Qed.

  (** The substitution of a branch's context at the fresh variables a stuck
      eliminator's readback makes, at admissible uniform parameters. *)
  Lemma br_fresh_glu : forall c gs, ind_con D c = Some gs ->
      forall SbB, EG elim_bctx p D gs A Us ++ Γ ∈ glu_ctx_env ↘ SbB ->
      forall Δ σ'' ua ns_x vs_x bss_x ihs_x, Δ ⊢s σ'' ® ρ ∈ SbΓ ->
        ind_adm D ups (ind_nr D ups) (ind_ar D ups) ua -> List.length ua = ind_nu D ->
        fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
        fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns_x)) gs (List.length Δ + ind_nn D) vs_x bss_x ->
        fresh_ihs gc_deps gc_stack ρ A gs vs_x bss_x (List.length Δ + ind_nn D + List.length gs) ihs_x ->
        tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ ⊢s sb_qn (List.length (elim_bctx p D gs A Us)) σ''
          ® env_args ρ (ns_x ++ vs_x ++ ihs_x) ∈ SbB.
  Proof.
    intros c gs Hcon SbB HSbB Δ σ'' ua ns_x vs_x bss_x ihs_x Hσ'' Hadm Lua Fx Cx Ix.
    pose proof (bctx_sem c gs Hcon) as HBs.
    set (s := List.length Δ) in *.
    destruct (IndElim.fresh_np2 p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ups ua s Had Hadm) as (ns_u & ns_x' & Fu & Fx' & Hux).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ Fx' Fx) as ->; clear Fx'.
    pose proof (ttrans _ _ _ Hux (tsym _ _ Hux)) as Huu.
    destruct (IndElim.fresh_args p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ups ua ns_u ns_x c gs Had Hadm ups_len Lua Hux Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1 & vs2 & bss1 & bss2 & ihs1 & ihs2 & C1 & C2 & _ & _ & I1 & I2 & P & Hia & Hir).
    rewrite !List.app_nil_r in C1, C2, Hia, Hir; cbn in P.
    destruct (functional_fresh_cargs _ _ _ _ _ _ _ C2 _ _ Cx) as [-> ->].
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I2 _ Ix) as ->.
    destruct (IndElim.fresh_args p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ups ups ns_u ns_u c gs Had Had ups_len ups_len Huu Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1' & vs1'' & bss1' & bss1'' & ihs1' & ihs1'' & C1' & C1'' & _ & _ & I1' & I1'' & P' & Hia' & Hir').
    rewrite !List.app_nil_r in C1', C1'', Hia', Hir'; cbn in P'.
    destruct (functional_fresh_cargs _ _ _ _ _ _ _ C1' _ _ C1) as [-> ->].
    destruct (functional_fresh_cargs _ _ _ _ _ _ _ C1'' _ _ C1) as [-> ->].
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1' _ I1) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1'' _ I1) as ->.
    pose proof (tele_full_of_pre _ _ _ _ P) as Har.
    pose proof (tele_full_of_pre _ _ _ _ P') as Har'.
    pose proof (fresh_tele_length _ _ _ _ Fu) as Lu; rewrite List.length_rev, length_nparams in Lu.
    pose proof (fresh_tele_length _ _ _ _ Fx) as Lx; rewrite List.length_rev, length_nparams in Lx.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv1 Lv2].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li1 Li2].
    assert (Lb : List.length (elim_bctx p D gs A Us) = ind_nn D + List.length gs + cargs_nrec gs) by (rewrite length_elim_bctx; lia).
    (** Glued at the variables at [ups]. *)
    assert (Hws : tele_sub (elim_bctx p D gs A Us) σ'' ++ Δ ⊢s sb_qn (List.length (elim_bctx p D gs A Us)) σ''
                    ® env_args ρ (ns_u ++ vs1 ++ ihs1) ∈ SbB).
    { apply (glu_sub_fresh _ Γ SbΓ (elim_bctx_ass p D gs A Us Hc) HSbΓ SbB HSbB Δ σ'' ρ _ Hσ'');
        [ rewrite Lb, !List.length_app; lia |].
      intros k X a HX Ea.
      exact (bctx_entry_link c gs Hcon s ns_u vs1 bss1 ihs1 Fu C1 I1 Huu Har' Hia' Hir' k X a HX Ea). }
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
  Lemma motive_rb : forall Δ σ'' ua ns_x af A'', Δ ⊢s σ'' ® ρ ∈ SbΓ ->
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) ua -> List.length ua = ind_nu D ->
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
      ⟦ A ⟧ env_args ρ (ns_x ++ ⇑! (d_ind p (ua ++ ns_x)) (List.length Δ + ind_nn D) :: nil) ↘ af ->
      Rtyp af in gc_deps ⍮ gc_stack ⍮ S (List.length Δ + ind_nn D) ↘ A'' ->
      elim_mctx p D (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ A[sb_qn nm σ''] ≈ A'' : Typeω@iA.
  Proof.
    intros * Hσ'' Hadm Lua Fx Eaf HRA.
    pose proof HAg as [SbM [HSbM _]].
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
  Lemma br_rb : forall Δ σ'' ua c gs n B ns_x vs_x bss_x ihs_x b t Bn, Δ ⊢s σ'' ® ρ ∈ SbΓ ->
      ind_adm D ups (ind_nr D ups) (ind_ar D ups) ua -> List.length ua = ind_nu D ->
      ind_con D c = Some gs -> In (c, n, B) Bs ->
      fresh_tele gc_deps gc_stack (env_args nil ua) (List.rev (ind_nparams D)) (List.length Δ) ns_x ->
      fresh_cargs gc_deps gc_stack p ua (env_args nil (ua ++ ns_x)) gs (List.length Δ + ind_nn D) vs_x bss_x ->
      fresh_ihs gc_deps gc_stack ρ A gs vs_x bss_x (List.length Δ + ind_nn D + List.length gs) ihs_x ->
      ⟦ B ⟧ env_args ρ (ns_x ++ vs_x ++ ihs_x) ↘ b ->
      ⟦ A ⟧ env_args ρ (ns_x ++ d_con p c (ua ++ ns_x ++ vs_x) :: nil) ↘ t ->
      Rnf ⇓ t b in gc_deps ⍮ gc_stack ⍮ (List.length Δ + n) ↘ Bn ->
      elim_bctx p D gs A[sb_qn nm σ''] (List.map (fun U => U[σ'']) Us) ++ Δ ⊢ B[sb_qn n σ''] ≈ Bn
        : elim_bty p D c gs A[sb_qn nm σ''] (List.map (fun U => U[σ'']) Us).
  Proof.
    intros * Hσ'' Hadm Lua Hcon Hin Fx Cx Ix Eb Et HRn.
    pose proof (HBa c gs n B Hcon Hin) as Hn.
    pose proof (HBg c gs n B Hcon Hin) as HBgl; destruct HBgl as [SbB [HSbB _]].
    pose proof (br_fresh_glu c gs Hcon SbB HSbB Δ σ'' ua ns_x vs_x bss_x ihs_x Hσ'' Hadm Lua Fx Cx Ix) as Hτ.
    destruct (glu_rel_exp_clean_inversion1 HSbB (HBg c gs n B Hcon Hin)) as [iB HiB].
    destruct (HiB _ _ _ Hτ) as [eb rb Pb Elb Eeb Erb Hgb HBglue]; clear HiB.
    assert (rb = b) as -> by (eapply functional_eval_exp; eassumption).
    set (s := List.length Δ) in *.
    pose proof (bctx_sem c gs Hcon) as HBs.
    (** The relations of the variables at [ua] to themselves. *)
    destruct (IndElim.fresh_np2 p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ua ua s Hadm Hadm) as (ns1 & ns2 & F1 & F2 & Hxx).
    pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F1 Fx) as ->; pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F2 Fx) as ->.
    clear F1 F2.
    destruct (IndElim.fresh_args p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ua ua ns_x ns_x c gs Hadm Hadm Lua Lua Hxx Hcon
                gs nil nil nil (s + ind_nn D) (s + ind_nn D + List.length gs) eq_refl (tele_pre_nil _))
      as (vs1 & vs2 & bss1 & bss2 & ihs1 & ihs2 & C1 & C2 & _ & _ & I1 & I2 & P & Hia & Hir).
    rewrite !List.app_nil_r in C1, C2, Hia, Hir; cbn in P.
    destruct (functional_fresh_cargs _ _ _ _ _ _ _ C1 _ _ Cx) as [-> ->].
    destruct (functional_fresh_cargs _ _ _ _ _ _ _ C2 _ _ Cx) as [-> ->].
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I1 _ Ix) as ->.
    pose proof (functional_fresh_ihs _ _ _ _ _ _ _ I2 _ Ix) as ->.
    pose proof (tele_full_of_pre _ _ _ _ P) as Har.
    pose proof (fresh_tele_length _ _ _ _ Fx) as LX; rewrite List.length_rev, length_nparams in LX.
    destruct (ElimCases.ind_args_rel_len _ _ _ _ _ _ _ _ _ Hia) as [Lv _].
    destruct (ElimCases.ihs_rel_len _ _ _ _ _ _ _ Hir) as [Li _].
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
    assert (Hm1 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns_x (d_con p c ((w ++ ns_x) ++ vs_x)) (d_con p c ((ua ++ ns_x) ++ vs_x))).
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
  Lemma motive_glu : forall Δ' σ' Q M' m' ns, Δ' ⊢s σ' ® ρ ∈ SbΓ ->
      List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us -> List.length Q = ind_np D -> Δ' ⊢ M' : apps (a_ind p) Q ->
      (forall Δ'' φ Q', Δ'' ⊢k φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl Δ'' Q' M'[φ]ʷ m') ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns m' m' ->
      glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns ->
      exists a, ⟦ A ⟧ env_args ρ (ns ++ m' :: nil) ↘ a /\ Dom a ≈ a ∈ per_univ iA /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® P.
  Proof.
    intros * Hσ' HQU HQl HMt HK Hns Hrel Hgn.
    pose proof HAg as [SbM [HSbM _]].
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
    destruct (ind_elem_glue u R ups ns bu NP NEl AP AEl Δ' Q M' m' ups_len Hbu Hule HNP HAP HR HΔ' Hga HMt
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
  Definition elim_prop (Δ' : ctx) (Q : list exp) (M' : exp) (m' : domain) : Prop :=
    forall σ', Δ' ⊢s σ' ® ρ ∈ SbΓ -> List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us ->
      List.length Q = ind_np D -> Δ' ⊢ M' : apps (a_ind p) Q ->
      (forall Δ'' φ Q', Δ'' ⊢k φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl Δ'' Q' M'[φ]ʷ m') ->
      forall ns, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns m' m' ->
        glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns ->
        exists r a, ⟦elim m' under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r /\ ⟦ A ⟧ env_args ρ (ns ++ m' :: nil) ↘ a /\
          forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
            Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M'
               : A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® r ∈ El.

  (** *** A Constructor *)
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
      (Hrec : forall gs1 Pr gs2 N A v bsr Q', gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q' ->
          List.length Q' = ind_np D /\ tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr /\
          (forall bsr', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr' ->
             glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q') (List.skipn (ind_nu D) Q') bsr' /\
             forall Δ φ, Δ ⊢k φ : Δ' -> glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Q') (ups ++ bsr')))
      (Hrec' : forall gs1 Pr gs2 N A v bsr Q', gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q' ->
          forall Δ φ Q'', Δ ⊢k φ : Δ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q') Q'' ->
            glu_ind p D ups NEl AEl Δ Q'' N[φ]ʷ v)
      (IH : forall gs1 Pr gs2 N A v bsr Q', gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q' ->
          forall Δ φ Q'', Δ ⊢k φ : Δ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q') Q'' ->
            elim_prop Δ Q'' N[φ]ʷ v).
    Variable (σ' : sub).
    Hypothesis (Hσ' : Δ' ⊢s σ' ® ρ ∈ SbΓ) (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us)
      (HMt : Δ' ⊢ M' : apps (a_ind p) Q).
    Variable (ns : list domain).
    Hypothesis (Hns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns)
      (Hrel : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)))
      (HKm : forall Δ'' φ Q', Δ'' ⊢k φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl Δ'' Q' M'[φ]ʷ (d_con p c (bs ++ vs)))
      (Hgnm : glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns).
    Let X := List.skipn (ind_nu D) bs.

    Lemma con_rel : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns X /\
        ind_rel p D ups (ind_nr D ups) (ind_ar D ups) X (d_con p c (bs ++ vs)) (d_con p c (bs ++ vs)) /\
        ind_args_rel p D ups (ind_nr D ups) (ind_ar D ups) (env_args nil (ups ++ X)) gs vs vs.
    Proof.
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl Hrel) as (_ & HnX & _ & _).
      pose proof (imv _ _ _ _ Hrel HnX) as HrX.
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl HrX) as (_ & _ & _ & Hia).
      auto.
    Qed.

    Definition rec_ps (gs1 : list carg) (Pr : list exp) : list exp :=
      List.map (fun P => P[sb_of_list Id (Q ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))]) Pr.

    Lemma con_ih : forall gs1 Pr gs2, gs = gs1 ++ ca_rec Pr :: gs2 ->
        exists N v bsr, List.nth_error As (List.length gs1) = Some N /\ List.nth_error vs (List.length gs1) = Some v /\
          eval_exps gc_deps gc_stack Pr (env_args nil (ups ++ X ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr /\
          tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr /\
          ind_rel p D ups (ind_nr D ups) (ind_ar D ups) bsr v v /\
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1)
            = Some (apps (a_ind p) (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr)) /\
          forall Xq, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr Xq ->
            exists r a, ⟦elim v under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r /\ ⟦ A ⟧ env_args ρ (Xq ++ v :: nil) ↘ a /\
              forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
                Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') N
                   : A[sb_qn nm σ'][sb_of_list Id (rec_ps gs1 Pr ++ N :: nil)] ® r ∈ El.
    Proof.
    Proof.
      intros gs1 Pr gs2 Heq.
      destruct con_rel as (HnsX & HrelX & HiaX).
      clearbody HD Ua Usem HM HAv Hcan HnP HnI HaP HaI Had Hass Hle imv tsym ttrans mmid Hbrm pelim.
      clear pelim Hbrm mmid HBg HBt HBx HBa HBn HAg HMx HAt HUg HeN HNP HeA HAP HR0 HNt HUs HRU HRΓ HΓ Hbu Hule
        HM HAv Hcan HnP HnI HaP HaI Had Rel Ua Usem HD Hrel Harg Hnp HMeq HMt.
      destruct (ElimCases.ind_args_rel_at D p ups _ gs vs vs HiaX gs1 Pr gs2 Heq) as (v & v' & bsr & Hv1 & Hv1' & Ebsr & Hbr).
      rewrite Hv1' in Hv1; injection Hv1 as <-.
      rewrite <- env_args_app, <- List.app_assoc in Ebsr.
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As _ Hlt) as [N HN].
      destruct (nth_error_lt_some (tele_insts (cargs_ctx p D gs) (sb_of_list Id Q) As) (List.length gs1)) as [T HT].
      { rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. }
      pose proof (cargs_rec_type_eq p D gs gs1 Pr gs2 Q As T Heq Hle HQl HT) as HTeq.
      change (List.map _ Pr) with (rec_ps gs1 Pr) in HTeq.
      destruct (Hrec gs1 Pr gs2 N T v' bsr _ Heq HN HT Hv1' Ebsr HTeq) as (HQrl & Hbsr & Hgn').
      exists N, v', bsr; split; [ exact HN | split; [ exact Hv1' | split; [ exact Ebsr | split; [ exact Hbsr
        | split; [ exact Hbr | split; [ rewrite HT, HTeq; reflexivity |] ] ] ] ] ].
      intros Xq HXq.
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (Hid : Δ' ⊢k wk_id : Δ') by mauto 3.
      pose proof (proj2 (Hgn' bsr Hbsr) Δ' wk_id Hid) as Htop.
      pose proof (IH gs1 Pr gs2 N T v' bsr _ Heq HN HT Hv1' Ebsr HTeq Δ' wk_id _ Hid (glu_params_top_refl _ _ _ _ Htop)) as HE.
      rewrite map_wk_id, exp_wk_id in HE.
      assert (HfQ : List.firstn (ind_nu D) (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr) = List.map (fun U => U[σ']) Us)
        by (rewrite firstn_app_len by (rewrite List.length_firstn; lia); exact HQU).
      assert (HNt' : Δ' ⊢ N : apps (a_ind p) (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr)) by (rewrite <- HTeq; eapply HAs; eassumption).
      destruct (HE σ' Hσ' HfQ HQrl HNt') with (ns := Xq) as (r & a & Er & Ea & Hg).
      - intros Δ'' φ Q'' Hφ HQ''; exact (Hrec' gs1 Pr gs2 N T v' bsr _ Heq HN HT Hv1' Ebsr HTeq Δ'' φ Q'' Hφ HQ'').
      - exact (ttrans _ _ _ (tsym _ _ HXq) HXq).
      - exact (imv _ _ _ _ Hbr HXq).
      - exact (proj1 (Hgn' Xq HXq)).
      - exists r, a; split; [ exact Er | split; [ exact Ea |] ].
        intros P El Hga; specialize (Hg P El Hga).
        rewrite skipn_app_len in Hg by (rewrite List.length_firstn; lia); exact Hg.
    Qed.
    Lemma con_rec_glue : forall gs1 Pr gs2 N v bsr, gs = gs1 ++ ca_rec Pr :: gs2 ->
        List.nth_error As (List.length gs1) = Some N -> List.nth_error vs (List.length gs1) = Some v ->
        eval_exps gc_deps gc_stack Pr (env_args nil (ups ++ X ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
        exists P El, DG d_ind p (ups ++ bsr) ∈ glu_univ_elem (ul u) ↘ P ↘ El /\
          Δ' ⊢ apps (a_ind p) (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr) ® P /\
          Δ' ⊢ N : apps (a_ind p) (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr) ® v ∈ El.
    Proof.
      intros gs1 Pr gs2 N v bsr Heq HN Hv1 Ebsr.
      destruct (con_ih gs1 Pr gs2 Heq) as (N' & v' & bsr' & HN' & Hv' & Ebsr' & Hbsr & Hbr & HT & _).
      rewrite HN in HN'; injection HN' as <-; rewrite Hv1 in Hv'; injection Hv' as <-.
      pose proof (functional_eval_exps' _ _ _ _ Ebsr' Ebsr) as <-; clear Ebsr'.
      pose proof (us_glu_args Δ' σ' Hσ') as HUga.
      clearbody HD Ua Usem HM HAv Hcan HnP HnI HaP HaI Had Hass Hle imv tsym ttrans mmid Hbrm pelim.
      clear pelim Hbrm mmid HBg HBt HBx HBa HBn HAg HMx HAt HUg HeA HNt HUs HRU HRΓ HΓ HM HAv Hcan HnP HnI HaP HaI Had Rel
        Ua Usem HD Hrel Harg Hnp HMeq HMt IH.
      destruct (Hrec gs1 Pr gs2 N _ v bsr' _ Heq HN HT Hv1 Ebsr eq_refl) as (HQrl & _ & Hgn').
      destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ HR0 Hl ups_len ups_len bsr' bsr' Hbsr) as [R HR].
      assert (HΔ' : ⊢ Δ') by (pose proof (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'); gen_presups; assumption).
      assert (HfQ : List.length (List.firstn (ind_nu D) Q) = ind_nu D) by (rewrite List.length_firstn; lia).
      assert (Hga : glu_args Δ' (ind_params D) Id nil (List.firstn (ind_nu D) Q ++ rec_ps gs1 Pr) (ups ++ bsr')).
      { rewrite params_split; apply glu_args_app; [ exact (decl_uparams_ass D Hc) | rewrite HfQ, length_ind_uparams by exact Hle; reflexivity
                                                   | rewrite ups_len, length_ind_uparams by exact Hle; reflexivity |].
        split; [ rewrite HQU; exact HUga |].
        destruct (Hgn' bsr' Hbsr) as [Hgn _].
        rewrite firstn_app_len, skipn_app_len in Hgn by exact HfQ.
        exact (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hgn Hbsr). }
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR Hl ups_len ups_len) as (_ & _ & _ & _ & _ & _ & _ & HRi).
      eapply (ind_elem_glue u R ups bsr' bu NP NEl AP AEl Δ' _ N v ups_len Hbu Hule HNP HAP HR HΔ' Hga).
      - eapply HAs; eassumption.
      - apply HRi; exact Hbr.
      - intros Δ'' φ Q'' Hφ HQ''; exact (Hrec' gs1 Pr gs2 N _ v bsr' _ Heq HN HT Hv1 Ebsr eq_refl Δ'' φ Q'' Hφ HQ'').
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
      pose proof con_ih as Hih.
      pose proof con_rec_glue as Hrg.
      pose proof (fun gs1 Pr gs2 Heq ns1 fa a0 H1 H2 H3 H4 H5 H6 H7 => ElimCases.rec_entry_char D HD Hc Hsu p Hl Us HUl c gs Hcon gs1 Pr gs2 Heq ups ns1 fa a0 ups_len H1 H2 ups_gargs H3 H4 H5 H6 H7) as Hrec_char.
      clearbody HD Ua Usem HM HAv Hcan HnP HnI HaP HaI Had Hass Hle imv tsym ttrans mmid Hbrm pelim.
      clear pelim Hbrm mmid HBg HBt HBx HBa HBn HAg HMx HAt HUg HNt HUs HRΓ HΓ HM HAv Hcan HnP HnI HaP HaI Had Rel Usem HD Hrel HMeq HMt IH Hrec Hrec'.
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      rewrite <- HQU.
      apply glu_args_app; [ exact (decl_closed_nparams_ass D Hc) | rewrite length_nparams; exact LXs | rewrite length_nparams; exact LX |].
      split; [ exact (glu_args_of_nparams D ups u NP NEl HeN HNP Δ' _ _ _ Hnp Hb) |].
      rewrite <- sb_of_list_app, List.firstn_skipn, <- env_args_app.
      split; [ rewrite length_cargs_ctx; exact HAl | split; [ rewrite length_cargs_ctx; exact Hvl |] ].
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
      destruct (per_gargs_nth _ _ _ _ _ _ _ Hpgf HBf ltac:(rewrite List.length_app; lia)) as (i0 & Ra & a1 & a2 & Ea1 & _ & HRa).
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
        exists k', a1, P', El'; auto.
      - pose proof (cargs_rev_nth_rec p D gs gs1 Pr gs2 Heq) as HB'; rewrite HB in HB'; injection HB' as ->.
        destruct (Hih gs1 Pr gs2 Heq) as (N' & v'' & bsr & HN' & Hv'' & Ebsr & Hbsr & Hbr & HT' & _).
        rewrite HN in HN'; injection HN' as <-; rewrite Hv' in Hv''; injection Hv'' as <-.
        rewrite HT in HT'; injection HT' as ->.
        destruct (Hrg gs1 Pr gs2 N v bsr Heq HN Hv' Ebsr) as (P & El & Hg & HP & HM).
        pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk.
        pose proof Ea1 as Ea1c; rewrite <- !env_args_app in Ea1c.
        destruct (Hrec_char gs1 Pr gs2 Heq X (List.firstn (List.length gs1) vs) bu LX ltac:(rewrite List.length_firstn; lia) Hbu Hb Hpk
                    ltac:(intros R' HR'; apply (per_ctx_env_right_irrel _ _ _ _ _ HR HR'); exact HE) _ _ _ _ Ea1c HRa)
          as (bs0 & bs1 & Ebs0 & Ebs1 & Hbb & -> & _).
        pose proof (functional_eval_exps' _ _ _ _ Ebs0 Ebsr) as ->.
        pose proof (IndCases.ind_relate D HDc Hc Hsu p Hl ups ups bsr bs1 bu Hug ups_len Hbu Hbb) as Hrel1.
        destruct (IndSem.per_univ_elem_to_nat _ _ _ _ Hrel1) as [n Hn].
        assert (Hpu : Dom d_ind p (ups ++ bsr) ≈ d_ind p (ups ++ bs1) ∈ per_univ n) by (eexists; exact Hn).
        destruct (glu_transfer_per' u n _ _ P El Δ' _ N v Hg Hpu HP HM) as (k' & P' & El' & Hg' & HP' & HM').
        exists k', (d_ind p (ups ++ bs1)), P', El'; auto.
    Qed.
    (** The recursive results, glued at their types in the branch's
        context. *)
    Lemma con_ihs_args : forall ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs ->
        forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
        RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs)) ->
        glu_args Δ' (ihs_ctx_aux D A Us (List.length gs) nil 0 gs) (sb_of_list σ' (List.skipn (ind_nu D) Q ++ As))
          (env_args ρ (X ++ vs)) (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As) ihs.
    Proof.
      intros ihs Ei RB HRB HZ.
      pose proof con_ih as Hih.
      pose proof (bctx_sem c gs Hcon) as HBs.
      pose proof (fun gs1 gs2 Heq => ElimCases.ihs_pre_sem D p Γ Us A gs HBs gs1 gs2 Heq) as Hpre.
      pose proof (fun gs1 Pr gs2 E Heq HE => ElimCases.gsub_ih D HD Hc Hdt p Hl Γ HΓ Us HUl HUs ups ups_len HM c gs gs1 Pr gs2 E Hcon Heq HE) as Hgih.
      pose proof (ElimCases.ih_bridge D HD Hc Hsu Hdt p Hl Γ RΓ HRΓ HΓ RU HRU Us HUl HUs ups bu ups_gargs ups_len Hbu HNt HM A ρ HUv c gs Hcon HBs) as Hbrd.
      destruct con_rel as (HnsX & HrelX & HiaX).
      pose proof (fun k Hk => ElimCases.closed_args_gargs D HD Hc Hsu p Hl Us HUl ups bu ups_gargs ups_len Hbu c gs Hcon X X X vs vs Hb Hb Hv HiaX k Hk) as Hpg.
      pose proof HAv as HAv'.
      clearbody HD Ua Usem HM HAv Hcan HnP HnI HaP HaI Had Hass Hle imv tsym ttrans mmid Hbrm pelim.
      clear pelim Hbrm mmid HBg HBt HBx HBa HBn HAg HMx HAt HUg HNt HUs HM HAv Hcan HnP HnI HaP HaI Had Rel Usem HD Hrel HMeq HMt IH
        Hrec Hrec' Harg HeN HNP HeA HAP Hnp.
      assert (LX : List.length X = ind_nn D) by (destruct Hb as [L _]; rewrite List.length_rev, length_nparams in L; exact L).
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      destruct (eval_ihs_length _ _ _ _ _ _ _ Ei) as [_ Lih].
      split; [ rewrite length_elim_ihs, length_ihs_ctx_aux by exact HAl; reflexivity | split; [ rewrite length_ihs_ctx_aux; exact Lih |] ].
      intros k M T r B HM HT Hr HB.
      destruct (ihs_rev_nth D A Us (List.length gs) gs k _ HB) as (gs1 & Pr & gs2 & Heq & Hk & EB).
      injection EB as ->; subst k.
      destruct (Hih gs1 Pr gs2 Heq) as (N & v & bsr & HN & Hv1 & Ebsr & Hbsr & Hbr & HTN & Hres).
      rewrite (elim_ihs_nth _ _ _ _ gs1 Pr gs2 As N Heq HAl HN) in HM; injection HM as <-.
      destruct (eval_ihs_nth _ _ _ _ gs1 _ _ _ Ei Pr gs2 v Heq Hv1) as (r' & Hr' & Er').
      rewrite Hr in Hr'; injection Hr' as <-.
      set (k := cargs_nrec gs1) in *.
      assert (Lk : k <= List.length ihs) by (rewrite Lih; unfold k; rewrite Heq, ElimCases.cargs_nrec_app; lia).
      set (L := List.firstn k ihs).
      assert (Esp : ihs_ctx_aux D A Us (List.length gs) nil 0 gs
                   = ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) k (ca_rec Pr :: gs2) ++ ihs_ctx_aux D A Us (List.length gs) nil 0 gs1)
        by (rewrite Heq at 2; rewrite ElimCases.ihs_ctx_aux_app, List.app_nil_r; reflexivity).
      pose proof (Hpre gs1 (ca_rec Pr :: gs2) Heq) as HEs.
      destruct (sem_ctx_per_ctx_env HEs) as [RE HRE].
      assert (HEE : RE (env_args ρ (X ++ vs ++ L)) (env_args ρ (X ++ vs ++ L))).
      { rewrite ElimCases.bctx_split, Esp, <- List.app_assoc in HRB, HBs.
        rewrite <- (List.rev_involutive (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) k (ca_rec Pr :: gs2))) in HRB, HBs.
        assert (Lr : List.length (List.skipn k ihs) = List.length (List.rev (ihs_ctx_aux D A Us (List.length gs) (cargs_pat gs1) k (ca_rec Pr :: gs2))))
          by (rewrite List.length_rev, length_ihs_ctx_aux, List.length_skipn, Lih; unfold k; rewrite Heq, ElimCases.cargs_nrec_app; lia).
        assert (HZ' : RB (env_args (env_args ρ (X ++ vs ++ L)) (List.skipn k ihs)) (env_args (env_args ρ (X ++ vs ++ L)) (List.skipn k ihs)))
          by (rewrite <- env_args_app, <- !List.app_assoc; unfold L; rewrite List.firstn_skipn; exact HZ).
        destruct (IndSem.rel_gargs _ _ _ _ HRE HBs (List.Forall_rev (ihs_ctx_aux_ass _ _ _ _ _ _ _)) HRB _ _ _ _ Lr Lr HZ') as [H _].
        exact H. }
      clear HZ HRB HBs.
      assert (Lvs : List.length vs = List.length gs1 + S (List.length gs2)) by (rewrite Hvl, Heq, List.length_app; cbn; lia).
      set (fa := List.firstn (List.length gs1) vs).
      set (aft := List.skipn (S (List.length gs1)) vs).
      assert (Evs : vs = fa ++ v :: aft) by (unfold fa, aft; rewrite <- (skipn_nth_cons _ _ _ Hv1), List.firstn_skipn; reflexivity).
      pose proof (nonrec_prefix_pre _ _ _ _ _ _ Hv Hvl Heq) as Hpk.
      pose proof (Hpg (List.length gs1) ltac:(lia)) as Hpg1.
      replace (List.firstn (List.length gs1) gs) with gs1 in Hpg1 by (rewrite Heq; symmetry; apply firstn_app_len; reflexivity).
      assert (LL : List.length L = k) by (unfold L; rewrite List.length_firstn; lia).
      assert (HRS : RE (env_args ρ (X ++ fa ++ v :: aft ++ L)) (env_args ρ (X ++ fa ++ v :: aft ++ L))).
      { replace (X ++ fa ++ v :: aft ++ L) with (X ++ vs ++ L) by (rewrite Evs, <- !List.app_assoc; reflexivity); exact HEE. }
      destruct (Hbrd gs1 Pr gs2 Heq ρ Hρ X X fa fa v aft L bsr RE Hb ltac:(unfold fa; rewrite List.length_firstn; lia)
                  ltac:(unfold fa; rewrite List.length_firstn; lia) ltac:(unfold aft; rewrite List.length_skipn; lia) LL Hpk Hpg1 Ebsr HRE HRS)
        as (Xq & EXq & HXq).
      rewrite length_ihs_ctx_aux in EXq; fold k in EXq.
      destruct (Hres Xq HXq) as (r'' & a & Er'' & Ea & Hgl).
      pose proof (functional_eval_elim _ _ _ _ _ _ _ Er'' Er') as ->.
      pose proof (Hgih gs1 Pr gs2 _ Heq HEs) as Hgτ.
      rewrite length_ihs_ctx_aux in Hgτ; fold k in Hgτ.
      clear Hpg Hpre Hgih Hbrd Hih Hres.
      assert (LZ : List.length (X ++ fa ++ v :: aft ++ L) = k + List.length gs + ind_nn D)
        by (assert (List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia);
            assert (List.length aft = List.length gs2) by (unfold aft; rewrite List.length_skipn; lia);
            rewrite !List.length_app; cbn [List.length]; rewrite !List.length_app; rewrite Heq, List.length_app; cbn [List.length]; lia).
      assert (Lfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
      assert (Hevτ : ⟦ sb_of_list (ι (wk_shiftn (k + List.length gs + ind_nn D)))
                        (List.map (fun P => P[wk_pat (cargs_pat gs1)]ʷ[sb_qn (List.length (cargs_pat gs1) + ind_nn D) (sb_of_list Id Us)]
                                           [wk_shiftn (List.length gs - List.length (cargs_pat gs1) + k)]ʷ) Pr
                         ++ a_var (k + List.length gs - 1 - List.length (cargs_pat gs1)) :: nil) ⟧s
                      env_args ρ (X ++ fa ++ v :: aft ++ L) ↘ env_args ρ (Xq ++ v :: nil)).
      { apply IndSem.eval_sb_of_list.
        - rewrite <- LZ.
          pose proof (@eval_sub_of_wk gc_deps gc_stack (wk_shiftn (List.length (X ++ fa ++ v :: aft ++ L))) (env_args ρ (X ++ fa ++ v :: aft ++ L)) (IndSem.wk_mono_shiftn _)) as H.
          rewrite IndSem.eval_wk_shiftn_args in H; exact H.
        - apply Modules.eval_exps_app; [ exact EXq |].
          econstructor; [| constructor ].
          rewrite length_cargs_pat.
          assert (Hx : k + List.length gs - 1 - List.length gs1 < List.length (X ++ fa ++ v :: aft ++ L)) by (rewrite LZ, Heq, List.length_app; cbn; lia).
          pose proof (ElimCases.eval_var_args ρ (X ++ fa ++ v :: aft ++ L) _ Hx) as H.
          replace (List.length (X ++ fa ++ v :: aft ++ L) - 1 - (k + List.length gs - 1 - List.length gs1)) with (List.length X + List.length fa) in H
            by (rewrite LZ, LX, Lfa, Heq, List.length_app; cbn; lia).
          rewrite List.app_nth2 in H by lia; replace (List.length X + List.length fa - List.length X) with (List.length fa) in H by lia.
          rewrite List.app_nth2, Nat.sub_diag in H by lia; exact H. }
      replace (X ++ vs ++ L) with (X ++ fa ++ v :: aft ++ L) in HEE by (rewrite Evs, <- !List.app_assoc; reflexivity).
      destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv' HRE (InstanceCases.gsub_valid Hgτ) HEE Hevτ) as (ae & a' & Eae & Ea' & Hlk).
      assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).

      assert (Hrr : Dom a ≈ a ∈ per_univ iA) by (eapply per_univ_trans'; [ apply per_univ_sym'; exact Hlk | exact Hlk ]).
      destruct (per_univ_glu_univ_elem _ _ Hrr) as (P & El & Hga).
      pose proof (Hgl P El Hga) as HE.
      destruct (tele_insts_nth _ _ _ _ _ HT) as (B' & HB' & ET).
      rewrite HB in HB'; injection HB' as <-.
      rewrite <- sb_of_list_app, <- List.app_assoc in ET.
      pose proof Hc as (_ & _ & _ & _ & _ & HPs & HPl).
      pose proof (HPs _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HPsc.
      pose proof (HPl _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) Heq) as HPlen.
      clear HPs HPl.
      set (L' := List.firstn k (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As)) in *.
      assert (LL' : List.length L' = k) by (unfold L'; rewrite List.length_firstn, length_elim_ihs by exact HAl; unfold k; rewrite Heq, ElimCases.cargs_nrec_app; lia).
      assert (Hlt : List.length gs1 < List.length As) by (rewrite HAl, Heq, List.length_app; cbn; lia).
      pose proof (ih_entry_inst D A Us σ' gs1 Pr (List.skipn (ind_nu D) Q) As L' Hle HUl LXs Hlt HPlen HPsc) as EI.
      rewrite LL', HAl in EI.
      rewrite EI in ET; clear EI.
      rewrite (List.nth_error_nth _ _ _ HN) in ET.
      rewrite <- HQU, List.firstn_skipn in ET.
      change (List.map _ Pr) with (rec_ps gs1 Pr) in ET.
      rewrite <- Hnm in ET; subst T.
      destruct (glu_transfer_per' iA iA a ae P El Δ' _ _ r Hga (per_univ_sym' _ _ _ Hlk) (glu_univ_elem_trm_typ _ _ _ _ Hga _ _ _ _ HE) HE)
        as (k' & P' & El' & Hg' & HP' & HM').
      exists k', ae, P', El'; split; [| split; [ exact Hg' | split; [ exact HP' | exact HM' ] ] ].
      replace (env_args (env_args ρ (X ++ vs)) L) with (env_args ρ (X ++ fa ++ v :: aft ++ L))
        by (rewrite <- env_args_app, Evs, <- !List.app_assoc; reflexivity).
      exact Eae.
    Qed.
    (** The substitution of the branch's context at the constructor's
        non-uniform parameters, its arguments and the recursive results. *)
    Lemma con_bctx : exists ihs, ⟦ihs vs of gs under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ihs /\
        (forall RB, EF elim_bctx p D gs A Us ++ Γ ≈ elim_bctx p D gs A Us ++ Γ ∈ per_ctx_env ↘ RB ->
           RB (env_args ρ (X ++ vs ++ ihs)) (env_args ρ (X ++ vs ++ ihs))) /\
        forall SbB, EG elim_bctx p D gs A Us ++ Γ ∈ glu_ctx_env ↘ SbB ->
          Δ' ⊢s sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As)
            ® env_args ρ (X ++ vs ++ ihs) ∈ SbB.
    Proof.
      destruct con_rel as (HnsX & HrelX & HiaX).
      destruct (proj2 pelim _ _ _ _ HiaX) as (ihs & ihs' & Ei & Ei' & Hir).
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

    Lemma con_main : exists r a, ⟦elim d_con p c (bs ++ vs) under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r /\
        ⟦ A ⟧ env_args ρ (ns ++ d_con p c (bs ++ vs) :: nil) ↘ a /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M'
             : A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® r ∈ El.
    Proof.
      destruct con_bctx as (ihs & Ei & HZ & Hgs).
      destruct (ind_rel_con_inv _ _ _ _ _ _ _ _ Hcon Hbl Hrel) as (_ & HnX & Hvn & Hian).
      destruct (IndElim.brs_names_lookup _ _ _ _ HBn Hcon) as (n & B & HBl & HBin).
      pose proof (HBa c gs n B Hcon HBin) as Hn.
      pose proof (HBg c gs n B Hcon HBin) as HBgl.
      destruct HBgl as [SbB [HSbB _]].
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
      assert (Hm1 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns (d_con p c (bs ++ vs)) (d_con p c ((w ++ X) ++ vs))).
      { eapply ind_rel_con; [ exact Hns | exact Hcon | exact Hbl | rewrite List.length_app; pose proof Hle; unfold ind_nn in *; lia
                            | exact HnX | rewrite skipn_app_exact by exact Lw; exact HnX | exact Hvn | exact Hian ]. }
      destruct (mmid _ _ _ _ HnX Hm1) as (a & a' & Ea & Ea' & Haa).
      rewrite <- List.app_assoc in Ea'.
      assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
      assert (Hpe : Dom eb ≈ a ∈ per_univ iA).
      { eapply per_univ_trans'; [ exact Hebb | apply per_univ_sym'; eexists; exact Haa ]. }
      exists rb, a; split; [ exact Er | split; [ exact Ea |] ].
      intros P El HgP.
      pose proof con_Q_typed as HQt.
      assert (Hσt : Δ' ⊢s σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      assert (HΔ' : ⊢ Δ') by (gen_presups; assumption).
      destruct (motive_glu Δ' σ' Q M' _ ns Hσ' HQU HQl HMt HKm Hns Hrel Hgnm) as (a0 & Ea0 & _ & HTP).
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (HTP P El HgP) as HTg; clear HTP.
      clearbody HD Ua Usem HM HAv Hcan HnP HnI HaP HaI Had Hass Hle imv tsym ttrans mmid Hbrm pelim.
      destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ' σ' Hσt)
        as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
      rewrite <- HQU in HAt', HMx', HBx', HBt'.
      assert (LXs : List.length (List.skipn (ind_nu D) Q) = ind_nn D) by (rewrite List.length_skipn; unfold ind_nn; lia).
      assert (Lei : List.length (elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As) = cargs_nrec gs) by (apply length_elim_ihs; exact HAl).
      assert (LZ : List.length (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As) = n)
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
      assert (EB : B[sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As)]
                   = B[sb_qn n σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As)])
        by (rewrite <- LZ; symmetry; apply exp_sub_qn_of_list).
      assert (ET : (elim_bty p D c gs A Us)[sb_of_list σ' (List.skipn (ind_nu D) Q ++ As ++ elim_ihs nm A[sb_qn nm σ'] (brs_sub Bs σ') gs As)]
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
      (Hrb : forall Δ φ M0, Δ ⊢k φ : Δ' -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
         Δ ⊢ M'[φ]ʷ ≈ M0 : (apps (a_ind p) Q)[φ]ʷ).
    Variable (σ' : sub).
    Hypothesis (Hσ' : Δ' ⊢s σ' ® ρ ∈ SbΓ) (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ']) Us)
      (HQl : List.length Q = ind_np D) (HMt : Δ' ⊢ M' : apps (a_ind p) Q).
    Variable (ns : list domain).
    Hypothesis (Hns : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns)
      (Hrel : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns (⇑ (d_ind p as') m) (⇑ (d_ind p as') m))
      (HKm : forall Δ'' φ Q', Δ'' ⊢k φ : Δ' -> exps_eq_at Δ'' (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
         glu_ind p D ups NEl AEl Δ'' Q' M'[φ]ʷ (⇑ (d_ind p as') m))
      (Hgnm : glu_nparams D NEl Δ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) ns).

    Lemma neut_inv : List.length as' = ind_np D /\ ind_adm D ups (ind_nr D ups) (ind_ar D ups) (List.firstn (ind_nu D) as') /\
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

    Lemma neut_rb : forall Δ φ M0, Δ ⊢k φ : Δ' -> Rne d_elim ρ nm A Bs p as' m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M0 ->
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
      assert (Hσt : Δ ⊢s σ'' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ'').
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
          as (gs & ns1 & vs1 & bss1 & ihs1 & b1 & t1 & Bn & Hcs & HBk & F1 & C1 & I1 & Eb1 & Et1 & HRn).
        rewrite HBk in H2; injection H2 as <-.
        pose proof (IndElim.cons_lookup_nodup_in _ _ _ (IndCases.sd_nodup D HDc) (List.nth_error_In _ _ Hcs)) as Hc1.
        assert (gs = gs0) as <- by (unfold ind_con in Hc0; congruence).
        pose proof (IndElim.functional_fresh_tele _ _ _ _ _ F1 Fx) as ->.
        rewrite HQU'.
        exact (br_rb Δ σ'' ua c1 gs n1 B1 nsx vs1 bss1 ihs1 b1 t1 Bn Hσ'' Hadm Lua Hc0 (List.nth_error_In _ _ H1) Fx C1 I1 Eb1 Et1 HRn).
    Qed.

    Lemma neut_main : exists r a, ⟦elim ⇑ (d_ind p as') m under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ r /\
        ⟦ A ⟧ env_args ρ (ns ++ ⇑ (d_ind p as') m :: nil) ↘ a /\
        forall P El, DG a ∈ glu_univ_elem iA ↘ P ↘ El ->
          Δ' ⊢ a_elim nm A[sb_qn nm σ'] (brs_sub Bs σ') M'
             : A[sb_qn nm σ'][sb_of_list Id (List.skipn (ind_nu D) Q ++ M' :: nil)] ® r ∈ El.
    Proof.
      destruct neut_inv as (Lan & Hadm & Hsn).
      destruct (mmid _ _ _ _ Hsn Hrel) as (a & a1 & Ea & Ea1 & Haa).
      assert (Er : ⟦elim ⇑ (d_ind p as') m under nm A Bs ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ ⇑ a1 (d_elim ρ nm A Bs p as' m))
        by (eapply eval_elim_neut; eassumption).
      exists (⇑ a1 (d_elim ρ nm A Bs p as' m)), a; split; [ exact Er | split; [ exact Ea |] ].
      intros P El HgP.
      destruct (motive_glu Δ' σ' Q M' _ ns Hσ' HQU HQl HMt HKm Hns Hrel Hgnm) as (a0 & Ea0 & _ & HTP).
      assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
      pose proof (HTP P El HgP) as HTg.
      pose proof (glu_univ_elem_resp_per_univ _ a a1 _ _ (ltac:(eexists; exact Haa) : Dom a ≈ a1 ∈ per_univ iA) HgP) as HgP1.
      eapply realize_glu_elem_bot; [ exact HgP1 |].
      assert (Hσt : Δ' ⊢s σ' : Γ) by exact (glu_ctx_env_sub_escape HSbΓ _ _ _ Hσ').
      destruct (elim_prems_at p D Hc Γ Us nm A iA Bs HUl Hnm HAt HMx HBn HBx HBa HBt Δ' σ' Hσt)
        as (HAt' & HMx' & HBn' & HBx' & HBa' & HBt').
      rewrite <- HQU in HAt', HMx', HBx', HBt'.
      econstructor; [ | exact HgP1 | exact HTg | |].
      - eapply wf_elim; [ exact Hl | exact HQl | exact neut_Q_typed | exact HMt | exact Hnm | exact HAt' | exact HMx'
                        | exact HBn' | exact HBx' | exact HBa' | exact HBt' ].
      - exact (IndElim.per_bot_elim p D ups _ _ Hl Hass HnP HnI HaP HaI Had Hle iA nm ρ ρ A A Bs Bs Rel Hnm
                 (IndCases.sd_nodup D HDc) HBn HBn HBa HBa mmid Hbrm ns as' as' m m Lan Lan Hadm Hadm Hsn Hsn Hm).
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
       (forall gs1 Pr gs2 N A v bsr Q, gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q ->
          List.length Q = ind_np D /\ tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr /\
          (forall bsr', tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bsr bsr' ->
             glu_nparams D NEl Γ' (List.firstn (ind_nu D) Q) (List.skipn (ind_nu D) Q) bsr' /\
             forall Δ φ, Δ ⊢k φ : Γ' -> glu_params_top D Δ (List.map (fun P => P[φ]ʷ) Q) (ups ++ bsr'))) ->
       (forall gs1 Pr gs2 N A v bsr Q, gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q ->
          forall Δ φ Q', Δ ⊢k φ : Γ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
            glu_ind p D ups NEl AEl Δ Q' N[φ]ʷ v) ->
       (forall gs1 Pr gs2 N A v bsr Q, gs = gs1 ++ ca_rec Pr :: gs2 ->
          List.nth_error As (List.length gs1) = Some N ->
          List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some A ->
          List.nth_error vs (List.length gs1) = Some v ->
          eval_exps gc_deps gc_stack Pr
            (env_args nil (ups ++ List.skipn (ind_nu D) bs ++ nonrec_vals gs1 (List.firstn (List.length gs1) vs))) bsr ->
          A = apps (a_ind p) Q ->
          forall Δ φ Q', Δ ⊢k φ : Γ' -> exps_eq_at Δ (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
            elim_prop Δ Q' N[φ]ʷ v) ->
       elim_prop Γ' Ps M (d_con p c (bs ++ vs)).
  Proof.
    intros * Hcon HPl Hbl Hvl HAl HMeq Hb Hv Hnp HAs Harg Hrec Hrec' IH.
    unfold elim_prop; intros σ' Hσ' HQU HQl HMt HK ns Hns Hrel Hgn.
    eapply con_main; eassumption.
  Qed.

  Lemma elim_neut_case : forall m Γ' Ps M as',
      per_bot m m ->
      (forall Δ φ M', Δ ⊢k φ : Γ' -> Rne m in gc_deps ⍮ gc_stack ⍮ length Δ ↘ M' ->
         Δ ⊢ M[φ]ʷ ≈ M' : (apps (a_ind p) Ps)[φ]ʷ) ->
      elim_prop Γ' Ps M (⇑ (d_ind p as') m).
  Proof.
    intros * Hm Hrb; unfold elim_prop; intros σ' Hσ' HQU HQl HMt HK ns Hns Hrel Hgn.
    eapply neut_main; eassumption.
  Qed.

  Theorem elim_glu : forall Δ' Q M' m', glu_ind p D ups NEl AEl Δ' Q M' m' -> elim_prop Δ' Q M' m'.
  Proof.
    induction 1.
    - eapply elim_con_case; eassumption.
    - eapply elim_neut_case; eassumption.
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
  pose proof Hdt as (_ & _ & _ & _ & Hsu & _).
  pose proof (decl_closed_nu D Hc) as Hle.
  pose proof (decl_closed_params D Hc) as Hass.
  pose proof Hc as (_ & _ & Hs0 & _).
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
  pose proof HMg as [SbΓ [HSbΓ _]].
  exists SbΓ; split; [ exact HSbΓ |]; exists i; intros Δ σ ρ Hσ.
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
    as (NP & NEl & AP & AEl & P2 & El2 & R' & Hg2 & HP2 & HEl2 & HRR & HeN & HNP & HeA & HAP).
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hg1 Hg2) as [_ EE].
  apply EE, HEl2 in HMσ1; destruct HMσ1 as (HMt' & Hmm & Ps0 & HT0 & HK0).
  clear EE HgM HMσ HP2 HEl2 Hg2 P1 El1 Hg1 PM ElM.
  destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (_ & _ & Hcp & _ & _ & Hadm & Hns0 & HRi).
  assert (Hrel0 : ind_rel p D ups (ind_nr D ups) (ind_ar D ups) ns0 m m) by (apply HRi, HRR; exact Hmm).
  clear HMg Hmm HRR R'.
  (** The scrutinee at the instance of the parameters. *)
  set (Q := List.map (fun P => P[σ]) Ps) in *.
  assert (HQl : List.length Q = ind_np D) by (unfold Q; rewrite List.length_map; exact HPl).
  assert (HQeq : forall Δ0 φ, Δ0 ⊢k φ : Δ -> exps_eq_at Δ0 (ind_params D) (List.map (fun P => P[φ]ʷ) Ps0) (List.map (fun P => P[φ]ʷ) Q)).
  { intros Δ0 φ Hφ.
    destruct HT0 as (_ & HT0); destruct (HT0 _ _ Hφ) as (Hpt0 & _ & _).
    eapply glu_params_top_eq; [ exact Hl | eapply kripke_dom; exact Hφ | exact (ind_rps_of_per _ _ _ _ _ _ HR0 Hl _) | exact Hpt0 |].
    rewrite <- Evs; apply glu_args_params_top; [ exact Hass | exact Hs0 |].
    exact (glu_args_wk _ _ _ _ _ _ _ Hass Hs0 Hφ HPga). }
  assert (HKQ : forall Δ0 φ Q', Δ0 ⊢k φ : Δ -> exps_eq_at Δ0 (ind_params D) (List.map (fun P => P[φ]ʷ) Q) Q' ->
                  glu_ind p D ups NEl AEl Δ0 Q' M[σ][φ]ʷ m).
  { intros Δ0 φ Q' Hφ HQ'; apply (HK0 _ _ _ Hφ).
    eapply exps_eq_at_params_trans; [ exact Hl | eapply kripke_dom; exact Hφ | | exact (HQeq _ _ Hφ) | exact HQ' ].
    destruct (HQeq _ _ Hφ) as [L _]; rewrite !List.length_map in *; congruence. }
  clear HK0 HQeq HT0 Ps0.
  assert (HQU : List.firstn (ind_nu D) Q = List.map (fun U => U[σ]) Us) by (unfold Q, Us; apply List.firstn_map).
  assert (HQN : List.skipn (ind_nu D) Q = List.map (fun U => U[σ]) Ns) by (unfold Q, Ns; apply List.skipn_map).
  pose proof (comps_of_uparams p D HG Hc Hdt Hsu ups bu (ul u) NP NEl AP AEl Hu Hbu Hule HeN HNP HeA HAP Δ _ HΔ HUga) as Hcomps.
  pose proof (nparams_of_glu_args p D Hc ups (ul u) NP NEl AP AEl Hu HNP Δ _ _ _ Hcomps HNga Hns0) as Hgn.
  rewrite <- HQU, <- HQN in Hgn.
  assert (HMQ : Δ ⊢ M[σ] : apps (a_ind p) Q) by (unfold Q; rewrite <- sub_apps_ind; exact HMt').
  assert (HM0 : glu_ind p D ups NEl AEl Δ Q M[σ] m).
  { pose proof (HKQ Δ wk_id Q ltac:(mauto 3)) as H; rewrite map_wk_id, exp_wk_id in H; apply H.
    eapply glu_params_top_refl; apply glu_args_params_top; [ exact Hass | exact Hs0 | exact HPga ]. }
  destruct (elim_glu p D Hl HG Hc Hdt Hsu HDc Γ RΓ HRΓ HΓs RU HRU Us HUl HUs ρ ups Hρ HUv bu Hbu HNt SbΓ HSbΓ nm A i Bs
              Hnm HAt HMx Hn HBx Hk HBt HAg HBg HUg u NP NEl AP AEl Hule HeN HNP HeA HAP R0 ns0 HR0 Δ Q M[σ] m HM0
              σ Hσ HQU HQl HMQ HKQ ns0 Hns0 Hrel0 Hgn) as (r & a & Er & Ea & Hglr).
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
