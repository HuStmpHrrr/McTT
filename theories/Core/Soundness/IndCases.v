(** * Inductive Types in the Gluing Model

    The soundness counterpart of [Core/Completeness/IndCases.v]: the type
    former and the constructors are glued at their [Π]-types, and the
    eliminator at its motive.  Lists of terms glued positionwise along a
    telescope ([glu_args]) make glued substitutions ([glu_sub_of_list]); a
    constant whose applications to glued arguments are glued is glued at a
    [Π] over the telescope ([ctx_pi_glu_elem]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Completeness Require IndCases IndSem UnitCases ElimCases TeleSem SubstitutionCases GlobalArgs.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Semantic Require Import Realizability IndCanon.
From Mctt.Core.Syntactic Require Import Substitution IndCong.
From Mctt.Core.Syntactic.System Require Import MemberLemmas GlobalPresup IndTyping.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Glued Arguments

    A list of terms glued positionwise to a list of values along a
    telescope [C] (innermost first), each at the instance of its type at the
    terms before it, over a base [τ] and [ρ]. *)
(** One argument: the type [A], evaluated in [ρ], is glued at a universe,
    and the term [M] at its instance [T] to the value [v]. *)
#[warnings="-cannot-define-projection"]
Record glu_arg (Δ : ctx) (ρ : env) (A T M : exp) (v : domain) : Prop := mk_glu_arg
  { ga_lvl : uidx
  ; ga_val : domain
  ; ga_typ : glu_typ_pred
  ; ga_exp : glu_exp_pred
  ; ga_eval : ⟦ A ⟧ ρ ↘ ga_val
  ; ga_elem : DG ga_val ∈ glu_univ_elem ga_lvl ↘ ga_typ ↘ ga_exp
  ; ga_glu_typ : Δ ⊢ T ® ga_typ
  ; ga_glu : Δ ⊢ M : T ® v ∈ ga_exp }.

Record glu_args (Δ : ctx) (C : ctx) (τ : sub) (ρ : env) (Ms : list exp) (vs : list domain) : Prop := mk_glu_args
  { gas_len : List.length Ms = List.length C
  ; gas_vals_len : List.length vs = List.length C
  ; gas_glu : forall k M T v A, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T ->
      List.nth_error vs k = Some v -> List.nth_error (List.rev C) k = Some (ce_ass A) ->
      glu_arg Δ (env_args ρ (List.firstn k vs)) A T M v }.

Lemma glu_args_nil : forall Δ τ ρ, glu_args Δ nil τ ρ nil nil.
Proof. intros; constructor; [ reflexivity | reflexivity |]; intros [] *; discriminate. Qed.

Lemma glu_args_snoc : forall Δ C A τ ρ M Ms v vs,
    glu_args Δ (C ++ ⋅ ▹ A) τ ρ (M :: Ms) (v :: vs) <->
    glu_arg Δ ρ A A[τ] M v /\ glu_args Δ C (τ,,M) (ρ ↦ v) Ms vs.
Proof.
  intros; split.
  - intros [L1 L2 H]; rewrite tele_insts_snoc, List.rev_app_distr, !List.length_app in *;
      cbn [List.rev List.app List.length] in *.
    split; [ exact (H 0 _ _ _ _ eq_refl eq_refl eq_refl eq_refl) |].
    constructor; [ lia | lia |].
    intros k M' T v' A' HM HT Hv HA; exact (H (S k) _ _ _ _ HM HT Hv HA).
  - intros [H0 [L1 L2 H]]; constructor;
      rewrite ?tele_insts_snoc, ?List.rev_app_distr, ?List.length_app; cbn [List.rev List.app List.length];
      [ lia | lia |].
    intros [| k] M' T v' A' HM HT Hv HA; cbn in HM, HT, Hv, HA.
    + injection HM as <-; injection HT as <-; injection Hv as <-; injection HA as <-; exact H0.
    + exact (H k _ _ _ _ HM HT Hv HA).
Qed.

Lemma glu_args_typed : forall Δ C τ ρ Ms vs, tele_ass C -> glu_args Δ C τ ρ Ms vs ->
    forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts C τ Ms) k = Some T -> Δ ⊢ M : T.
Proof.
  intros * Hass [L1 L2 H] k M T HM HT.
  assert (Hk : k < List.length C) by (rewrite <- L1; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
  assert (HA : exists A, List.nth_error (List.rev C) k = Some (ce_ass A)).
  { destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; lia)) as [e He].
    pose proof (List.nth_error_In _ _ He) as Hin; apply List.in_rev in Hin.
    unfold tele_ass in Hass; rewrite List.Forall_forall in Hass; destruct (Hass _ Hin) as [A ->]; eauto. }
  destruct HA as [A HA].
  destruct (H _ _ _ _ _ HM HT Hv HA) as [i a P El _ Hglu _ HMg].
  eapply glu_univ_elem_trm_escape; eassumption.
Qed.

Lemma glu_args_sb_eq : forall Δ C τ τ' ρ Ms vs, sb_eq τ τ' -> glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof. intros * Hτ [L1 L2 H]; constructor; [ exact L1 | exact L2 |]; rewrite <- (tele_insts_sb_eq _ _ _ _ Hτ); exact H. Qed.

Lemma glu_args_length : forall Δ C τ ρ Ms vs, glu_args Δ C τ ρ Ms vs ->
    List.length Ms = List.length C /\ List.length vs = List.length C.
Proof. intros * [L1 L2 _]; split; assumption. Qed.

(** ** Glued Substitutions from Glued Arguments *)

Lemma glu_ctx_env_suffix : forall C Γ Sb, tele_ass C -> EG C ++ Γ ∈ glu_ctx_env ↘ Sb ->
    exists Sb', EG Γ ∈ glu_ctx_env ↘ Sb'.
Proof.
  induction C as [| e C IH]; intros * Hass H; [ eauto |].
  apply List.Forall_cons_iff in Hass as [[A ->] Hass].
  cbn [List.app] in H; inversion H; subst; eauto.
Qed.

Lemma glu_sub_of_list : forall C Γ0 Sb Sb0 Δ σ0 ρ0 Ms vs,
    tele_ass C -> EG C ++ Γ0 ∈ glu_ctx_env ↘ Sb -> EG Γ0 ∈ glu_ctx_env ↘ Sb0 ->
    Δ ⊢ˢ σ0 ® ρ0 ∈ Sb0 -> glu_args Δ C σ0 ρ0 Ms vs ->
    Δ ⊢ˢ sb_of_list σ0 Ms ® env_args ρ0 vs ∈ Sb.
Proof.
  induction C as [| e C IH] using List.rev_ind; intros * Hass HC H0 Hσ Hg.
  - destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2].
    destruct Ms; [| discriminate ]; destruct vs; [| discriminate ]; cbn.
    apply (functional_glu_ctx_env H0 HC); exact Hσ.
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A ->] _].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2]; rewrite List.length_app in L1, L2; cbn in L1, L2.
    destruct Ms as [| M0 Ms]; [ cbn in L1; lia |]; destruct vs as [| v0 vs]; [ cbn in L2; lia |].
    apply glu_args_snoc in Hg as [[i a P El Ha Hglu HP HM] Hg].
    rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
    destruct (glu_ctx_env_suffix _ _ _ Hass HC) as [Sb1 HC1].
    destruct (glu_ctx_env_cons_clean_inversion H0 HC1) as (i' & HA & HT & HSb1).
    destruct (HT _ _ _ Hσ) as [a' P' El' Ha' Hglu' HP'].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_univ_elem_cumu_ge_uidx (i := i) (j := ul (ulvl i)) (uidx_le_ulvl i) Hglu) as (P1 & El1 & Hglu1).
    assert (HM1 : Δ ⊢ M0 : A[σ0] ® v0 ∈ El1) by (eapply glu_univ_elem_exp_cumu_ge_uidx; [ apply uidx_le_ulvl | exact Hglu | exact Hglu1 | exact HM ]).
    assert (HM' : Δ ⊢ M0 : A[σ0] ® v0 ∈ El')
      by (eapply glu_univ_elem_exp_conv; [ eapply glu_univ_elem_per_univ; exact Hglu1 | exact Hglu1 | exact Hglu' | exact HM1 | exact HP' ]).
    assert (Hσ1 : Δ ⊢ˢ σ0,,M0 ® ρ0 ↦ v0 ∈ Sb1)
      by (apply HSb1; eapply cons_glu_sub_pred_helper; eassumption).
    cbn [sb_of_list env_args List.fold_left].
    exact (IH _ _ _ _ _ _ _ _ Hass HC HC1 Hσ1 Hg).
Qed.

(** ** Constants of [Π]-Types over Telescopes *)

Lemma exp_wk_q_sub_extend : forall C σ φ N, C[q σ][wk_q φ]ʷ[Id,,N] = C[(sb_wk σ φ),,N].
Proof.
  intros; rewrite exp_wk_sub, exp_sub_sub; apply exp_sub_sb_eq.
  intros [| x]; cbn; [ reflexivity |].
  change ((q σ) (S x)) with (sentry_wk (σ x) wk_shift).
  rewrite sentry_wk_wk, sentry_sub_wk, <- sentry_sub_of_wk; apply sentry_sub_sb_eq; intros y; reflexivity.
Qed.

Lemma wf_app_wk_q : forall Δ Δ' σ φ A C M N,
    Δ ⊢ M : Π A[σ] C[q σ] -> Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ N : A[σ][φ]ʷ ->
    Δ' ⊢ M[φ]ʷ $ N : C[(sb_wk σ φ),,N].
Proof.
  intros * HM Hφ HN.
  assert (Hw : Δ' ⊢ M[φ]ʷ : (Π A[σ] C[q σ])[φ]ʷ) by mauto 3.
  cbn [exp_wk] in Hw.
  pose proof (wf_app' _ _ _ _ _ _ _ Hw HN) as H.
  rewrite exp_wk_q_sub_extend in H.
  exact H.
Qed.

(** A type of a glued context, glued at a glued substitution. *)
Lemma glu_rel_typ_at : forall Γ Sb A (i : nat) Δ σ ρ, EG Γ ∈ glu_ctx_env ↘ Sb -> Γ ⊩ A : Typeω@i ->
    Δ ⊢ˢ σ ® ρ ∈ Sb ->
    Δ ⊢ A[σ] : Typeω@i /\ exists a, ⟦ A ⟧ ρ ↘ a /\ Dom a ≈ a ∈ per_univ i /\
      forall P El, DG a ∈ glu_univ_elem i ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
Proof.
  intros * HΓ HA Hσ.
  destruct (glu_rel_exp_of_univ_inversion (u := ul i) HΓ HA _ _ _ Hσ) as (HAσ & a & Ha & Hper & HP & _).
  split; [ exact HAσ | exists a; split; [ exact Ha | split; [ exact Hper | exact HP ] ] ].
Qed.

(** A constant [X], whose value is [f] at the arguments it is applied to, is
    glued at a [Π] over a telescope when its applications to glued arguments
    are glued at the codomain. *)
Lemma ctx_pi_glu_elem : forall (N0 : nat) (f : list domain -> domain) X,
    (forall xs x, List.length xs < N0 -> $| f xs & x | gc_deps ⍮ gc_stack ↘ f (xs ++ x :: nil)) ->
    (forall φ, X[φ]ʷ = X) ->
    forall Δt Γb Sb_b Sb B (i : nat), tele_ass Δt -> EG Γb ∈ glu_ctx_env ↘ Sb_b -> EG Δt ++ Γb ∈ glu_ctx_env ↘ Sb ->
    (forall Δ1 A Δ2, Δt = Δ1 ++ ce_ass A :: Δ2 -> Δ2 ++ Γb ⊩ A : Typeω@i) ->
    (forall Δ1 Δ2, Δt = Δ1 ++ Δ2 -> Δ2 ++ Γb ⊢ ctx_pi Δ1 B : Typeω@i) ->
    forall Δ σ ρ xs Xs, Δ ⊢ˢ σ ® ρ ∈ Sb_b -> List.length xs + List.length Δt = N0 ->
      Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ->
      (forall R a, ⟦ ctx_pi Δt B ⟧ ρ ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R -> R (f xs) (f xs)) ->
      (forall Δ' φ Ms vs, Δ' ⊢ᵏ φ : Δ -> glu_args Δ' Δt (sb_wk σ φ) ρ Ms vs ->
         forall b P El, ⟦ B ⟧ env_args ρ vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
           (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R (f (xs ++ vs)) (f (xs ++ vs))) ->
           Δ' ⊢ apps X (List.map (fun N => N[φ]ʷ) Xs ++ Ms) : B[sb_of_list (sb_wk σ φ) Ms] ® f (xs ++ vs) ∈ El) ->
      forall a P El, ⟦ ctx_pi Δt B ⟧ ρ ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ apps X Xs : (ctx_pi Δt B)[σ] ® f xs ∈ El.
Proof.
  intros N0 f X Happ HXw Δt.
  induction Δt as [| e Δt IH] using List.rev_ind;
    intros * Hass HCb HC HA HCs * Hσ Hlen HXt HPER Hbase * Ha Hglu.
  - cbn [ctx_pi] in *.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    pose proof (Hbase Δ wk_id nil nil (kripke_id _ HΔ) (glu_args_nil _ _ _) _ _ _ Ha Hglu) as H.
    cbn [sb_of_list] in H; rewrite <- exp_wk_sub, exp_wk_id, map_wk_id, !List.app_nil_r in H.
    apply H; intros R HR; exact (HPER _ _ Ha HR).
  - assert (Hass' := Hass); unfold tele_ass in Hass'; apply List.Forall_app in Hass' as [HassΔ He].
    apply List.Forall_cons_iff in He as [[A ->] _].
    rewrite ctx_pi_snoc in Ha, HXt, HPER.
    inversion Ha; subst.
    invert_glu_univ_elem Hglu.
    pose proof (HPER _ _ Ha H2) as Hfx.
    pose proof H2 as H2'.
    basic_invert_per_univ_elem H2'.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HCb _ _ _ Hσ)).
    assert (Hσt : Δ ⊢ˢ σ : Γb) by exact (glu_ctx_env_sub_escape HCb _ _ _ Hσ).
    pose proof (HCs (Δt ++ ⋅ ▹ A) nil (eq_sym (List.app_nil_r _))) as HCp; cbn [List.app] in HCp.
    assert (HPit : Δ ⊢ (ctx_pi (Δt ++ ⋅ ▹ A) B)[σ] : Typeω@i) by mauto 3.
    rewrite ctx_pi_snoc in HPit; cbn [exp_sub] in HPit.
    pose proof (HA Δt A nil eq_refl) as HAp; cbn [List.app] in HAp.
    destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσ) as (HAt & _).
    pose proof (HCs Δt (⋅ ▹ A) eq_refl) as HCqw; cbn [List.app] in HCqw.
    assert (HAw : Γb ⊢ A : Typeω@i) by (eapply glu_rel_exp_to_wf_exp; exact HAp).
    assert (HCqt : Δ ▹ A[σ] ⊢ (ctx_pi Δt B)[q σ] : Typeω@i) by mauto 3.
    pose proof (per_univ_elem_right_irrel _ _ _ _ _ _ _ H0 equiv_a_a') as Hin.
    rewrite ctx_pi_snoc; apply H4; cbn [exp_sub] in HXt |- *.
    eapply mk_pi_glu_exp_pred with (IT := A[σ]) (OT := (ctx_pi Δt B)[q σ]);
      [ exact HXt | exact Hfx | apply wf_exp_eq_refl; exact HPit | exact HAt | exact HCqt | |].
    + intros Δ' φ Hφ.
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσφ) as (_ & a1 & Ha1 & _ & HP1).
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
      rewrite exp_wk_sub; exact (HP1 _ _ H).
    + intros Δ' φ N n Hφ HN equiv_n.
      assert (Hn0 : in_rel0 n n) by (apply Hin; exact equiv_n).
      destruct (H7 _ _ Hn0) as [b b' Hb Hb' Hbb].
      destruct (proj1 (H8 _ _) Hfx n n Hn0) as [r r' Er Er' Hrr].
      assert (Hlt : List.length xs < List.length xs + List.length (Δt ++ ⋅ ▹ A)) by (rewrite List.length_app; cbn; lia).
      pose proof (Happ _ n Hlt) as Ef.
      assert (r = f (xs ++ n :: nil)) as -> by (eapply functional_eval_app; eassumption).
      assert (r' = f (xs ++ n :: nil)) as -> by (eapply functional_eval_app; eassumption).
      exists (f (xs ++ n :: nil)); split; [ exact Ef |].
      rewrite exp_sub_q_extend_wk.
      assert (HNt : Δ' ⊢ N : A[σ][φ]ʷ) by (eapply glu_univ_elem_trm_escape; eassumption).
      pose proof (wf_app_wk_q _ _ _ _ _ _ _ _ HXt Hφ HNt) as HXt'.
      replace ((apps X Xs)[φ]ʷ $ N) with (apps X (List.map (fun M => M[φ]ʷ) Xs ++ N :: nil)) in HXt' |- *
        by (rewrite apps_exp_snoc, apps_wk, HXw; reflexivity).
      rewrite <- List.app_assoc in HC; cbn [List.app] in HC.
      destruct (glu_ctx_env_suffix _ _ _ HassΔ HC) as [Sb1 HC1].
      destruct (glu_ctx_env_cons_clean_inversion HCb HC1) as (i' & HAi' & HTi' & HSb1).
      pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (HTi' _ _ _ Hσφ) as [a1 P1 El1 Ha1 Hg1 HP1].
      assert (a1 = a0) as -> by (eapply functional_eval_exp; eassumption).
      assert (HN1 : Δ' ⊢ N : A[σ][φ]ʷ ® n ∈ El1)
        by (eapply glu_univ_elem_exp_conv;
            [ eapply glu_univ_elem_per_univ; exact H | exact H | exact Hg1 | exact HN | rewrite exp_wk_sub; exact HP1 ]).
      assert (Hσ1 : Δ' ⊢ˢ (sb_wk σ φ),,N ® ρ ↦ n ∈ Sb1)
        by (apply HSb1; eapply cons_glu_sub_pred_pi_helper; eassumption).
      eapply (IH (Γb ▹ A) Sb1 Sb B i HassΔ HC1 HC);
        [ | | exact Hσ1 | rewrite !List.length_app; cbn; lia | exact HXt' | | | exact Hb | exact (H1 _ _ _ Hb) ].
      * intros Δ1 A0 Δ2 Heq.
        pose proof (HA Δ1 A0 (Δ2 ++ ⋅ ▹ A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'.
      * intros Δ1 Δ2 Heq.
        pose proof (HCs Δ1 (Δ2 ++ ⋅ ▹ A) ltac:(rewrite Heq, <- List.app_assoc; reflexivity)) as H'.
        rewrite <- List.app_assoc in H'; exact H'.
      * intros R a' Ha' HR.
        assert (a' = b) as -> by (eapply functional_eval_exp; eassumption).
        apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Hbb HR); exact Hrr.
      * intros Δ'' φ' Ms vs Hφ' Hg b0 P0 El0 Hb0 Hg0 HPb0.
        pose proof (kripke_compose _ _ _ _ _ Hφ' Hφ) as Hφφ.
        assert (Hsb : sb_eq (sb_wk ((sb_wk σ φ),,N) φ') ((sb_wk σ (φ ⊙ φ')),,N[φ']ʷ))
          by (intros [| x]; cbn; [ reflexivity | apply sentry_wk_wk ]).
        assert (Hg' : glu_args Δ'' (Δt ++ ⋅ ▹ A) (sb_wk σ (φ ⊙ φ')) ρ (N[φ']ʷ :: Ms) (n :: vs)).
        { apply glu_args_snoc; split; [| eapply glu_args_sb_eq; [ exact Hsb | exact Hg ] ].
          pose proof (glu_ctx_env_sub_monotone _ _ HCb _ _ _ _ _ Hσ Hφφ) as Hσφφ.
          destruct (glu_rel_typ_at _ _ _ _ _ _ _ HCb HAp Hσφφ) as (_ & a2 & Ha2 & _ & HP2).
          assert (a2 = a0) as -> by (eapply functional_eval_exp; eassumption).
          apply (mk_glu_arg _ _ _ _ _ _ i a0 IP IEl H5 H (HP2 _ _ H)).
          rewrite <- exp_wk_sub, <- exp_wk_wk.
          eapply glu_univ_elem_exp_monotone; eassumption. }
        rewrite <- List.app_assoc in HPb0; cbn [List.app] in HPb0.
        pose proof (Hbase Δ'' (φ ⊙ φ') (N[φ']ʷ :: Ms) (n :: vs) Hφφ Hg' b0 P0 El0 Hb0 Hg0 HPb0) as Hr.
        cbn [sb_of_list] in Hr.
        rewrite <- (exp_sub_sb_eq _ _ _ (sb_of_list_cong Ms _ _ Hsb)) in Hr.
        rewrite List.map_app, map_wk_wk, <- List.app_assoc, <- List.app_assoc; cbn [List.map List.app].
        exact Hr.
Qed.

(** ** Closed Constants *)

Lemma typ_nil_rel' : forall T (i : nat) ρ ρ',
    ⋅ ⊢ T : Typeω@i ->
    exists a a', ⟦ T ⟧ ρ ↘ a /\ ⟦ T ⟧ ρ' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HT%completeness_fundamental_exp.
  destruct (rel_exp_of_typ_inversion_simple HT) as [env_rel [Hnil H]].
  apply H.
  inversion Hnil as [? Heq | | |]; subst.
  apply Heq; exact I.
Qed.

(** A closed constant glued at the value of its closed type at the empty
    environment is glued at the empty context. *)
Lemma glu_closed_const : forall X T (i : nat) m0,
    (forall σ, X[σ] = X) -> (forall σ, T[σ] = T) -> ⋅ ⊢ T : Typeω@i ->
    (forall ρ, ⟦ X ⟧ ρ ↘ m0) ->
    (forall Δ σ, Δ ⊢ˢ σ : ⋅ -> forall a P El, ⟦ T ⟧ nil ↘ a -> DG a ∈ glu_univ_elem i ↘ P ↘ El ->
       Δ ⊢ X : T ® m0 ∈ El) ->
    ⋅ ⊩ X : T.
Proof.
  intros * HXs HTs HT HXe H.
  assert (Hg : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; eapply presup_exp_ctx; exact HT).
  eapply mk_glu_rel_exp with (gre_lvl := i); [ econstructor; [ reflexivity | exact Hg ] |].
  intros Δ σ ρ Hσ; cbn in Hσ.
  destruct (typ_nil_rel' _ _ ρ nil HT) as (a & a0 & Ha & Ha0 & Haa).
  assert (Ha00 : Dom a0 ≈ a0 ∈ per_univ i) by (etransitivity; [ symmetry; exact Haa | exact Haa ]).
  destruct (per_univ_glu_univ_elem _ _ Ha00) as (P & El & Hglu).
  assert (Hglu' : DG a ∈ glu_univ_elem i ↘ P ↘ El) by (eapply glu_univ_elem_resp_per_univ; [ symmetry; exact Haa | exact Hglu ]).
  econstructor; [ exact Ha | apply HXe | exact Hglu' |].
  rewrite HXs, HTs; exact (H _ _ Hσ _ _ _ Ha0 Hglu).
Qed.

(** ** The Entries of a Glued Telescope *)

Lemma glu_rel_exp_lift_nat : forall Γ A (i j : nat), i <= j -> Γ ⊩ A : Typeω@i -> Γ ⊩ A : Typeω@j.
Proof. intros * Hle HA; exact (glu_rel_exp_lift_uidx (u := ul i) (v := ul j) Hle HA). Qed.

Lemma glu_ctx_env_head_valid : forall Γ A Sb, EG Γ ▹ A ∈ glu_ctx_env ↘ Sb -> exists i, Γ ⊩ A : Typeω@i.
Proof.
  intros * H; inversion H as [| ? ? i TSb ? HΓ HA HT HSb | |]; subst.
  exists i; eapply glu_rel_exp_of_typ; [ exact HΓ |].
  intros Δ σ ρ Hσ; destruct (HT _ _ _ Hσ) as [a P El Ha Hglu HP].
  split; [ mauto 3 |].
  exists a; split; [ exact Ha | split; [ eapply glu_univ_elem_per_univ; exact Hglu |] ].
  intros P' El' Hglu'; handle_functional_glu_univ_elem; exact HP.
Qed.

Lemma glu_ctx_env_entries_valid : forall C Γb Sb, tele_ass C -> EG C ++ Γb ∈ glu_ctx_env ↘ Sb ->
    forall (i0 : nat), exists (i : nat), i0 <= i /\
      forall Δ1 A Δ2, C = Δ1 ++ ce_ass A :: Δ2 -> Δ2 ++ Γb ⊩ A : Typeω@i.
Proof.
  induction C as [| e C IH]; intros * Hass H i0.
  - exists i0; split; [ lia |]; intros [] *; discriminate.
  - apply List.Forall_cons_iff in Hass as [[A ->] Hass].
    cbn [List.app] in H; pose proof H as H'; inversion H' as [| ? ? ? ? ? HC _ _ _ | |]; subst.
    destruct (glu_ctx_env_head_valid _ _ _ H) as [k Hk].
    destruct (IH _ _ Hass HC (Nat.max i0 k)) as (i1 & Hle & Hi).
    exists i1; split; [ lia |].
    intros [| e' Δ1] A' Δ2 Heq; cbn [List.app] in Heq; injection Heq; intros; subst;
      [ eapply glu_rel_exp_lift_nat; [| exact Hk ]; lia | eauto ].
Qed.

(** ** Glued Arguments of Closed Telescopes *)

Lemma uidx_le_max : forall u j, uidx_le u (ul (Nat.max (ulvl u) j)).
Proof. intros [] j; cbn; [ exact I | lia ]. Qed.

Lemma wf_sub_nil' : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
Proof.
  intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
    intros * Hx; inversion Hx.
Qed.

Lemma tele_insts_closed_base : forall C σ σ' Ms, tele_ass C -> ctx_scoped 0 C ->
    tele_insts C σ Ms = tele_insts C σ' Ms.
Proof.
  intros * Hass Hs.
  pose proof (tele_insts_sub C 0 σ σ' Id Ms Hass Hs ltac:(intros; lia)) as H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  rewrite (List.map_ext _ (fun T => T) exp_sub_id), List.map_id in H.
  exact H.
Qed.

Lemma glu_args_closed_base : forall Δ C τ τ' ρ Ms vs, tele_ass C -> ctx_scoped 0 C ->
    glu_args Δ C τ ρ Ms vs -> glu_args Δ C τ' ρ Ms vs.
Proof.
  intros * Hass Hs [L1 L2 H]; constructor; [ exact L1 | exact L2 |].
  rewrite <- (tele_insts_closed_base _ τ τ'); assumption.
Qed.

Lemma glu_args_wk : forall Δ Δ' φ C ρ Ms vs, tele_ass C -> ctx_scoped 0 C -> Δ' ⊢ᵏ φ : Δ ->
    glu_args Δ C Id ρ Ms vs -> glu_args Δ' C Id ρ (List.map (fun M => M[φ]ʷ) Ms) vs.
Proof.
  intros * Hass Hs Hφ [L1 L2 H]; constructor; [ rewrite List.length_map; exact L1 | exact L2 |].
  intros k M T v A HM HT Hv HA.
  rewrite List.nth_error_map in HM.
  destruct (List.nth_error Ms k) as [M0 |] eqn:HM0; [| discriminate ]; injection HM as <-.
  rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
  destruct (List.nth_error (tele_insts C Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
  destruct (H _ _ _ _ _ HM0 HT0 Hv HA) as [i a P El Ha Hglu HP HMg].
  apply (mk_glu_arg _ _ _ _ _ _ i a P El Ha Hglu).
  - eapply glu_univ_elem_typ_monotone; eassumption.
  - eapply glu_univ_elem_exp_monotone; eassumption.
Qed.

Lemma glu_args_resp_eq : forall Δ C ρ Ms Ms' vs, tele_ass C -> ⊢ C -> ⊢ Δ ->
    exps_eq_at Δ C Ms Ms' -> glu_args Δ C Id ρ Ms vs -> glu_args Δ C Id ρ Ms' vs.
Proof.
  intros * Hass HC HΔ [Hl HMM] [L1 L2 H].
  constructor; [ congruence | exact L2 |].
  intros k M' T' v A HM' HT' Hv HA.
  assert (Hk : k < List.length C) by (rewrite <- L1, Hl; apply List.nth_error_Some; congruence).
  destruct (nth_error_lt_some Ms k ltac:(lia)) as [M HM].
  destruct (nth_error_lt_some (tele_insts C Id Ms) k) as [T HT]; [ rewrite length_tele_insts by exact Hass; lia |].
  destruct (H _ _ _ _ _ HM HT Hv HA) as [i a P El Ha Hglu HP HMg].
  assert (HCe : ⊢ C ++ ⋅) by (rewrite List.app_nil_r; exact HC).
  assert (HId : Δ ⊢ˢ Id ≈ Id : ⋅) by (apply wf_sub_eq_refl, wf_sub_nil'; exact HΔ).
  destruct (tele_insts_cong C Δ ⋅ Id Id Ms Ms' Hass HCe HId L1 ltac:(lia) HMM k T T' HT HT') as [j HTT].
  pose proof (uidx_le_max i j) as Hij.
  destruct (glu_univ_elem_cumu_ge_uidx (i := i) (j := ul (Nat.max (ulvl i) j)) Hij Hglu) as (P' & El' & Hglu').
  assert (HP' : Δ ⊢ T ® P') by (eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hij | exact Hglu | exact Hglu' | exact HP ]).
  assert (HTT' : Δ ⊢ T ≈ T' : Typeω@(Nat.max (ulvl i) j)) by (eapply lift_exp_eq_ge; [| exact HTT ]; lia).
  apply (mk_glu_arg _ _ _ _ _ _ (ul (Nat.max (ulvl i) j)) a P' El' Ha Hglu');
    [ eapply glu_univ_elem_typ_resp_exp_eq; eassumption |].
  eapply glu_univ_elem_trm_resp_typ_exp_eq; [ exact Hglu' | | exact HTT' ].
  eapply glu_univ_elem_trm_resp_exp_eq;
    [ exact Hglu' | eapply glu_univ_elem_exp_cumu_ge_uidx; [ exact Hij | exact Hglu | exact Hglu' | exact HMg ] | exact (HMM _ _ _ _ HM HM' HT) ].
Qed.

Lemma firstn_app_ge : forall {X} (l1 l2 : list X) k, List.length l1 <= k ->
    List.firstn k (l1 ++ l2) = l1 ++ List.firstn (k - List.length l1) l2.
Proof. intros; rewrite List.firstn_app, List.firstn_all2 by lia; reflexivity. Qed.

Lemma firstn_app_le : forall {X} (l1 l2 : list X) k, k <= List.length l1 ->
    List.firstn k (l1 ++ l2) = List.firstn k l1.
Proof. intros; rewrite List.firstn_app; replace (k - List.length l1) with 0 by lia; cbn; apply List.app_nil_r. Qed.

Lemma glu_args_app : forall Δ C1 C2 τ ρ Ms1 Ms2 vs1 vs2, tele_ass C1 ->
    List.length Ms1 = List.length C1 -> List.length vs1 = List.length C1 ->
    glu_args Δ (C2 ++ C1) τ ρ (Ms1 ++ Ms2) (vs1 ++ vs2) <->
    glu_args Δ C1 τ ρ Ms1 vs1 /\ glu_args Δ C2 (sb_of_list τ Ms1) (env_args ρ vs1) Ms2 vs2.
Proof.
  intros * Hass HM1 Hv1.
  assert (Ht1 : List.length (tele_insts C1 τ Ms1) = List.length C1) by (rewrite length_tele_insts by exact Hass; lia).
  assert (Hr1 : List.length (List.rev C1) = List.length C1) by apply List.length_rev.
  split.
  - intros [L1 L2 H]; rewrite !List.length_app in L1, L2.
    rewrite tele_insts_app, List.rev_app_distr in H by assumption.
    split; constructor; [ lia | lia | | lia | lia |].
    + intros k M T v A HM HT Hv HA.
      assert (Hk : k < List.length C1) by (rewrite <- HM1; apply List.nth_error_Some; congruence).
      pose proof (H k M T v A) as H'.
      rewrite (firstn_app_le vs1) in H' by lia.
      apply H'; rewrite List.nth_error_app1 by lia; assumption.
    + intros k M T v A HM HT Hv HA.
      pose proof (H (List.length C1 + k) M T v A) as H'.
      rewrite firstn_app_ge, env_args_app in H' by lia.
      replace (List.length C1 + k - List.length vs1) with k in H' by lia.
      apply H'; rewrite List.nth_error_app2 by lia.
      * replace (List.length C1 + k - List.length Ms1) with k by lia; exact HM.
      * replace (List.length C1 + k - List.length (tele_insts C1 τ Ms1)) with k by lia; exact HT.
      * replace (List.length C1 + k - List.length vs1) with k by lia; exact Hv.
      * replace (List.length C1 + k - List.length (List.rev C1)) with k by lia; exact HA.
  - intros [[L1 L2 H1] [L3 L4 H2]]; constructor; [ rewrite !List.length_app; lia | rewrite !List.length_app; lia |].
    rewrite tele_insts_app, List.rev_app_distr by assumption.
    intros k M T v A HM HT Hv HA.
    destruct (Nat.lt_ge_cases k (List.length C1)) as [Hk | Hk].
    + rewrite List.nth_error_app1 in HM, HT, Hv, HA by lia.
      rewrite (firstn_app_le vs1) by lia.
      exact (H1 _ _ _ _ _ HM HT Hv HA).
    + rewrite List.nth_error_app2 in HM, HT, Hv, HA by lia.
      rewrite firstn_app_ge, env_args_app by lia.
      rewrite HM1, Ht1, Hv1, Hr1 in *.
      exact (H2 _ _ _ _ _ HM HT Hv HA).
Qed.

Lemma read_ps_nth : forall s ρ T vs Rs, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Rs ->
    List.length (nfs_to_exps Rs) = List.length vs /\
    forall k v A, List.nth_error vs k = Some v -> List.nth_error T k = Some (ce_ass A) ->
      exists a (V : nf), ⟦ A ⟧ env_args ρ (List.firstn k vs) ↘ a /\ Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ V /\
        List.nth_error (nfs_to_exps Rs) k = Some (V : exp).
Proof.
  induction 1; [ split; [ reflexivity | intros [] *; discriminate ] |].
  match goal with H : _ /\ _ |- _ => destruct H as [IHl IHn] end.
  split; [ cbn; congruence |].
  intros [| k] v0 A0 Hv HA; cbn in Hv, HA.
  - injection Hv as <-; injection HA as <-; do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ].
  - destruct (IHn _ _ _ Hv HA) as (a0 & V0 & Ha0 & HV0 & HN0); exists a0, V0; repeat split; assumption.
Qed.

Lemma glu_args_ass_nth : forall C k, tele_ass C -> k < List.length C -> exists A, List.nth_error (List.rev C) k = Some (ce_ass A).
Proof.
  intros * Hass Hk.
  destruct (nth_error_lt_some (List.rev C) k ltac:(rewrite List.length_rev; exact Hk)) as [e He].
  assert (He' := He); apply List.nth_error_In in He'; apply List.in_rev in He'.
  destruct (proj1 (List.Forall_forall _ _) Hass _ He') as [A ->]; eauto.
Qed.

Lemma glu_args_params_top : forall D Δ Ms vs, tele_ass (ind_params D) -> ctx_scoped 0 (ind_params D) ->
    glu_args Δ (ind_params D) Id nil Ms vs -> glu_params_top D Δ Ms vs.
Proof.
  intros * Hass Hs Hg; pose proof Hg as [L1 L2 H].
  constructor; [ exact L1 | |].
  - intros k M T HM HT.
    assert (Hk : k < List.length (ind_params D)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (H _ _ _ _ _ HM HT Hv He) as [i a P El _ Hglu _ HMg].
    eapply glu_univ_elem_trm_escape; eassumption.
  - intros Δ' φ Rs Hφ HRs.
    destruct (read_ps_nth _ _ _ _ _ HRs) as [HRl HRn].
    split; [ rewrite List.length_map, HRl; congruence |].
    intros k X Y T HX HY HT.
    rewrite List.nth_error_map in HX.
    destruct (List.nth_error Ms k) as [M |] eqn:HM; [| discriminate ]; injection HX as <-.
    rewrite <- (tele_insts_closed_wk _ _ _ Hass Hs), List.nth_error_map in HT.
    destruct (List.nth_error (tele_insts (ind_params D) Id Ms) k) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
    assert (Hk : k < List.length (ind_params D)) by (rewrite <- L1; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some vs k ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth _ _ Hass Hk) as [A He].
    destruct (HRn _ _ _ Hv He) as (a' & V & Ha' & HV & HY').
    rewrite HY' in HY; injection HY as <-.
    destruct (H _ _ _ _ _ HM HT0 Hv He) as [i a P El Ha Hglu HP HMg].
    assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
    destruct (realize_glu_elem_top _ _ _ _ Hglu _ _ _ _ HMg) as [? ? _ _ _ _ Hrb].
    exact (Hrb _ _ _ Hφ HV).
Qed.

(** ** The Non-Recursive Arguments, Syntactically *)

Fixpoint nonrec_exps (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ :: gs, A :: As => A :: nonrec_exps gs As
  | ca_rec _ :: gs, _ :: As => nonrec_exps gs As
  | _, _ => nil
  end.

Lemma nonrec_exps_app : forall gs gs' As As', List.length As = List.length gs ->
    nonrec_exps (gs ++ gs') (As ++ As') = nonrec_exps gs As ++ nonrec_exps gs' As'.
Proof.
  induction gs as [| [] gs IH]; intros gs' [| A As] As' Hl; cbn in *; try discriminate; try reflexivity;
    rewrite IH by lia; reflexivity.
Qed.

Lemma length_nonrec_exps : forall gs As, List.length As = List.length gs ->
    List.length (nonrec_exps gs As) = List.length (cargs_nonrec gs).
Proof.
  induction gs as [| [] gs IH]; intros [| A As] Hl; cbn in *; try discriminate; try reflexivity;
    rewrite ?IH by lia; reflexivity.
Qed.

Lemma nonrec_exps_firstn : forall gs gs1 g gs2 As, gs = gs1 ++ g :: gs2 -> List.length As = List.length gs ->
    List.firstn (List.length (cargs_nonrec gs1)) (nonrec_exps gs As) = nonrec_exps gs1 (List.firstn (List.length gs1) As).
Proof.
  intros * Heq Hl.
  rewrite <- (List.firstn_skipn (List.length gs1) As) at 1.
  rewrite Heq at 1.
  rewrite nonrec_exps_app by (rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite firstn_app_exact by (apply length_nonrec_exps; rewrite List.length_firstn; subst; rewrite List.length_app in Hl; cbn in Hl; lia).
  reflexivity.
Qed.

Lemma nonrec_exps_nth_arg : forall gs gs1 A gs2 As N, gs = gs1 ++ ca_arg A :: gs2 -> List.length As = List.length gs ->
    List.nth_error As (List.length gs1) = Some N ->
    List.nth_error (nonrec_exps gs As) (List.length (cargs_nonrec gs1)) = Some N.
Proof.
  intros * Heq Hl Hv; subst gs.
  rewrite <- (List.firstn_skipn (List.length gs1) As) in Hv |- *.
  assert (Hl1 : List.length (List.firstn (List.length gs1) As) = List.length gs1)
    by (rewrite List.length_firstn; rewrite List.length_app in Hl; cbn in Hl; lia).
  rewrite nonrec_exps_app by exact Hl1.
  rewrite List.nth_error_app2 in Hv by lia; rewrite Hl1 in Hv.
  replace (List.length gs1 - List.length gs1) with 0 in Hv by lia.
  rewrite List.nth_error_app2 by (rewrite length_nonrec_exps by exact Hl1; lia).
  rewrite length_nonrec_exps by exact Hl1.
  replace (List.length (cargs_nonrec gs1) - List.length (cargs_nonrec gs1)) with 0 by lia.
  destruct (List.skipn (List.length gs1) As) as [| v0 ws]; cbn in Hv |- *; [ discriminate | exact Hv ].
Qed.

(** [wk_pat] picks the non-recursive arguments out of an instance of all of
    them. *)
Lemma wk_pat_sb_of_list : forall gs1 σ As, List.length As = List.length gs1 ->
    sb_eq ((ι (wk_pat (cargs_pat gs1))) ⨟ sb_of_list σ As) (sb_of_list σ (nonrec_exps gs1 As)).
Proof.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros σ As Hl.
  - destruct As; [| discriminate ]; intros x; reflexivity.
  - rewrite List.length_app in Hl; cbn in Hl.
    destruct As as [| A As] using List.rev_ind; [ cbn in Hl; lia |]; clear IHAs.
    rewrite List.length_app in Hl; cbn in Hl.
    rewrite cargs_pat_snoc, nonrec_exps_app by lia.
    rewrite !sb_of_list_app.
    destruct g as [B | Ps]; cbn [wk_pat nonrec_exps sb_of_list].
    + intros [| x]; [ reflexivity |].
      cbn [sb_compose sb_of_wk sentry_sub wk_q sb_extend]; specialize (IH σ As ltac:(lia) x).
      cbn [sb_compose sb_of_wk sentry_sub] in IH; exact IH.
    + intros x; specialize (IH σ As ltac:(lia) x).
      cbn [sb_compose sb_of_wk sentry_sub wk_compose] in IH |- *; exact IH.
Qed.

Corollary exp_wk_pat_sb_of_list : forall B gs1 σ As, List.length As = List.length gs1 ->
    B[wk_pat (cargs_pat gs1)]ʷ[sb_of_list σ As] = B[sb_of_list σ (nonrec_exps gs1 As)].
Proof.
  intros; rewrite <- exp_sub_of_wk, exp_sub_sub; apply exp_sub_sb_eq, wk_pat_sb_of_list; assumption.
Qed.

(** The type of a non-recursive argument. *)
Lemma cargs_arg_type : forall p D gs gs1 A gs2 σ As T, gs = gs1 ++ ca_arg A :: gs2 ->
    List.nth_error (tele_insts (cargs_ctx p D gs) σ As) (List.length gs1) = Some T ->
    T = A[wk_pat (cargs_pat gs1)]ʷ[sb_of_list σ (List.firstn (List.length gs1) As)].
Proof.
  intros * -> HT.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (A0 & HA & ->).
  unfold cargs_ctx in HA; rewrite cargs_ctx_aux_app in HA; cbn [cargs_ctx_aux] in HA.
  rewrite !List.rev_app_distr in HA; cbn [List.rev List.app] in HA.
  rewrite List.nth_error_app2 in HA by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag in HA; cbn in HA.
  injection HA as <-; rewrite List.app_nil_r; reflexivity.
Qed.

(** ** The Components of an Inductive Type at Glued Parameters

    The types of the telescopes of a valid declaration, at uniform
    parameters glued to [ups], are glued at the gluings of the clause of
    [d_ind] at the index of the sort's universe. *)
(** The substitution of the uniform parameters and the parameters of a
    recursive argument before a position, over the context the recursive
    argument's parameters are typed in, as [Completeness.IndCases.rec_closure]
    builds it. *)
Lemma rec_sub_valid : forall D0, valid_ind_decl D0 -> decl_closed D0 -> forall c gs gs1 t gs2, ind_con D0 c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
    forall m, m <= ind_nn D0 ->
      ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D0 ⊨ˢ
        sb_of_list (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + ind_nn D0))) (List.firstn m (ptyp_ps t))
        ≈ sb_of_list (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec gs1) + ind_nn D0))) (List.firstn m (ptyp_ps t))
        : nparams_prefix D0 m ++ ind_uparams D0.
Proof.
  intros D0 HD Hc0 c gs gs1 t gs2 Hcon Heq.
  pose proof (decl_closed_nu D0 Hc0) as Hle.
  set (K := List.length (cargs_nonrec gs1)).
  set (L := ptyp_depth t + K + ind_nn D0).
  set (Ξ0 := ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_params D0).
  assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
  assert (HΞ0 : ⊨ Ξ0).
  { pose proof (vid_dctx _ HD _ _ _ _ _ (List.length (ptyp_doms t)) Hcon Heq (le_n _)) as H.
    rewrite List.firstn_all in H; exact H. }
  pose proof (IndCases.length_rec_ps _ Hc0 _ _ _ _ _ Hcon Heq) as HPl.
  induction m as [| m IH]; intros Hmn.
  - cbn [List.firstn sb_of_list]; unfold nparams_prefix; cbn [List.firstn List.rev List.app].
    apply rel_sub_of_wk.
    assert (HL : L = List.length (ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_nparams D0))
      by (unfold L, ptyp_tele, ptyp_depth; rewrite !List.length_app, IndCases.length_nonrec_args_prefix, length_nparams, doms_ctx_length
            by exact HK; lia).
    assert (HΞe : Ξ0 = (ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_nparams D0) ++ ind_uparams D0)
      by (unfold Ξ0; rewrite params_split, <- !List.app_assoc; reflexivity).
    fold L; rewrite HΞe, HL; apply UnitCases.rel_wk_under_ctx_shiftn; rewrite <- HΞe; exact HΞ0.
  - pose proof (IH ltac:(lia)) as Hτ.
    destruct (nth_error_lt_some (ptyp_ps t) m ltac:(lia)) as [P HP].
    assert (HT : exists T, List.nth_error (tele_insts (ind_nparams D0) (sb_of_wk (wk_shiftn L)) (ptyp_ps t)) m = Some T).
    { apply nth_error_lt_some.
      rewrite length_tele_insts by exact (decl_closed_nparams_ass D0 Hc0).
      rewrite length_nparams; lia. }
    destruct HT as [T HT].
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
    pose proof (vid_rec _ HD _ _ _ _ _ _ _ _ Hcon Heq HP HT) as HPv.
    destruct (vid_npar _ HD _ _ HA) as (_ & j & HAv).
    rewrite (firstn_S_snoc _ _ _ HP), sb_of_list_app, (IndCases.nparams_prefix_S _ _ _ HA); cbn [sb_of_list List.app].
    eapply SubstitutionCases.rel_sub_under_ctx_extend; [ exact Hτ | exact HAv | exact HPv ].
Qed.

(** A term glued at a type of a value is glued at that type of a value
    related to it, at a larger universe. *)
Lemma glu_transfer_per : forall (j i : nat) a b P El Γ T M m, DG a ∈ glu_univ_elem j ↘ P ↘ El -> Dom a ≈ b ∈ per_univ i ->
    Γ ⊢ T ® P -> Γ ⊢ M : T ® m ∈ El ->
    exists (k : uidx) P' El', DG b ∈ glu_univ_elem k ↘ P' ↘ El' /\ Γ ⊢ T ® P' /\ Γ ⊢ M : T ® m ∈ El'.
Proof.
  intros * Hg [R HR] HT HM.
  destruct (glu_univ_elem_cumu_ge (i := j) (j := Nat.max j i) (Nat.le_max_l _ _) Hg) as (P1 & El1 & Hg1).
  pose proof (per_univ_elem_cumu_ge i (Nat.max j i) _ _ _ (Nat.le_max_r _ _) HR) as HR1.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R HR1) Hg1) as Hg2.
  exists (Nat.max j i), P1, El1; split; [ exact Hg2 | split ].
  - eapply glu_univ_elem_typ_cumu_ge; [ apply Nat.le_max_l | exact Hg | exact Hg1 | exact HT ].
  - eapply glu_univ_elem_exp_cumu_ge; [ apply Nat.le_max_l | exact Hg | exact Hg1 | exact HM ].
Qed.

(** The type of a recursive argument: the shape's type at the uniform
    parameters of the parameters, under the parameters and the
    non-recursive arguments before it. *)
Lemma cargs_rec_type_sh : forall p D gs gs1 t gs2 Ps As T, gs = gs1 ++ ca_rec t :: gs2 ->
    ind_nu D <= ind_np D -> List.length Ps = ind_np D ->
    List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) (List.length gs1) = Some T ->
    T = ptyp_ty_at p (List.firstn (ind_nu D) Ps) (sb_of_list Id (Ps ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))) t.
Proof.
  intros * Heq Hnu HPl HT.
  assert (HAl : List.length gs1 < List.length As).
  { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
    rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
    rewrite length_tele_insts by apply cargs_ctx_aux_ass; subst gs; lia. }
  rewrite (cargs_rec_type_at _ _ _ _ _ _ _ _ _ Heq Hnu HPl HT).
  apply ptyp_ty_at_sb_eq.
  rewrite !sb_of_list_app; apply wk_pat_sb_of_list; rewrite List.length_firstn; lia.
Qed.

(** The types of the non-uniform parameters of a recursive argument, at an
    instance [Us ++ Ys] of the context it is declared in. *)
Lemma rec_tele_inst : forall D Pr L τ Us Ys m T, decl_closed D ->
    List.length Us = ind_nu D -> List.length Ys = L ->
    List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) Pr) m = Some T ->
    List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) Pr)) m
      = Some T[sb_of_list τ (Us ++ Ys)].
Proof.
  intros * Hc HUl HYl HT.
  rewrite <- (tele_insts_sub _ (ind_nu D) (sb_of_wk (wk_shiftn L)));
    [ rewrite List.nth_error_map, HT; reflexivity
    | apply decl_closed_nparams_ass, Hc | apply decl_closed_nparams_scoped, Hc |].
  intros x Hx; cbn [sb_of_wk sentry_sub wk_shiftn].
  rewrite (sb_of_list_app Us Ys).
  replace (x + L) with (List.length Ys + x) by lia.
  rewrite sb_of_list_ge, (sb_of_list_nth Us τ x (a_var 0)), (sb_of_list_nth Us Id x (a_var 0)) by lia; reflexivity.
Qed.

Lemma eval_exps_firstn : forall Ms ρ ms k, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms ->
    ⟦ List.firstn k Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn k ms.
Proof.
  induction Ms as [| M Ms IH]; intros * H; inversion H; subst; destruct k; cbn;
    solve [ constructor | econstructor; [ eassumption | apply IH; assumption ] ].
Qed.

(** A weakened list instance is the list of the weakened terms, over the
    weakened base. *)
Lemma sb_wk_sb_of_list : forall Xs τ φ,
    sb_eq (sb_wk (sb_of_list τ Xs) φ) (sb_of_list (sb_wk τ φ) (List.map (fun X => X[φ]ʷ) Xs)).
Proof.
  induction Xs as [| X Xs IH]; intros τ φ; cbn [sb_of_list List.map]; [ reflexivity |].
  intros x; rewrite (IH (τ,,X) φ x); apply sb_of_list_cong, sb_wk_extend.
Qed.

(** The substitution of the codomain of a shape's [Π], instantiated at an
    argument [b] after a weakening: the list instance extended by [b]. *)
Lemma sb_q_shape_step : forall τ Xs φ b,
    sb_eq ((q (sb_of_list τ Xs)) ⨟ ((ι φ),,b)) (sb_of_list (sb_wk τ φ) (List.map (fun X => X[φ]ʷ) Xs ++ b :: nil)).
Proof.
  intros; rewrite sb_of_list_app; cbn [sb_of_list].
  intros [| x]; [ reflexivity |].
  unfold sb_q, sb_extend, sb_wk; cbn.
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  rewrite sentry_sub_of_wk; exact (sb_wk_sb_of_list Xs τ φ x).
Qed.

(** The type of a shape's rest after a [Π], instantiated at an argument
    [b] after a weakening. *)
Lemma ptyp_ty_at_shape_step : forall p t τ Us Ys φ b,
    (ptyp_ty_at p (List.map (fun U => U[↑]ʷ) Us) (q (sb_of_list τ (Us ++ Ys))) t)[(ι φ),,b]
    = ptyp_ty_at p (List.map (fun U => U[φ]ʷ) Us)
        (sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t.
Proof.
  intros; rewrite ptyp_ty_at_sub, List.map_map.
  rewrite (List.map_ext _ (fun U => U[φ]ʷ) (fun U => exp_shift_extend_wk U φ b)).
  apply ptyp_ty_at_sb_eq.
  rewrite List.app_assoc, <- List.map_app; apply sb_q_shape_step.
Qed.

(** A glued instance of a context extended by a term glued at the new
    entry's type. *)
Lemma glu_sub_snoc : forall Γ B Sb Sb' Δ σ ρ b c',
    EG Γ ∈ glu_ctx_env ↘ Sb -> EG ce_ass B :: Γ ∈ glu_ctx_env ↘ Sb' -> Δ ⊢ˢ σ ® ρ ∈ Sb ->
    glu_arg Δ ρ B B[σ] b c' ->
    Δ ⊢ˢ σ,,b ® ρ ↦ c' ∈ Sb'.
Proof.
  intros * HSb HSb' Hσ Hb.
  apply (glu_sub_of_list (⋅ ▹ B) Γ Sb' Sb Δ σ ρ (b :: nil) (c' :: nil)); [ repeat constructor; eauto | exact HSb' | exact HSb | exact Hσ |].
  apply (glu_args_snoc Δ nil B σ ρ b nil c' nil); split; [ exact Hb | apply glu_args_nil ].
Qed.

(** An element glued at a type of a value is glued at another type of it,
    at another gluing of it. *)
Lemma glu_elem_retype : forall (i j : uidx) a P El P' El' Γ A A' M m,
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> DG a ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P -> Γ ⊢ M : A ® m ∈ El -> Γ ⊢ A' ® P' -> Γ ⊢ M : A' ® m ∈ El'.
Proof.
  intros * Hi Hj HA HM HA'.
  set (n := Nat.max (ulvl i) (ulvl j)).
  assert (Hin : uidx_le i (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  assert (Hjn : uidx_le j (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_uidx Hin Hi) as (Pn & Eln & Hn).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hin Hi Hn HA) as HAn.
  pose proof (glu_univ_elem_exp_cumu_ge_uidx Hin Hi Hn HM) as HMn.
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hjn Hj Hn HA') as HA'n.
  pose proof (glu_univ_elem_typ_unique_upto_exp_eq' Hn HAn HA'n) as HE.
  pose proof (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hn _ _ _ _ _ HMn HE) as HMn'.
  exact (glu_univ_elem_exp_lower_uidx Hjn Hj Hn HA' HMn').
Qed.

(** A type glued at a value of a lower index is glued at a related value
    of a higher one. *)
Lemma glu_typ_transfer : forall (i j k : uidx) a a' P El P' El' Γ A,
    uidx_le i j -> uidx_le k j -> Dom a ≈ a' ∈ per_univ k ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El -> DG a' ∈ glu_univ_elem j ↘ P' ↘ El' ->
    Γ ⊢ A ® P -> Γ ⊢ A ® P'.
Proof.
  intros * Hij Hkj [R HR] Hi Hj HA.
  destruct (glu_univ_elem_cumu_ge_uidx Hij Hi) as (Pj & Elj & Hgj).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hij Hi Hgj HA) as HAj.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R (per_univ_elem_cumu_uidx _ _ _ _ HR _ Hkj)) Hgj) as Hgj'.
  destruct (functional_glu_univ_elem _ _ _ _ _ _ Hgj' Hj) as [EP _].
  apply EP; exact HAj.
Qed.

(** An element of the relation of a domain's type, read at a related value. *)
Lemma dr_to_rel : forall B ρ b a1 c (i : uidx) R (jd : uidx), ⟦ B ⟧ ρ ↘ b -> Dom a1 ≈ b ∈ per_univ jd ->
    DF a1 ≈ a1 ∈ per_univ_elem i ↘ R -> per_head B B ρ ρ c c -> R c c.
Proof.
  intros * Eb [Rab HRab] HR Hc.
  pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRab) HRab) as Hbb.
  pose proof (Hc _ _ _ _ Eb Eb Hbb) as H.
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR HRab); exact H.
Qed.

Lemma sb_q_extend_wk : forall σ φ b, sb_eq ((q σ) ⨟ ((ι φ),,b)) ((sb_wk σ φ),,b).
Proof.
  intros σ φ b [| x]; [ reflexivity |].
  unfold sb_q, sb_extend, sb_wk; cbn.
  rewrite sentry_sub_wk, (sentry_sub_sb_eq _ _ (ι φ)) by (intros y; reflexivity).
  apply sentry_sub_of_wk.
Qed.

Section Comps.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)).
  Variable (ups : list domain) (bu : domain) (u : uidx) (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (IndSem.univ_idx bu) u)
    (HeN : forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b)
    (HNP : forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs)
    (HeA : forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b)
    (HAP : forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs)
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
       DG b ∈ glu_univ_elem u ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B).

  Lemma comps_params_wf : ⊢ ind_params D.
  Proof. exact (dt_params _ _ _ Hdt). Qed.

  (** A type of a context ending in the uniform parameters at the sort's
      universe, glued at the sort's universe's index at uniform parameters
      [ups]. *)
  Lemma sort_typ_glued : forall Pre A Sb Δ σ zs, ⊢ Pre ++ ind_uparams D -> List.length zs = List.length Pre ->
      EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ Sb -> Pre ++ ind_uparams D ⊩ A : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ ->
      Δ ⊢ˢ σ ® env_args nil (ups ++ zs) ∈ Sb ->
      exists a, ⟦ A ⟧ env_args nil (ups ++ zs) ↘ a /\ Dom a ≈ a ∈ per_univ (IndSem.univ_idx bu) /\
        forall P El, DG a ∈ glu_univ_elem (IndSem.univ_idx bu) ↘ P ↘ El -> Δ ⊢ A[σ] ® P.
  Proof.
    intros * HPre Hzs HSb HA Hσ.
    pose proof (dt_sort _ _ _ Hdt) as [iS HS].
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in HA, HS, Hbu; cbn [exp_wk] in HA.
    - destruct (glu_rel_exp_of_univ_inversion (u := ul i0) HSb HA _ _ _ Hσ) as (_ & a & Ha & Hpa & HP & _).
      inversion Hbu; subst; cbn [IndSem.univ_idx].
      exists a; split; [ exact Ha | split; [ exact Hpa | exact HP ] ].
    - destruct (glu_rel_exp_of_suniv_tm_inversion' HSb HA _ _ _ Hσ) as (l & Hlv & _ & _ & a & Ha & Hpa & HP & _).
      exists a; split; [ exact Ha |].
      assert (Hidx : IndSem.univ_idx bu = us (dlvl_real l)).
      { assert (HCs : ⊨ Pre ++ ind_uparams D) by (apply completeness_fundamental_ctx; exact HPre).
        assert (HSs : ind_uparams D ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
        destruct (rel_ctx_wf_per_ctx_env HCs) as [R HR].
        pose proof (glu_ctx_env_per_env HSb HR Hσ) as HE.
        assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length Pre)]ʷ ⟧ env_args nil (ups ++ zs) ↘ d_suniv l) by (cbn [exp_wk]; econstructor; exact Hlv).
        assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length Pre)⟫ (env_args nil (ups ++ zs)) ↘ bu)
          by (rewrite env_args_app, <- Hzs, UnitCases.eval_wk_shiftn_args; exact Hbu).
        pose proof (IndSem.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HR HE Eb Ea ltac:(right; eauto)) as Hi.
        rewrite Hi; reflexivity. }
      rewrite Hidx; split; [ exact Hpa | exact HP ].
  Qed.

  Lemma nparams_prefix_ass' : forall k, tele_ass (nparams_prefix D k ++ ind_uparams D).
  Proof.
    intros; destruct (IndCases.nparams_prefix_suffix D k) as [Δ HΔ].
    pose proof (decl_closed_params D Hc) as H; rewrite HΔ in H.
    apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma nparams_prefix_wf : forall k, ⊢ nparams_prefix D k ++ ind_uparams D.
  Proof.
    intros; destruct (IndCases.nparams_prefix_suffix D k) as [Δ HΔ].
    pose proof comps_params_wf as H; rewrite HΔ in H; eapply ctx_app_wf_tail; exact H.
  Qed.

  Lemma nparams_nparams_prefix_split' : forall k, exists Δ, ind_nparams D = Δ ++ nparams_prefix D k.
  Proof.
    intros; exists (List.rev (List.skipn k (List.rev (ind_nparams D)))).
    unfold nparams_prefix; rewrite <- List.rev_app_distr, List.firstn_skipn, List.rev_involutive; reflexivity.
  Qed.

  Lemma length_uparams' : List.length (ind_uparams D) = ind_nu D.
  Proof. apply length_ind_uparams, decl_closed_nu, Hc. Qed.

  Lemma comps_npar : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall k Ns ns T, List.length ns = k -> k < ind_nn D ->
        List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k = Some T ->
        (forall j N T' n, j < k -> List.nth_error Ns j = Some N ->
           List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T' ->
           List.nth_error ns j = Some n -> Δ ⊢ N : T' ® n ∈ NEl j (List.firstn j ns)) ->
        tele_pre (ind_nr D ups) k ns ns -> Δ ⊢ T ® NP k ns.
  Proof.
    intros Δ Us HΔ HUs k Ns ns T Hlk Hk HT Hpre Hp.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (decl_uparams_ass D Hc) as HassU.
    assert (Hk' : k < List.length (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams; lia).
    destruct (nparams_lt_ass D k Hass Hk') as [A HA].
    pose proof (gid_npar _ HG k A HA) as HV.
    pose proof HV as [SbC HSbC _ _].
    pose proof (nparams_prefix_ass' k) as HassC.
    pose proof (IndCases.length_nparams_prefix D k ltac:(lia)) as Hlpre.
    destruct (nparams_nparams_prefix_split' k) as [Δy HΔy].
    assert (HassN : tele_ass (nparams_prefix D k)) by (unfold tele_ass in HassC; apply List.Forall_app in HassC as [H _]; exact H).
    assert (HlNs : k < List.length Ns).
    { assert (Hs : List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) k <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by (apply Forall_firstn'; exact Hass); lia. }
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id (Us ++ List.firstn k Ns) ® env_args nil (ups ++ ns) ∈ SbC).
    { eapply glu_sub_of_list with (C := nparams_prefix D k ++ ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact HassC | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ |].
      apply glu_args_app; [ exact HassU | exact LU | rewrite length_uparams'; exact Hu |].
      split; [ exact HUs |].
      constructor; [ rewrite List.length_firstn; lia | lia |].
      intros j M T' v A' HM HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlk; apply List.nth_error_Some; congruence).
      rewrite List.nth_error_firstn in HM; destruct (Nat.ltb_spec j k); [| lia ].
      assert (HT'' : List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T').
      { rewrite HΔy, <- (List.firstn_skipn k Ns), tele_insts_app by (try exact HassN; rewrite List.length_firstn, Hlpre; lia).
        rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact HassN; rewrite List.length_firstn; lia); exact HT'. }
      assert (HA'' : List.nth_error (List.rev (ind_nparams D)) j = Some (ce_ass A')).
      { unfold nparams_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn in HA'.
        destruct (Nat.ltb_spec j k); [ exact HA' | lia ]. }
      pose proof (Hpre _ _ _ _ Hj HM HT'' Hv) as HMg.
      assert (Hpj : tele_pre (ind_nr D ups) j (List.firstn j ns) (List.firstn j ns)) by (eapply tele_pre_of_pre; [ exact Hp | lia ]).
      destruct (HeN _ _ _ HA'' Hpj) as [b Hb].
      pose proof (HNP _ _ _ _ HA'' Hpj Hb) as Hgb.
      apply (mk_glu_arg _ _ _ _ _ _ u b (NP j (List.firstn j ns)) (NEl j (List.firstn j ns)));
        [ rewrite <- env_args_app; exact Hb | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ]. }
    destruct (sort_typ_glued (nparams_prefix D k) A SbC Δ _ ns (nparams_prefix_wf k) ltac:(lia) HSbC ltac:(rewrite Hlpre; exact HV) Hσ)
      as (a & Ha & Hpb & HP).
    pose proof (HNP _ _ _ _ HA Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    destruct (tele_insts_nth _ _ _ _ _ HT) as (A0 & HA0 & ->).
    rewrite HA in HA0; injection HA0 as <-.
    rewrite <- sb_of_list_app.
    eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  Lemma glu_args_of_nparams : forall Δ Us Ns ns, glu_nparams D NEl Δ Us Ns ns ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      glu_args Δ (ind_nparams D) (sb_of_list Id Us) (env_args nil ups) Ns ns.
  Proof.
    intros * [L1 L2 H] Hns.
    constructor; [ rewrite L1; symmetry; apply length_nparams | rewrite L2; symmetry; apply length_nparams |].
    intros j M T v A HM HT Hv HA.
    pose proof (H _ _ _ _ HM HT Hv) as HMg.
    assert (Hj : j <= List.length (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams, <- L2; apply Nat.lt_le_incl, List.nth_error_Some; congruence).
    pose proof (tele_pre_of_full _ _ _ _ _ Hns Hj) as Hpj.
    destruct (HeN _ _ _ HA Hpj) as [b Hb].
    pose proof (HNP _ _ _ _ HA Hpj Hb) as Hgb.
    apply (mk_glu_arg _ _ _ _ _ _ u b (NP j (List.firstn j ns)) (NEl j (List.firstn j ns)));
      [ rewrite <- env_args_app; exact Hb | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HMg ].
  Qed.

  Lemma nonrec_args_prefix_ass : forall gs k, tele_ass (nonrec_args_prefix gs k).
  Proof.
    intros; unfold nonrec_args_prefix, tele_ass; apply List.Forall_rev, Forall_firstn'.
    apply List.Forall_map, List.Forall_forall; intros; eauto.
  Qed.

  Lemma comps_arg : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall c gs gs1 A0 gs2 Ns ns As vs T, ind_con D c = Some gs -> gs = gs1 ++ ca_arg A0 :: gs2 ->
        glu_nparams D NEl Δ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs) (nonrec_vals gs1 vs) ->
        Δ ⊢ T ® AP ns c (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs).
  Proof.
    intros Δ Us HΔ HUs c gs gs1 A0 gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (decl_uparams_ass D Hc) as HassU.
    assert (HassN : tele_ass (ind_nparams D)) by (apply Forall_firstn'; exact Hass).
    assert (HA0 : List.nth_error (cargs_nonrec gs) k = Some A0)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2 by lia; unfold k; rewrite Nat.sub_diag; reflexivity).
    assert (Hkn : k < List.length (cargs_nonrec gs)) by (apply List.nth_error_Some; congruence).
    pose proof (gid_arg _ HG c gs k A0 Hcon HA0) as HV.
    pose proof HV as [SbC HSbC _ _].
    assert (HlAs : List.length gs1 < List.length As).
    { assert (Hs : List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) <> None) by congruence.
      apply List.nth_error_Some in Hs; rewrite length_tele_insts in Hs by apply cargs_ctx_aux_ass; lia. }
    set (As1 := List.firstn (List.length gs1) As).
    assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_vals gs1 vs).
    assert (HlNs' : List.length Ns' = k) by (unfold Ns'; apply length_nonrec_exps; exact HlAs1).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_vals; exact Hvl).
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply IndCases.length_nonrec_args_prefix; lia).
    assert (Hσ : Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ Ns') ® env_args nil ((ups ++ ns) ++ vs') ∈ SbC).
    { eapply glu_sub_of_list with (C := nonrec_args_prefix gs k ++ ind_params D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ unfold tele_ass; apply List.Forall_app; split; [ apply nonrec_args_prefix_ass | exact Hass ]
        | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ |].
      apply glu_args_app; [ exact Hass | rewrite params_split, !List.length_app, LU, LN, length_nparams; lia
                          | rewrite params_split, !List.length_app, length_uparams', Hu, LNn, length_nparams; lia |].
      split.
      - rewrite params_split; apply glu_args_app; [ exact HassU | exact LU | rewrite length_uparams'; exact Hu |].
        split; [ exact HUs | exact (glu_args_of_nparams _ _ _ _ Hnp Hns) ].
      - constructor; [ lia | lia |].
        intros j M T' v A' HM HT' Hv HA'.
        assert (Hj : j < k) by (rewrite <- Hlvs'; apply List.nth_error_Some; congruence).
        assert (HA1 : List.nth_error (cargs_nonrec gs1) j = Some A').
        { unfold nonrec_args_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn, List.nth_error_map in HA'.
          destruct (Nat.ltb_spec j k); [| lia ].
          rewrite Heq, cargs_nonrec_app, List.nth_error_app1 in HA' by lia.
          destruct (List.nth_error (cargs_nonrec gs1) j); cbn in HA'; [ injection HA' as ->; reflexivity | discriminate ]. }
        destruct (IndCases.nonrec_nth_split _ _ _ HA1) as (hs1 & hs2 & Heq1 & Hlh).
        assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        destruct (nth_error_lt_some As (List.length hs1) ltac:(lia)) as [N HN].
        assert (HN1 : List.nth_error As1 (List.length hs1) = Some N)
          by (unfold As1; rewrite List.nth_error_firstn; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [ exact HN | lia ]).
        pose proof (nonrec_exps_nth_arg _ _ _ _ _ _ Heq1 HlAs1 HN1) as HN'.
        rewrite Hlh in HN'; fold Ns' in HN'; rewrite HN' in HM; injection HM as <-.
        destruct (nth_error_lt_some vs (List.length hs1) ltac:(lia)) as [v' Hv'].
        pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq1 Hvl Hv') as Hv''.
        rewrite Hlh in Hv''; fold vs' in Hv''; rewrite Hv'' in Hv; injection Hv as <-.
        assert (HTc : exists Tc, List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some Tc).
        { apply nth_error_lt_some; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx, Heq, List.length_app; cbn; lia. }
        destruct HTc as [Tc HTc].
        pose proof (Hpre _ _ _ _ _ _ Heq1 HN HTc Hv') as HNg.
        assert (Heqgs : gs = hs1 ++ ca_arg A' :: (hs2 ++ ca_arg A0 :: gs2)) by (rewrite Heq, Heq1, <- List.app_assoc; reflexivity).
        pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ Heqgs HTc) as ETc.
        rewrite exp_wk_pat_sb_of_list in ETc by (rewrite List.length_firstn; lia).
        destruct (tele_insts_nth _ _ _ _ _ HT') as (A2 & HA2 & ET').
        rewrite HA' in HA2; injection HA2 as <-.
        assert (Efn : List.firstn j Ns' = nonrec_exps hs1 (List.firstn (List.length hs1) As)).
        { unfold Ns'; rewrite <- Hlh, (nonrec_exps_firstn _ _ _ _ _ Heq1 HlAs1); unfold As1; rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity. }
        assert (Tc = T') as <- by (rewrite ETc, ET', Efn; reflexivity).
        assert (Efv : List.firstn j vs' = nonrec_vals hs1 (List.firstn (List.length hs1) vs))
          by (unfold vs'; rewrite <- Hlh; exact (nonrec_firstn _ _ _ _ _ Heq1 Hvl)).
        assert (Hpj : tele_pre (ind_ar D ups ns c) j (nonrec_vals hs1 (List.firstn (List.length hs1) vs))
                        (nonrec_vals hs1 (List.firstn (List.length hs1) vs)))
          by (rewrite <- Efv; eapply tele_pre_of_pre; [ exact Hp | lia ]).
        assert (HAj : List.nth_error (cargs_nonrec gs) j = Some A') by (rewrite Heq, cargs_nonrec_app, List.nth_error_app1 by lia; exact HA1).
        destruct (HeA _ _ _ _ _ _ Hns Hcon HAj Hpj) as [b Hb].
        pose proof (HAP _ _ _ _ _ _ _ Hns Hcon HAj Hpj Hb) as Hgb.
        rewrite Hlh in HNg.
        apply (mk_glu_arg _ _ _ _ _ _ u b (AP ns c j (nonrec_vals hs1 (List.firstn (List.length hs1) vs)))
          (AEl ns c j (nonrec_vals hs1 (List.firstn (List.length hs1) vs))));
          [ rewrite Efv, <- !env_args_app, <- List.app_assoc; exact Hb
          | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HNg ]. }
    assert (HPre : ⊢ (nonrec_args_prefix gs k ++ ind_nparams D) ++ ind_uparams D)
      by (rewrite <- List.app_assoc, <- params_split; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HV).
    assert (HSbC' : EG (nonrec_args_prefix gs k ++ ind_nparams D) ++ ind_uparams D ∈ glu_ctx_env ↘ SbC)
      by (rewrite <- List.app_assoc, <- params_split; exact HSbC).
    assert (HV' : (nonrec_args_prefix gs k ++ ind_nparams D) ++ ind_uparams D
                  ⊩ A0 : (ind_sort D)[wk_shiftn (List.length (nonrec_args_prefix gs k ++ ind_nparams D))]ʷ)
      by (rewrite <- List.app_assoc, <- params_split, List.length_app, Hlast, length_nparams; exact HV).
    rewrite <- List.app_assoc, <- List.app_assoc in Hσ.
    destruct (sort_typ_glued _ A0 SbC Δ _ (ns ++ vs') HPre ltac:(rewrite !List.length_app, Hlast, length_nparams; lia) HSbC' HV' Hσ)
      as (a & Ha & Hpb & HP).
    pose proof (HAP _ _ _ _ _ _ _ Hns Hcon HA0 Hp Ha) as Hga.
    destruct (per_univ_glu_univ_elem _ _ Hpb) as (Pb & Elb & Hgb).
    pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ Heq HT) as ET.
    rewrite exp_wk_pat_sb_of_list in ET by (rewrite List.length_firstn; lia).
    fold As1 in ET; fold Ns' in ET.
    rewrite ET, <- !sb_of_list_app, <- List.app_assoc.
    eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hga | exact (HP _ _ Hgb) ].
  Qed.

  (** Glued arguments of the non-uniform parameters' telescope are glued
      at the gluings of the clause, given the components. *)
  Lemma nparams_of_glu_args : forall Δ Us Ns ns, ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us ->
      glu_args Δ (ind_nparams D) (sb_of_list Id Us) (env_args nil ups) Ns ns ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      glu_nparams D NEl Δ Us Ns ns.
  Proof.
    intros * Hc0 Hg Hns.
    pose proof Hc0 as [HCN _ _].
    pose proof (decl_closed_params D Hc) as Hass.
    assert (HassN : tele_ass (ind_nparams D)) by (apply Forall_firstn'; exact Hass).
    pose proof Hg as [L1 L2 H].
    rewrite length_nparams in L1, L2.
    constructor; [ exact L1 | exact L2 |].
    enough (forall m, m <= ind_nn D -> forall j N T v, j < m -> List.nth_error Ns j = Some N ->
              List.nth_error (tele_insts (ind_nparams D) (sb_of_list Id Us) Ns) j = Some T ->
              List.nth_error ns j = Some v -> Δ ⊢ N : T ® v ∈ NEl j (List.firstn j ns)) as Hm.
    { intros j N T v HN HT Hv.
      assert (Hj : j < ind_nn D) by (rewrite <- L2; apply List.nth_error_Some; congruence).
      exact (Hm (ind_nn D) ltac:(lia) _ _ _ _ Hj HN HT Hv). }
    induction m as [| m IH]; intros Hm j N T v Hj HN HT Hv; [ lia |].
    destruct (Nat.eq_dec j m) as [-> | Hne]; [| eapply IH; eauto; lia ].
    assert (Hk' : m < List.length (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams; lia).
    destruct (nparams_lt_ass D m Hass Hk') as [A HA].
    destruct (H _ _ _ _ _ HN HT Hv HA) as [i' a P' El' Ha Hglu' HP' HM'].
    assert (Hpm : tele_pre (ind_nr D ups) m (List.firstn m ns) (List.firstn m ns))
      by (eapply tele_pre_of_full; [ exact Hns | rewrite List.length_rev, length_nparams; lia ]).
    rewrite <- env_args_app in Ha.
    pose proof (HNP _ _ _ _ HA Hpm Ha) as Hgu.
    assert (HTP : Δ ⊢ T ® NP m (List.firstn m ns)).
    { eapply (HCN m Ns (List.firstn m ns) T); [ rewrite List.length_firstn; lia | lia | exact HT | | exact Hpm ].
      intros j' N' T' v' Hj' HN' HT' Hv'.
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec j' m); [| discriminate ].
      eapply IH; eauto; lia. }
    eapply glu_univ_elem_exp_conv_uidx; [ eapply glu_univ_elem_per_univ; exact Hglu' | exact Hglu' | exact Hgu | exact HM' | exact HTP ].
  Qed.

  (** The substitution of the parameters and the non-recursive arguments
      before a position, glued at the context of the types there. *)
  Lemma nonrec_args_prefix_glu_sub : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall c gs gs1 g gs2 Ns ns As vs SbC, ind_con D c = Some gs -> gs = gs1 ++ g :: gs2 ->
        glu_nparams D NEl Δ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        List.length vs = List.length gs1 -> List.length gs1 <= List.length As ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs) (nonrec_vals gs1 vs) ->
        EG nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ nonrec_exps gs1 (List.firstn (List.length gs1) As))
          ® env_args nil ((ups ++ ns) ++ nonrec_vals gs1 vs) ∈ SbC.
  Proof.
    intros Δ Us HΔ HUs c gs gs1 g gs2 Ns ns As vs SbC Hcon Heq Hnp Hns Hvl HlAs Hpre Hp HSbC.
    set (k := List.length (cargs_nonrec gs1)) in *.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (decl_uparams_ass D Hc) as HassU.
    assert (HassN : tele_ass (ind_nparams D)) by (apply Forall_firstn'; exact Hass).
    assert (Hkn : k <= List.length (cargs_nonrec gs)) by (unfold k; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    set (As1 := List.firstn (List.length gs1) As).
    assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
    set (Ns' := nonrec_exps gs1 As1); set (vs' := nonrec_vals gs1 vs).
    assert (HlNs' : List.length Ns' = k) by (unfold Ns'; apply length_nonrec_exps; exact HlAs1).
    assert (Hlvs' : List.length vs' = k) by (unfold vs'; apply length_nonrec_vals; exact Hvl).
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (Hlast : List.length (nonrec_args_prefix gs k) = k) by (apply IndCases.length_nonrec_args_prefix; lia).
    eapply glu_sub_of_list with (C := nonrec_args_prefix gs k ++ ind_params D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ unfold tele_ass; apply List.Forall_app; split; [ apply nonrec_args_prefix_ass | exact Hass ]
      | rewrite List.app_nil_r; exact HSbC | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ |].
    apply glu_args_app; [ exact Hass | rewrite params_split, !List.length_app, LU, LN, length_nparams; lia
                        | rewrite params_split, !List.length_app, length_uparams', Hu, LNn, length_nparams; lia |].
    split.
    - rewrite params_split; apply glu_args_app; [ exact HassU | exact LU | rewrite length_uparams'; exact Hu |].
      split; [ exact HUs | exact (glu_args_of_nparams _ _ _ _ Hnp Hns) ].
    - constructor; [ lia | lia |].
      intros j M T' v A' HM HT' Hv HA'.
      assert (Hj : j < k) by (rewrite <- Hlvs'; apply List.nth_error_Some; congruence).
      assert (HA1 : List.nth_error (cargs_nonrec gs1) j = Some A').
      { unfold nonrec_args_prefix in HA'; rewrite List.rev_involutive, List.nth_error_firstn, List.nth_error_map in HA'.
        destruct (Nat.ltb_spec j k); [| lia ].
        rewrite Heq, cargs_nonrec_app, List.nth_error_app1 in HA' by lia.
        destruct (List.nth_error (cargs_nonrec gs1) j); cbn in HA'; [ injection HA' as ->; reflexivity | discriminate ]. }
      destruct (IndCases.nonrec_nth_split _ _ _ HA1) as (hs1 & hs2 & Heq1 & Hlh).
      assert (Hh : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
      destruct (nth_error_lt_some As (List.length hs1) ltac:(lia)) as [N HN].
      assert (HN1 : List.nth_error As1 (List.length hs1) = Some N)
        by (unfold As1; rewrite List.nth_error_firstn; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [ exact HN | lia ]).
      pose proof (nonrec_exps_nth_arg _ _ _ _ _ _ Heq1 HlAs1 HN1) as HN'.
      rewrite Hlh in HN'; fold Ns' in HN'; rewrite HN' in HM; injection HM as <-.
      destruct (nth_error_lt_some vs (List.length hs1) ltac:(lia)) as [v' Hv'].
      pose proof (nonrec_nth_arg _ _ _ _ _ _ Heq1 Hvl Hv') as Hv''.
      rewrite Hlh in Hv''; fold vs' in Hv''; rewrite Hv'' in Hv; injection Hv as <-.
      assert (HTc : exists Tc, List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some Tc).
      { apply nth_error_lt_some; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx, Heq, List.length_app; cbn; lia. }
      destruct HTc as [Tc HTc].
      pose proof (Hpre _ _ _ _ _ _ Heq1 HN HTc Hv') as HNg.
      assert (Heqgs : gs = hs1 ++ ca_arg A' :: (hs2 ++ g :: gs2)) by (rewrite Heq, Heq1, <- List.app_assoc; reflexivity).
      pose proof (cargs_arg_type _ _ _ _ _ _ _ _ _ Heqgs HTc) as ETc.
      rewrite exp_wk_pat_sb_of_list in ETc by (rewrite List.length_firstn; lia).
      destruct (tele_insts_nth _ _ _ _ _ HT') as (A2 & HA2 & ET').
      rewrite HA' in HA2; injection HA2 as <-.
      assert (Efn : List.firstn j Ns' = nonrec_exps hs1 (List.firstn (List.length hs1) As)).
      { unfold Ns'; rewrite <- Hlh, (nonrec_exps_firstn _ _ _ _ _ Heq1 HlAs1); unfold As1; rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity. }
      assert (Tc = T') as <- by (rewrite ETc, ET', Efn; reflexivity).
      assert (Efv : List.firstn j vs' = nonrec_vals hs1 (List.firstn (List.length hs1) vs))
        by (unfold vs'; rewrite <- Hlh; exact (nonrec_firstn _ _ _ _ _ Heq1 Hvl)).
      assert (Hpj : tele_pre (ind_ar D ups ns c) j (nonrec_vals hs1 (List.firstn (List.length hs1) vs))
                      (nonrec_vals hs1 (List.firstn (List.length hs1) vs)))
        by (rewrite <- Efv; eapply tele_pre_of_pre; [ exact Hp | lia ]).
      assert (HAj : List.nth_error (cargs_nonrec gs) j = Some A') by (rewrite Heq, cargs_nonrec_app, List.nth_error_app1 by lia; exact HA1).
      destruct (HeA _ _ _ _ _ _ Hns Hcon HAj Hpj) as [b Hb].
      pose proof (HAP _ _ _ _ _ _ _ Hns Hcon HAj Hpj Hb) as Hgb.
      rewrite Hlh in HNg.
      apply (mk_glu_arg _ _ _ _ _ _ u b (AP ns c j (nonrec_vals hs1 (List.firstn (List.length hs1) vs)))
        (AEl ns c j (nonrec_vals hs1 (List.firstn (List.length hs1) vs))));
        [ rewrite Efv, <- !env_args_app, <- List.app_assoc; exact Hb
        | exact Hgb | eapply glu_univ_elem_trm_typ; eassumption | exact HNg ].
  Qed.

  (** The parameters of the type of a recursive argument, at an instance
      [Us ++ Ys] of the context of its shape glued to [ups ++ ns ++ nv ++ ys],
      are glued at the non-uniform parameters' telescope to their values. *)
  Lemma rec_params_args : valid_ind_decl D -> forall Δ c gs gs1 t gs2 τ Us Ys ns nv ys SbC bsr,
      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      List.length Us = ind_nu D -> List.length Ys = ptyp_depth t + List.length (cargs_nonrec gs1) + ind_nn D ->
      List.length ns = ind_nn D -> List.length nv = List.length (cargs_nonrec gs1) -> List.length ys = ptyp_depth t ->
      EG ptyp_tele t ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D ∈ glu_ctx_env ↘ SbC ->
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC ->
      eval_exps gc_deps gc_stack (ptyp_ps t) (env_args nil (ups ++ ns ++ nv ++ ys)) bsr ->
      glu_args Δ (ind_nparams D) (sb_of_list Id Us) (env_args nil ups)
        (List.map (fun P => P[sb_of_list τ (Us ++ Ys)]) (ptyp_ps t)) bsr.
  Proof.
    intros HDc Δ c gs gs1 t gs2 τ Us Ys ns nv ys SbC bsr Hcon Heq HUl HYl Hnsl Hnvl Hysl HSbC Hσ Hbsr.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (L := ptyp_depth t + K + ind_nn D) in *.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (ρ := env_args nil (ups ++ ns ++ nv ++ ys)) in *.
    pose proof (IndCases.length_rec_ps D Hc c gs gs1 t gs2 Hcon Heq) as HPl.
    pose proof (IndCases.eval_exps_length _ _ _ Hbsr) as Hbl.
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    constructor; [ rewrite List.length_map, length_nparams; exact HPl | rewrite length_nparams; lia |].
    intros k M T v A HM HT Hv HA.
    rewrite List.nth_error_map in HM.
    destruct (List.nth_error (ptyp_ps t) k) as [P |] eqn:HP; [ injection HM as <- | discriminate ].
    assert (Hk : k < ind_nn D) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn L)) (ptyp_ps t)) k) as [Tk HTk].
    { rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc); rewrite length_nparams; lia. }
    pose proof (rec_tele_inst D (ptyp_ps t) L τ Us Ys k Tk Hc HUl HYl HTk) as HT'.
    fold σ in HT'; rewrite HT in HT'; injection HT' as ->.
    destruct (tele_insts_nth _ _ _ _ _ HTk) as (A0 & HA0 & ETk).
    rewrite HA in HA0; injection HA0 as <-.
    destruct (gid_rec _ HG c gs gs1 t gs2 k P Tk Hcon Heq HP HTk) as [SbC' HSbC' j HV].
    pose proof (functional_glu_ctx_env HSbC HSbC') as ESb.
    assert (Hσ' : Δ ⊢ˢ σ ® ρ ∈ SbC') by (apply ESb; exact Hσ).
    destruct (HV _ _ _ Hσ') as [a1 m1 P1 El1 Ha1 Hm1 Hg1 HM1].
    destruct (IndCases.eval_exps_nth _ _ _ _ _ Hbsr HP) as (v' & Hv' & Ev').
    rewrite Hv in Hv'; injection Hv' as <-.
    assert (m1 = v) as -> by (eapply functional_eval_exp; eassumption).
    (** The value of the type of the parameter, at the arguments' values, is
        related to the one at the parameters' before it. *)
    destruct (vid_npar _ HDc _ _ HA) as (_ & j0 & HAv).
    assert (HΞ0 : ⊨ ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_params D).
    { pose proof (vid_dctx _ HDc _ _ _ _ _ (List.length (ptyp_doms t)) Hcon Heq (le_n _)) as H.
      rewrite List.firstn_all in H; exact H. }
    destruct (rel_ctx_wf_per_ctx_env HΞ0) as [R0 HR0].
    pose proof (glu_ctx_env_per_env HSbC' HR0 Hσ') as HE.
    pose proof (rec_sub_valid D HDc Hc c gs gs1 t gs2 Hcon Heq k (Nat.lt_le_incl _ _ Hk)) as Hτ.
    assert (Hτev : ⟦ sb_of_list (sb_of_wk (wk_shiftn L)) (List.firstn k (ptyp_ps t)) ⟧s ρ ↘ env_args (env_args nil ups) (List.firstn k bsr)).
    { apply IndSem.eval_sb_of_list; [| apply eval_exps_firstn; exact Hbsr ].
      replace (env_args nil ups) with (⟪wk_shiftn L⟫ ρ); [ apply eval_sub_of_wk; apply UnitCases.wk_mono_shiftn |].
      unfold ρ, L; rewrite env_args_app.
      replace (ptyp_depth t + K + ind_nn D) with (List.length (ns ++ nv ++ ys)) by (rewrite !List.length_app; lia).
      apply UnitCases.eval_wk_shiftn_args. }
    destruct (TeleSem.typ_inst_link _ _ _ _ _ _ _ _ _ HAv HR0 Hτ HE Hτev) as (a & b & Ea & Eb & Hab).
    fold K L in Ea; rewrite <- ETk in Ea.
    assert (a = a1) as -> by (eapply functional_eval_exp; eassumption).
    destruct (glu_transfer_per j j0 a1 b P1 El1 Δ _ _ v Hg1 Hab ltac:(eapply glu_univ_elem_trm_typ; eassumption) HM1)
      as (k' & P' & El' & Hg' & HT' & HM').
    exact (mk_glu_arg _ _ _ _ _ _ k' b P' El' Eb Hg' HT' HM').
  Qed.

  (** A glued instance of a shape's context after [k] domains, weakened and
      extended by an argument glued at the next domain's gluing. *)
  Lemma shape_sub_step : forall c gs gs1 t gs2 k B ns nv ys Δ τ Us Ys SbC SbC' Δ' φ b b0 c',
      ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) k = Some B ->
      EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
        ∈ glu_ctx_env ↘ SbC ->
      EG doms_ctx (List.firstn (S k) (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
        ∈ glu_ctx_env ↘ SbC' ->
      Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC -> Δ' ⊢ᵏ φ : Δ ->
      ⟦ B ⟧ env_args nil (ups ++ ns ++ nv ++ ys) ↘ b0 ->
      DG b0 ∈ glu_univ_elem u ↘ DP (ns ++ nv ++ ys) B ↘ DEl (ns ++ nv ++ ys) B ->
      Δ' ⊢ B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® DP (ns ++ nv ++ ys) B ->
      Δ' ⊢ b : B[sb_of_list τ (Us ++ Ys)][φ]ʷ ® c' ∈ DEl (ns ++ nv ++ ys) B ->
      Δ' ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))
        ® env_args nil (ups ++ ns ++ nv ++ ys ++ c' :: nil) ∈ SbC'.
  Proof.
    intros * Hcon Heq HB HSbC HSbC' Hσ Hφ Hb0 Hgb0 HTy Hb.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    pose proof HSbC' as HSbC''.
    rewrite (firstn_S_snoc _ _ _ HB), IndCases.doms_ctx_snoc in HSbC''; cbn [List.app] in HSbC''.
    assert (Hσ' : Δ' ⊢ˢ (sb_wk σ φ),,b ® env_args nil (ups ++ ns ++ nv ++ ys) ↦ c' ∈ SbC').
    { eapply glu_sub_snoc; [ exact HSbC | exact HSbC'' | eapply glu_ctx_env_sub_monotone; eassumption |].
      rewrite <- exp_wk_sub.
      exact (mk_glu_arg _ _ _ _ _ _ u b0 (DP (ns ++ nv ++ ys) B) (DEl (ns ++ nv ++ ys) B) Hb0 Hgb0 HTy Hb). }
    assert (Esb : sb_eq ((sb_wk σ φ),,b) (sb_of_list (sb_wk τ φ) (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys) ++ b :: nil))).
    { rewrite (sb_of_list_app (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys)) (b :: nil)); cbn [sb_of_list].
      apply sb_extend_cong; unfold σ; apply sb_wk_sb_of_list. }
    rewrite List.map_app, <- List.app_assoc in Esb.
    replace (ups ++ ns ++ nv ++ ys ++ c' :: nil) with ((ups ++ ns ++ nv ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    rewrite env_args_snoc.
    eapply glu_ctx_env_sub_resp_sub_eq; [ exact HSbC' | exact Hσ' |].
    eapply wf_sub_eq_of_sb_eq; [ eapply glu_ctx_env_sub_escape; eassumption | exact Esb ].
  Qed.

  (** The type of a recursive argument after [k] of its shape's domains, at
      an instance [Us ++ Ys] of the shape's context glued to its values, is
      glued at the gluings of the domains. *)
  Lemma shape_typ_glu : forall c gs gs1 t gs2 ns nv, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) nv nv ->
      List.length ns = ind_nn D -> List.length nv = List.length (cargs_nonrec gs1) ->
      forall t' k ys Δ τ Us Ys SbC, ptyp_skip k t = t' -> k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr (ind_dr ups) ns nv (ptyp_doms t)) k ys ys -> ⊢ Δ ->
        List.length Us = ind_nu D -> List.length Ys = k + List.length (cargs_nonrec gs1) + ind_nn D ->
        EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nv ++ ys) ∈ SbC ->
        glu_shape_typ ups DP DEl Δ (ns ++ nv ++ ys) t' (ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) t').
  Proof.
    intros c gs gs1 t gs2 ns nv Hcon Heq Hns Hnv Hnsl Hnvl t'.
    set (K := List.length (cargs_nonrec gs1)) in *.
    assert (HKl : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    induction t' as [? ? | ? ? | B t'' IH]; intros k ys Δ τ Us Ys SbC Hsk Hk Hy HΔ HUl HYl HSbC Hσ;
      cbn [glu_shape_typ]; [ exact I | exact I |].
    intros IT OT HT; cbn [ptyp_ty_at] in HT; injection HT as <- <-.
    destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
    assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
    pose proof (gid_dom _ HG _ _ _ _ _ _ _ Hcon Heq HB) as HBv.
    destruct (HeD _ _ _ _ _ _ _ _ _ _ Hns Hcon Heq Hnv HB Hy) as [b0 Hb0].
    pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ Hns Hcon Heq Hnv HB Hy Hb0) as Hgb0.
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Pre := doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ ind_nparams D).
    assert (EPre : doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs K ++ ind_params D = Pre ++ ind_uparams D)
      by (unfold Pre; rewrite params_split, <- !List.app_assoc; reflexivity).
    assert (HlPre : List.length Pre = k + K + ind_nn D)
      by (unfold Pre; rewrite !List.length_app, doms_ctx_length, List.length_firstn, IndCases.length_nonrec_args_prefix, length_nparams
            by exact HKl; lia).
    assert (HPre : ⊢ Pre ++ ind_uparams D)
      by (rewrite <- EPre; eapply presup_exp_ctx; eapply glu_rel_exp_to_wf_exp; exact HBv).
    assert (HSbCp : EG Pre ++ ind_uparams D ∈ glu_ctx_env ↘ SbC) by (rewrite <- EPre; exact HSbC).
    assert (HBvp : Pre ++ ind_uparams D ⊩ B : (ind_sort D)[wk_shiftn (List.length Pre)]ʷ) by (rewrite <- EPre, HlPre; exact HBv).
    (** The domain, glued at its gluing at every weakening. *)
    assert (HTy : forall Δ' φ, Δ' ⊢ᵏ φ : Δ -> Δ' ⊢ B[σ][φ]ʷ ® DP (ns ++ nv ++ ys) B).
    { intros Δ' φ Hφ.
      pose proof (glu_ctx_env_sub_monotone _ _ HSbC _ _ _ _ _ Hσ Hφ) as Hσφ.
      destruct (sort_typ_glued Pre B SbC Δ' (sb_wk σ φ) (ns ++ nv ++ ys) HPre
                  ltac:(rewrite HlPre, !List.length_app; destruct Hy as [Hyl _]; lia) HSbCp HBvp Hσφ) as (a & Ha & Hpa & HP).
      assert (a = b0) as -> by (eapply functional_eval_exp; eassumption).
      destruct (per_univ_glu_univ_elem _ _ Hpa) as (Pb & Elb & Hgb).
      rewrite exp_wk_sub.
      eapply glu_univ_elem_typ_cumu_ge_uidx; [ exact Hule | exact Hgb | exact Hgb0 | exact (HP _ _ Hgb) ]. }
    split; [ exact HTy |].
    intros Δ' φ b c' Hφ Hc' Hb.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    destruct (gid_dctx _ HG _ _ _ _ _ (S k) Hcon Heq ltac:(lia)) as [SbC' HSbC'].
    pose proof HSbC' as HSbC''.
    rewrite (firstn_S_snoc _ _ _ HB), IndCases.doms_ctx_snoc in HSbC''; cbn [List.app] in HSbC''.
    assert (Hσ' : Δ' ⊢ˢ (sb_wk σ φ),,b ® env_args nil (ups ++ ns ++ nv ++ ys) ↦ c' ∈ SbC').
    { eapply glu_sub_snoc; [ exact HSbC | exact HSbC'' | eapply glu_ctx_env_sub_monotone; eassumption |].
      rewrite <- exp_wk_sub.
      exact (mk_glu_arg _ _ _ _ _ _ u b0 (DP (ns ++ nv ++ ys) B) (DEl (ns ++ nv ++ ys) B) Hb0 Hgb0 (HTy _ _ Hφ) Hb). }
    assert (Esb : sb_eq ((sb_wk σ φ),,b) (sb_of_list (sb_wk τ φ) (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys) ++ b :: nil))).
    { rewrite (sb_of_list_app (List.map (fun Y => Y[φ]ʷ) (Us ++ Ys)) (b :: nil)); cbn [sb_of_list].
      apply sb_extend_cong; unfold σ; apply sb_wk_sb_of_list. }
    rewrite List.map_app, <- List.app_assoc in Esb.
    assert (Hσ'' : Δ' ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))
                     ® env_args nil (ups ++ ns ++ nv ++ ys ++ c' :: nil) ∈ SbC').
    { replace (ups ++ ns ++ nv ++ ys ++ c' :: nil) with ((ups ++ ns ++ nv ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
      rewrite env_args_snoc.
      eapply glu_ctx_env_sub_resp_sub_eq; [ exact HSbC' | exact Hσ' |].
      eapply wf_sub_eq_of_sb_eq; [ eapply glu_ctx_env_sub_escape; eassumption | exact Esb ]. }
    unfold σ; rewrite ptyp_ty_at_shape_step.
    replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    apply (IH (S k) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil) SbC');
      [ exact Hs' | lia | | exact HΔ' | rewrite List.length_map; exact HUl
      | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'' ].
    apply tele_pre_snoc; [ exact Hy |].
    unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
  Qed.

  (** The types of the recursive arguments, at uniform parameters glued to
      [ups], are glued at the gluings of the domains of their shapes. *)
  Lemma comps_rec : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      forall c gs gs1 t gs2 Ns ns As vs T, ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
        glu_nparams D NEl Δ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
        List.length vs = List.length gs1 ->
        List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length gs1) = Some T ->
        (forall hs1 B hs2 N T' v, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
           List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
           List.nth_error vs (List.length hs1) = Some v ->
           Δ ⊢ N : T' ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) vs))) ->
        tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 vs) (nonrec_vals gs1 vs) ->
        glu_shape_typ ups DP DEl Δ (ns ++ nonrec_vals gs1 vs) t T.
  Proof.
    intros Δ Us HΔ HUs c gs gs1 t gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp.
    pose proof (dc_nu _ Hc) as Hle.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; rewrite length_uparams' in LU.
    pose proof Hnp as [LN LNn _].
    assert (HlAs : List.length gs1 < List.length As).
    { destruct (Nat.lt_ge_cases (List.length gs1) (List.length As)) as [| Hge]; [ assumption |].
      rewrite (proj2 (List.nth_error_None _ _)) in HT; [ discriminate |].
      rewrite length_tele_insts by apply cargs_ctx_aux_ass; subst gs; lia. }
    destruct (gid_dctx _ HG _ _ _ _ _ 0 Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
    cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
    pose proof (nonrec_args_prefix_glu_sub Δ Us HΔ HUs c gs gs1 (ca_rec t) gs2 Ns ns As vs SbC0 Hcon Heq Hnp Hns Hvl ltac:(lia) Hpre Hp HSbC0) as Hσ.
    pose proof (cargs_rec_type_sh p D gs gs1 t gs2 (Us ++ Ns) As T Heq Hle ltac:(rewrite List.length_app, LU, LN; unfold ind_nn; lia) HT) as ET.
    rewrite firstn_app_exact in ET by exact LU.
    assert (Hlnv : List.length (nonrec_vals gs1 vs) = List.length (cargs_nonrec gs1)) by (apply length_nonrec_vals; exact Hvl).
    pose proof (shape_typ_glu c gs gs1 t gs2 ns (nonrec_vals gs1 vs) Hcon Heq Hns Hp LNn Hlnv t 0 nil Δ Id Us
                  (Ns ++ nonrec_exps gs1 (List.firstn (List.length gs1) As)) SbC0 eq_refl ltac:(lia) (tele_pre_nil _) HΔ LU) as H.
    rewrite !List.app_nil_r, List.app_assoc in H.
    rewrite ET, <- List.app_assoc; apply H.
    - rewrite List.length_app, length_nonrec_exps by (rewrite List.length_firstn; lia); lia.
    - cbn [List.firstn doms_ctx List.map List.rev List.app]; exact HSbC0.
    - rewrite <- !List.app_assoc in Hσ; exact Hσ.
  Qed.

  (** The components, at uniform parameters glued to [ups]. *)
  Lemma comps_of_uparams : forall Δ Us, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us.
  Proof.
    intros * HΔ HUs; constructor.
    - intros k Ns ns T Hl' Hk HT Hpre Hp; eapply comps_npar; eassumption.
    - intros c gs gs1 A0 gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply comps_arg; eassumption.
    - intros c gs gs1 t gs2 Ns ns As vs T Hcon Heq Hnp Hns Hvl HT Hpre Hp; eapply comps_rec; eassumption.
  Qed.

End Comps.

(** ** The Type Former at Glued Parameters *)

Section Former.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)).

  Lemma comps_params_wf' : ⊢ ind_params D.
  Proof. exact (dt_params _ _ _ Hdt). Qed.

  Lemma params_uparams_typed : forall Δ Ms,
      List.length Ms = ind_np D ->
      (forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T -> Δ ⊢ M : T) ->
      forall k U T, List.nth_error (List.firstn (ind_nu D) Ms) k = Some U ->
        List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ms)) k = Some T -> Δ ⊢ U : T.
  Proof.
    intros * HMl HMs k U T HU HT.
    pose proof (decl_closed_nu D Hc) as Hle.
    apply (HMs k).
    - rewrite List.nth_error_firstn in HU; destruct (Nat.ltb_spec k (ind_nu D)); [ exact HU | discriminate ].
    - rewrite <- (List.firstn_skipn (ind_nu D) Ms), params_split, tele_insts_app
        by (try apply (decl_uparams_ass D Hc); rewrite List.length_firstn, length_ind_uparams by exact Hle; unfold ind_np in *; lia).
      rewrite List.nth_error_app1; [ exact HT |].
      apply List.nth_error_Some; congruence.
  Qed.

  Lemma ind_sort_le : forall Δ Ms bu ups, ⊢ Δ -> List.length Ms = ind_np D ->
      (forall k M T, List.nth_error Ms k = Some M -> List.nth_error (tele_insts (ind_params D) Id Ms) k = Some T -> Δ ⊢ M : T) ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ bu ->
      Δ ⊢ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms] ⊆ Typeω@(ulvl (IndSem.univ_idx bu)).
  Proof.
    intros * HΔ HMl HMs Hbu.
    pose proof (decl_closed_nu D Hc) as Hle.
    assert (HUl : List.length (List.firstn (ind_nu D) Ms) = ind_nu D) by (rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (Hσ : Δ ⊢ˢ sb_of_list Id (List.firstn (ind_nu D) Ms) : ind_uparams D ++ Δ)
      by (eapply wf_sub_uparams; [ exact Hdt | exact Hc | exact HΔ | exact HUl | eapply params_uparams_typed; eassumption ]).
    destruct (sort_lvl_at _ _ _ Hdt Hc _ _ HΔ Hσ) as [n Hn].
    rewrite <- (List.firstn_skipn (ind_nu D) Ms) at 1.
    replace (ind_nn D) with (List.length (List.skipn (ind_nu D) Ms)) by (rewrite List.length_skipn; unfold ind_nn, ind_np in *; lia).
    rewrite exp_shift_past.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hbu, Hn |- *; inversion Hbu; subst; cbn [IndSem.univ_idx ulvl exp_sub].
    - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
    - cbn in Hn; eapply wf_subtyp_small_large; eassumption.
  Qed.

  Lemma glu_args_uparams_of_params : forall Δ Ms vs, glu_args Δ (ind_params D) Id nil Ms vs ->
      glu_args Δ (ind_uparams D) Id nil (List.firstn (ind_nu D) Ms) (List.firstn (ind_nu D) vs).
  Proof.
    intros * Hg.
    pose proof (decl_closed_nu D Hc) as Hle.
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [L1 L2].
    rewrite <- (List.firstn_skipn (ind_nu D) Ms), <- (List.firstn_skipn (ind_nu D) vs), params_split in Hg.
    apply glu_args_app in Hg; [ exact (proj1 Hg) | exact (decl_uparams_ass D Hc) | |];
      rewrite List.length_firstn, length_ind_uparams by exact Hle; unfold ind_np in *; lia.
  Qed.

  Lemma ind_typ_at_of_args : forall Δ Ms ups ns bu (u : uidx) NP NEl AP AEl DP DEl, ⊢ Δ ->
      glu_args Δ (ind_params D) Id nil Ms (ups ++ ns) -> List.length ups = ind_nu D ->
      ⟦ ind_sort D ⟧ env_args nil ups ↘ bu -> uidx_le (IndSem.univ_idx bu) u ->
      (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) ->
      (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
         tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs) ->
      (forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
         tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) ->
      (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
         tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs) ->
      (forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
         exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) ->
      (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
         ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
         tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
         List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
         ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
         DG b ∈ glu_univ_elem u ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B) ->
      ind_typ_at p D ups ns NP NEl AP AEl DP DEl Typeω@(ulvl u) Δ (apps (a_ind p) Ms) Ms.
  Proof.
    intros * HΔ Hg Hu Hbu Hule HeN HNP HeA HAP HeD HDP.
    assert (Hsub : forall Δ' Ms', ⊢ Δ' -> List.length Ms' = ind_np D ->
              (forall k M T, List.nth_error Ms' k = Some M -> List.nth_error (tele_insts (ind_params D) Id Ms') k = Some T -> Δ' ⊢ M : T) ->
              Δ' ⊢ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms'] ⊆ Typeω@(ulvl u)).
    { intros Δ' Ms' HΔ'0 HMl' HMs'.
      eapply wf_subtyp_trans; [ eapply ind_sort_le; eassumption |].
      pose proof (uidx_le_ulvl_le _ _ Hule) as Hlv.
      destruct (Nat.eq_dec (ulvl (IndSem.univ_idx bu)) (ulvl u)) as [-> | Hne].
      - eapply wf_subtyp_refl'; apply wf_exp_eq_refl; mauto 3.
      - apply wf_subtyp_univ; [ exact HΔ'0 | lia ]. }
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    destruct (glu_args_params_top _ _ _ _ Hass Hs Hg) as [HMl HMs _].
    split.
    - eapply wf_exp_eq_subtyp'; [| eapply Hsub; eassumption ].
      eapply wf_exp_eq_ind_apps; [ exact Hl | exact HΔ | exact HMl | exact HMl |].
      intros k N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; eapply HMs; eassumption.
    - intros Δ' φ Hφ.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      pose proof (glu_args_wk _ _ _ _ _ _ _ Hass Hs Hφ Hg) as Hg'.
      pose proof (glu_args_params_top _ _ _ _ Hass Hs Hg') as Htop.
      split; [ exact Htop | split ].
      + destruct Htop as [HMl' HMs' _]; eapply Hsub; eassumption.
      + intros Ps' HPs'.
        pose proof (glu_args_resp_eq _ _ _ _ _ _ Hass comps_params_wf' HΔ' HPs' Hg') as Hg''.
        pose proof (glu_args_uparams_of_params _ _ _ Hg'') as HUs.
        rewrite <- Hu, firstn_app_exact in HUs by reflexivity; rewrite Hu in HUs.
        eapply (comps_of_uparams p D); eassumption.
  Qed.

  (** The gluing of an inductive type in the PER model. *)
  Lemma ind_glu_elem_of_per : forall (u : uidx) R ups ns,
      DF d_ind p (ups ++ ns) ≈ d_ind p (ups ++ ns) ∈ per_univ_elem u ↘ R -> List.length ups = ind_nu D ->
      exists NP NEl AP AEl DP DEl P El R',
        DG d_ind p (ups ++ ns) ∈ glu_univ_elem u ↘ P ↘ El /\
        (P <∙> ind_glu_typ_pred p D ups ns NP NEl AP AEl DP DEl Typeω@(ulvl u)) /\
        (El <∙> ind_glu_exp_pred p D ups ns NP NEl AP AEl DP DEl R' Typeω@(ulvl u)) /\ (R <~> R') /\
        (forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
           tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b) /\
        (forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
           tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
           DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs) /\
        (forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
           ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
           tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b) /\
        (forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
           ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
           tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
           DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs) /\
        (forall ms c gs gs1 t gs2 ws k B ys, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
           ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
           tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
           List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
           exists b, ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b) /\
        (forall ms c gs gs1 t gs2 ws k B ys b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
           ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
           tele_pre (ind_ar D ups ms c) (List.length (cargs_nonrec gs1)) ws ws ->
           List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr (ind_dr ups) ms ws (ptyp_doms t)) k ys ys ->
           ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ b ->
           DG b ∈ glu_univ_elem u ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B).
  Proof.
    intros * HR Hu.
    destruct (per_univ_glu_univ_elem u _ (ex_intro _ R HR)) as (P & El & Hglu).
    pose proof Hglu as Hglu'.
    invert_glu_univ_elem Hglu'.
    match goal with H : ind_lookup _ _ p = Some ?D0 |- _ => assert (D0 = D) as -> by congruence end.
    match goal with H : ?w ++ ?x = ups ++ ns, H' : List.length ?w = ind_nu D |- _ =>
      destruct (app_split_eq _ _ _ _ H ltac:(congruence)) as [-> ->] end.
    handle_per_univ_elem_irrel.
    do 9 eexists; split; [ exact Hglu |].
    split; [ eassumption | split; [ eassumption | split; [ reflexivity | split; [ eassumption | split; [ eassumption |
      split; [ eassumption | split; [ eassumption | split; [ eassumption | eassumption ] ] ] ] ] ] ] ].
  Qed.


  Lemma glu_sub_params : forall Δ Ms vs Sb, ⊢ Δ -> EG ind_params D ∈ glu_ctx_env ↘ Sb ->
      glu_args Δ (ind_params D) Id nil Ms vs -> Δ ⊢ˢ sb_of_list Id Ms ® env_args nil vs ∈ Sb.
  Proof.
    intros * HΔ HSb Hg.
    eapply glu_sub_of_list with (C := ind_params D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ exact (decl_closed_params D Hc) | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ | exact Hg ].
  Qed.

  Lemma glu_sub_uparams : forall Δ Us ups Sb, ⊢ Δ -> EG ind_uparams D ∈ glu_ctx_env ↘ Sb ->
      glu_args Δ (ind_uparams D) Id nil Us ups -> Δ ⊢ˢ sb_of_list Id Us ® env_args nil ups ∈ Sb.
  Proof.
    intros * HΔ HSb Hg.
    eapply glu_sub_of_list with (C := ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
      [ exact (decl_uparams_ass D Hc) | rewrite List.app_nil_r; exact HSb | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
      | cbn; apply wf_sub_nil'; exact HΔ | exact Hg ].
  Qed.

  (** The universe of the sort at the parameters' values is the one at the
      uniform ones. *)
  Lemma sort_idx_params : forall Δ Ms vs b, ⊢ Δ -> glu_args Δ (ind_params D) Id nil Ms vs ->
      ⟦ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ ⟧ env_args nil vs ↘ b ->
      exists bu, ⟦ ind_sort D ⟧ env_args nil (List.firstn (ind_nu D) vs) ↘ bu /\ IndSem.univ_idx bu = IndSem.univ_idx b.
  Proof.
    intros * HΔ Hg Hb.
    pose proof (dc_nu _ Hc) as Hle.
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hvl].
    pose proof (dt_params _ _ _ Hdt) as HΔP; pose proof (dt_sort _ _ _ Hdt) as [iS HS].
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb, HS |- *; cbn [exp_wk] in Hb.
    - inversion Hb; subst; exists (d_univ i0); split; [ constructor | reflexivity ].
    - inversion Hb; subst.
      match goal with Hlv : ⟦ t[wk_shiftn _]ʷ ⟧ _ ↘ ?l |- _ => rename l into lv; rename Hlv into Hlv0 end.
      destruct (gid_lvl _ HG) as [n HLu]; rewrite Heq in HLu; cbn [ind_sort_lvl] in HLu.
      pose proof HLu as [SbU HSbU _ _].
      pose proof (glu_sub_uparams _ _ _ _ HΔ HSbU (glu_args_uparams_of_params _ _ _ Hg)) as Hσu.
      destruct (glu_rel_exp_level_elim HSbU HLu _ _ _ Hσu) as (l' & Hl' & _).
      exists (d_suniv l'); split; [ econstructor; exact Hl' |].
      destruct (gid_params _ HG) as [SbP HSbP].
      pose proof (glu_sub_params _ _ _ _ HΔ HSbP Hg) as Hσ.
      assert (HCs : ⊨ ind_nparams D ++ ind_uparams D) by (rewrite <- params_split; apply completeness_fundamental_ctx; exact HΔP).
      assert (HSs : ind_uparams D ⊨ Type⟨t⟩ : Typeω@iS) by (apply completeness_fundamental_exp; exact HS).
      destruct (rel_ctx_wf_per_ctx_env HCs) as [R HR].
      rewrite <- params_split in HR.
      pose proof (glu_ctx_env_per_env HSbP HR Hσ) as HE.
      rewrite params_split in HR.
      assert (Eb : ⟦ Type⟨t⟩[wk_shiftn (List.length (ind_nparams D))]ʷ ⟧ env_args nil vs ↘ d_suniv lv)
        by (rewrite length_nparams; cbn [exp_wk]; econstructor; exact Hlv0).
      assert (Ea : ⟦ Type⟨t⟩ ⟧ ⟪wk_shiftn (List.length (ind_nparams D))⟫ (env_args nil vs) ↘ d_suniv l').
      { replace (env_args nil vs) with (env_args (env_args nil (List.firstn (ind_nu D) vs)) (List.skipn (ind_nu D) vs))
          by (rewrite <- env_args_app, List.firstn_skipn; reflexivity).
        replace (List.length (ind_nparams D)) with (List.length (List.skipn (ind_nu D) vs))
          by (rewrite List.length_skipn, length_nparams; unfold ind_nn, ind_np in *; lia).
        rewrite UnitCases.eval_wk_shiftn_args; econstructor; exact Hl'. }
      exact (IndSem.univ_idx_wk _ _ _ _ _ _ _ _ _ HCs HSs HR HE Eb Ea ltac:(right; eauto)).
  Qed.

  Lemma sort_shift_scoped : exp_scoped (ind_np D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ.
  Proof.
    pose proof Hc as [_ Hle _ HsS _ _ _].
    eapply exp_scoped_wk; [ exact HsS |]; intros x Hx.
    unfold wk_shiftn, ind_nn; unfold ind_np in *; lia.
  Qed.

  Lemma scoped_inst_wk : forall n M Ms φ, exp_scoped n M -> List.length Ms = n ->
      M[sb_of_list Id Ms][φ]ʷ = M[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ms)].
  Proof.
    intros * Hs Hlen.
    rewrite <- exp_sub_of_wk, exp_sub_sub.
    rewrite <- (List.map_ext _ _ (fun N => exp_sub_of_wk N φ)).
    eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx; cbn [sb_compose].
    apply sb_of_list_lt_compose; lia.
  Qed.

  (** The type former applied to glued parameters is glued at the sort's
      universe. *)
  Lemma ind_former_base : forall Δ Ms vs (i : nat) b P El, ⊢ Δ -> glu_args Δ (ind_params D) Id nil Ms vs ->
      ⟦ (ind_sort D)[wk_shiftn (ind_nn D)]ʷ ⟧ env_args nil vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R (d_ind p vs) (d_ind p vs)) ->
      Δ ⊢ apps (a_ind p) Ms : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms] ® d_ind p vs ∈ El.
  Proof.
    intros * HΔ Hg Hb Hglu HPER.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    pose proof (glu_args_params_top _ _ _ _ Hass Hs Hg) as Htop.
    pose proof Htop as [HMl HMs HMr].
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [_ Hvl].
    destruct (sort_idx_params _ _ _ _ HΔ Hg Hb) as (bu & Hbu & Hidx).
    assert (Hvs : vs = List.firstn (ind_nu D) vs ++ List.skipn (ind_nu D) vs) by (symmetry; apply List.firstn_skipn).
    set (ups := List.firstn (ind_nu D) vs) in *; set (ns := List.skipn (ind_nu D) vs) in *.
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (HAeq : Δ ⊢ apps (a_ind p) Ms ≈ apps (a_ind p) Ms : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms]).
    { eapply wf_exp_eq_ind_apps; [ exact Hl | exact HΔ | exact HMl | exact HMl |].
      intros k N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; eapply HMs; eassumption. }
    assert (HAt : Δ ⊢ apps (a_ind p) Ms : (ind_sort D)[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms]) by (gen_presups; assumption).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
    pose proof (HPER _ HRb) as Hdind.
    assert (Hub : IndSem.is_univ b)
      by (destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb; cbn in Hb; inversion Hb; [ left | right ]; eauto).
    destruct (IndSem.per_univ_elem_univ _ _ _ _ HRb Hub) as [_ HRb'].
    apply HRb' in Hdind; destruct Hdind as [R' HR'].
    rewrite <- Hidx in HR'; rewrite Hvs in HR', Hg.
    destruct (ind_glu_elem_of_per _ R' ups ns HR' Hu)
      as (NP & NEl & AP & AEl & DP & DEl & Pd & Eld & R'' & Hglud & HPd & HEd & HRR & HeN & HNP & HeA & HAP & HeD & HDP).
    pose proof (ind_typ_at_of_args _ _ _ _ _ _ _ _ _ _ _ _ HΔ Hg Hu Hbu (uidx_le_refl _) HeN HNP HeA HAP HeD HDP) as Hit.
    assert (Hgd : glu_univ_typ (IndSem.univ_idx bu) (d_ind p vs) Δ (apps (a_ind p) Ms))
      by (rewrite Hvs; apply (mk_glu_typ_at _ _ _ _ Pd Eld); [ exact Hglud | apply HPd; exists Ms; exact Hit ]).
    clear HPER.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq in Hb, HAt |- *; cbn [exp_wk exp_sub] in Hb, HAt |- *; inversion Hb; subst b.
    - invert_glu_univ_elem Hglu.
      apply_predicate_equivalence.
      cbn [IndSem.univ_idx] in Hidx; rewrite Hidx in Hgd.
      econstructor; [ exact HAt | apply wf_exp_eq_refl; mauto 3 | exact Hgd ].
    - invert_glu_univ_elem Hglu.
      apply_predicate_equivalence.
      cbn [IndSem.univ_idx] in Hidx; rewrite Hidx in Hgd.
      destruct (gid_lvlP _ HG) as [n HLv]; rewrite Heq in HLv; cbn [ind_sort_lvl exp_wk] in HLv.
      pose proof HLv as [SbP HSbP _ _].
      rewrite <- Hvs in Hg.
      pose proof (glu_sub_params _ _ _ _ HΔ HSbP Hg) as Hσ.
      destruct (glu_rel_exp_level_elim HSbP HLv _ _ _ Hσ) as (m & Hm & _ & Hglul).
      assert (m = l) as -> by (eapply functional_eval_exp; eassumption).
      assert (Htl : Δ ⊢ t[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms] : Level@n)
        by (eapply glu_lvl_escape; [ eassumption | exact Hglul | exact HΔ ]).
      econstructor; [ exact HAt | | exact Hgd |].
      + apply (mk_suniv_glu_typ _ _ _ _ (t[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms]) n); [ exact Hglul |].
        apply wf_exp_eq_refl; mauto 3.
      + intros Δ' φ W Hφ HW.
        inversion HW.
        match goal with H : ind_lookup _ _ p = Some ?D1 |- _ => assert (D1 = D) as -> by congruence end.
        match goal with HR : Rps vs at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Rs |- _ => pose proof (HMr _ _ _ Hφ HR) as [HRl HRs] end.
        cbn [nf_to_exp].
        rewrite apps_wk; cbn [exp_wk].
        assert (HS' : exp_scoped (ind_np D) (Type⟨t[wk_shiftn (ind_nn D)]ʷ⟩))
          by (pose proof sort_shift_scoped as Hss; rewrite Heq in Hss; exact Hss).
        change (Type⟨t[wk_shiftn (ind_nn D)]ʷ[sb_of_list Id Ms][φ]ʷ⟩) with ((Type⟨t[wk_shiftn (ind_nn D)]ʷ⟩)[sb_of_list Id Ms][φ]ʷ).
        rewrite (scoped_inst_wk _ _ _ _ HS' HMl).
        assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
        assert (Hl1 : List.length (List.map (fun N => N[φ]ʷ) Ms) = ind_np D) by (rewrite List.length_map; exact HMl).
        pose proof (wf_exp_eq_ind_apps _ _ _ _ _ Hl HΔ' Hl1 ltac:(rewrite <- HRl; exact Hl1) HRs) as Heqn.
        rewrite Heq in Heqn; exact Heqn.
  Qed.

  Lemma sb_of_list_scoped_base : forall M Ms σ τ, exp_scoped (List.length Ms) M ->
      M[sb_of_list σ Ms] = M[sb_of_list τ Ms].
  Proof.
    intros * Hs; eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx.
    rewrite !(sb_of_list_nth _ _ _ (a_var 0)) by exact Hx; reflexivity.
  Qed.

  (** The PER of the closed constant [a_ind p] at its type. *)
  Lemma ind_former_per : forall (i : nat) R a, ⟦ ind_ty D ⟧ nil ↘ a -> DF a ≈ a ∈ per_univ_elem i ↘ R ->
      R (d_ind p nil) (d_ind p nil).
  Proof.
    intros * Ha HR.
    assert (HΔ0 : ⊢ ⋅) by (constructor; pose proof comps_params_wf' as H; eapply ctx_wf_gctx; exact H).
    assert (Hty : ⋅ ⊢ a_ind p : ind_ty D) by (eapply wf_ind; eassumption).
    destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hty)) as (env_rel & Henv & j & Hsimp).
    assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    inversion Hm1; subst; inversion Hm2; subst.
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
  Qed.

  (** The type former is glued at its type. *)
  Lemma glu_rel_exp_ind0 : ⋅ ⊩ a_ind p : ind_ty D.
  Proof.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    destruct (ind_ty_typed0 _ _ _ Hdt) as [j Hj].
    destruct (gid_params _ HG) as [SbP HSbP].
    assert (HSbP0 : EG ind_params D ++ ⋅ ∈ glu_ctx_env ↘ SbP) by (rewrite List.app_nil_r; exact HSbP).
    destruct (glu_ctx_env_entries_valid _ _ _ Hass HSbP0 j) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ ind_ty D : Typeω@i) by (eapply lift_exp_ge; [ exact Hji | exact Hj ]).
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact comps_params_wf').
    eapply (glu_closed_const _ _ i (d_ind p nil)); [ reflexivity | intros; apply ind_ty_sub, Hc | exact Hi | intros; constructor |].
    intros Δ σ Hσ a P El Ha Hglu.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold ind_ty in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ Hass Hi') as [HCs _].
    unfold ind_ty in Ha |- *.
    replace (ctx_pi (ind_params D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ) with ((ctx_pi (ind_params D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)[σ])
      by (change (ctx_pi (ind_params D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ) with (ind_ty D); apply ind_ty_sub, Hc).
    change (a_ind p) with (apps (a_ind p) nil).
    eapply (ctx_pi_glu_elem (ind_np D) (d_ind p) (a_ind p)) with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbP) (ρ := nil) (xs := nil);
      [ | reflexivity | exact Hass | eapply glu_ctx_env_nil; [ reflexivity | exact Hg0 ] | exact HSbP0
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | exact Hσ | reflexivity | | | | exact Ha | exact Hglu ].
    - intros xs x Hx; eapply eval_app_indty; [ exact Hl | exact Hx ].
    - cbn [apps_exp]; change (ctx_pi (ind_params D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ) with (ind_ty D).
      rewrite ind_ty_sub by exact Hc; eapply wf_ind; eassumption.
    - intros R a' Ha' HR; exact (ind_former_per _ _ _ Ha' HR).
    - intros Δ' φ Ms vs Hφ Hg b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ Hass Hs) in Hg.
      destruct (glu_args_length _ _ _ _ _ _ Hg) as [HMl _].
      rewrite (sb_of_list_scoped_base _ _ _ Id) by (rewrite HMl; exact sort_shift_scoped).
      exact (ind_former_base _ _ _ _ _ _ _ HΔ' Hg Hb Hglub HPb).
  Qed.

End Former.

(** ** The Arguments of a Constructor

    The values of the types of a constructor's arguments, at the arguments
    before them, are related to the values the clause of [d_ind] reads
    them at: a non-recursive argument's type is weakened past the recursive
    arguments before it. *)

Section ConArgs.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (HDc : valid_ind_decl D).
  Variable (c : String.string) (gs : list carg).
  Hypothesis (Hcon : ind_con D c = Some gs).

  Lemma cargs_arg_val_rel : forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 ->
      forall R E a1 a2, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R -> R E E ->
        ⟦ A[wk_pat (cargs_pat gs1)]ʷ ⟧ E ↘ a1 -> ⟦ A ⟧ ⟪wk_pat (cargs_pat gs1)⟫ E ↘ a2 ->
        exists k : uidx, Dom a1 ≈ a2 ∈ per_univ k.
  Proof.
    intros * Heq * HR HE Ha1 Ha2.
    destruct (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon gs1 (ca_arg A :: gs2) Heq) as [_ Hwk].
    assert (HA : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
      by (rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (vid_arg _ HDc _ _ _ _ Hcon HA) as (_ & j & HAv).
    rewrite Heq, <- IndCases.nonrec_args_prefix_cargs_strat in HAv.
    destruct (rel_exp_under_ctx_wk_simple Hwk HAv) as (R' & HR' & i0 & Hsimp).
    assert (ER : R <~> R') by (eapply per_ctx_env_right_irrel; eassumption).
    destruct (Hsimp E E ltac:(apply ER; exact HE)) as (b & b' & Rb & Hb & Hb' & HRb & m & m' & Hm & Hm' & Hmm).
    inversion Hb; subst; inversion Hb'; subst.
    destruct (IndSem.per_univ_elem_univ _ _ _ _ HRb ltac:(left; eauto)) as [_ HRb'].
    assert (m = a1) as -> by (eapply functional_eval_exp; eassumption).
    assert (m' = a2) as -> by (eapply functional_eval_exp; eassumption).
    exists (ul j); apply HRb' in Hmm; exact Hmm.
  Qed.

  Lemma cargs_suffix_glu : forall gs1 gs2, gs = gs1 ++ gs2 -> ⊩ cargs_ctx p D gs ++ ind_params D ->
      exists Sb, EG cargs_ctx p D gs1 ++ ind_params D ∈ glu_ctx_env ↘ Sb.
  Proof.
    intros * Heq [Sb HSb].
    rewrite Heq in HSb; unfold cargs_ctx in HSb; rewrite cargs_ctx_aux_app, <- List.app_assoc in HSb.
    eapply glu_ctx_env_suffix; [| exact HSb ]; apply cargs_ctx_aux_ass.
  Qed.

  Lemma cargs_env_rel : forall gs1 gs2 R Sb Δ Ps bs As1 zs, gs = gs1 ++ gs2 -> ⊢ Δ ->
      EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
      EG cargs_ctx p D gs1 ++ ind_params D ∈ glu_ctx_env ↘ Sb ->
      glu_args Δ (ind_params D) Id nil Ps bs ->
      glu_args Δ (cargs_ctx p D gs1) (sb_of_list Id Ps) (env_args nil bs) As1 zs ->
      R (env_args nil (bs ++ zs)) (env_args nil (bs ++ zs)).
  Proof.
    intros * Heq HΔ HR HSb HgP HgA.
    pose proof (decl_closed_params D Hc) as Hass.
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LB].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id (Ps ++ As1) ® env_args nil (bs ++ zs) ∈ Sb).
    { eapply glu_sub_of_list with (C := cargs_ctx p D gs1 ++ ind_params D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ unfold tele_ass; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]
        | rewrite List.app_nil_r; exact HSb | eapply glu_ctx_env_nil; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ |].
      apply glu_args_app; [ exact Hass | exact LP | exact LB |]; split; [ exact HgP | exact HgA ]. }
    exact (glu_ctx_env_per_env HSb HR Hσ).
  Qed.

  (** The uniform parameters of arguments related at the arguments'
      telescope are related at theirs. *)
  Lemma cargs_uparams_gargs : forall gs1 gs2 ups ns fa, gs = gs1 ++ gs2 ->
      List.length ups = ind_nu D -> List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
      (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups.
  Proof.
    intros * Heq Hlu Hlns Hlfa INV.
    pose proof (decl_closed_nu D Hc) as Hle.
    destruct (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon gs1 gs2 Heq) as [HC _].
    destruct (rel_ctx_wf_per_ctx_env HC) as [R0 HR0].
    assert (HC' : ⊨ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
    assert (HR0' : EF List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅
                     ≈ List.rev (List.rev (cargs_ctx p D gs1 ++ ind_params D)) ++ ⋅ ∈ per_ctx_env ↘ R0)
      by (rewrite List.rev_involutive, List.app_nil_r; exact HR0).
    assert (Hl0 : List.length (ups ++ ns ++ fa) = List.length (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
      by (rewrite !List.length_app, List.length_rev, List.length_app, length_cargs_ctx, Hlu, Hlns, Hlfa; unfold ind_nn; unfold ind_np in Hle |- *; lia).
    assert (Hta : tele_ass (List.rev (cargs_ctx p D gs1 ++ ind_params D)))
      by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_params D Hc) ]).
    pose proof (proj2 (IndSem.rel_gargs _ _ _ _ GlobalArgs.per_ctx_env_nil_true HC' Hta HR0' nil nil _ _ Hl0 Hl0 (INV _ HR0))) as Hgpf.
    rewrite List.rev_app_distr in Hgpf.
    replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) in Hgpf by (rewrite <- List.app_assoc; reflexivity).
    assert (Hlp : List.length (ups ++ ns) = List.length (List.rev (ind_params D)))
      by (rewrite List.length_app, List.length_rev, Hlu, Hlns; unfold ind_nn; unfold ind_np in Hle |- *; lia).
    destruct (IndSem.per_gargs_app _ _ _ _ _ _ _ _ Hlp Hgpf Hlp) as [Hp _].
    destruct (IndCases.params_split_rel D HDc Hc _ _ _ _ Hp ltac:(rewrite List.length_app, Hlu, Hlns; unfold ind_nn; lia))
      as (Hu0 & _).
    rewrite firstn_app_exact in Hu0 by exact Hlu; exact Hu0.
  Qed.

End ConArgs.

Lemma cargs_rev_nth_arg : forall p D gs gs1 B gs2, gs = gs1 ++ ca_arg B :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D gs)) (List.length gs1) = Some (ce_ass B[wk_pat (cargs_pat gs1)]ʷ).
Proof.
  intros * ->.
  unfold cargs_ctx; rewrite cargs_ctx_aux_app; cbn [cargs_ctx_aux].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag, List.app_nil_r; reflexivity.
Qed.

Lemma cargs_rev_nth_rec : forall p D gs gs1 Pr gs2, gs = gs1 ++ ca_rec Pr :: gs2 ->
    List.nth_error (List.rev (cargs_ctx p D gs)) (List.length gs1)
      = Some (ce_ass (ptyp_ty p D (cargs_pat gs1) Pr)).
Proof.
  intros * ->.
  unfold cargs_ctx; rewrite cargs_ctx_aux_app; cbn [cargs_ctx_aux].
  rewrite !List.rev_app_distr; cbn [List.rev List.app].
  rewrite List.nth_error_app2 by (rewrite List.length_rev, length_cargs_ctx_aux; lia).
  rewrite List.length_rev, length_cargs_ctx_aux, Nat.sub_diag, !List.app_nil_r; reflexivity.
Qed.

Lemma cargs_split_aux : forall p D gs gs1 g gs2, gs = gs1 ++ g :: gs2 ->
    cargs_ctx p D gs = cargs_ctx_aux p D (cargs_pat gs1) (g :: gs2) ++ cargs_ctx p D gs1.
Proof. intros * ->; unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; reflexivity. Qed.

Section ConGlu.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (HDc : valid_ind_decl D).
  Variable (c : String.string) (gs : list carg).
  Hypothesis (Hcon : ind_con D c = Some gs) (HΨ : ⊩ cargs_ctx p D gs ++ ind_params D).
  Variable (ups : list domain) (bu : domain) (u : uidx) (NP : nat -> list domain -> glu_typ_pred) (NEl : nat -> list domain -> glu_exp_pred)
    (AP : list domain -> String.string -> nat -> list domain -> glu_typ_pred)
    (AEl : list domain -> String.string -> nat -> list domain -> glu_exp_pred)
    (DP : list domain -> exp -> glu_typ_pred) (DEl : list domain -> exp -> glu_exp_pred).
  Hypothesis (Hu : List.length ups = ind_nu D) (Hbu : ⟦ ind_sort D ⟧ env_args nil ups ↘ bu)
    (Hule : uidx_le (IndSem.univ_idx bu) u)
    (HeN : forall k A vs, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b)
    (HNP : forall k A vs b, List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) ->
       tele_pre (ind_nr D ups) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem u ↘ NP k vs ↘ NEl k vs)
    (HeA : forall ms c gs k A vs, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> exists b, ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b)
    (HAP : forall ms c gs k A vs b, tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ms ms ->
       ind_con D c = Some gs -> List.nth_error (cargs_nonrec gs) k = Some A ->
       tele_pre (ind_ar D ups ms c) k vs vs -> ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ b ->
       DG b ∈ glu_univ_elem u ↘ AP ms c k vs ↘ AEl ms c k vs)
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
       DG b ∈ glu_univ_elem u ↘ DP (ms ++ ws ++ ys) B ↘ DEl (ms ++ ws ++ ys) B).
  (** The types of the rests of a recursive argument's shape are types, in
      the context of the arguments before it and the shape's domains before
      the rest. *)
  Hypothesis (HshV : forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       exists j : nat, sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
         ⊩ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t) : Typeω@j).

  (** Glued arguments of a constructor's non-recursive arguments are glued
      at the gluings of the clause. *)
  Lemma args_of_glu_args : forall Δ Us Ns ns As ws, ⊢ Δ ->
      ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      glu_nparams D NEl Δ Us Ns ns -> tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      glu_args Δ (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As ws ->
      tele_full (ind_ar D ups ns c) (cargs_nonrec gs) (nonrec_vals gs ws) (nonrec_vals gs ws) ->
      forall hs1 B hs2 N T v, gs = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
        List.nth_error ws (List.length hs1) = Some v ->
        Δ ⊢ N : T ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) ws)).
  Proof.
    intros Δ Us Ns ns As ws HΔ Hc0 HUs Hnp Hns HgA Hv.
    pose proof Hc0 as [_ HCA _].
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (decl_uparams_ass D Hc) as HassU.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _].
    pose proof Hnp as [LN LNn _].
    assert (HgP : glu_args Δ (ind_params D) Id nil (Us ++ Ns) (ups ++ ns)).
    { rewrite params_split; apply glu_args_app; [ exact HassU | exact LU | rewrite (length_ind_uparams D (decl_closed_nu D Hc)); exact Hu |].
      split; [ exact HUs |].
      exact (glu_args_of_nparams D ups u NP NEl HeN HNP _ _ _ _ Hnp Hns). }
    enough (forall m hs1 B hs2 N T v, List.length hs1 < m -> gs = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N ->
              List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T ->
              List.nth_error ws (List.length hs1) = Some v ->
              Δ ⊢ N : T ® v ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) ws))) as Hm
      by (intros; eapply (Hm (S (List.length hs1))); eauto).
    induction m as [| m IH]; intros hs1 B hs2 N T v Hlt Heq HN HT Hvv; [ lia |].
    destruct (Nat.eq_dec (List.length hs1) m) as [Hlm | Hne]; [| eapply IH; eauto; lia ].
    assert (Hh : List.length hs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
    pose proof HgA as [_ _ HA].
    destruct (HA _ _ _ _ _ HN HT Hvv (cargs_rev_nth_arg p D _ _ _ _ Heq)) as [i' a1 P' El' Ha1 Hglu' HP' HM'].
    set (k := List.length (cargs_nonrec hs1)).
    assert (HBk : List.nth_error (cargs_nonrec gs) k = Some B)
      by (unfold k; rewrite Heq, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (Hpk : tele_pre (ind_ar D ups ns c) k (nonrec_vals hs1 (List.firstn (List.length hs1) ws))
                    (nonrec_vals hs1 (List.firstn (List.length hs1) ws)))
      by (eapply nonrec_prefix_pre; [ exact Hv | lia | exact Heq ]).
    destruct (HeA _ _ _ _ _ _ Hns Hcon HBk Hpk) as [b Hb].
    pose proof (HAP _ _ _ _ _ _ _ Hns Hcon HBk Hpk Hb) as Hgb.
    (** The two values of the argument's type. *)
    assert (Hrel : exists k0 : uidx, Dom a1 ≈ b ∈ per_univ k0).
    { destruct (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon hs1 (ca_arg B :: hs2) Heq) as [HC1 _].
      destruct (rel_ctx_wf_per_ctx_env HC1) as [R HR].
      destruct (cargs_suffix_glu p D gs hs1 (ca_arg B :: hs2) Heq HΨ) as [Sb1 HSb1].
      assert (HgA1 : glu_args Δ (cargs_ctx p D hs1) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns))
                       (List.firstn (List.length hs1) As) (List.firstn (List.length hs1) ws)).
      { pose proof HgA as HgA'.
        rewrite (cargs_split_aux p D gs hs1 (ca_arg B) hs2 Heq), <- (List.firstn_skipn (List.length hs1) As),
          <- (List.firstn_skipn (List.length hs1) ws) in HgA'.
        apply glu_args_app in HgA'; [ exact (proj1 HgA') | apply cargs_ctx_aux_ass | |];
          rewrite List.length_firstn, length_cargs_ctx; lia. }
      pose proof (cargs_env_rel p D Hc gs hs1 (ca_arg B :: hs2) R Sb1 Δ (Us ++ Ns) (ups ++ ns) _ _ Heq HΔ HR HSb1 HgP HgA1) as HE.
      rewrite <- env_args_app in Ha1.
      assert (Ea2 : ⟦ B ⟧ ⟪wk_pat (cargs_pat hs1)⟫ (env_args nil ((ups ++ ns) ++ List.firstn (List.length hs1) ws)) ↘ b).
      { rewrite env_args_app, IndSem.eval_wk_pat_args by (rewrite List.length_firstn; lia).
        rewrite <- env_args_app, <- List.app_assoc; exact Hb. }
      exact (cargs_arg_val_rel p D Hl Hc Hdt Hsu HDc c gs Hcon hs1 B hs2 Heq R _ a1 b HR HE Ha1 Ea2). }
    destruct Hrel as [k0 Hrel].
    assert (HTP : Δ ⊢ T ® AP ns c k (nonrec_vals hs1 (List.firstn (List.length hs1) ws))).
    { eapply (HCA c gs hs1 B hs2 Ns ns As (List.firstn (List.length hs1) ws) T Hcon Heq Hnp Hns);
        [ rewrite List.length_firstn; lia | exact HT | | exact Hpk ].
      intros hs1' B' hs2' N' T' v' Heq1 HN' HT' Hv'.
      assert (Hlt' : List.length hs1' < List.length hs1) by (rewrite Heq1, List.length_app; cbn; lia).
      rewrite List.firstn_firstn, Nat.min_l by lia.
      rewrite List.nth_error_firstn in Hv'; destruct (Nat.ltb_spec (List.length hs1') (List.length hs1)); [| discriminate ].
      eapply (IH hs1' B' (hs2' ++ ca_arg B :: hs2)); [ lia | rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN' | exact HT' | exact Hv' ]. }
    eapply glu_univ_elem_exp_conv_uidx; [ exact Hrel | exact Hglu' | exact Hgb | exact HM' | exact HTP ].
  Qed.

  (** The gluings of the non-uniform parameters move along their relations. *)
  Lemma nel_resp_per : forall R0 ns0, DF d_ind p (ups ++ ns0) ≈ d_ind p (ups ++ ns0) ∈ per_univ_elem u ↘ R0 ->
      forall k vs vs', k < ind_nn D -> tele_pre (ind_nr D ups) k vs vs' ->
        forall Γ A N n n', NEl k vs Γ A N n -> ind_nr D ups k vs n n' -> NEl k vs' Γ A N n'.
  Proof.
    intros * HR0 k vs vs' Hk Hp Γ0 A0 N n n' HN Hnn.
    pose proof (decl_closed_params D Hc) as Hass.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (_ & _ & Hcp & _).
    destruct (per_univ_elem_ind_evals _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (HevN & _ & _).
    pose proof Hcp as [HnP HnI HaP HaI HdP HdI].
    assert (Hk' : k < List.length (List.rev (ind_nparams D))) by (rewrite List.length_rev, length_nparams; exact Hk).
    destruct (nparams_lt_ass D k Hass Hk') as [S HS].
    pose proof (tnrp_refl_l p D ups _ (ind_ar D ups) (ind_dr ups) Hass HnP HnI HaP HaI HdP HdI k vs vs' ltac:(lia) Hp) as Hd.
    pose proof (tnrp_refl_r p D ups _ (ind_ar D ups) (ind_dr ups) Hass HnP HnI HaP HaI HdP HdI k vs vs' ltac:(lia) Hp) as Hd'.
    destruct (HeN _ _ _ HS Hd) as [b Eb].
    pose proof (HNP _ _ _ _ HS Hd Eb) as Hgb.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hgb) as [Rb HRb].
    assert (Hnn' : Rb n n') by (apply (per_head_iff Eb Eb HRb); unfold ind_nr in Hnn; rewrite (nth_ctyp_eq _ _ _ HS) in Hnn; exact Hnn).
    pose proof (glu_univ_elem_trm_resp_per_elem _ _ _ _ Hgb _ HRb _ _ _ _ _ HN Hnn') as Hn2.
    destruct (HevN _ _ _ _ HS Hp) as (a & a' & Ea & Ea' & Haa).
    assert (a = b) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro (fun R1 => per_univ_elem u R1 b a') _ Haa) Hgb) as Hga'.
    pose proof (HNP _ _ _ _ HS Hd' Ea') as Hgb'.
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hga' Hgb') as [_ HEq].
    apply HEq; exact Hn2.
  Qed.

  (** A recursive argument of a constructor, after [k] of its shape's
      domains: an element of the type of the rest of the shape, at a glued
      instance of the shape's context (on the side of the non-recursive
      arguments, [σ], and on the one of all the arguments, [σc]), is a
      recursive argument of the rest of the shape. *)
  Lemma con_rec_glu : forall R0 ns0, DF d_ind p (ups ++ ns0) ≈ d_ind p (ups ++ ns0) ∈ per_univ_elem u ↘ R0 ->
      forall gs1 t gs2 ns fa, gs = gs1 ++ ca_rec t :: gs2 ->
      List.length ns = ind_nn D -> List.length fa = List.length gs1 ->
      tele_full (ind_nr D ups) (List.rev (ind_nparams D)) ns ns ->
      tele_pre (ind_ar D ups ns c) (List.length (cargs_nonrec gs1)) (nonrec_vals gs1 fa) (nonrec_vals gs1 fa) ->
      per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
      (forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
         R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))) ->
      forall t' k ys Δ τ Us Ys SbC σc Sbc N v a (i : uidx) P El,
        ptyp_skip k t = t' -> k <= List.length (ptyp_doms t) ->
        tele_pre (shape_tr (ind_dr ups) ns (nonrec_vals gs1 fa) (ptyp_doms t)) k ys ys ->
        per_gargs (List.rev (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t))))
          (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa)) ys ys ->
        ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
        List.length Ys = k + List.length (cargs_nonrec gs1) + ind_nn D ->
        EG doms_ctx (List.firstn k (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ ind_params D
          ∈ glu_ctx_env ↘ SbC ->
        Δ ⊢ˢ sb_of_list τ (Us ++ Ys) ® env_args nil (ups ++ ns ++ nonrec_vals gs1 fa ++ ys) ∈ SbC ->
        EG sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D ∈ glu_ctx_env ↘ Sbc ->
        Δ ⊢ˢ σc ® env_args nil (ups ++ ns ++ fa ++ ys) ∈ Sbc ->
        ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) t' = (ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) t')[σc] ->
        ⟦ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) t' ⟧ env_args nil (ups ++ ns ++ fa ++ ys) ↘ a ->
        DG a ∈ glu_univ_elem i ↘ P ↘ El ->
        Δ ⊢ ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) t' ® P ->
        Δ ⊢ N : ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) t' ® v ∈ El ->
        glu_rec p D ups NEl AEl DP DEl Δ (ns ++ nonrec_vals gs1 fa ++ ys) t' (ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) t') N v.
  Proof.
    intros R0 ns0 HR0 gs1 t gs2 ns fa Heq Hlns Hlfa Hnsd Hp Hgu0 INV.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (_ & _ & Hcp & _ & _ & Hadm & _ & _).
    pose proof (nel_resp_per R0 ns0 HR0) as HNe.
    destruct (ElimCases.cargs_sem_all D HDc Hc Hsu Hdt p Hl c gs Hcon gs nil (eq_sym (List.app_nil_r gs))) as [HΨc _].
    pose proof (IndCases.shape_links D HDc Hc Hsu p c gs Hcon HΨc gs1 t gs2 Heq ups ns fa bu Hu Hlns Hlfa Hgu0 Hbu Hnsd Hp INV)
      as Hlinks.
    set (nv := nonrec_vals gs1 fa) in *.
    set (K := List.length (cargs_nonrec gs1)) in *.
    set (pat := cargs_pat gs1) in *.
    assert (Hlnv : List.length nv = K) by (apply length_nonrec_vals; exact Hlfa).
    assert (HK : K <= List.length (cargs_nonrec gs)) by (unfold K; rewrite Heq, cargs_nonrec_app, List.length_app; lia).
    assert (Hsimp : ptyp_simple t = true) by exact (vid_simple _ HDc _ _ _ _ _ Hcon Heq).
    induction t' as [j0 Ps0 | j0 Ps0 | B t'' IH];
      intros k ys Δ τ Us Ys SbC σc Sbc N v a i P El Hsk Hk Hy Hgy HΔ HUs HYl HSbC Hσ HSbc Hσc HTeq Ea Hg HTP HN.
    3:{ (** A domain: an element of the domain's gluing, moved to the gluing
            of the [Π]'s domain, applied to the argument gives a recursive
            argument of the rest of the shape. *)
        destruct (ptyp_skip_pi _ _ _ _ Hsk) as [HB Hs'].
        assert (Hkl : k < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence).
        pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
        assert (HUl : List.length Us = ind_nu D)
          by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; rewrite (length_ind_uparams D Hle) in LU; exact LU).
        (** The rest of the shape's type is glued at the domains' gluings. *)
        assert (Hsh : glu_shape_typ ups DP DEl Δ (ns ++ nv ++ ys) (pt_pi B t'') (ptyp_ty_at p Us (sb_of_list τ (Us ++ Ys)) (pt_pi B t''))).
        { eapply shape_typ_glu; eassumption. }
        cbn [ptyp_ty ptyp_ty_at exp_sub glu_shape_typ] in Ea, HTeq, HTP, HN, Hsh |- *.
        destruct (Hsh _ _ eq_refl) as [HshD _].
        injection HTeq as HITeq HOTeq.
        destruct (proj1 (Hlinks k ys Hk Hy Hgy) B HB) as (jd & a1 & b0 & Ea1 & Eb0 & Hab).
        inversion Ea; subst a.
        match goal with H : ⟦ B[wk_pat _]ʷ ⟧ _ ↘ ?x |- _ => assert (x = a1) as -> by (eapply functional_eval_exp; eassumption) end.
        set (σ := sb_of_list τ (Us ++ Ys)) in *.
        set (OTc := ptyp_ty p D (false :: List.repeat false k ++ pat) t'') in *.
        set (E := env_args nil (ups ++ ns ++ fa ++ ys)) in *.
        (** A level above the ones at hand. *)
        set (n := ul (Nat.max (ulvl i) (Nat.max (ulvl u) jd))).
        assert (Hin : uidx_le i n) by (apply uidx_le_ul_max; unfold n; lia).
        assert (Hun : uidx_le u n) by (apply uidx_le_ul_max; unfold n; lia).
        assert (Hjn : uidx_le (ul jd) n) by (apply uidx_le_ul_max; unfold n; cbn; lia).
        destruct (glu_univ_elem_cumu_ge_uidx Hin Hg) as (Pn & Eln & Hgn).
        pose proof (glu_univ_elem_typ_cumu_ge_uidx Hin Hg Hgn HTP) as HTPn.
        pose proof (glu_univ_elem_exp_cumu_ge_uidx Hin Hg Hgn HN) as HNn.
        destruct Hab as [Rab HRab].
        pose proof (per_univ_trans _ _ _ _ _ _ HRab (per_univ_sym _ _ _ _ HRab)) as HRaa.
        pose proof (per_univ_elem_cumu_uidx _ _ _ _ HRaa _ Hjn) as HRaan.
        destruct (glu_univ_elem_pi_clean_inversion1 HRaan Hgn) as (IP & IEl & OP & OEl & elem_rel & HgI & HgO & Hper & EP & EEl).
        apply EEl in HNn.
        inversion_clear HNn as [? ? ? ? IT2 OT2 HMt Hm HAeq HITt HOTt HIP HApp].
        pose proof (HDP _ _ _ _ _ _ _ _ _ _ _ Hnsd Hcon Heq Hp HB Hy Eb0) as Hgb0.
        (** An argument glued at the domain's gluing, at the [Π]'s domain. *)
        assert (Hdom : forall Δ' φ b c', Δ' ⊢ᵏ φ : Δ -> ind_dr ups (ns ++ nv ++ ys) B c' c' ->
                  Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ DEl (ns ++ nv ++ ys) B ->
                  Rab c' c' /\ Δ' ⊢ B[σ][φ]ʷ ® IP /\ Δ' ⊢ b : B[σ][φ]ʷ ® c' ∈ IEl /\ Δ' ⊢ b : IT2[φ]ʷ ® c' ∈ IEl).
        { intros Δ' φ b c' Hφ Hc' Hb.
          pose proof (dr_to_rel B _ b0 a1 c' (ul jd) Rab (ul jd) Eb0 (ex_intro _ Rab HRab) HRaa Hc') as Hcc.
          pose proof (glu_typ_transfer u n (ul jd) b0 a1 _ _ IP IEl Δ' _ Hun Hjn (per_univ_sym' _ _ _ (ex_intro _ Rab HRab))
                        Hgb0 HgI (HshD _ _ Hφ)) as HTyI.
          pose proof (glu_univ_elem_exp_conv_uidx (per_univ_sym' _ _ _ (ex_intro _ Rab HRab)) Hgb0 HgI Hb HTyI) as HbI.
          split; [ exact Hcc | split; [ exact HTyI | split; [ exact HbI |] ] ].
          exact (glu_elem_retype n n a1 IP IEl IP IEl Δ' _ _ b c' HgI HgI HTyI HbI (HIP _ _ Hφ)). }
        apply glu_rec_pi.
        + intros IT OT HA0 Δ' φ Hφ; injection HA0 as <- <-; exact (HshD Δ' φ Hφ).
        + intros IT OT HA0 Δ' φ b c' Hφ Hc' Hb; injection HA0 as <- <-.
          destruct (Hdom _ _ _ _ Hφ Hc' Hb) as (Hcc & _ & _ & HbI).
          destruct (HApp Δ' φ b c' Hφ HbI Hcc) as (mn & Hmn & _); exists mn; exact Hmn.
        + intros IT OT HA0 Δ' φ b c' fc Hφ Hc' Hb Hfc; injection HA0 as <- <-.
          destruct (Hdom _ _ _ _ Hφ Hc' Hb) as (Hcc & HTyI & HbI0 & HbI).
          destruct (HApp Δ' φ b c' Hφ HbI Hcc) as (mn & Hmn & Happ).
          assert (mn = fc) as <- by (eapply functional_eval_app; eassumption).
          assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
          (** The substitutions after the argument. *)
          destruct (gid_dctx _ HG _ _ _ _ _ (S k) Hcon Heq ltac:(lia)) as [SbC' HSbC'].
          pose proof (HshD _ _ Hφ) as HTy0.
          assert (Hσ' : Δ' ⊢ˢ sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))
                          ® env_args nil (ups ++ ns ++ nv ++ ys ++ c' :: nil) ∈ SbC')
            by (eapply shape_sub_step; eassumption).
          destruct (HshV gs1 t gs2 (S k) Heq ltac:(lia)) as [jv HVv].
          pose proof HVv as [Sbc' HSbc' _ _].
          pose proof HSbc' as HSbc''.
          rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l in HSbc'' by lia.
          cbn [List.app] in HSbc''.
          assert (Hσc' : Δ' ⊢ˢ (sb_wk σc φ),,b ® E ↦ c' ∈ Sbc').
          { eapply glu_sub_snoc; [ exact HSbc | exact HSbc'' | eapply glu_ctx_env_sub_monotone; eassumption |].
            fold pat; rewrite <- exp_wk_sub, <- HITeq.
            exact (mk_glu_arg _ _ _ _ _ _ n a1 IP IEl Ea1 HgI HTyI HbI0). }
          (** The type of the rest, and its value. *)
          assert (HTeq' : ptyp_ty_at p (List.map (fun U => U[φ]ʷ) Us)
                            (sb_of_list (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us ++ (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil))) t''
                          = (ptyp_ty p D (List.repeat false (S k) ++ pat) t'')[(sb_wk σc φ),,b]).
          { rewrite <- ptyp_ty_at_shape_step; fold σ; rewrite HOTeq, exp_sub_sub.
            apply exp_sub_sb_eq, sb_q_extend_wk. }
          destruct (glu_rel_typ_at _ _ _ _ _ _ _ HSbc' HVv Hσc') as (_ & a2 & Ea2 & Hpa2 & HXP).
          rewrite Hs' in Ea2, HXP; fold pat in Ea2, HXP.
          destruct (per_univ_glu_univ_elem _ _ Hpa2) as (P2 & El2 & Hga2).
          pose proof (HXP _ _ Hga2) as HXP2.
          pose proof (HgO c' Hcc a2 Ea2) as HgOc.
          pose proof (glu_univ_elem_trm_typ _ _ _ _ HgOc _ _ _ _ Happ) as HOT2P.
          pose proof (glu_elem_retype n jv a2 _ _ P2 El2 Δ' _ _ _ _ HgOc Hga2 HOT2P Happ HXP2) as Happ'.
          rewrite <- HTeq' in HXP2, Happ'.
          unfold σ; rewrite ptyp_ty_at_shape_step.
          replace ((ns ++ nv ++ ys) ++ c' :: nil) with (ns ++ nv ++ ys ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
          apply (IH (S k) (ys ++ c' :: nil) Δ' (sb_wk τ φ) (List.map (fun U => U[φ]ʷ) Us) (List.map (fun Y => Y[φ]ʷ) Ys ++ b :: nil)
                   SbC' ((sb_wk σc φ),,b) Sbc' (a_app N[φ]ʷ b) mn a2 jv P2 El2);
            [ exact Hs' | lia | | | exact HΔ' | | rewrite List.length_app, List.length_map; cbn; lia | exact HSbC' | exact Hσ'
            | exact HSbc' | | exact HTeq' | | exact Hga2 | exact HXP2 | exact Happ' ].
          * apply tele_pre_snoc; [ exact Hy |].
            unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hc'.
          * rewrite (firstn_S_snoc _ _ _ HB), sh_ctx_snoc, List.length_firstn, Nat.min_l by lia.
            cbn [List.rev].
            apply (IndSem.per_gargs_snoc _ _ _ _ _ _ _ _ jd Rab);
              [ rewrite List.length_rev, length_sh_ctx, List.length_firstn; lia | exact Hgy | | exact Hcc ].
            rewrite <- !env_args_app, <- !List.app_assoc.
            exact (mk_rel_mod_eval a1 a1 Ea1 Ea1 HRaa).
          * exact (glu_args_wk _ _ _ _ _ _ _ (decl_uparams_ass D Hc) (decl_uparams_closed D Hc) Hφ HUs).
          * replace (ups ++ ns ++ fa ++ ys ++ c' :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact Hσc'.
          * replace (ups ++ ns ++ fa ++ ys ++ c' :: nil) with ((ups ++ ns ++ fa ++ ys) ++ c' :: nil) by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc; exact Ea2. }
    2:{ exfalso.
        destruct (Nat.lt_ge_cases k (List.length (ptyp_doms t))) as [Hlt | Hge].
        - destruct (ptyp_skip_lt k t Hlt) as (B & _ & Hs'); rewrite Hs' in Hsk; discriminate.
        - assert (k = List.length (ptyp_doms t)) as -> by lia.
          rewrite (ptyp_skip_end t Hsimp) in Hsk; discriminate. }
    (** The end of the shape. *)
    destruct (ptyp_skip_self _ _ _ _ Hsk) as [HkL HPs].
    assert (Hkd : k = List.length (ptyp_doms t)) by lia.
    subst Ps0.
    pose proof Hy as Hy0; rewrite tele_pre_iff in Hy0; destruct Hy0 as (Hly & _ & _).
    cbn [ptyp_ty ptyp_ty_at ptyp_ps] in Ea, HTP, HN |- *.
    destruct (proj2 (Hlinks k ys Hk Hy Hgy) Hkd) as (bs & bs1 & Ebs & Ebs1 & Htf).
    assert (HPl : List.length (ptyp_ps t) = ind_nn D) by exact (IndCases.length_rec_ps D Hc _ _ _ _ _ Hcon Heq).
    assert (Et0 : ⟦ apps (a_ind p) (ind_uvars D (List.length (List.repeat false k ++ pat))
                                     ++ List.map (fun P => P[wk_pat (List.repeat false k ++ pat)]ʷ) (ptyp_ps t)) ⟧
                    env_args nil (ups ++ ns ++ fa ++ ys) ↘ d_ind p (ups ++ bs1)).
    { apply Modules.eval_apps_exp; exists (d_ind p nil), (ups ++ bs1); split; [ constructor | split ].
      - apply Modules.eval_exps_app; [| exact Ebs1 ].
        unfold ind_uvars.
        replace (List.length (List.repeat false k ++ pat) + ind_nn D) with (List.length (ns ++ fa ++ ys))
          by (unfold pat; rewrite !List.length_app, List.repeat_length, length_cargs_pat; lia).
        replace (ind_nu D) with (List.length ups) by exact Hu.
        apply IndSem.eval_vars_from_args.
      - change (d_ind p (ups ++ bs1)) with (d_ind p (nil ++ (ups ++ bs1))).
        apply (IndCases.eval_apps_ind D p Hl).
        rewrite List.length_app, (IndCases.eval_exps_length _ _ _ Ebs1), List.length_map, HPl; cbn; unfold ind_nn; lia. }
    assert (a = d_ind p (ups ++ bs1)) as -> by (eapply functional_eval_exp; eassumption).
    set (σ := sb_of_list τ (Us ++ Ys)) in *.
    set (Qn := List.map (fun P => P[σ]) (ptyp_ps t)) in *.
    assert (HUl : List.length Us = ind_nu D)
      by (destruct (glu_args_length _ _ _ _ _ _ HUs) as [LU _]; rewrite (length_ind_uparams D Hle) in LU; exact LU).
    assert (HSbCt : EG ptyp_tele t ++ nonrec_args_prefix gs K ++ ind_params D ∈ glu_ctx_env ↘ SbC)
      by (rewrite Hkd, List.firstn_all in HSbC; exact HSbC).
    assert (HQn : glu_args Δ (ind_nparams D) (sb_of_list Id Us) (env_args nil ups) Qn bs).
    { unfold Qn, σ.
      eapply rec_params_args; try eassumption; unfold ptyp_depth; lia. }
    assert (HQp : glu_args Δ (ind_params D) Id nil (Us ++ Qn) (ups ++ bs)).
    { rewrite params_split; apply glu_args_app;
        [ exact (decl_uparams_ass D Hc) | rewrite (length_ind_uparams D Hle); exact HUl | rewrite (length_ind_uparams D Hle); exact Hu |].
      split; [ exact HUs | exact HQn ]. }
    assert (Hcomps : ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us) by (eapply comps_of_uparams; eassumption).
    assert (H01 : tele_full (ind_nr D ups) (List.rev (ind_nparams D)) bs bs)
      by exact (canon_tnr_trans p D ups Hass Hcp _ _ _ Htf (canon_tnr_sym p D ups Hass Hcp _ _ Htf)).
    assert (HnQ : glu_nparams D NEl Δ Us Qn bs) by (eapply nparams_of_glu_args; eassumption).
    assert (HQl : List.length Qn = ind_nn D) by (unfold Qn; rewrite List.length_map; exact HPl).
    assert (EQ : forall Q, apps (a_ind p) (Us ++ Qn) = apps (a_ind p) Q -> Q = Us ++ Qn)
      by (intros Q HQ; apply apps_ind_inj in HQ; congruence).
    apply glu_rec_self.
    - intros bsr Q Hbsr HQ.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      rewrite (EQ _ HQ).
      split; [ rewrite List.length_app, HUl, HQl; unfold ind_nn; lia | split; [ exact H01 |] ].
      intros bsr' Hb'.
      rewrite firstn_app_exact, skipn_app_exact by exact HUl.
      split; [ eapply glu_nparams_resp_per; [ exact HNe | exact Hb' | exact HnQ ] |].
      intros Δ0 φ Hφ.
      pose proof (glu_args_params_top _ _ _ _ Hass Hs (glu_args_wk _ _ _ _ _ _ _ Hass Hs Hφ HQp)) as Ht.
      destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ HR0 Hl Hu Hu _ _ Hb') as [Rr HRr].
      eapply glu_params_top_resp_per_top; [ exact Hl | exact (per_univ_then_per_top_typ HRr) | exact Ht ].
    - intros bsr Q Hbsr HQ Δ' φ Q' Hφ HQ'.
      pose proof (functional_eval_exps' _ _ _ _ Hbsr Ebs) as ->.
      pose proof (EQ _ HQ) as ->.
      destruct (per_univ_elem_ind_reinst _ _ _ _ _ _ _ _ HR0 Hl Hu Hu _ _ (canon_tnr_sym p D ups Hass Hcp _ _ Htf)) as [Rq HRq].
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRq) HRq) as Hself.
      destruct (ind_glu_elem_of_per p D Hl u Rq ups bs Hself Hu)
        as (NP2 & NEl2 & AP2 & AEl2 & DP2 & DEl2 & P2 & El2 & R2 & Hg2 & HP2 & HEl2 & HR2 & HeN2 & HNP2 & HeA2 & HAP2 & HeD2 & HDP2).
      assert (HT2 : Δ ⊢ apps (a_ind p) (Us ++ Qn) ® P2).
      { apply HP2; exists (Us ++ Qn).
        exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Δ (Us ++ Qn) ups bs bu u NP2 NEl2 AP2 AEl2 DP2 DEl2 HΔ HQp Hu Hbu Hule
                 HeN2 HNP2 HeA2 HAP2 HeD2 HDP2). }
      pose proof (glu_univ_elem_exp_conv_uidx (ex_intro _ Rq HRq) Hg Hg2 HN HT2) as HM2.
      apply HEl2 in HM2; destruct HM2 as [_ _ Ps2 HPs2 Hk2].
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      pose proof (glu_args_params_top _ _ _ _ Hass Hs (glu_args_wk _ _ _ _ _ _ _ Hass Hs Hφ HQp)) as Ht.
      destruct (proj2 HPs2 _ _ Hφ) as (HPt2 & _ & _).
      pose proof (glu_params_top_eq p D Δ' _ _ _ Hl HΔ' (ind_rps_of_per _ _ _ _ _ _ Hself Hl _) HPt2 Ht) as Heqq.
      assert (Heqq' : exps_eq_at Δ' (ind_params D) (List.map (fun P => P[φ]ʷ) Ps2) Q').
      { destruct Heqq as [HlE1 HE1]; destruct HQ' as [HlE2 HE2]; split; [ rewrite ?List.length_map in *; lia |].
        destruct HPt2 as [HPl2 _ _]; destruct Ht as [HQl2 _ _].
        eapply (params_eq_trans _ p D _ _ _ Hl HΔ' HPl2 HQl2); [ rewrite ?List.length_map in *; lia | exact HE1 | exact HE2 ]. }
      pose proof (Hk2 Δ' φ Q' Hφ Heqq') as Hgi.
      eapply (ind_glu_elem_mono p D ups NEl2 AEl2 DP2 DEl2 Hass Hcp); [ | | | exact Hgi ].
      + intros k0 vs Hk' Hp0 Γ0 A0 M0 m0 HN0.
        destruct (nparams_lt_ass D k0 Hass ltac:(rewrite List.length_rev, length_nparams; exact Hk')) as [S HS].
        destruct (HeN _ _ _ HS Hp0) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HNP2 _ _ _ _ HS Hp0 Eb) (HNP _ _ _ _ HS Hp0 Eb)) as [_ EE].
        apply EE; exact HN0.
      + intros ms c0 gs0 k0 vs Hm Hc0 Hk' Hp0 Γ0 A0 M0 m0 HN0.
        destruct (nth_error_lt_some' _ _ Hk') as [S HS].
        destruct (HeA _ _ _ _ _ _ Hm Hc0 HS Hp0) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HAP2 _ _ _ _ _ _ _ Hm Hc0 HS Hp0 Eb) (HAP _ _ _ _ _ _ _ Hm Hc0 HS Hp0 Eb)) as [_ EE].
        apply EE; exact HN0.
      + intros ms c0 gs0 gs3 t0 gs4 ws k0 B ys0 Hm Hc0 Heq0 Hw HB Hy1.
        destruct (HeD _ _ _ _ _ _ _ _ _ _ Hm Hc0 Heq0 Hw HB Hy1) as [b Eb].
        destruct (functional_glu_univ_elem _ _ _ _ _ _ (HDP2 _ _ _ _ _ _ _ _ _ _ _ Hm Hc0 Heq0 Hw HB Hy1 Eb)
                    (HDP _ _ _ _ _ _ _ _ _ _ _ Hm Hc0 Heq0 Hw HB Hy1 Eb)) as [EP EE].
        split; intros; [ apply EP | apply EE ]; assumption.
  Qed.

  (** A constructor applied to glued parameters and arguments, related to
      itself in the PER of the inductive type, is an element of it. *)
  Lemma con_ind_glu_elem : forall R0 ns0, DF d_ind p (ups ++ ns0) ≈ d_ind p (ups ++ ns0) ∈ per_univ_elem u ↘ R0 ->
      forall Δ Ps As ns ws, ⊢ Δ ->
        glu_args Δ (ind_params D) Id nil Ps (ups ++ ns) ->
        glu_args Δ (cargs_ctx p D gs) (sb_of_list Id Ps) (env_args nil (ups ++ ns)) As ws ->
        ind_rel p D ups (ind_nr D ups) (ind_ar D ups) (ind_dr ups) ns (d_con p c ((ups ++ ns) ++ ws)) (d_con p c ((ups ++ ns) ++ ws)) ->
        ind_glu_elem p D ups NEl AEl DP DEl Δ Ps (apps (a_con p c) (Ps ++ As)) (d_con p c ((ups ++ ns) ++ ws)).
  Proof.
    intros R0 ns0 HR0 Δ Ps As ns ws HΔ HgP HgA Hrel.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (decl_uparams_ass D Hc) as HassU.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    pose proof (nel_resp_per R0 ns0 HR0) as HNe.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HR0 Hl Hu Hu) as (_ & _ & Hcp & _ & _ & Hadm & _ & _).
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV].
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (LPn : List.length Ps = ind_np D) by exact LP.
    assert (Lns : List.length ns = ind_nn D) by (rewrite List.length_app, Hu in LV; unfold ind_nn, ind_np in *; lia).
    inversion Hrel as [? ? gs0 bs bs' vs vs' Hnsr Hc0 Hbl Hbl' Hs1 Hs2 Hav Hia |]; subst.
    assert (Hlb : List.length bs = List.length (ups ++ ns)) by (rewrite List.length_app, Hu, Lns, Hbl; unfold ind_nn; lia).
    destruct (app_split_eq _ _ _ _ H1 Hlb) as [-> ->].
    assert (Hlb' : List.length bs' = List.length (ups ++ ns)) by (rewrite List.length_app, Hu, Lns, Hbl'; unfold ind_nn; lia).
    destruct (app_split_eq _ _ _ _ H2 Hlb') as [-> ->].
    rewrite Hcon in Hc0; injection Hc0 as <-.
    clear Hbl' Hs2 H1 H2 Hlb Hlb'.
    set (Us := List.firstn (ind_nu D) Ps); set (Ns := List.skipn (ind_nu D) Ps).
    assert (EPs : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
    assert (LU : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
    assert (LN : List.length Ns = ind_nn D) by (unfold Ns; rewrite List.length_skipn; unfold ind_nn; lia).
    assert (HUs : glu_args Δ (ind_uparams D) Id nil Us ups).
    { pose proof (glu_args_uparams_of_params D Hc _ _ _ HgP) as H; rewrite firstn_app_exact in H by exact Hu; exact H. }
    assert (HgP' : glu_args Δ (ind_params D) Id nil (Us ++ Ns) (ups ++ ns)) by (rewrite <- EPs; exact HgP).
    rewrite params_split in HgP'.
    apply glu_args_app in HgP'; [| exact HassU | rewrite (length_ind_uparams D Hle); exact LU | rewrite (length_ind_uparams D Hle); exact Hu ].
    destruct HgP' as [_ HNs].
    assert (Hcomps : ind_glu_comps p D ups NP NEl AP AEl DP DEl Δ Us) by (eapply comps_of_uparams; eassumption).
    assert (Hnp : glu_nparams D NEl Δ Us Ns ns) by (eapply nparams_of_glu_args; eassumption).
    assert (HgA' : glu_args Δ (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As ws) by (rewrite <- EPs; exact HgA).
    pose proof (args_of_glu_args Δ Us Ns ns As ws HΔ Hcomps HUs Hnp Hnsr HgA' Hav) as Harg.
    pose proof (glu_args_params_top _ _ _ _ Hass Hs HgP) as HPt.
    pose proof HPt as [_ HPty _].
    assert (HAty : forall k N T, List.nth_error As k = Some N -> List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id Ps) As) k = Some T -> Δ ⊢ N : T)
      by (intros; eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ]).
    assert (HMt : Δ ⊢ apps (a_con p c) (Ps ++ As) ≈ apps (a_con p c) (Ps ++ As) : apps (a_ind p) Ps).
    { eapply wf_exp_eq_con_apps; [ exact Hl | exact Hcon | exact HΔ | exact LPn | exact LPn | | exact LA | exact LA | ].
      - intros k P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HPty; eassumption.
      - intros k N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl; eapply HAty; eassumption. }
    eapply ind_glu_elem_con; [ exact Hcon | exact LPn | exact Hbl | exact LW | exact LA | exact HMt | | | | exact HAty | | ].
    all: rewrite ?skipn_app_exact by exact Hu.
    - exact Hnsr.
    - exact Hav.
    - fold Us Ns; exact Hnp.
    - rewrite EPs; exact Harg.
    - (** A recursive argument: by its shape, from its gluing at its type. *)
      intros gs1 t gs2 N A v Heq HN HA Hv.
      set (fa := List.firstn (List.length gs1) ws).
      set (As1 := List.firstn (List.length gs1) As).
      assert (Hl1 : List.length gs1 < List.length gs) by (rewrite Heq, List.length_app; cbn; lia).
      assert (Hlfa : List.length fa = List.length gs1) by (unfold fa; rewrite List.length_firstn; lia).
      assert (HlAs1 : List.length As1 = List.length gs1) by (unfold As1; rewrite List.length_firstn; lia).
      assert (HlAs : List.length gs1 <= List.length As) by lia.
      assert (Hpre1 : forall hs1 B hs2 N0 T' v0, gs1 = hs1 ++ ca_arg B :: hs2 -> List.nth_error As (List.length hs1) = Some N0 ->
                List.nth_error (tele_insts (cargs_ctx p D gs) (sb_of_list Id (Us ++ Ns)) As) (List.length hs1) = Some T' ->
                List.nth_error fa (List.length hs1) = Some v0 ->
                Δ ⊢ N0 : T' ® v0 ∈ AEl ns c (List.length (cargs_nonrec hs1)) (nonrec_vals hs1 (List.firstn (List.length hs1) fa))).
      { intros * Heq1 HN0 HT0 Hv0.
        assert (Hlt : List.length hs1 < List.length gs1) by (rewrite Heq1, List.length_app; cbn; lia).
        unfold fa in Hv0 |- *; rewrite List.firstn_firstn, Nat.min_l by lia.
        rewrite List.nth_error_firstn in Hv0; destruct (Nat.ltb_spec (List.length hs1) (List.length gs1)); [| lia ].
        eapply (Harg hs1 B (hs2 ++ ca_rec t :: gs2)); [ rewrite Heq, Heq1, <- List.app_assoc; reflexivity | exact HN0 | exact HT0 | exact Hv0 ]. }
      pose proof (nonrec_prefix_pre _ gs ws gs1 (ca_rec t) gs2 Hav LW Heq) as Hp1; fold fa in Hp1.
      (** The arguments before, glued on the side of all the arguments. *)
      destruct (cargs_suffix_glu p D gs gs1 (ca_rec t :: gs2) Heq HΨ) as [Sb1 HSb1].
      assert (HgA1 : glu_args Δ (cargs_ctx p D gs1) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As1 fa).
      { pose proof HgA' as HgA''.
        rewrite (cargs_split_aux p D gs gs1 (ca_rec t) gs2 Heq), <- (List.firstn_skipn (List.length gs1) As),
          <- (List.firstn_skipn (List.length gs1) ws) in HgA''.
        apply glu_args_app in HgA''; [ exact (proj1 HgA'') | apply cargs_ctx_aux_ass | |];
          rewrite List.length_firstn, length_cargs_ctx; lia. }
      assert (HgPU : glu_args Δ (ind_params D) Id nil (Us ++ Ns) (ups ++ ns)) by (rewrite <- EPs; exact HgP).
      assert (Hσc0 : Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ As1) ® env_args nil ((ups ++ ns) ++ fa) ∈ Sb1).
      { eapply glu_sub_of_list with (C := cargs_ctx p D gs1 ++ ind_params D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
          [ unfold tele_ass; apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]
          | rewrite List.app_nil_r; exact HSb1 | eapply glu_ctx_env_nil; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
          | cbn; apply wf_sub_nil'; exact HΔ |].
        destruct (glu_args_length _ _ _ _ _ _ HgPU) as [LP' LB'].
        apply glu_args_app; [ exact Hass | exact LP' | exact LB' |]; split; [ exact HgPU | exact HgA1 ]. }
      assert (INV : forall R, EF cargs_ctx p D gs1 ++ ind_params D ≈ cargs_ctx p D gs1 ++ ind_params D ∈ per_ctx_env ↘ R ->
                R (env_args nil (ups ++ ns ++ fa)) (env_args nil (ups ++ ns ++ fa))).
      { intros R HR.
        pose proof (cargs_env_rel p D Hc gs gs1 (ca_rec t :: gs2) R Sb1 Δ (Us ++ Ns) (ups ++ ns) _ _ Heq HΔ HR HSb1 HgPU HgA1) as H.
        rewrite <- List.app_assoc in H; exact H. }
      pose proof (cargs_uparams_gargs p D Hl Hc Hdt Hsu HDc c gs Hcon gs1 (ca_rec t :: gs2) ups ns fa Heq Hu Lns Hlfa INV) as Hgu0.
      (** The arguments before, glued on the side of the non-recursive ones. *)
      destruct (gid_dctx _ HG _ _ _ _ _ 0 Hcon Heq ltac:(lia)) as [SbC0 HSbC0].
      cbn [List.firstn doms_ctx List.map List.rev List.app] in HSbC0.
      assert (Hσ0 : Δ ⊢ˢ sb_of_list Id ((Us ++ Ns) ++ nonrec_exps gs1 As1) ® env_args nil ((ups ++ ns) ++ nonrec_vals gs1 fa) ∈ SbC0)
        by (eapply nonrec_args_prefix_glu_sub; eassumption).
      (** The argument, glued at its type. *)
      pose proof HgA as [_ _ HgAe].
      destruct (HgAe _ _ _ _ _ HN HA Hv (cargs_rev_nth_rec p D gs gs1 t gs2 Heq)) as [i' a1 P1 El1 Ha1 Hg1 HP1 HM1].
      fold fa in Ha1.
      pose proof (cargs_rec_type_sh p D gs gs1 t gs2 Ps As A Heq Hle LPn HA) as ETs.
      pose proof (cargs_rec_type p D gs gs1 t gs2 (sb_of_list Id Ps) As A Heq HA) as ETc.
      fold As1 in ETs, ETc.
      rewrite <- sb_of_list_app in ETc.
      fold Us in ETs.
      rewrite EPs in ETs, ETc.
      rewrite <- List.app_assoc in ETs.
      assert (HlNs' : List.length (Ns ++ nonrec_exps gs1 As1) = 0 + List.length (cargs_nonrec gs1) + ind_nn D)
        by (rewrite List.length_app, length_nonrec_exps by exact HlAs1; lia).
      assert (Hfinal : glu_rec p D ups NEl AEl DP DEl Δ (ns ++ nonrec_vals gs1 fa ++ nil) t
                         (ptyp_ty_at p Us (sb_of_list Id (Us ++ (Ns ++ nonrec_exps gs1 As1))) t) N v).
      { eapply (con_rec_glu R0 ns0 HR0 gs1 t gs2 ns fa Heq Lns Hlfa Hnsr Hp1 Hgu0 INV t 0 nil Δ Id Us (Ns ++ nonrec_exps gs1 As1)
                  SbC0 (sb_of_list Id ((Us ++ Ns) ++ As1)) Sb1 N v a1 i' P1 El1);
          [ reflexivity | lia | apply tele_pre_nil | apply per_gargs_nil | exact HΔ | exact HUs | exact HlNs'
          | cbn [List.firstn doms_ctx List.map List.rev List.app]; exact HSbC0
          | rewrite !List.app_nil_r; rewrite <- !List.app_assoc in Hσ0; exact Hσ0
          | cbn [List.firstn sh_ctx List.app]; exact HSb1
          | rewrite !List.app_nil_r; replace (ups ++ ns ++ fa) with ((ups ++ ns) ++ fa) by (rewrite <- List.app_assoc; reflexivity); exact Hσc0
          | cbn [List.repeat List.app]; rewrite <- ETs, <- ETc; reflexivity
          | cbn [List.repeat List.app]; rewrite List.app_nil_r; rewrite <- env_args_app, <- List.app_assoc in Ha1; exact Ha1
          | exact Hg1
          | rewrite <- ETs; exact HP1
          | rewrite <- ETs; exact HM1 ]. }
      rewrite List.app_nil_r in Hfinal; rewrite ETs; exact Hfinal.
  Qed.

End ConGlu.

(** ** The Constructors *)

Section ConFT.
  Variable (p : qname) (D : ind_decl).
  Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (HG : glu_ind_decl D) (Hc : decl_closed D)
    (Hdt : decl_typed gc_deps gc_stack D) (Hsu : ind_sort_univ (ind_sort D)) (HDc : valid_ind_decl D).
  Variable (c : String.string) (gs : list carg).
  Hypothesis (Hcon : ind_con D c = Some gs) (HΨ : ⊩ cargs_ctx p D gs ++ ind_params D).
  Hypothesis (HshV : forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       exists j : nat, sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D
         ⊩ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t) : Typeω@j).

  (** The universes of the sort, below a large one. *)
  Lemma sort_bound : exists n, forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> forall i, n <= i -> uidx_le (IndSem.univ_idx bu) (ul i).
  Proof.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; [ exists i0 | exists 0 ]; intros * Hb i Hi; inversion Hb; subst; cbn; [ lia | exact I ].
  Qed.

  Lemma sort_eval : forall Δ Us ups, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups -> exists bu, ⟦ ind_sort D ⟧ env_args nil ups ↘ bu.
  Proof.
    intros * HΔ HUs.
    destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; [ eexists; constructor |].
    destruct (gid_lvl _ HG) as [n HLu]; rewrite Heq in HLu; cbn [ind_sort_lvl] in HLu.
    pose proof HLu as [SbU HSbU _ _].
    pose proof (glu_sub_uparams D Hc _ _ _ _ HΔ HSbU HUs) as Hσu.
    destruct (glu_rel_exp_level_elim HSbU HLu _ _ _ Hσu) as (l' & Hl' & _).
    exists (d_suniv l'); econstructor; exact Hl'.
  Qed.

  Lemma exps_eq_at_app_refl : forall Δ C1 C2 Xs Ys Zs, tele_ass C1 -> tele_ass C2 -> List.length Xs = List.length C1 ->
      exps_eq_at Δ C1 Xs Ys ->
      (forall k Z T, List.nth_error Zs k = Some Z -> List.nth_error (tele_insts C2 (sb_of_list Id Xs) Zs) k = Some T -> Δ ⊢ Z : T) ->
      exps_eq_at Δ (C2 ++ C1) (Xs ++ Zs) (Ys ++ Zs).
  Proof.
    intros * HC1 HC2 HXl [HlXY HXY] HZ; split; [ rewrite !List.length_app; congruence |].
    intros k X Y A HX HY HA.
    rewrite tele_insts_app in HA by (try exact HC1; exact HXl).
    assert (Hl2 : List.length (tele_insts C1 Id Xs) = List.length Xs) by (rewrite length_tele_insts by exact HC1; lia).
    destruct (Nat.lt_ge_cases k (List.length Xs)) as [Hk | Hk].
    - rewrite List.nth_error_app1 in HX, HA by lia; rewrite List.nth_error_app1 in HY by lia; eauto.
    - rewrite List.nth_error_app2 in HX, HA by lia; rewrite List.nth_error_app2 in HY by lia.
      rewrite Hl2 in HA; replace (k - List.length Ys) with (k - List.length Xs) in HY by lia.
      rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; eapply HZ; eassumption.
  Qed.

  Lemma con_apps_eq : forall Δ Ps Ps' As vs ρ ws, ⊢ Δ -> glu_args Δ (ind_params D) Id nil Ps vs ->
      glu_args Δ (cargs_ctx p D gs) (sb_of_list Id Ps) ρ As ws -> exps_eq_at Δ (ind_params D) Ps Ps' ->
      Δ ⊢ apps (a_con p c) (Ps ++ As) ≈ apps (a_con p c) (Ps' ++ As) : apps (a_ind p) Ps.
  Proof.
    intros * HΔ HgP HgA [HlPP HPP].
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (dc_params _ Hc) as Hs.
    destruct (glu_args_params_top _ _ _ _ Hass Hs HgP) as [HPl _ _].
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA _]; rewrite length_cargs_ctx in LA.
    eapply wf_exp_eq_con_apps; [ exact Hl | exact Hcon | exact HΔ | exact HPl | congruence | exact HPP | exact LA | exact LA |].
    intros k N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl.
    eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ].
  Qed.

  (** The constructor applied to glued parameters and arguments is glued at
      the type at the parameters. *)
  Lemma con_base : forall Δ Ms vs (i : nat) b P El, ⊢ Δ ->
      (forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> uidx_le (IndSem.univ_idx bu) (ul i)) ->
      glu_args Δ (cargs_ctx p D gs ++ ind_params D) Id nil Ms vs ->
      ⟦ apps (a_ind p) (ind_pvars D (List.length gs)) ⟧ env_args nil vs ↘ b -> DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R (d_con p c vs) (d_con p c vs)) ->
      Δ ⊢ apps (a_con p c) Ms : (apps (a_ind p) (ind_pvars D (List.length gs)))[sb_of_list Id Ms] ® d_con p c vs ∈ El.
  Proof.
    intros * HΔ Hbnd Hg Hb Hglu HPER.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof Hc as [_ Hle Hs _ _ _ _].
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : tele_ass (cargs_ctx p D gs ++ ind_params D)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]).
    pose proof (cargs_ctx_closed p D c gs gs nil Hc Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct (cargs_ctx_wf _ _ p D c gs Hdt Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HwfC & _ & _).
    destruct (glu_args_length _ _ _ _ _ _ Hg) as [LM LV]; rewrite List.length_app, length_cargs_ctx in LM, LV.
    set (Ps := List.firstn (ind_np D) Ms); set (As := List.skipn (ind_np D) Ms).
    set (ps := List.firstn (ind_np D) vs); set (ws := List.skipn (ind_np D) vs).
    assert (EM : Ms = Ps ++ As) by (symmetry; apply List.firstn_skipn).
    assert (EV : vs = ps ++ ws) by (symmetry; apply List.firstn_skipn).
    assert (LPs : List.length Ps = ind_np D) by (unfold Ps; rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (Lps : List.length ps = ind_np D) by (unfold ps; rewrite List.length_firstn; unfold ind_np in *; lia).
    assert (LAs : List.length As = List.length gs) by (unfold As; rewrite List.length_skipn; unfold ind_np in *; lia).
    assert (Lws : List.length ws = List.length gs) by (unfold ws; rewrite List.length_skipn; unfold ind_np in *; lia).
    pose proof Hg as Hg0.
    rewrite EM, EV in Hg0; apply glu_args_app in Hg0; [| exact Hass | exact LPs | exact Lps ].
    destruct Hg0 as [HgP HgA].
    assert (EB : (apps (a_ind p) (ind_pvars D (List.length gs)))[sb_of_list Id Ms] = apps (a_ind p) Ps).
    { rewrite EM, apps_exp_sub; cbn [exp_sub]; f_equal.
      unfold ind_pvars; rewrite <- LAs, <- LPs; apply vars_from_sb_of_list_app. }
    rewrite EB.
    assert (Eb : ⟦ apps (a_ind p) (ind_pvars D (List.length gs)) ⟧ env_args nil vs ↘ d_ind p ps).
    { apply Modules.eval_apps_exp; exists (d_ind p nil), ps; split; [ constructor | split ].
      - unfold ind_pvars; rewrite EV, <- Lws, <- Lps; apply IndSem.eval_vars_from_args.
      - change (d_ind p ps) with (d_ind p (nil ++ ps)); apply (IndCases.eval_apps_ind D p Hl); cbn; lia. }
    assert (b = d_ind p ps) as -> by (eapply functional_eval_exp; eassumption).
    set (ups := List.firstn (ind_nu D) ps) in *; set (ns := List.skipn (ind_nu D) ps) in *.
    assert (Eps : ps = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; lia).
    clearbody ups ns.
    rewrite Eps in Hglu, HPER, HgP, HgA, EV.
    clear Hb Eb Eps.
    destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
    destruct (ind_glu_elem_of_per p D Hl i Rb ups ns HRb Hu)
      as (NP & NEl & AP & AEl & DP & DEl & P2 & El2 & R2 & Hg2 & HP2 & HEl2 & HR2 & HeN & HNP & HeA & HAP & HeD & HDP).
    destruct (functional_glu_univ_elem _ _ _ _ _ _ Hglu Hg2) as [_ EEl].
    apply EEl, HEl2.
    destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ HRb Hl Hu Hu) as (_ & _ & _ & _ & _ & _ & _ & Hrel).
    pose proof (HPER _ HRb) as Hrb.
    assert (HUs : glu_args Δ (ind_uparams D) Id nil (List.firstn (ind_nu D) Ps) ups).
    { pose proof (glu_args_uparams_of_params D Hc _ _ _ HgP) as H; rewrite firstn_app_exact in H by exact Hu; exact H. }
    destruct (sort_eval _ _ _ HΔ HUs) as [bu Hbu].
    pose proof (Hbnd _ _ Hbu) as Hule.
    pose proof (glu_args_params_top _ _ _ _ Hass Hs HgP) as HPt.
    refine (mk_ind_glu_exp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ps _ _); [ | apply HR2; exact Hrb | |].
    { rewrite EM; pose proof (con_apps_eq Δ Ps Ps As _ _ ws HΔ HgP HgA (glu_params_top_refl _ _ _ _ HPt)) as H; gen_presups; assumption. }
    { exact (ind_typ_at_of_args p D Hl HG Hc Hdt Hsu Δ Ps ups ns bu (ul i) NP NEl AP AEl DP DEl HΔ HgP Hu Hbu Hule HeN HNP HeA HAP HeD HDP). }
    intros Δ' φ Ps' Hφ HPs'.
    assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
    pose proof (glu_args_resp_eq Δ' _ nil _ Ps' _ Hass (comps_params_wf' D Hdt) HΔ' HPs' (glu_args_wk _ _ _ _ _ _ _ Hass Hs Hφ HgP)) as HgP'.
    pose proof (glu_args_wk _ _ _ _ _ _ _ HassC HsC Hφ Hg) as Hgw.
    rewrite EM, List.map_app, EV in Hgw.
    assert (LPw : List.length (List.map (fun M => M[φ]ʷ) Ps) = List.length (ind_params D)) by (rewrite List.length_map; exact LPs).
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [_ Lupn].
    pose proof Hgw as Hgw'; apply glu_args_app in Hgw'; [| exact Hass | exact LPw | exact Lupn ].
    destruct Hgw' as [_ HgAw].
    pose proof (exps_eq_at_app_refl Δ' (ind_params D) (cargs_ctx p D gs) _ Ps' (List.map (fun M => M[φ]ʷ) As)
                  Hass (cargs_ctx_aux_ass _ _ _ _) LPw HPs'
                  ltac:(intros; eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgAw | eassumption | eassumption ])) as Heq2.
    pose proof (glu_args_resp_eq Δ' _ nil _ _ _ HassC HwfC HΔ' Heq2 Hgw) as Hg'.
    destruct HPs' as [HlPP HPP].
    apply glu_args_app in Hg'; [| exact Hass | rewrite <- HlPP; exact LPw | exact Lupn ].
    destruct Hg' as [_ HgA'].
    pose proof (con_ind_glu_elem p D Hl HG Hc Hdt Hsu HDc c gs Hcon HΨ ups bu (ul i) NP NEl AP AEl DP DEl Hu Hbu Hule HeN HNP HeA HAP
                  HeD HDP HshV Rb ns HRb Δ' Ps' (List.map (fun M => M[φ]ʷ) As) ns ws HΔ' HgP' HgA'
                  ltac:(apply Hrel; rewrite <- EV; exact Hrb)) as Hgi.
    rewrite EV.
    eapply ind_glu_elem_resp_exp_eq; [ exact Hgi |].
    rewrite EM, apps_wk, List.map_app; cbn [exp_wk].
    eapply con_apps_eq; [ exact HΔ' | exact HgP' | exact HgA' |].
    split; [ congruence |].
    eapply (params_eq_sym _ p D); [ exact Hl | exact HΔ' | | | exact HPP ]; rewrite ?List.length_map in *; congruence.
  Qed.

  (** The PER of the closed constant [a_con p c] at its type. *)
  Lemma con_former_per : forall (i : nat) R a, ⟦ ctx_pi (cargs_ctx p D gs ++ ind_params D) (apps (a_ind p) (ind_pvars D (List.length gs))) ⟧ nil ↘ a ->
      DF a ≈ a ∈ per_univ_elem i ↘ R -> R (d_con p c nil) (d_con p c nil).
  Proof.
    intros * Ha HR.
    assert (HΔ0 : ⊢ ⋅) by (constructor; eapply ctx_wf_gctx; exact (comps_params_wf' D Hdt)).
    destruct (con_ty_typed0 _ _ _ _ _ _ Hdt Hc Hl Hcon) as [j Hj].
    destruct (cargs_ctx_wf _ _ p D c gs Hdt Hc Hl (cons_lookup_in _ _ _ Hcon) gs nil (eq_sym (List.app_nil_r gs))) as (HΨ0 & _ & _).
    pose proof (shape_rest_wf' _ _ _ _ _ _ Hdt Hc Hl Hcon) as Hsh0.
    assert (Hty : ⋅ ⊢ a_con p c : con_ty p D gs) by (eapply wf_con; eassumption).
    unfold con_ty in Hty; rewrite <- ctx_pi_app in Hty.
    destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hty)) as (env_rel & Henv & j' & Hsimp).
    assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
    destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
    assert (a1 = a) as -> by (eapply functional_eval_exp; eassumption).
    assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
    inversion Hm1; subst; inversion Hm2; subst.
    apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
  Qed.

  (** The constructor is glued at its type. *)
  Lemma glu_rel_exp_con0 : ⋅ ⊩ a_con p c : con_ty p D gs.
  Proof.
    pose proof (decl_closed_params D Hc) as Hass.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : tele_ass (cargs_ctx p D gs ++ ind_params D)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact Hass ]).
    pose proof (cargs_ctx_closed p D c gs gs nil Hc Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct (cargs_ctx_wf _ _ p D c gs Hdt Hc Hl Hin gs nil (eq_sym (List.app_nil_r gs))) as (HwfC & _ & _).
    destruct (con_ty_typed0 _ _ _ _ _ _ Hdt Hc Hl Hcon) as [j Hj].
    destruct sort_bound as [n0 Hn0].
    destruct HΨ as [SbC HSbC].
    assert (HSbC0 : EG (cargs_ctx p D gs ++ ind_params D) ++ ⋅ ∈ glu_ctx_env ↘ SbC) by (rewrite List.app_nil_r; exact HSbC).
    destruct (glu_ctx_env_entries_valid _ _ _ HassC HSbC0 (Nat.max j n0)) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ con_ty p D gs : Typeω@i) by (eapply lift_exp_ge; [| exact Hj ]; lia).
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact HwfC).
    eapply (glu_closed_const _ _ i (d_con p c nil)); [ reflexivity | intros; apply (con_ty_sub p D c gs); assumption | exact Hi | intros; constructor |].
    intros Δ σ Hσ a P El Ha Hglu.
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold con_ty in Hi'; rewrite <- ctx_pi_app in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassC Hi') as [HCs _].
    replace (con_ty p D gs) with ((con_ty p D gs)[σ]) by (apply (con_ty_sub p D c gs); assumption).
    unfold con_ty in Ha |- *; rewrite <- ctx_pi_app in Ha |- *.
    change (a_con p c) with (apps (a_con p c) nil).
    eapply (ctx_pi_glu_elem (List.length gs + ind_np D) (d_con p c) (a_con p c)) with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbC) (ρ := nil) (xs := nil);
      [ | reflexivity | exact HassC | eapply glu_ctx_env_nil; [ reflexivity | exact Hg0 ] | exact HSbC0
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | exact Hσ | rewrite List.length_app, length_cargs_ctx; reflexivity | | | | exact Ha | exact Hglu ].
    - intros xs x Hx; eapply eval_app_con; [ exact Hl | exact Hcon | lia ].
    - cbn [apps_exp]; rewrite ctx_pi_app; change (ctx_pi (ind_params D) (ctx_pi (cargs_ctx p D gs) (apps (a_ind p) (ind_pvars D (List.length gs))))) with (con_ty p D gs).
      pose proof (shape_rest_wf' _ _ _ _ _ _ Hdt Hc Hl Hcon) as Hsh0.
      rewrite (con_ty_sub p D c gs) by assumption; eapply wf_con; eassumption.
    - intros R a' Ha' HR; exact (con_former_per _ _ _ Ha' HR).
    - intros Δ' φ Ms vs Hφ Hg b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ HassC HsC) in Hg.
      destruct (glu_args_length _ _ _ _ _ _ Hg) as [HMl _].
      rewrite (sb_of_list_scoped_base _ _ _ Id).
      2:{ rewrite HMl, List.length_app, length_cargs_ctx; apply exp_scoped_apps; split; [ cbn; exact I | apply vars_from_scoped; unfold ind_np; lia ]. }
      eapply con_base; [ exact HΔ' | | exact Hg | exact Hb | exact Hglub | exact HPb ].
      intros; eapply Hn0; [ eassumption | lia ].
  Qed.

End ConFT.

End Fixed_GCtx.

(** ** Closed Gluing at [⋅] Weakens to Every Glued Context

    Simpler than [closed_weaken_sem]: [nil_glu_sub_pred] does not constrain
    the environment, and the terms are the same, so no closedness is needed. *)

Section Weaken.
  Context {GC : GCtx}.

  Lemma wf_sub_nil : forall Δ σ, ⊢ Δ -> Δ ⊢ˢ σ : ⋅.
  Proof.
    intros * HΔ; constructor; [ exact HΔ | apply wf_ctx_empty; eapply ctx_wf_gctx; exact HΔ | | |];
      intros * Hx; inversion Hx.
  Qed.

  Lemma glu_rel_exp_nil_weaken : forall Γ N T, ⊩ Γ -> ⋅ ⊩ N : T -> Γ ⊩ N : T.
  Proof.
    intros * [SbΓ HΓ] [Sb0 H0 i Hi].
    eapply mk_glu_rel_exp with (gre_lvl := i); [ exact HΓ |]; intros Δ σ ρ Hσ.
    apply Hi.
    inversion H0 as [Sb' Heq Hg | | |]; subst.
    apply (Heq Δ σ ρ); cbn.
    apply wf_sub_nil, (wf_sub_dom _ _ _ _ _ (glu_ctx_env_sub_escape HΓ _ _ _ Hσ)).
  Qed.

  (** A type a glued context ends with is glued. *)
  Lemma glu_rel_typ_of_ctx_ext : forall Γ A, ⊩ Γ ▹ A -> exists i : nat, Γ ⊩ A : Typeω@i.
  Proof.
    intros * [Sb HS].
    assert (HΓ : exists TSb, EG Γ ∈ glu_ctx_env ↘ TSb) by (inversion HS; subst; eexists; eassumption).
    destruct HΓ as [TSb HΓ].
    destruct (glu_ctx_env_cons_clean_inversion HΓ HS) as (i & _ & HAs & _).
    exists i; eapply mk_glu_rel_exp with (gre_lvl := S i); [ exact HΓ |]; intros Δ σ ρ Hσ.
    exact (glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub (glu_ctx_env_sub_escape HΓ _ _ _ Hσ) (HAs _ _ _ Hσ)).
  Qed.
End Weaken.

(** ** The Type Former and the Constructors, at the Target *)

Lemma glu_ind_decl_of_emb : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    ind_lookup Θ2 Ξ2 p = Some D /\ @glu_ind_decl (gc_mk Θ2 Ξ2) D /\ decl_closed D /\ ind_sort_univ (ind_sort D) /\
    decl_typed Θ2 Ξ2 D.
Proof.
  intros * He HΓ Hl.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
  pose proof (decl_typed_emb _ _ _ _ _ (gem_emb _ _ _ _ He) Hdt) as Hdt2.
  pose proof (dt_sort_univ _ _ _ Hdt) as Hsu.
  pose proof (ind_lookup_gc_sub _ _ _ _ _ _ (em_res _ _ _ _ (gem_emb _ _ _ _ He)) Hl) as Hl2.
  split; [ exact Hl2 | split; [ exact (gem_ind _ _ _ _ He _ _ Hl) | split; [ exact Hc | split; [ exact Hsu | exact Hdt2 ] ] ] ].
Qed.

Lemma glu_rel_exp_ind_of_emb : forall Θ Ξ Θ2 Ξ2 Γ p D, glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ind_lookup Θ Ξ p = Some D ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_ind p) (ind_ty D).
Proof.
  intros * He HΓ Hl HΓ2.
  destruct (glu_ind_decl_of_emb _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_ind0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

Lemma glu_rel_exp_con_of_emb : forall Θ Ξ Θ2 Ξ2 Γ p D c gs (i : nat), glu_emb Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ind_lookup Θ Ξ p = Some D -> ind_con D c = Some gs ->
    @glu_rel_ctx (gc_mk Θ2 Ξ2) Γ -> @glu_rel_ctx (gc_mk Θ2 Ξ2) (cargs_ctx p D gs ++ ind_params D) ->
    (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       forall Θ0 Ξ0, glu_emb Θ Ξ Θ0 Ξ0 ->
       @glu_rel_ctx (gc_mk Θ0 Ξ0) ((sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                                    ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t))) ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i -> @glu_rel_exp (gc_mk Θ2 Ξ2) ⋅ (con_ty p D gs) (Typeω@i) ->
    @glu_rel_exp (gc_mk Θ2 Ξ2) Γ (a_con p c) (con_ty p D gs).
Proof.
  intros * He HΓ Hl Hcon HΓ2 HΨ2 Hsh Hty HTy.
  assert (HshV : forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
       exists j : nat, @glu_rel_exp (gc_mk Θ2 Ξ2)
         (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
         (ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) (Typeω@j))
    by (intros * Heq Hk; apply (@glu_rel_typ_of_ctx_ext (gc_mk Θ2 Ξ2)); exact (Hsh _ _ _ _ Heq Hk _ _ He)).
  destruct (glu_ind_decl_of_emb _ _ _ _ _ _ _ He HΓ Hl) as (Hl2 & HG & Hc & Hsu & Hdt2).
  pose proof (vem_ind _ _ _ _ (valid_emb_refl _ _ (em_wf _ _ _ _ (gem_emb _ _ _ _ He))) p D Hl2) as HDc.
  apply (@glu_rel_exp_nil_weaken (gc_mk Θ2 Ξ2)); [ exact HΓ2 |].
  eapply (@glu_rel_exp_con0 (gc_mk Θ2 Ξ2)); eassumption.
Qed.

(** ** The Rules

    The type former and the constructors read syntactic premises of their
    rules: a declaration is typed by its derivation. *)

#[local] Generalizable All Variables.

Lemma glu_ind :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_ind p : ind_ty D ).
Proof. glu_intro; eapply glu_rel_exp_ind_of_emb; eassumption. Qed.

Lemma glu_con :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     (forall gs1 t gs2 k, gs = gs1 ++ ca_rec t :: gs2 -> k <= List.length (ptyp_doms t) ->
        ⊩ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn k (ptyp_doms t)) ++ cargs_ctx p D gs1 ++ ind_params D)
                  ▹ ptyp_ty p D (List.repeat false k ++ cargs_pat gs1) (ptyp_skip k t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ ⋅ ⊩ con_ty p D gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ a_con p c : con_ty p D gs ).
Proof. glu_intro; eapply glu_rel_exp_con_of_emb; eassumption. Qed.

Lemma glu_exp_eq_ind_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_con_cong :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_con D c = Some gs ->
     ⊩ Θ ⍮ Ξ ⍮ cargs_ctx p D gs ++ ind_params D ->
     Θ ⍮ Ξ ⍮ ⋅ ⊩ con_ty p D gs : Typeω@i ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
