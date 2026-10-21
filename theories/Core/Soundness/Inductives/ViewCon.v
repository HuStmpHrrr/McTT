(** * The Constructors of a View in the Gluing Model

    A view's constructor is its container's at the view's instance of the
    container's uniform parameters ([wf_exp_eq_con_view]): the view's
    parameters and arguments, glued along the view's telescopes, are glued
    along the container's at the instance, since the two telescopes are
    equal there, syntactically ([dt_view_nparams], [dt_view_args]) and in
    the PER model; then the container's constructor is glued at its type
    ([con_base]), which is the view's constructor's. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Completeness.Inductives Require Decl.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes FiledViews ViewEquations ViewArgs.
From Mctt.Core.Completeness.Inductives Require Con.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.LogicalRelation Require Substitution.
From Mctt.Core.Completeness.Global Require Args.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Presup DescTyping.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Inductives Require Views.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  LevelCases
  LogicalRelation
  SubtypingCases
  VariableCases
  UniverseCases.
From Mctt.Core.Soundness.Inductives Require Import Args Comps Con.
Import Domain_Notations Wk_Notations.
#[local] Open Scope list_scope.
Import Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Equal Telescopes, Instantiated

    The instances of two equal telescopes at the same terms are equal. *)

Lemma ctx_rev_split : forall (C : ctx) k e, List.nth_error (List.rev C) k = Some e ->
    exists C1 Pre, C = C1 ++ e :: Pre /\ List.length Pre = k.
Proof.
  intros * H; destruct (List.nth_error_split _ _ H) as (l1 & l2 & E & Hl).
  exists (List.rev l2), (List.rev l1); split; [| rewrite List.length_rev; exact Hl ].
  rewrite <- (List.rev_involutive C), E, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma ext_eq_split : forall Γ C1 e Pre C1' e' Pre', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ C1 ++ e :: Pre ≈ C1' ++ e' :: Pre' ->
    List.length C1 = List.length C1' -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ e :: Pre ≈ e' :: Pre'.
Proof.
  induction C1 as [| e1 C1 IH]; intros * H Hl; destruct C1' as [| e1' C1']; cbn in Hl; try lia; [ exact H |].
  eapply IH; [ eapply ext_eq_cons_inv; exact H | lia ].
Qed.

Lemma tele_insts_ext_eq : forall Γ Δ Δ' Ms, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Γ ⊢ N : T) ->
    forall k T T', List.nth_error (tele_insts Δ Id Ms) k = Some T -> List.nth_error (tele_insts Δ' Id Ms) k = Some T' ->
      exists i : nat, Γ ⊢ T ≈ T' : Typeω@i.
Proof.
  intros * HΔ Ha Ha' Hl HMs k T T' HT HT'.
  destruct (tele_insts_nth _ _ _ _ _ HT) as (A & HA & ->).
  destruct (tele_insts_nth _ _ _ _ _ HT') as (A' & HA' & ->).
  destruct (ctx_rev_split _ _ _ HA) as (C1 & Pre & -> & HPl).
  destruct (ctx_rev_split _ _ _ HA') as (C1' & Pre' & -> & HPl').
  pose proof (ext_eq_length _ _ _ _ _ HΔ) as HlΔ; rewrite !List.length_app in HlΔ; cbn in HlΔ.
  pose proof (ext_eq_split _ _ _ _ _ _ _ HΔ ltac:(lia)) as H.
  destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H) as (i & HPre & _ & HAA & _).
  assert (HaP : tele_ass Pre) by (unfold tele_ass in Ha; apply List.Forall_app in Ha as [_ H']; inversion H'; assumption).
  assert (Hk : k <= List.length Ms) by (rewrite Hl, List.length_app; cbn; lia).
  assert (Hσ : Γ ⊢ˢ sb_of_list Id (List.firstn k Ms) : Pre ++ Γ).
  { apply wf_sub_of_list_id; [ exact HaP | exact (ext_eq_ctx_left _ _ _ _ _ HPre) | rewrite List.length_firstn; lia |].
    intros j N T0 HN HT0.
    assert (Hj : j < k) by (assert (j < List.length (List.firstn k Ms)) by (apply List.nth_error_Some; congruence);
                            rewrite List.length_firstn in *; lia).
    apply (HMs j).
    - rewrite List.nth_error_firstn in HN; destruct (Nat.ltb_spec j k); [ exact HN | lia ].
    - rewrite <- (List.firstn_skipn k Ms).
      replace (C1 ++ ce_ass A :: Pre) with ((C1 ++ ce_ass A :: nil) ++ Pre) by (rewrite <- List.app_assoc; reflexivity).
      rewrite tele_insts_app by (try exact HaP; rewrite List.length_firstn; lia).
      rewrite List.nth_error_app1; [ exact HT0 |].
      rewrite length_tele_insts by exact HaP; rewrite List.length_firstn; lia. }
  exists i; exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HAA Hσ).
Qed.

(** ** Glued Arguments along Related Telescopes

    A term glued at a type of a value is glued at an equal type of a
    related value. *)
Lemma glu_arg_transfer : forall Δ ρ ρ' A A' T T' M v a' (k j : nat), glu_arg Δ ρ A T M v -> ⟦ A' ⟧ ρ' ↘ a' ->
    (forall a, ⟦ A ⟧ ρ ↘ a -> Dom a ≈ a' ∈ per_univ k) -> Δ ⊢ T ≈ T' : Typeω@j -> glu_arg Δ ρ' A' T' M v.
Proof.
  intros * [l a P El Ea Hg HP HM] Ea' Hrel HTT.
  destruct (Hrel _ Ea) as [R HR].
  set (n := Nat.max (ulvl l) (Nat.max k j)).
  assert (Hln : uidx_le l (ul n)) by (apply uidx_le_ul_max; unfold n; lia).
  destruct (glu_univ_elem_cumu_ge_uidx Hln Hg) as (Pn & Eln & Hgn).
  pose proof (glu_univ_elem_typ_cumu_ge_uidx Hln Hg Hgn HP) as HPn.
  pose proof (glu_univ_elem_exp_cumu_ge_uidx Hln Hg Hgn HM) as HMn.
  pose proof (per_univ_elem_cumu_ge k n _ _ _ ltac:(unfold n; lia) HR) as HRn.
  pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ R HRn) Hgn) as Hgn'.
  pose proof (lift_exp_eq_ge _ _ _ _ _ j n ltac:(unfold n; lia) HTT) as HTTn.
  exact (mk_glu_arg _ _ _ _ _ _ (ul n) a' Pn Eln Ea' Hgn' (glu_univ_elem_typ_resp_exp_eq _ _ _ _ Hgn' _ _ _ HPn HTTn)
           (glu_univ_elem_trm_resp_typ_exp_eq _ _ _ _ Hgn' _ _ _ _ _ HMn HTTn)).
Qed.

(** Glued arguments of a telescope are glued arguments of another one of
    the same length, whose types, at the arguments before, have values
    related to the first's and instances equal to its. *)
Lemma glu_args_transfer : forall Δ C C' τ τ' ρ ρ' Ms vs, tele_ass C -> tele_ass C' -> List.length C = List.length C' ->
    glu_args Δ C τ ρ Ms vs ->
    (forall k A A' a, List.nth_error (List.rev C) k = Some (ce_ass A) -> List.nth_error (List.rev C') k = Some (ce_ass A') ->
       k < List.length vs -> ⟦ A ⟧ env_args ρ (List.firstn k vs) ↘ a ->
       per_gargs (List.firstn k (List.rev C')) ρ' ρ' (List.firstn k vs) (List.firstn k vs) ->
       exists a' (i : nat), ⟦ A' ⟧ env_args ρ' (List.firstn k vs) ↘ a' /\ Dom a ≈ a' ∈ per_univ i) ->
    (forall k T T', List.nth_error (tele_insts C τ Ms) k = Some T -> List.nth_error (tele_insts C' τ' Ms) k = Some T' ->
       exists j : nat, Δ ⊢ T ≈ T' : Typeω@j) ->
    glu_args Δ C' τ' ρ' Ms vs.
Proof.
  intros * Hass Hass' HlC [L1 L2 H] Hsem Hsyn.
  assert (Hall : forall n, n <= List.length C ->
             (forall k M T v A', k < n -> List.nth_error Ms k = Some M -> List.nth_error (tele_insts C' τ' Ms) k = Some T ->
                List.nth_error vs k = Some v -> List.nth_error (List.rev C') k = Some (ce_ass A') ->
                glu_arg Δ (env_args ρ' (List.firstn k vs)) A' T M v) /\
             per_gargs (List.firstn n (List.rev C')) ρ' ρ' (List.firstn n vs) (List.firstn n vs)).
  { induction n as [| n IH]; intros Hn; [ split; [ intros; lia | constructor ] |].
    destruct (IH ltac:(lia)) as [IHg IHp].
    destruct (nth_error_lt_some' Ms n ltac:(lia)) as [M HM].
    destruct (nth_error_lt_some' vs n ltac:(lia)) as [v Hv].
    destruct (glu_args_ass_nth C n Hass ltac:(lia)) as [A HA].
    destruct (glu_args_ass_nth C' n Hass' ltac:(lia)) as [A' HA'].
    destruct (nth_error_lt_some' (tele_insts C τ Ms) n) as [T HT]; [ rewrite length_tele_insts by exact Hass; lia |].
    destruct (nth_error_lt_some' (tele_insts C' τ' Ms) n) as [T' HT']; [ rewrite length_tele_insts by exact Hass'; lia |].
    pose proof (H _ _ _ _ _ HM HT Hv HA) as Hga.
    pose proof Hga as [l a P El Ea Hg _ _].
    destruct (Hsem n A A' a HA HA' ltac:(lia) Ea IHp) as (a' & i & Ea' & Hrel).
    destruct (Hsyn n T T' HT HT') as [j Hj].
    assert (Hga' : glu_arg Δ (env_args ρ' (List.firstn n vs)) A' T' M v).
    { eapply glu_arg_transfer; [ exact Hga | exact Ea' | | exact Hj ].
      intros a0 Ea0; assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption); exact Hrel. }
    split.
    - intros k M0 T0 v0 A0 Hk HM0 HT0 Hv0 HA0.
      destruct (Nat.lt_ge_cases k n) as [Hlt | Hge]; [ exact (IHg _ _ _ _ _ Hlt HM0 HT0 Hv0 HA0) |].
      assert (k = n) as -> by lia.
      rewrite HM in HM0; rewrite HT' in HT0; rewrite Hv in Hv0; rewrite HA' in HA0.
      injection HM0 as <-; injection HT0 as <-; injection Hv0 as <-; injection HA0 as <-; exact Hga'.
    - rewrite (firstn_S_snoc _ _ _ HA'), (firstn_S_snoc _ _ _ Hv).
      destruct Hga' as [l' a'' P' El' Ea'' Hg' _ HM'].
      destruct (glu_univ_elem_per_univ _ _ _ _ Hg') as [R' HR'].
      pose proof (glu_univ_elem_per_elem _ _ _ _ Hg' _ _ _ _ _ HM' HR') as Hvv.
      apply (Decl.per_gargs_snoc _ _ _ _ _ _ _ _ (ulvl l') R');
        [ rewrite List.length_firstn, List.length_firstn, List.length_rev; lia | exact IHp | | exact Hvv ].
      exact (mk_rel_mod_eval a'' a'' Ea'' Ea'' (per_univ_elem_cumu_uidx _ _ _ _ HR' _ (uidx_le_ulvl l'))). }
  constructor; [ lia | lia |].
  intros k M T v A' HM HT Hv HA'.
  assert (Hk : k < List.length C) by (assert (k < List.length vs) by (apply List.nth_error_Some; congruence); lia).
  exact (proj1 (Hall (List.length C) (le_n _)) k M T v A' Hk HM HT Hv HA').
Qed.

(** ** Arguments of a Closed Telescope, Glued *)

(** A term glued at a type of one of two related values is glued at that
    type of the other, at some universe. *)
Lemma glu_transfer_per_elem : forall (j : uidx) (i : nat) a b P El Γ T M m, DG a ∈ glu_univ_elem j ↘ P ↘ El ->
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
  pose proof (gsub_closed_inst C Γ Ms Hass HC HΓ Hl HMs) as Hg0.
  destruct (closed_app_sem C Γ Hass HC HΓ) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ]; destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  pose proof (Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) Hv) as Hev.
  pose proof (rel_sub_under_ctx_at' (Completeness.LogicalRelation.Instance.gsub_valid Hg0) HRΓ HRCΓ _ _ _ _ Hρ Hev Hev) as H1.
  apply (Hres _ _ HRC HRCΓ) in H1.
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Hv)).
  pose proof (closed_env_base C RC vs vs ρ ρ ρ nil Hass HC HRC Lv Lv H1) as H2.
  assert (HC' : ⊨ List.rev (List.rev C) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HC).
  assert (HRC' : EF List.rev (List.rev C) ++ ⋅ ≈ List.rev (List.rev C) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  assert (L' : List.length vs = List.length (List.rev C)) by (rewrite List.length_rev; exact Lv).
  destruct (Decl.rel_gargs (List.rev C) ⋅ _ RC Args.per_ctx_env_nil_true HC' (List.Forall_rev Hass) HRC' ρ nil vs vs L' L' H2)
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
  assert (Lv : List.length vs = List.length C) by (rewrite <- Hl; exact (Completeness.Inductives.Model.eval_exps_length _ _ _ Hv)).
  constructor; [ rewrite List.length_map; exact Hl | exact Lv |].
  intros k M T v A HM HT Hv' HA.
  apply nth_error_map_inv in HM as (N & HN & ->).
  rewrite <- (tele_insts_sub C 0 Id Id σ Ms Hass Hs ltac:(intros; lia)) in HT.
  apply nth_error_map_inv in HT as (T0 & HT0 & ->).
  destruct (glu_rel_exp_clean_inversion1 HSb (HMg k N T0 HN HT0)) as [i Hi].
  destruct (Hi _ _ _ Hσ) as [a m P El Ea Em Hgl HNg].
  destruct (Completeness.Inductives.Model.eval_exps_nth _ _ _ _ _ Hv HN) as (v0 & Hv0 & Ev0).
  rewrite Hv0 in Hv'; injection Hv' as <-.
  assert (m = v0) as -> by (eapply functional_eval_exp; eassumption).
  destruct (tele_insts_nth _ _ _ _ _ HT0) as (A0 & HA0 & ET0).
  rewrite HA in HA0; injection HA0 as <-.
  assert (Hk : k < List.length vs) by (apply List.nth_error_Some; congruence).
  destruct (per_gargs_nth _ _ _ _ _ _ _ Hpg HA Hk) as (i' & R & a1 & a2 & Ea1 & Ea2 & HR).
  (** The value of the instance, against the type at the values before it. *)
  destruct (ctx_rev_split C k _ HA) as (C1 & Pre & EC & HPl).
  assert (HPa : tele_ass Pre) by (rewrite EC in Hass; unfold tele_ass in Hass; apply List.Forall_app in Hass as [_ H']; inversion H'; assumption).
  pose proof HC as HC1; rewrite EC in HC1; pose proof (Completeness.UnitCases.rel_ctx_wf_app_r _ _ HC1) as HC2.
  destruct (Completeness.Modules.MemberTypes.rel_ctx_wf_ass_inv HC2) as [j HAj].
  pose proof (rel_ctx_wf_tail HC2) as HPre.
  pose proof (closed_app_valid Pre Γ _ A A HPa HPre HΓ HAj) as HAj'.
  assert (Hle : List.length Pre <= List.length Ms) by (rewrite Hl, EC, List.length_app; cbn; lia).
  rewrite EC in HMs; replace (C1 ++ ce_ass A :: Pre) with ((C1 ++ ce_ass A :: nil) ++ Pre) in HMs by (rewrite <- List.app_assoc; reflexivity).
  pose proof (tele_typed_prefix _ _ _ _ HPa Hle HMs) as HMs'.
  assert (Lf : List.length (List.firstn (List.length Pre) Ms) = List.length Pre) by (rewrite List.length_firstn; lia).
  pose proof (gsub_closed_inst Pre Γ _ HPa HPre HΓ Lf HMs') as Hgs.
  pose proof (Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id ρ) (eval_exps_firstn _ _ _ (List.length Pre) Hv)) as Hevτ.
  destruct (typ_inst_link _ _ _ _ _ _ _ _ _ HAj' HRΓ (Completeness.LogicalRelation.Instance.gsub_valid Hgs) Hρ Hevτ)
    as (a' & b' & Ea' & Eb' & Hab).
  rewrite HPl in Ea', Eb'; rewrite <- ET0 in Ea'.
  assert (a' = a) as -> by (eapply functional_eval_exp; eassumption).
  assert (b' = a1) as -> by (eapply functional_eval_exp; eassumption).
  assert (Hlink : Dom a ≈ a2 ∈ per_univ j) by (eapply per_univ_trans'; [ exact Hab | exists R; exact HR ]).
  destruct (glu_transfer_per_elem i j a a2 P El Δ T0[σ] N[σ] v0 Hgl Hlink ltac:(eapply glu_univ_elem_trm_typ; eassumption) HNg)
    as (k' & P' & El' & Hg' & HP' & HM').
  apply (mk_glu_arg _ _ _ _ _ _ k' a2 P' El'); assumption.
Qed.

(** A closed telescope's type at the same arguments over two bases: related
    values. *)
Lemma closed_typ_base : forall C A (i : nat) zs B1 B2, tele_ass C -> ⊨ C -> C ⊨ A : Typeω@i ->
    List.length zs = List.length C -> per_gargs (List.rev C) nil nil zs zs ->
    exists a b, ⟦ A ⟧ env_args B1 zs ↘ a /\ ⟦ A ⟧ env_args B2 zs ↘ b /\ Dom a ≈ b ∈ per_univ i.
Proof.
  intros * Hass HC HA Hl Hg.
  destruct (rel_ctx_wf_per_ctx_env HC) as [RC HRC].
  pose proof (gargs_env_rel _ _ _ _ _ _ HRC HC Hl Hg) as H0.
  pose proof (closed_env_base C RC zs zs nil nil B1 B2 Hass HC HRC Hl Hl H0) as H1.
  exact (rel_exp_of_typ_inversion_simple_at HRC HA _ _ H1).
Qed.

(** A list instance followed by a substitution, below the list's length:
    the instance of the substituted list. *)
Lemma sb_of_list_map_nth : forall Is τ x, x < List.length Is ->
    (sb_of_list Id Is ⨟ τ) x = sb_of_list Id (List.map (fun I => I[τ]) Is) x.
Proof.
  intros * Hx; cbn [sb_compose].
  rewrite (sb_of_list_nth Is Id x (a_var 0) Hx), (sb_of_list_nth _ Id x (a_var 0)) by (rewrite List.length_map; exact Hx).
  cbn [sentry_sub]; rewrite List.length_map.
  rewrite (List.nth_indep (List.map (fun I : typ => I[τ]) Is) (a_var 0) ((a_var 0)[τ])) by (rewrite List.length_map; lia).
  rewrite (List.map_nth (fun I : typ => I[τ])); reflexivity.
Qed.

(** The entry of a constructor's argument, last in a prefix. *)
Lemma cargs_ctx_last : forall p D M gs gsA g gsB, gs = gsA ++ g :: gsB ->
    exists G, cargs_ctx p D M (gsA ++ g :: nil) = ce_ass G :: cargs_ctx p D M gsA /\
      List.nth_error (List.rev (cargs_ctx p D M gs)) (List.length gsA) = Some (ce_ass G).
Proof.
  intros * Heq; destruct g as [B | t];
    [ exists B[wk_pat (cargs_pat gsA)]ʷ | exists (ptyp_ty p D (im_nn M) (cargs_pat gsA) t) ];
    (split; [ unfold cargs_ctx; rewrite cargs_ctx_aux_app, List.app_nil_r; reflexivity |]);
    [ exact (cargs_rev_nth_arg p D M gs gsA B gsB Heq) | exact (cargs_rev_nth_rec p D M gs gsA t gsB Heq) ].
Qed.

(** The list instance [q^n] of a substitution, then a list instance of
    [Us ++ Ns] with [n] the length of [Ns], is the list instance of the
    substituted list and [Ns], below the lengths. *)
Lemma sb_qn_list_agree : forall Is Us Ns x, x < List.length Ns + List.length Is ->
    (sb_qn (List.length Ns) (sb_of_list Id Is) ⨟ (sb_of_list Id (Us ++ Ns) ⨟ Id)) x
    = sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) x.
Proof.
  intros * Hx.
  transitivity ((sb_qn (List.length Ns) (sb_of_list Id Is) ⨟ sb_of_list Id (Us ++ Ns)) x);
    [ cbn [sb_compose]; apply sentry_sub_sb_eq, sb_compose_id_right |].
  rewrite (sb_of_list_app Us Ns Id), (sb_of_list_app _ Ns Id).
  rewrite (sb_qn_of_list Ns (sb_of_list Id Is) (sb_of_list Id Us) x).
  destruct (Nat.lt_ge_cases x (List.length Ns)) as [Hlt | Hge].
  - rewrite !(sb_of_list_nth Ns _ x (a_var 0) Hlt); reflexivity.
  - replace x with (List.length Ns + (x - List.length Ns)) by lia; rewrite !sb_of_list_ge.
    apply sb_of_list_map_nth; lia.
Qed.

(** ** A View's Parameters and Arguments, at its Container's Telescopes *)

Section ViewConArgs.
  Variable (VP : qname -> ind_decl -> Prop).
  Variables (p : qname) (D : ind_decl).
  Hypotheses (HVP : valid_groups VP) (HPD : VP p D) (HG : glu_ind_decl D).
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hg.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (Dq : ind_decl).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some Dq).
  Let HgQ := Hcv _ _ _ _ _ _ _ HMk Hh Hq.
  Let HcQ := vgr_closed _ _ HgQ.

  Lemma view_is_length : List.length Is = ind_nu Dq.
  Proof.
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (D2 & Mk' & Hl2 & _ & _ & HIl & _).
    rewrite Hq in Hl2; injection Hl2 as <-; exact HIl.
  Qed.

  (** The view's instance of the container's uniform parameters, at glued
      uniform parameters of the group. *)
  Lemma view_uparams_glu : forall Δ Us ups cs, ⊢ Δ -> glu_args Δ (ind_uparams D) Id nil Us ups ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (ind_uparams Dq) Id nil (List.map (fun I => I[sb_of_list Id Us]) Is) cs.
  Proof.
    intros * HΔ HUs Ecs.
    pose proof (gid_params _ HG _ _ HMk) as [SbP HSbP].
    unfold im_params in HSbP.
    destruct (glu_ctx_env_suffix _ _ _ (gta_nparams _ Hass _ _ HMk) HSbP) as [SbU HSbU].
    assert (Hσ : Δ ⊢ˢ sb_of_list Id Us ® env_args nil ups ∈ SbU).
    { eapply glu_sub_of_list with (C := ind_uparams D) (Γ0 := ⋅) (Sb0 := nil_glu_sub_pred);
        [ exact (dc_ass _ Hc) | rewrite List.app_nil_r; exact HSbU | econstructor; [ reflexivity | eapply ctx_wf_gctx; exact HΔ ]
        | cbn; apply wf_sub_nil'; exact HΔ | exact HUs ]. }
    destruct (rel_ctx_wf_per_ctx_env (vid_uparams _ HD)) as [RU HRU].
    eapply params_glu_args with (Γ := ind_uparams D) (RΓ := RU) (Sb := SbU) (ρ := env_args nil ups);
      [ exact (dc_ass _ HcQ) | exact (dc_uparams _ HcQ) | exact (vid_uparams _ (vgr_valid _ _ HgQ)) | exact (vid_uparams _ HD)
      | exact HRU | exact HSbU | exact Hσ | exact view_is_length | | | exact Ecs ].
    - intros j I T HI HT; exact (vg_view_is p D Hg Hcv _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI HT).
    - intros j I T HI HT; exact (gid_view_is _ HG _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HI HT).
  Qed.

  (** The types of a non-uniform parameter of a member of the container
      and of the group's member the view takes it to, at the group's
      [ups] and the container's instance [cups] there: related values. *)
  Lemma view_nparam_types : forall ups cups i' Mi' v Mv, per_gargs (List.rev (ind_uparams D)) nil nil ups ups ->
      List.length ups = ind_nu D -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups ->
      ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      forall j vs G C, List.length vs = j ->
        List.nth_error (List.rev (im_nparams Mv)) j = Some (ce_ass G) -> List.nth_error (List.rev (im_nparams Mi')) j = Some (ce_ass C) ->
        per_gargs (List.firstn j (List.rev (im_nparams Mv))) (env_args nil ups) (env_args nil ups) vs vs ->
        per_gargs (List.firstn j (List.rev (im_nparams Mi'))) (env_args nil cups) (env_args nil cups) vs vs ->
        exists b a (i : nat), ⟦ G ⟧ env_args (env_args nil ups) vs ↘ b /\ ⟦ C ⟧ env_args (env_args nil cups) vs ↘ a /\
          Dom b ≈ a ∈ per_univ i.
  Proof.
    intros ups cups i' Mi' v Mv Hgu Hu Ecups HMi' Hv HMv j vs G C Hlv HeG HeC Hgg Hgc.
    pose proof (view_cups_rel p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq ups cups Hgu Hu Ecups) as Hcr.
    pose proof (length_cups p D Hg k Mk qc kc Is vm Dq HMk Hh Hq ups cups Ecups) as Hlc.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (vgr_valid _ _ HgQ) as HDQ.
    set (tc := List.rev (im_nparams Mi')) in *; set (tg := List.rev (im_nparams Mv)) in *.
    assert (Hlr : j <= List.length tc) by (assert (j < List.length tc) by (apply List.nth_error_Some; congruence); lia).
    (** The container's telescope, from no base to the instance's. *)
    pose proof (vid_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (Hlc' : List.length cups = List.length (ind_uparams Dq)) by (rewrite Hlc; reflexivity).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups)) by exact (gargs_env_rel _ _ _ _ _ _ HRQ HUQ Hlc' Hcr).
    assert (HQ1 : RQ (env_args nil cups) (env_args (env_args nil ups) cups))
      by exact (closed_env_base _ _ _ _ _ _ _ _ (dc_ass _ HcQ) HUQ HRQ Hlc' Hlc' HQ0).
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass Dq HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams Dq) by (unfold tc; rewrite List.rev_involutive; exact (vid_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HDQ _ _ _ _ HMi' HA))).
    destruct (tele_base_change tc (ind_uparams Dq) RQ (env_args nil cups) (env_args (env_args nil ups) cups)
                Hac HWc0 HTc0 HRQ HQ1 j vs Hlv Hlr Hgc) as [Hg1 _].
    (** The two telescopes, equal under the view's instance. *)
    pose proof (vid_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams Dq)) by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (dc_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams Dq ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams Dq ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams Dq))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (dc_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (vid_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (vid_npar _ HD _ _ _ _ HMv HA))).
    assert (Heq : ind_uparams D ⊨ˣ tele_sub (List.rev tg) Id ≈ tele_sub (List.rev tc) (sb_of_list Id Is)).
    { unfold tg, tc; rewrite !List.rev_involutive, tele_sub_id.
      exact (vg_view_nparams p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv). }
    assert (Hlen : List.length tg = List.length tc) by (unfold tg, tc; rewrite !List.length_rev, !length_im_nparams; exact Hnn).
    destruct (Completeness.LogicalRelation.Instance.gsub_props (vg_view_args_gsub p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq)) as [Hτ _].
    pose proof (Decl.eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil ups)) Ecups) as Eτ.
    destruct (tele_link_types (ind_uparams D) RU (env_args nil ups) HRU HρU (ind_uparams D) (ind_uparams Dq ++ ind_uparams D)
                Id (sb_of_list Id Is) (env_args nil ups) (env_args (env_args nil ups) cups)
                (rel_sub_id (ex_intro _ _ HRU)) Hτ (eval_sub_id _) Eτ tg tc Hag Hac Hlen HWg HWc HTg HTc Heq
                j vs G C Hlv HeG HeC Hgg Hg1) as (i & R & b & a' & Eb & Ea' & Hba).
    (** The container's type, back at no base. *)
    destruct (HTc0 _ _ HeC) as [i0 HC0].
    assert (HaC1 : tele_ass (List.rev (List.firstn j tc) ++ ind_uparams Dq))
      by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (dc_ass _ HcQ) ]).
    assert (Hgz : per_gargs (List.rev (List.rev (List.firstn j tc) ++ ind_uparams Dq)) nil nil (cups ++ vs) (cups ++ vs)).
    { rewrite List.rev_app_distr, List.rev_involutive.
      apply Decl.per_gargs_app_intro; [ rewrite List.length_rev; exact Hlc | exact Hcr | exact Hgc ]. }
    destruct (closed_typ_base _ C i0 (cups ++ vs) nil (env_args nil ups) HaC1 (rel_ctx_wf_firstn _ _ j HWc0) HC0
                ltac:(rewrite !List.length_app, List.length_rev, List.length_firstn; lia) Hgz) as (a0 & b0 & Ea0 & Eb0 & Hab0).
    rewrite env_args_app in Ea0, Eb0.
    assert (b0 = a') as -> by (eapply functional_eval_exp; eassumption).
    exists b, a0, i; split; [ exact Eb | split; [ exact Ea0 |] ].
    exact (per_univ_trans' _ _ _ _ _ (ex_intro _ R Hba) (per_univ_sym' _ _ _ Hab0)).
  Qed.

  (** The view's non-uniform parameters, glued along the group's member's
      telescope at the view's uniform parameters, are glued along the
      container's at the view's instance. *)
  Lemma view_nparams_glu : forall Δ Us Ns ups ns cs i' Mi' v Mv, ⊢ Δ -> List.length ups = ind_nu D ->
      glu_args Δ (ind_uparams D) Id nil Us ups ->
      ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      glu_args Δ (im_nparams Mv) (sb_of_list Id Us) (env_args nil ups) Ns ns ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) (env_args nil cs) Ns ns.
  Proof.
    intros * HΔ Hu HUs HMi' Hv HMv HNs Ecs.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (dc_ass _ Hc) HUs) as Hgu.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (decl_closed_nparams_ass D Hc _ _ HMv) as HaV.
    pose proof (decl_closed_nparams_ass Dq HcQ _ _ HMi') as HaC.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HaV HNs) as Hgn.
    destruct (glu_args_length _ _ _ _ _ _ HUs) as [HUl _].
    destruct (glu_args_length _ _ _ _ _ _ HNs) as [HNl Hnl].
    apply (glu_args_transfer Δ (im_nparams Mv) (im_nparams Mi') (sb_of_list Id Us) _ (env_args nil ups) (env_args nil cs) Ns ns HaV HaC
             ltac:(rewrite !length_im_nparams; exact Hnn) HNs).
    - intros kk A A' a HA HA' Hk Ea Hpc.
      assert (Hpg : per_gargs (List.firstn kk (List.rev (im_nparams Mv))) (env_args nil ups) (env_args nil ups)
                      (List.firstn kk ns) (List.firstn kk ns)).
      { rewrite <- (List.firstn_skipn kk (List.rev (im_nparams Mv))), <- (List.firstn_skipn kk ns) in Hgn.
        assert (Hl1 : List.length (List.firstn kk ns) = List.length (List.firstn kk (List.rev (im_nparams Mv))))
          by (rewrite !List.length_firstn, List.length_rev; lia).
        exact (proj1 (Decl.per_gargs_app _ _ _ _ _ _ _ _ Hl1 Hgn Hl1)). }
      destruct (view_nparam_types ups cs i' Mi' v Mv Hgu Hu Ecs HMi' Hv HMv kk (List.firstn kk ns) A A'
                  ltac:(rewrite List.length_firstn; lia) HA HA' Hpg Hpc) as (b & a0 & i & Eb & Ea0 & Hba).
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a0, i; split; [ exact Ea0 | exact Hba ].
    - intros kk T T' HT HT'.
      pose proof (dt_view_nparams _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv) as Hext.
      assert (HσU : Δ ⊢ˢ sb_of_list Id Us : ind_uparams D).
      { apply (wf_uparams_sub _ _ _ _ _ Hdt HΔ HUl).
        intros; eapply glu_args_typed; [ exact (dc_ass _ Hc) | exact HUs | eassumption | eassumption ]. }
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ Hext HσU) as He.
      assert (EV : forall X, tele_insts (tele_sub X (sb_of_list Id Us)) Id Ns = tele_insts X (sb_of_list Id Us) Ns)
        by (intros; rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right).
      assert (EC : tele_insts (tele_sub (tele_sub (im_nparams Mi') (sb_of_list Id Is)) (sb_of_list Id Us)) Id Ns
                   = tele_insts (im_nparams Mi') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is)) Ns).
      { rewrite EV, tele_insts_tele_sub.
        apply (tele_insts_agree _ (ind_nu Dq)); [ exact HaC | exact (decl_closed_nparams_scoped Dq HcQ _ _ HMi') |].
        intros x Hx; rewrite <- view_is_length in Hx.
        exact (sb_of_list_map_nth Is (sb_of_list Id Us) x Hx). }
      rewrite <- EV in HT; rewrite <- EC in HT'.
      eapply (tele_insts_ext_eq Δ _ _ Ns He (tele_ass_sub _ _ HaV) (tele_ass_sub _ _ (tele_ass_sub _ _ HaC))
                ltac:(rewrite length_tele_sub; exact HNl)); [| exact HT | exact HT' ].
      intros j N T0 HN HT0; rewrite EV in HT0.
      eapply glu_args_typed; [ exact HaV | exact HNs | eassumption | eassumption ].
  Qed.

  Let HPq := valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq.
  Let HcvQ := containers_valid_of_groups VP HVP qc Dq HPq.

  (** The arguments of a constructor of the group's member the view takes a
      container's member to, glued along their telescope at the view's
      parameters, are glued along the container's at the view's instance. *)
  Lemma view_args_glu : forall Δ Us Ns As ups ns ws cs i' Mi' v Mv c gs' gs, ⊢ Δ -> List.length ups = ind_nu D ->
      ind_member Dq i' = Some Mi' -> List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
      ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs -> List.length Us = ind_nu D ->
      glu_args Δ (im_params D Mv) Id nil (Us ++ Ns) (ups ++ ns) ->
      glu_args Δ (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) (env_args nil (ups ++ ns)) As ws ->
      ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cs ->
      glu_args Δ (im_params Dq Mi') Id nil (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) (cs ++ ns) ->
      glu_args Δ (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns))
        (env_args nil (cs ++ ns)) As ws.
  Proof.
    intros * HΔ Hu HMi' Hv HMv Hcon' Hcon Hcorr HUl HgP HgA Ecs HgPc.
    pose proof (decl_closed_params_ass D v Mv Hc HMv) as HassP.
    pose proof (decl_closed_params_ass Dq i' Mi' HcQ HMi') as HassPc.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassP HgP) as HgPd.
    pose proof (glu_args_per_gargs _ _ _ _ _ _ HassPc HgPc) as HgPcd.
    destruct (glu_args_length _ _ _ _ _ _ HgP) as [LP LV]; rewrite length_im_params in LP, LV.
    destruct (glu_args_length _ _ _ _ _ _ HgA) as [LA LW]; rewrite length_cargs_ctx in LA, LW.
    assert (Hlns : List.length ns = im_nn Mv) by (rewrite List.length_app in LV; unfold im_np in LV; lia).
    assert (HlNs : List.length Ns = im_nn Mv) by (rewrite List.length_app in LP; unfold im_np in LP; lia).
    pose proof (cargs_corr_length _ _ _ Hcorr) as Hlg.
    assert (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil ups ups).
    { pose proof HgPd as H; rewrite rev_im_params in H.
      assert (L : List.length ups = List.length (List.rev (ind_uparams D))) by (rewrite List.length_rev; exact Hu).
      exact (proj1 (Decl.per_gargs_app (List.rev (ind_uparams D)) (List.rev (im_nparams Mv)) nil nil ups ups ns ns L H L)). }
    pose proof (glu_args_per_gargs _ _ _ _ _ _ (cargs_ctx_aux_ass _ _ _ _ _) HgA) as HgAd.
    apply (glu_args_transfer Δ (cargs_ctx p D Mv gs) (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (Us ++ Ns)) _
             (env_args nil (ups ++ ns)) (env_args nil (cs ++ ns)) As ws (cargs_ctx_aux_ass _ _ _ _ _) (cargs_ctx_aux_ass _ _ _ _ _)
             ltac:(rewrite !length_cargs_ctx; lia) HgA).
    - intros kk A A' a HA HA' Hk Ea Hpc.
      destruct (nth_error_lt_some' gs kk ltac:(lia)) as [g Hgk].
      destruct (List.nth_error_split _ _ Hgk) as (gsA & gsB & Egs & HlA).
      destruct (nth_error_lt_some' gs' kk ltac:(lia)) as [g' Hgk'].
      destruct (List.nth_error_split _ _ Hgk') as (gsA' & gsB' & Egs' & HlA').
      destruct (cargs_ctx_last p D Mv gs gsA g gsB Egs) as (G & HG1 & HG2).
      destruct (cargs_ctx_last qc Dq Mi' gs' gsA' g' gsB' Egs') as (Cc & HC1 & HC2).
      rewrite HlA in HG2; rewrite HG2 in HA; injection HA as <-.
      rewrite HlA' in HC2; rewrite HC2 in HA'; injection HA' as <-.
      set (vs := List.firstn kk ws) in *.
      assert (Hlvs : List.length vs = kk) by (unfold vs; rewrite List.length_firstn; lia).
      (** The arguments before, related at both telescopes. *)
      assert (Hg1 : per_gargs (List.rev (cargs_ctx p D Mv gsA ++ im_params D Mv)) nil nil (ups ++ ns ++ vs) (ups ++ ns ++ vs)).
      { pose proof HgAd as H.
        change (cargs_ctx_aux p D (im_nn Mv) nil gs) with (cargs_ctx p D Mv gs) in H.
        rewrite (cargs_split_aux p D Mv gs gsA g gsB Egs), List.rev_app_distr, <- (List.firstn_skipn kk ws) in H.
        assert (L1 : List.length vs = List.length (List.rev (cargs_ctx p D Mv gsA)))
          by (rewrite List.length_rev, length_cargs_ctx; lia).
        destruct (Decl.per_gargs_app _ _ _ _ _ _ _ _ L1 H L1) as [H1 _].
        rewrite List.rev_app_distr, List.app_assoc.
        apply Decl.per_gargs_app_intro; [ rewrite List.length_rev, length_im_params, List.length_app; unfold im_np in *; lia
                                        | exact HgPd | exact H1 ]. }
      assert (Hg2 : per_gargs (List.rev (cargs_ctx qc Dq Mi' gsA' ++ im_params Dq Mi')) nil nil (cs ++ ns ++ vs) (cs ++ ns ++ vs)).
      { assert (Ef : List.firstn kk (List.rev (cargs_ctx qc Dq Mi' gs')) = List.rev (cargs_ctx qc Dq Mi' gsA')).
        { rewrite (cargs_split_aux qc Dq Mi' gs' gsA' g' gsB' Egs'), List.rev_app_distr.
          apply firstn_app_exact; rewrite List.length_rev, length_cargs_ctx; lia. }
        rewrite Ef in Hpc.
        rewrite List.rev_app_distr, List.app_assoc.
        apply Decl.per_gargs_app_intro; [| exact HgPcd | exact Hpc ].
        destruct (glu_args_length _ _ _ _ _ _ HgPc) as [_ L]; rewrite List.length_rev; exact L. }
      destruct (view_arg_link p D Hg Hcv k Mk qc kc Is vm Dq HMk Hh Hq HcvQ ups cs Hgu Hu Ecs i' Mi' v Mv HMi' Hv HMv c gs' gs
                  Hcon' Hcon Hcorr ns Hlns gsA' g' gsB' gsA g gsB Cc G vs Egs' Egs ltac:(lia) ltac:(lia) HC1 HG1 Hg1 Hg2)
        as [_ _ _ (i & R & b & a0 & Eb & Ea0 & Hba)].
      rewrite List.app_assoc, env_args_app in Eb, Ea0.
      assert (b = a) as -> by (eapply functional_eval_exp; eassumption).
      exists a0, i; split; [ exact Ea0 | exists R; exact Hba ].
    - intros kk T T' HT HT'.
      pose proof (dt_view_args _ _ _ _ (ctx_wf_gctx _ _ _ HΔ) Hdt Hl _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hq HMi' Hv HMv Hcon' Hcon) as Hext.
      assert (Hσ0 : Δ ⊢ˢ sb_of_list Id (Us ++ Ns) : im_params D Mv).
      { rewrite <- (List.app_nil_r (im_params D Mv)).
        eapply wf_sub_of_list; [ exact HassP | rewrite List.app_nil_r; exact (member_params_wf _ _ _ _ _ Hdt HMv)
                               | exact (wf_sub_to_nil _ _ _ HΔ) | rewrite List.length_app, length_im_params; unfold im_np in *; lia |].
        intros; eapply glu_args_typed; [ exact HassP | exact HgP | eassumption | eassumption ]. }
      pose proof (sub_preserves_ext _ _ _ _ _ _ _ Hext Hσ0) as He.
      apply Views.ext_eq_sym_ass in He; [| apply tele_ass_sub, tele_ass_sub, cargs_ctx_aux_ass ].
      assert (EV : tele_insts (tele_sub (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns))) Id As
                   = tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Us ++ Ns)) As)
        by (rewrite tele_insts_tele_sub; apply tele_insts_sb_eq, sb_compose_id_right).
      assert (EC : tele_insts (tele_sub (tele_sub (cargs_ctx qc Dq Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id Is)))
                                 (sb_of_list Id (Us ++ Ns))) Id As
                   = tele_insts (cargs_ctx qc Dq Mi' gs') (sb_of_list Id (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)) As).
      { rewrite !tele_insts_tele_sub.
        apply (tele_insts_agree _ (im_np Dq Mi')); [ apply cargs_ctx_aux_ass
                                                   | exact (decl_closed_cargs_scoped Dq HcQ qc _ _ c gs' HMi' (cons_lookup_in _ _ _ Hcon')) |].
        intros x Hx; rewrite <- HlNs.
        apply sb_qn_list_agree; rewrite view_is_length; unfold im_np in Hx; rewrite HlNs; pose proof (vmb_nn_eq := view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq i' Mi' v Mv HMi' Hv HMv); lia. }
      rewrite <- EV in HT; rewrite <- EC in HT'.
      eapply (tele_insts_ext_eq Δ _ _ As He (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))
                (tele_ass_sub _ _ (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _)))
                ltac:(rewrite length_tele_sub, length_cargs_ctx; exact LA)); [| exact HT | exact HT' ].
      intros j N T0 HN HT0; rewrite EV in HT0.
      eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ].
  Qed.
End ViewConArgs.

(** ** The Constructor of a View *)

(** A constructor's value does not depend on the environment. *)
Lemma eval_con_env : forall p k c ρ ρ' m, ⟦ a_con p k c ⟧ ρ ↘ m -> ⟦ a_con p k c ⟧ ρ' ↘ m.
Proof. intros * H; inversion H; subst; [ eapply eval_exp_con | eapply eval_exp_con_view ]; eassumption. Qed.

(** The universes of a sort, below a large one. *)
Lemma sort_bound_of : forall D : ind_decl, ind_sort_univ (ind_sort D) ->
    exists n, forall ρ bu, ⟦ ind_sort D ⟧ ρ ↘ bu -> forall i, n <= i -> uidx_le (Completeness.Inductives.Decl.univ_idx bu) (ul i).
Proof.
  intros D Hsu; destruct Hsu as [[i0 Heq] | [t Heq]]; rewrite Heq; [ exists i0 | exists 0 ]; intros * Hb i Hi;
    inversion Hb; subst; cbn; [ lia | exact I ].
Qed.

(** The codomain of a view's constructor, at a list of terms: the
    container's member at the view's instance there. *)
Lemma view_ty_inst : forall p D k Mk qc kc Is vm τ Us Ns As, decl_closed D -> ind_member D k = Some Mk ->
    im_head Mk = mh_view qc kc Is vm -> List.length Us = ind_nu D -> List.length Ns = im_nn Mk ->
    (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length As)) (vars_from (List.length As) (im_nn Mk)))[sb_of_list τ (Us ++ Ns ++ As)]
    = apps (a_ind qc kc) (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns).
Proof.
  intros * Hc HMk Hh HUl HNl.
  unfold ind_mty; rewrite HMk; unfold im_ty_at, im_ref, im_pre; rewrite Hh; cbn [fst snd].
  rewrite apps_exp_sub; cbn [exp_sub]; f_equal.
  rewrite List.map_app; f_equal.
  - rewrite List.map_map; apply List.map_ext_in; intros I HI.
    pose proof (decl_closed_head_scoped D Hc _ _ _ _ _ _ HMk Hh) as HsIs.
    rewrite List.Forall_forall in HsIs.
    rewrite exp_sub_sub; apply (exp_scoped_sub_agree _ (ind_nu D)); [ exact (HsIs _ HI) |].
    intros x Hx; rewrite sb_of_list_map_nth by (unfold ind_uvars; rewrite length_vars_from; exact Hx).
    f_equal; unfold ind_uvars.
    replace (List.length As + im_nn Mk) with (List.length (Ns ++ As)) by (rewrite List.length_app; lia).
    rewrite <- HUl; exact (vars_from_sb_of_list_app Us (Ns ++ As) τ).
  - rewrite sb_of_list_app, <- HNl; exact (vars_from_sb_of_list_app Ns As (sb_of_list τ Us)).
Qed.

Section ConViewFT.
  Variable (VP : qname -> ind_decl -> Prop).
  Hypotheses (HVP : valid_groups VP) (HGall : forall qn G, VP qn G -> glu_ind_decl G)
    (Hviewsall : forall qn G, VP qn G -> glu_views_ok qn G).
  Variables (p : qname) (D : ind_decl).
  Hypothesis (HPD : VP p D).
  Let HG := HGall _ _ HPD.
  Let Hg := valid_groups_valid VP HVP p D HPD.
  Let Hcv := containers_valid_of_groups VP HVP p D HPD.
  Let Hl := vgr_lookup _ _ Hg.
  Let HD := vgr_valid _ _ Hg.
  Let Hc := vgr_closed _ _ Hg.
  Let Hsu := vgr_sort _ _ Hg.
  Let Hass := vgr_ass _ _ Hg.
  Let Hdt := vgr_typed _ _ Hg.
  Variables (k : nat) (Mk : imember) (qc : qname) (kc : nat) (Is : list exp) (vm : list nat) (c : String.string) (gs : list carg).
  Hypotheses (HMk : ind_member D k = Some Mk) (Hh : im_head Mk = mh_view qc kc Is vm) (Hcon : ind_con Mk c = Some gs)
    (HΨ : ⊩ cargs_ctx p D Mk gs ++ im_params D Mk).

  (** The constructor applied to glued parameters and arguments is glued at
      the type at the parameters: it is the container's at the view's
      instance. *)
  Lemma con_view_base : forall Dq Mkc pmc gs' (i : nat) Δ Ms vs w b P El, ind_lookup gc_deps gc_stack qc = Some Dq ->
      ind_member Dq kc = Some Mkc -> im_head Mkc = mh_decl pmc -> List.nth_error vm kc = Some k ->
      ind_con Mkc c = Some gs' -> cargs_corr vm gs' gs -> ⊢ Δ ->
      (forall ρ bu, ⟦ ind_sort Dq ⟧ ρ ↘ bu -> uidx_le (Completeness.Inductives.Decl.univ_idx bu) (ul i)) ->
      glu_args Δ (cargs_ctx p D Mk gs ++ im_params D Mk) Id nil Ms vs ->
      Completeness.Inductives.Con.con_value p D k Mk c vs w ->
      ⟦ ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)) ⟧ env_args nil vs ↘ b ->
      DG b ∈ glu_univ_elem i ↘ P ↘ El ->
      (forall R, DF b ≈ b ∈ per_univ_elem i ↘ R -> R w w) ->
      forall τ, Δ ⊢ apps (a_con p k c) Ms
        : (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))[sb_of_list τ Ms]
        ® w ∈ El.
  Proof.
    intros Dq Mkc pmc gs' i Δ Ms vs w b P El Hq HMkc Hhc Hvm Hcon' Hcorr HΔ Hbnd Hgall Hw Hb Hglu HPER τ.
    pose proof (valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq) as HPq.
    pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
    pose proof (vgr_closed _ _ HgQ) as HcQ.
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (cargs_corr_length _ _ _ Hcorr) as Hlg.
    pose proof (view_nn p D Hg k Mk qc kc Is vm Dq HMk Hh Hq kc Mkc k Mk HMkc Hvm HMk) as Hnn.
    pose proof (view_is_length VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq) as HIl.
    destruct (glu_args_length _ _ _ _ _ _ Hgall) as [LM LV]; rewrite List.length_app, length_cargs_ctx, length_im_params in LM, LV.
    set (Ps := List.firstn (im_np D Mk) Ms); set (As := List.skipn (im_np D Mk) Ms).
    set (ps := List.firstn (im_np D Mk) vs); set (ws := List.skipn (im_np D Mk) vs).
    assert (EM : Ms = Ps ++ As) by (symmetry; apply List.firstn_skipn).
    assert (EV : vs = ps ++ ws) by (symmetry; apply List.firstn_skipn).
    assert (LPs : List.length Ps = im_np D Mk) by (unfold Ps; rewrite List.length_firstn; lia).
    assert (Lps : List.length ps = im_np D Mk) by (unfold ps; rewrite List.length_firstn; lia).
    assert (LAs : List.length As = List.length gs) by (unfold As; rewrite List.length_skipn; lia).
    assert (Lws : List.length ws = List.length gs) by (unfold ws; rewrite List.length_skipn; lia).
    clearbody Ps As ps ws.
    subst Ms vs.
    apply glu_args_app in Hgall as [HgP HgA]; [| exact HassP | rewrite length_im_params; exact LPs | rewrite length_im_params; exact Lps ].
    set (Us := List.firstn (ind_nu D) Ps); set (Ns := List.skipn (ind_nu D) Ps).
    set (ups := List.firstn (ind_nu D) ps); set (ns := List.skipn (ind_nu D) ps).
    assert (EPs : Ps = Us ++ Ns) by (symmetry; apply List.firstn_skipn).
    assert (Eps : ps = ups ++ ns) by (symmetry; apply List.firstn_skipn).
    assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (Hu : List.length ups = ind_nu D) by (unfold ups; rewrite List.length_firstn; unfold im_np in *; lia).
    assert (HNl : List.length Ns = im_nn Mk) by (unfold Ns; rewrite List.length_skipn; unfold im_np in *; lia).
    assert (Hnl : List.length ns = im_nn Mk) by (unfold ns; rewrite List.length_skipn; unfold im_np in *; lia).
    clearbody Us Ns ups ns.
    subst Ps ps.
    pose proof HgP as HgP'; unfold im_params in HgP'.
    apply glu_args_app in HgP' as [HUs HNs]; [| exact (dc_ass _ Hc) | exact HUl | exact Hu ].
    (** The container's value, at the view's instance. *)
    inversion Hw as [pm' xs Hh0 | qc' kc' Is' vm' xs Hh0 Hlt | qc' kc' Is' vm' xs cs Hh0 Hle Ecs]; subst; rewrite Hh in Hh0;
      try discriminate; [ rewrite !List.length_app in Hlt; lia |].
    injection Hh0 as <- <- <- <-.
    rewrite <- List.app_assoc, firstn_app_exact in Ecs by exact Hu.
    rewrite <- List.app_assoc, skipn_app_exact in * by exact Hu.
    (** The parameters and arguments at the container's telescopes. *)
    pose proof (view_uparams_glu VP p D HVP HPD HG k Mk qc kc Is vm Dq HMk Hh Hq Δ Us ups cs HΔ HUs Ecs) as HUc.
    pose proof (view_nparams_glu VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq Δ Us Ns ups ns cs kc Mkc k Mk HΔ Hu HUs
                  HMkc Hvm HMk HNs Ecs) as HNc.
    assert (HPc : glu_args Δ (im_params Dq Mkc) Id nil (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) (cs ++ ns)).
    { unfold im_params; apply glu_args_app;
        [ exact (dc_ass _ HcQ) | rewrite List.length_map; exact HIl | rewrite (eval_exps_length _ _ _ Ecs); exact HIl |].
      split; [ exact HUc | exact HNc ]. }
    pose proof (view_args_glu VP p D HVP HPD k Mk qc kc Is vm Dq HMk Hh Hq Δ Us Ns As ups ns ws cs kc Mkc k Mk c gs' gs HΔ Hu
                  HMkc Hvm HMk Hcon' Hcon Hcorr HUl HgP HgA Ecs HPc) as HAc.
    assert (HgC : glu_args Δ (cargs_ctx qc Dq Mkc gs' ++ im_params Dq Mkc) Id nil
                    ((List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) ++ As) ((cs ++ ns) ++ ws)).
    { apply glu_args_app;
        [ exact (decl_closed_params_ass Dq kc Mkc HcQ HMkc)
        | rewrite List.length_app, List.length_map, length_im_params; unfold im_np, ind_nu in *; lia
        | rewrite List.length_app, (eval_exps_length _ _ _ Ecs), length_im_params; unfold im_np, ind_nu in *; lia |].
      split; [ exact HPc | exact HAc ]. }
    (** The container's type, related to the view's. *)
    set (b' := d_ind qc kc (cs ++ ns)).
    assert (Eb' : ⟦ ind_mty qc Dq kc (ind_uvars Dq (im_nn Mkc) (List.length gs')) (vars_from (List.length gs') (im_nn Mkc)) ⟧
                    env_args nil ((cs ++ ns) ++ ws) ↘ b').
    { unfold ind_mty; rewrite HMkc; unfold im_ty_at, im_ref, im_pre; rewrite Hhc; cbn [fst snd].
      apply Modules.eval_apps_exp; exists (d_ind qc kc nil), (cs ++ ns); split; [ constructor | split ].
      - unfold ind_uvars; rewrite vars_from_app.
        replace (List.length gs') with (List.length ws) by lia.
        replace (ind_nu Dq + im_nn Mkc) with (List.length (cs ++ ns))
          by (rewrite List.length_app, (eval_exps_length _ _ _ Ecs); lia).
        apply Decl.eval_vars_from_args.
      - change (d_ind qc kc (cs ++ ns)) with (d_ind qc kc (nil ++ (cs ++ ns))).
        apply (eval_apps_indty qc Dq kc Mkc (cs ++ ns) nil (vgr_lookup _ _ HgQ) HMkc).
        cbn; rewrite List.length_app, (eval_exps_length _ _ _ Ecs); unfold im_np; lia. }
    assert (Hbb : exists R, DF b ≈ b' ∈ per_univ_elem i ↘ R).
    { destruct (eval_mty_inv p D k Mk _ _ _ _ HMk Hb) as (cs0 & bs0 & Ecs0 & Ebs0 & ->).
      unfold im_ref in *; rewrite Hh in *; cbn [fst snd] in *.
      assert (Ebs0' : ⟦ vars_from (List.length gs) (im_nn Mk) ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ ns ++ ws) ↘ ns)
        by (rewrite env_args_app, <- Lws, <- Hnl; apply Decl.eval_vars_from_args).
      rewrite List.app_assoc in Ebs0.
      pose proof (functional_eval_exps' _ _ _ _ Ebs0 ltac:(rewrite <- List.app_assoc; exact Ebs0')) as ->.
      set (Z := cargs_ctx p D Mk gs ++ im_nparams Mk).
      assert (HZ : ⊨ Z ++ ind_uparams D)
        by (unfold Z; rewrite <- List.app_assoc; exact (vg_cargs_sem p D Hg Hcv k Mk c gs HMk Hcon)).
      destruct (rel_ctx_wf_per_ctx_env HZ) as [RZ HRZ].
      assert (HlZ : List.length (ns ++ ws) = List.length Z)
        by (unfold Z; rewrite !List.length_app, length_cargs_ctx, length_im_nparams; lia).
      assert (HE : RZ (env_args nil (ups ++ ns ++ ws)) (env_args nil (ups ++ ns ++ ws))).
      { apply (gargs_env_rel _ _ _ _ _ _ HRZ HZ); [ rewrite !List.length_app, <- HlZ, !List.length_app; unfold ind_nu in *; lia |].
        unfold Z; replace ((cargs_ctx p D Mk gs ++ im_nparams Mk) ++ ind_uparams D) with (cargs_ctx p D Mk gs ++ im_params D Mk)
          by (unfold im_params; rewrite List.app_assoc; reflexivity).
        replace (ups ++ ns ++ ws) with ((ups ++ ns) ++ ws) by (rewrite List.app_assoc; reflexivity).
        apply (glu_args_per_gargs _ Δ Id nil ((Us ++ Ns) ++ As) _
                 ltac:(apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ])).
        apply glu_args_app; [ exact HassP | rewrite List.length_app, length_im_params; unfold im_np in *; lia
                            | rewrite List.length_app, length_im_params; unfold im_np in *; lia |].
        split; [ exact HgP | exact HgA ]. }
      destruct (view_pre_values p D Hg Hcv k Mk qc kc Is vm Dq ups Z RZ (ns ++ ws) (im_nn Mk) (List.length gs) cs0 HMk Hh Hq Hu
                  (glu_args_per_gargs _ _ _ _ _ _ (dc_ass _ Hc) HUs) HZ HRZ HlZ ltac:(rewrite List.length_app; lia) HE Ecs0)
        as (cups & Ecups & Hgc).
      pose proof (functional_eval_exps' _ _ _ _ Ecups Ecs) as ->.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
      assert (Hl0 : List.length cs0 = ind_nu Dq)
        by (destruct (Decl.per_gargs_length _ _ _ _ _ Hgc) as [L1 L2]; pose proof (eval_exps_length _ _ _ Ecs);
            rewrite ?List.length_rev in *; unfold ind_nu in *; lia).
      destruct (per_univ_elem_ind_canon _ _ _ _ _ _ _ _ _ HRb (vgr_lookup _ _ HgQ) Hl0 Hl0) as [_ _ _ _ _ _ Hns _].
      unfold member_nparams in Hns; rewrite HMkc in Hns.
      pose proof (vgr_valid _ _ HgQ) as HDQ.
      pose proof (uparams_sym Dq HDQ HcQ _ _ Hgc ltac:(rewrite (eval_exps_length _ _ _ Ecs); exact HIl)) as Hgc'.
      destruct (sort_value Dq HDQ cs0 (uparams_refl_l Dq HDQ HcQ _ _ Hgc') Hl0) as [aq Eaq].
      pose proof (ind_relate Dq HDQ HcQ (vgr_sort _ _ HgQ) qc (vgr_lookup _ _ HgQ) (vgr_ass _ _ HgQ) kc Mkc pmc cs0 cs ns ns aq
                    HMkc Hhc Hgc' Hl0 Eaq Hns) as Hrel.
      eexists; exact (per_univ_elem_cumu_uidx _ _ _ _ Hrel _ (Hbnd _ _ Eaq)). }
    destruct Hbb as [Rbb Hbb].
    pose proof (glu_univ_elem_resp_per_univ _ _ _ _ _ (ex_intro _ Rbb Hbb) Hglu) as Hglu'.
    assert (HPER' : forall R, DF b' ≈ b' ∈ per_univ_elem i ↘ R -> R (d_con qc kc c ((cs ++ ns) ++ ws)) (d_con qc kc c ((cs ++ ns) ++ ws))).
    { intros R HR.
      destruct (glu_univ_elem_per_univ _ _ _ _ Hglu) as [Rb HRb].
      pose proof (HPER _ HRb) as Hww; rewrite <- List.app_assoc.
      apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR Hbb).
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HRb Hbb); exact Hww. }
    (** The container's constructor. *)
    pose proof (con_base VP qc Dq HVP HPq (HGall _ _ HPq) (Hviewsall _ _ HPq) kc Mkc pmc c gs' HMkc Hhc Hcon' Δ
                  ((List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns) ++ As) ((cs ++ ns) ++ ws) (d_con qc kc c ((cs ++ ns) ++ ws))
                  i b' P El HΔ Hbnd HgC (Completeness.Inductives.Con.con_value_decl qc Dq kc Mkc c pmc _ Hhc) Eb' Hglu' HPER') as Hcc.
    rewrite (con_codomain_inst qc Dq kc Mkc pmc gs' HMkc Hhc)
      in Hcc by (rewrite !List.length_app, List.length_map; unfold im_np, ind_nu in *; lia).
    rewrite firstn_app_exact in Hcc by (rewrite List.length_app, List.length_map; unfold im_np, ind_nu in *; lia).
    replace (List.skipn (ind_nu D) ((ups ++ ns) ++ ws)) with (ns ++ ws)
      by (rewrite <- List.app_assoc, skipn_app_exact by exact Hu; reflexivity).
    rewrite <- !List.app_assoc in Hcc.
    rewrite <- LAs, (view_ty_inst p D k Mk qc kc Is vm τ Us Ns As Hc HMk Hh HUl HNl).
    eapply glu_univ_elem_trm_resp_exp_eq; [ exact Hglu | exact Hcc |].
    (** The two constructors' applications. *)
    pose proof (glu_univ_elem_trm_escape _ _ _ _ Hglu _ _ _ _ Hcc) as HtR.
    assert (HtL : Δ ⊢ apps (a_con p k c) (Us ++ Ns ++ As) : apps (a_ind qc kc) (List.map (fun I => I[sb_of_list Id Us]) Is ++ Ns)).
    { pose proof HgP as [_ _ _].
      pose proof (glu_args_params_top _ _ _ _ _ HassP (decl_closed_params D k Mk Hc HMk) HgP) as [_ HPty _].
      pose proof (wf_exp_eq_con_apps_member Δ p D k Mk c gs (Us ++ Ns) (Us ++ Ns) As As Hl HMk Hcon HΔ
                    ltac:(rewrite List.length_app; unfold im_np in *; lia) ltac:(rewrite List.length_app; unfold im_np in *; lia)
                    ltac:(intros j0 P0 P0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                          eapply HPty; eassumption)
                    LAs LAs
                    ltac:(intros j0 N0 N0' T0 H0 H0' HT0; rewrite H0 in H0'; injection H0' as <-; apply wf_exp_eq_refl;
                          eapply glu_args_typed; [ apply cargs_ctx_aux_ass | exact HgA | eassumption | eassumption ])) as H.
      rewrite firstn_app_exact, skipn_app_exact, <- List.app_assoc in H by exact HUl.
      unfold ind_mty in H; rewrite HMk in H; unfold im_ty_at, im_ref, im_pre in H; rewrite Hh in H; cbn [fst snd] in H.
      gen_presups; assumption. }
    symmetry.
    replace (List.map (fun I : typ => I[sb_of_list Id Us]) Is ++ Ns ++ As) with (im_pre Mk Us ++ Ns ++ As)
      by (unfold im_pre; rewrite Hh; reflexivity).
    eapply wf_exp_eq_con_view; [ exact Hl | exact HMk | exact Hh | exact HUl | exact HtL |].
    unfold im_pre; rewrite Hh; exact HtR.
  Qed.

  (** The constructor of a view is glued at its type. *)
  Lemma glu_rel_exp_con_view0 : forall (j0 : nat), ⋅ ⊢ con_ty p D k Mk gs : Typeω@j0 -> ⋅ ⊢ a_con p k c : con_ty p D k Mk gs ->
      ⋅ ⊩ a_con p k c : con_ty p D k Mk gs.
  Proof.
    intros j0 Hj Hcty.
    (** The container. *)
    destruct (dt_view _ _ _ Hdt _ _ _ _ _ _ HMk Hh) as (Dq & Mkc & Hq & HMkc & Hkd & _ & _ & Hvm & _).
    pose proof (valid_groups_containers VP HVP p D k Mk qc kc Is vm Dq HPD HMk Hh Hq) as HPq.
    pose proof (valid_groups_valid VP HVP qc Dq HPq) as HgQ.
    assert (Hhd : exists pmc, im_head Mkc = mh_decl pmc).
    { pose proof (proj2 (dt_order _ _ _ (vgr_typed _ _ HgQ) _ _ HMkc) Hkd) as Hd0.
      unfold im_is_decl in Hd0; destruct (im_head Mkc); [ eauto | discriminate ]. }
    destruct Hhd as [pmc Hhc].
    destruct (Completeness.Inductives.Con.view_con_container p D Hass Hdt k Mk qc kc Is vm Dq Mkc c gs HMk Hh Hq HMkc Hcon)
      as (gs' & Hcon' & Hcorr).
    pose proof (decl_closed_params_ass D k Mk Hc HMk) as HassP.
    pose proof (cons_lookup_in _ _ _ Hcon) as Hin.
    assert (HassC : tele_ass (cargs_ctx p D Mk gs ++ im_params D Mk)) by (apply List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact HassP ]).
    pose proof (cargs_ctx_closed p D k Mk c gs gs nil Hc HMk Hin (eq_sym (List.app_nil_r gs))) as HsC.
    destruct (sort_bound_of Dq (vgr_sort _ _ HgQ)) as [n0 Hn0].
    pose proof HΨ as [SbC HSbC].
    assert (HSbC0 : EG (cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅ ∈ glu_ctx_env ↘ SbC) by (rewrite List.app_nil_r; exact HSbC).
    destruct (glu_ctx_env_entries_valid _ _ _ HassC HSbC0 (Nat.max j0 n0)) as (i & Hji & HAents).
    assert (Hi : ⋅ ⊢ con_ty p D k Mk gs : Typeω@i) by (eapply lift_exp_ge; [| exact Hj ]; lia).
    assert (Hg0 : ⊢ᵍ gc_deps ⍮ gc_stack) by (eapply ctx_wf_gctx; exact (glu_ctx_env_wf_ctx HSbC)).
    eapply (glu_closed_const_by _ _ i (fun m0 => ⟦ a_con p k c ⟧ nil ↘ m0));
      [ reflexivity | intros; eapply con_ty_sub; eassumption | exact Hi
      | intros ρ; destruct (Completeness.Inductives.Con.con_value_start VP p D HVP HPD k Mk c HMk ρ) as (m0 & Em0 & _);
        exists m0; split; [ exact Em0 | eapply eval_con_env; exact Em0 ] |].
    intros Δ σ m0 Hσ Em0 a P El Ha Hglu.
    destruct (Completeness.Inductives.Con.con_value_start VP p D HVP HPD k Mk c HMk nil) as (m1 & Em1 & Hv1).
    assert (m1 = m0) as -> by (eapply functional_eval_exp; eassumption).
    assert (HΔ : ⊢ Δ) by exact (wf_sub_dom _ _ _ _ _ Hσ).
    pose proof Hi as Hi'; unfold con_ty in Hi'; rewrite <- ctx_pi_app in Hi'.
    destruct (ctx_pi_split_typed _ _ _ _ HassC Hi') as [HCs _].
    replace (con_ty p D k Mk gs) with ((con_ty p D k Mk gs)[σ]) by (eapply con_ty_sub; eassumption).
    unfold con_ty in Ha |- *; rewrite <- ctx_pi_app in Ha |- *.
    change (a_con p k c) with (apps (a_con p k c) nil).
    eapply (ctx_pi_glu_elem_by (Completeness.Inductives.Con.con_value p D k Mk c) (a_con p k c)
              ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅))
      with (Γb := ⋅) (Sb_b := nil_glu_sub_pred) (Sb := SbC) (xs := nil);
      [ reflexivity | | exact HassC | eapply glu_ctx_env_nil; [ reflexivity | exact Hg0 ] | exact HSbC0
      | exists nil; reflexivity
      | intros; eapply HAents; eassumption
      | intros; eapply HCs; eassumption
      | exact Hσ | reflexivity | exact Hv1 | | | | exact Ha | exact Hglu ].
    - intros Δ1 Γ' Sb' Δ' σ' xs x w HT HSb' Hσ' HlΓ Hw.
      assert (HL : List.length Γ' <= List.length ((cargs_ctx p D Mk gs ++ im_params D Mk) ++ ⋅)) by (rewrite HT, List.length_app; lia).
      apply (Completeness.Inductives.Con.con_value_step VP p D HVP HPD k Mk c gs HMk Hcon xs x w);
        [ rewrite List.app_nil_r, List.length_app, length_cargs_ctx, length_im_params in HL; lia | | exact Hw ].
      intros qc' kc' Is' vm' Hh' Hnu; rewrite Hh in Hh'; injection Hh' as <- <- <- <-.
      (** The uniform parameters are glued, so related. *)
      assert (EΓ : Γ' = ind_uparams D).
      { rewrite List.app_nil_r in HT; unfold im_params in HT; rewrite List.app_assoc in HT.
        pose proof (f_equal (@List.length _) HT) as HLT; rewrite !List.length_app in HLT.
        assert (Hd : List.length (cargs_ctx p D Mk gs ++ im_nparams Mk) = List.length Δ1)
          by (rewrite List.length_app in *; unfold ind_nu in *; lia).
        destruct (app_split_eq _ _ _ _ HT Hd) as [_ E]; exact (eq_sym E). }
      subst Γ'.
      destruct (rel_ctx_wf_per_ctx_env (vid_uparams _ HD)) as [RU HRU].
      pose proof (glu_ctx_env_per_env HSb' HRU Hσ') as HE.
      assert (Hlen : List.length (xs ++ x :: nil) = ind_nu D) by (rewrite List.length_app; cbn; lia).
      pose proof (uparams_of_env D HD Hc _ _ RU HRU Hlen Hlen HE) as Hgu.
      destruct (vg_view_args_values p D Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq _ _ Hgu Hlen) as (cs & _ & Ecs & _ & _).
      exists cs; exact Ecs.
    - cbn [apps_exp]; rewrite ctx_pi_app.
      change (ctx_pi (im_params D Mk) (ctx_pi (cargs_ctx p D Mk gs)
                (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk)))))
        with (con_ty p D k Mk gs).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hcty Hσ) as Hcσ; cbn [exp_sub] in Hcσ; exact Hcσ.
    - intros R a' Ha' HR.
      destruct (rel_exp_under_ctx_simple (completeness_fundamental_exp _ _ _ Hcty)) as (env_rel & Henv & j' & Hsimp).
      assert (Hnil : env_rel nil nil) by (inversion Henv; subst; match goal with H : _ <~> _ |- _ => apply H; exact I end).
      destruct (Hsimp _ _ Hnil) as (a1 & a2 & R1 & Ha1 & Ha2 & HR1 & m1 & m2 & Hm1 & Hm2 & Hmm).
      unfold con_ty in Ha1; rewrite <- ctx_pi_app in Ha1.
      assert (a1 = a') as -> by (eapply functional_eval_exp; eassumption).
      assert (m1 = m0) as -> by (eapply functional_eval_exp; eassumption).
      assert (m2 = m0) as -> by (eapply functional_eval_exp; eassumption).
      assert (Ha2' : ⟦ ctx_pi (cargs_ctx p D Mk gs ++ im_params D Mk)
                       (ind_mty p D k (ind_uvars D (im_nn Mk) (List.length gs)) (vars_from (List.length gs) (im_nn Mk))) ⟧ nil ↘ a2)
        by (unfold con_ty in Ha2; rewrite <- ctx_pi_app in Ha2; exact Ha2).
      assert (a2 = a') as -> by (eapply functional_eval_exp; eassumption).
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR1 HR); exact Hmm.
    - intros Δ' φ Ms vs w' Hφ Hga Hw' b P' El' Hb Hglub HPb; cbn [List.map List.app] in *.
      assert (HΔ' : ⊢ Δ') by (eapply kripke_dom; eassumption).
      apply (glu_args_closed_base _ _ _ Id _ _ _ HassC HsC) in Hga.
      eapply (con_view_base Dq Mkc pmc gs' i); [ exact Hq | exact HMkc | exact Hhc | exact Hvm | exact Hcon' | exact Hcorr
                                               | exact HΔ' | | exact Hga | exact Hw' | exact Hb | exact Hglub | exact HPb ].
      intros; eapply Hn0; [ eassumption | lia ].
  Qed.
End ConViewFT.

End Fixed_GCtx.
