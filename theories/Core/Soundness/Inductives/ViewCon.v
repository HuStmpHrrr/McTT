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
  destruct (glu_transfer_per' i j a a2 P El Δ T0[σ] N[σ] v0 Hgl Hlink ltac:(eapply glu_univ_elem_trm_typ; eassumption) HNg)
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

End Fixed_GCtx.
